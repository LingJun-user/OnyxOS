// DevLink: a virtio-serial port the host can drive (batch 17).
//
// qemu's virt machine has eight virtio-mmio slots.  Slot 0 carries the
// disk; `make dev' puts a virtio-serial device in slot 1 and connects its
// port to a UNIX socket on the host.  Plain `make qemu' leaves the slot
// empty, in which case this driver does nothing and /dev/agent simply has
// no backend: reads fail, so user/agent.c exits instead of blocking.
//
// The protocol above the byte stream lives entirely in user space
// (user/agent.c and tools/onyxctl.py); the kernel only moves bytes:
//   - receiveq (0): the driver posts buffers, the device fills them, the
//     interrupt copies the bytes into a small FIFO for agentread().
//   - transmitq (1): agentwrite() copies bytes into a descriptor and waits
//     until the interrupt reports it consumed.
// No multiport, no control queue: one port, two queues, the simplest shape
// that satisfies the spec.

#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "defs.h"
#include "fs.h"
#include "file.h"
#include "virtio.h"

#define R(r) ((volatile uint32 *)(VIRTIO1 + (r)))

#define AGENT_BUFSZ 4096 // one frame plus its header must fit
// Must comfortably exceed one protocol body (64 KiB): the device pushes
// bytes as fast as the host writes them, and there is no way to throttle
// qemu's virtio-serial frontend.  A slow reader that fills this buffer
// would lose bytes and desynchronise the frames, so the size is part of
// the contract, not a tuning knob.
#define AGENT_FIFO (128 * 1024)

static struct devlink {
  int present;
  struct spinlock lock;

  // one descriptor table and pair of rings per queue
  struct virtq_desc *rxdesc;
  struct virtq_avail *rxavail;
  struct virtq_used *rxused;
  struct virtq_desc *txdesc;
  struct virtq_avail *txavail;
  struct virtq_used *txused;

  uint16 rx_used_idx;
  uint16 tx_used_idx;
  char free[NUM]; // transmit descriptors not in flight

  // DMA buffers the descriptors point at.  Static, because the device
  // keeps the physical addresses across interrupts.
  char rxbuf[NUM][AGENT_BUFSZ];
  char txbuf[NUM][AGENT_BUFSZ];

  // Bytes received but not yet read.  Monotonic counters, indexed modulo
  // AGENT_FIFO; r == w means empty.
  char fifo[AGENT_FIFO];
  uint64 fifo_r;
  uint64 fifo_w;
  uint64 fifo_drop;

  // agentread() copies through this scratch buffer so that copyout() runs
  // without the lock; the flag makes a second concurrent reader fail
  // instead of racing for the buffer.
  char readbuf[AGENT_BUFSZ];
  int reading;
} dev;

int agentread(int, uint64, int);
int agentwrite(int, uint64, int);

static int
probe(void)
{
  return *R(VIRTIO_MMIO_MAGIC_VALUE) == 0x74726976 &&
         *R(VIRTIO_MMIO_VERSION) == 2 &&
         *R(VIRTIO_MMIO_DEVICE_ID) == VIRTIO_ID_CONSOLE &&
         *R(VIRTIO_MMIO_VENDOR_ID) == 0x554d4551;
}

// Describe one queue and program its ring addresses.  Returns 0 on
// success, -1 if the device does not offer a queue this big.
static int
setup_queue(int sel, struct virtq_desc **desc, struct virtq_avail **avail,
            struct virtq_used **used)
{
  *R(VIRTIO_MMIO_QUEUE_SEL) = sel;
  if (*R(VIRTIO_MMIO_QUEUE_READY))
    return -1;
  uint32 max = *R(VIRTIO_MMIO_QUEUE_NUM_MAX);
  if (max < NUM) {
    printk("devlink: queue %d has %u descriptors, need %d\n", sel, max, NUM);
    return -1;
  }

  *desc = kalloc();
  *avail = kalloc();
  *used = kalloc();
  if (*desc == 0 || *avail == 0 || *used == 0)
    panic("devlink: kalloc");
  memset(*desc, 0, PGSIZE);
  memset(*avail, 0, PGSIZE);
  memset(*used, 0, PGSIZE);

  *R(VIRTIO_MMIO_QUEUE_NUM) = NUM;
  *R(VIRTIO_MMIO_QUEUE_DESC_LOW) = (uint64)*desc;
  *R(VIRTIO_MMIO_QUEUE_DESC_HIGH) = (uint64)*desc >> 32;
  *R(VIRTIO_MMIO_DRIVER_DESC_LOW) = (uint64)*avail;
  *R(VIRTIO_MMIO_DRIVER_DESC_HIGH) = (uint64)*avail >> 32;
  *R(VIRTIO_MMIO_DEVICE_DESC_LOW) = (uint64)*used;
  *R(VIRTIO_MMIO_DEVICE_DESC_HIGH) = (uint64)*used >> 32;
  *R(VIRTIO_MMIO_QUEUE_READY) = 0x1;
  return 0;
}

// Give one receive buffer back to the device.  Caller holds dev.lock.
static void
rx_post(uint16 id)
{
  struct virtq_desc *d = &dev.rxdesc[id];

  d->addr = (uint64)dev.rxbuf[id];
  d->len = AGENT_BUFSZ;
  d->flags = VRING_DESC_F_WRITE;
  d->next = 0;

  dev.rxavail->ring[dev.rxavail->idx % NUM] = id;
  io_fence();
  dev.rxavail->idx += 1;
}

// Caller holds dev.lock.
static int
alloc_desc(void)
{
  for (int i = 0; i < NUM; i++) {
    if (dev.free[i]) {
      dev.free[i] = 0;
      return i;
    }
  }
  return -1;
}

// Caller holds dev.lock.
static void
fifo_append(char *p, uint32 len)
{
  if (len > AGENT_BUFSZ)
    len = AGENT_BUFSZ;
  for (uint32 i = 0; i < len; i++) {
    if (dev.fifo_w - dev.fifo_r >= AGENT_FIFO) {
      // A slow reader is a bug in the agent, not a reason to block the
      // interrupt.  Drop and count; agentread() still makes progress.
      dev.fifo_drop++;
      return;
    }
    dev.fifo[dev.fifo_w % AGENT_FIFO] = p[i];
    dev.fifo_w++;
  }
}

void
virtio_console_init(void)
{
  uint32 status = 0, devlo, devhi;

  initlock(&dev.lock, "devlink");
  if (!probe())
    return; // plain `make qemu': slot 1 is empty

  dev.present = 1;

  *R(VIRTIO_MMIO_STATUS) = 0;
  *R(VIRTIO_MMIO_STATUS) = status |= VIRTIO_CONFIG_S_ACKNOWLEDGE;
  *R(VIRTIO_MMIO_STATUS) = status |= VIRTIO_CONFIG_S_DRIVER;

  // VIRTIO_F_VERSION_1 is bit 32, i.e. bit 0 of the high word.  Decline
  // every console feature: no multiport (we have exactly one port), no
  // size reports and no emergency write.
  devlo = *R(VIRTIO_MMIO_DEVICE_FEATURES);
  devhi = *R(VIRTIO_MMIO_DEVICE_FEATURES_HI);
  *R(VIRTIO_MMIO_DRIVER_FEATURES) = 0;
  *R(VIRTIO_MMIO_DRIVER_FEATURES_HI) = (devhi & 1) ? 1 : 0;
  (void)devlo;

  *R(VIRTIO_MMIO_STATUS) = status |= VIRTIO_CONFIG_S_FEATURES_OK;
  status = *R(VIRTIO_MMIO_STATUS);
  if (!(status & VIRTIO_CONFIG_S_FEATURES_OK)) {
    printk("devlink: device refused the feature set\n");
    dev.present = 0;
    return;
  }

  if (setup_queue(0, &dev.rxdesc, &dev.rxavail, &dev.rxused) < 0 ||
      setup_queue(1, &dev.txdesc, &dev.txavail, &dev.txused) < 0) {
    printk("devlink: device has no usable queue pair\n");
    dev.present = 0;
    return;
  }

  for (int i = 0; i < NUM; i++)
    dev.free[i] = 1;

  *R(VIRTIO_MMIO_STATUS) = status |= VIRTIO_CONFIG_S_DRIVER_OK;

  // Fill the receive queue only after DRIVER_OK: the device may start
  // writing into the buffers as soon as it sees them.
  for (int i = 0; i < NUM; i++)
    rx_post(i);
  io_fence();
  *R(VIRTIO_MMIO_QUEUE_NOTIFY) = 0;

  devsw[AGENT].read = agentread;
  devsw[AGENT].write = agentwrite;

  printk("devlink: virtio-serial ready, rxq=%d txq=%d descriptors=%d, "
         "features=%x:%x\n",
         NUM, NUM, NUM, devhi, devlo);
}

void
virtio_console_intr(void)
{
  int posted = 0;

  if (!dev.present)
    return;

  acquire(&dev.lock);
  *R(VIRTIO_MMIO_INTERRUPT_ACK) = *R(VIRTIO_MMIO_INTERRUPT_STATUS) & 0x3;
  io_fence();

  while (dev.rx_used_idx != dev.rxused->idx) {
    struct virtq_used_elem *e = &dev.rxused->ring[dev.rx_used_idx % NUM];

    fifo_append(dev.rxbuf[e->id], e->len);
    dev.rx_used_idx++;
    rx_post(e->id);
    posted = 1;
  }

  while (dev.tx_used_idx != dev.txused->idx) {
    struct virtq_used_elem *e = &dev.txused->ring[dev.tx_used_idx % NUM];

    dev.free[e->id] = 1;
    dev.tx_used_idx++;
  }
  release(&dev.lock);

  if (posted) {
    io_fence();
    *R(VIRTIO_MMIO_QUEUE_NOTIFY) = 0;
  }
  wakeup(&dev.fifo);
  wakeup(&dev.free[0]);
}

// Devsw read: return as soon as at least one byte is available, like the
// console.  A second concurrent reader gets -1 rather than sharing the
// scratch buffer.
int
agentread(int user_dst, uint64 dst, int n)
{
  int k, r, i;

  if (!dev.present)
    return -1;
  if (n <= 0)
    return 0;
  if (n > AGENT_BUFSZ)
    n = AGENT_BUFSZ;

  acquire(&dev.lock);
  if (dev.reading) {
    release(&dev.lock);
    return -1;
  }
  dev.reading = 1;
  while (dev.fifo_r == dev.fifo_w && dev.present) {
    sleep_prepare(&dev.fifo);
    release(&dev.lock);
    sleep();
    acquire(&dev.lock);
  }
  if (!dev.present) {
    dev.reading = 0;
    release(&dev.lock);
    return -1;
  }
  k = dev.fifo_w - dev.fifo_r;
  if (k > n)
    k = n;
  for (i = 0; i < k; i++)
    dev.readbuf[i] = dev.fifo[(dev.fifo_r + i) % AGENT_FIFO];
  dev.fifo_r += k;
  release(&dev.lock);

  r = either_copyout(user_dst, dst, dev.readbuf, k);

  acquire(&dev.lock);
  dev.reading = 0;
  release(&dev.lock);
  return r < 0 ? -1 : k;
}

// Devsw write: split into descriptor-sized chunks and wait for each one to
// be consumed.  The agent sends at most one frame at a time and the volume
// is small, so synchronous writes keep the bookkeeping trivial.
int
agentwrite(int user_src, uint64 src, int n)
{
  int total = 0;

  if (!dev.present)
    return -1;

  while (total < n) {
    int chunk = n - total;
    int idx;

    if (chunk > AGENT_BUFSZ)
      chunk = AGENT_BUFSZ;

    acquire(&dev.lock);
    while ((idx = alloc_desc()) < 0) {
      sleep_prepare(&dev.free[0]);
      release(&dev.lock);
      sleep();
      acquire(&dev.lock);
    }
    release(&dev.lock);

    if (either_copyin(dev.txbuf[idx], user_src, src + total, chunk) < 0) {
      acquire(&dev.lock);
      dev.free[idx] = 1;
      release(&dev.lock);
      return total > 0 ? total : -1;
    }

    acquire(&dev.lock);
    dev.txdesc[idx].addr = (uint64)dev.txbuf[idx];
    dev.txdesc[idx].len = chunk;
    dev.txdesc[idx].flags = 0;
    dev.txdesc[idx].next = 0;
    dev.txavail->ring[dev.txavail->idx % NUM] = idx;
    io_fence();
    dev.txavail->idx += 1;
    io_fence();
    *R(VIRTIO_MMIO_QUEUE_NOTIFY) = 1;

    while (!dev.free[idx]) {
      sleep_prepare(&dev.free[0]);
      release(&dev.lock);
      sleep();
      acquire(&dev.lock);
    }
    release(&dev.lock);

    total += chunk;
  }
  return total;
}
