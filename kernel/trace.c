// Syscall flight recorder (batch 15).
//
// The kernel keeps a fixed ring of records at the syscall boundary.  It is
// off unless a process asks for it with tracectl(), so the default path
// costs one branch per syscall and nothing else.
//
// Writers are serialised by trace_lock so that two harts can never claim
// the same index or interleave the fields of one record.  Readers stay
// lock-free because panic() must be able to read the ring without taking a
// lock or allocating memory.  A writer marks its slot in progress (seq =
// 0), fills the record, publishes the final sequence, then advances the
// write index with a release store.  A reader copies a record and checks
// that its sequence did not change; a slot being overwritten is skipped
// rather than reported torn.  This is a diagnostic stream, not a reliable
// audit log.

#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "proc.h"
#include "syscall.h"
#include "trace.h"
#include "defs.h"

// The process table, defined in proc.c; only tracectl() walks it.
extern struct proc proc[NPROC];

static struct spinlock trace_lock;
static struct trace_entry tracebuf[TRACE_NENT];

// Records ever published since the last CLEAR.  A slot for record w lives
// at w % TRACE_NENT, so w - TRACE_NENT is the number of records that have
// been overwritten.
static uint64 trace_w;

void
traceinit(void)
{
  initlock(&trace_lock, "trace");
}

static const char *
trace_syscall_name(int num)
{
  switch (num) {
#define TRACE_CASE(n, s)                                                       \
  case n:                                                                      \
    return s;
    TRACE_SYSCALLS(TRACE_CASE)
#undef TRACE_CASE
  default:
    return "unknown";
  }
}

// Path-taking syscalls pass the path as argument 0.  The recorder copies it
// at the boundary so that a failed open still shows which name it tried.
int
trace_takes_path(int num)
{
  switch (num) {
  case SYS_open:
  case SYS_mknod:
  case SYS_unlink:
  case SYS_link:
  case SYS_mkdir:
  case SYS_chdir:
  case SYS_exec:
  case SYS_chmod:
  case SYS_chown:
    return 1;
  default:
    return 0;
  }
}

// Append one record.  The caller has already checked the process's trace
// flag; path may be null when the call has no path or it could not be read.
// The write lock is held only while filling one slot: it gives every record
// a unique index and sequence number, and keeps a slower writer from
// publishing over a newer one when the ring wraps.
void
trace_record(int num, int flags, uint64 ret, uint64 a0, uint64 a1, uint64 a2,
             const char *path)
{
  struct proc *p = myproc();
  struct proc *parent;
  struct trace_entry *e;
  uint64 w;

  if (p == 0)
    return;

  acquire(&trace_lock);
  w = trace_w;
  e = &tracebuf[w % TRACE_NENT];

  __atomic_store_n(&e->seq, 0, __ATOMIC_RELEASE);
  e->tick = p->u_ticks + p->k_ticks;
  e->ret = ret;
  e->args[0] = a0;
  e->args[1] = a1;
  e->args[2] = a2;
  e->pid = p->pid;
  // p->parent is only stable under wait_lock; this is a diagnostic field,
  // so a concurrent reparent shows the new parent rather than blocking
  // the syscall path on a lock.
  parent = p->parent;
  e->ppid = parent ? parent->pid : 0;
  e->uid = p->uid;
  e->syscall = num;
  e->mode = TRACE_MODE_SYSCALL;
  e->flags = flags;
  safestrcpy(e->path, path ? path : "", TRACE_PATH);
  __atomic_store_n(&e->seq, (uint32)(w + 1), __ATOMIC_RELEASE);
  __atomic_store_n(&trace_w, w + 1, __ATOMIC_RELEASE);
  release(&trace_lock);
}

static void
trace_printk(struct trace_entry *e)
{
  printk("trace: %d %d %s %s(", e->pid, e->ppid,
         (e->flags & TRACE_EXIT) ? "exit" : "enter",
         trace_syscall_name(e->syscall));
  if (e->path[0])
    printk("\"%s\"", e->path);
  else
    printk("%lx", e->args[0]);
  printk(",%lx,%lx)", e->args[1], e->args[2]);
  if (e->flags & TRACE_EXIT)
    printk(" = %ld", e->ret);
  printk("\n");
}

// panic() calls this after printing the reason.  No locks, no allocation:
// the ring may be mid-rewrite, in which case the dump is marked partial.
void
trace_panic_dump(struct proc *p)
{
  // Static, not stack: a panic has little stack left and is not reentrant.
  static struct trace_entry last[32];
  uint64 w, avail, i, oldest;
  int n = 0, shown, partial;

  if (p == 0 || p->trace == 0)
    return;

  w = __atomic_load_n(&trace_w, __ATOMIC_ACQUIRE);
  avail = w < TRACE_NENT ? w : TRACE_NENT;
  partial = w > TRACE_NENT;

  // Oldest to newest, so that a short dump reads in call order.
  for (i = 0; i < avail; i++) {
    struct trace_entry *e = &tracebuf[(w - avail + i) % TRACE_NENT];
    struct trace_entry tmp;
    uint32 s1, s2;

    s1 = __atomic_load_n(&e->seq, __ATOMIC_ACQUIRE);
    if (s1 == 0) {
      partial = 1;
      continue;
    }
    tmp = *e;
    s2 = __atomic_load_n(&e->seq, __ATOMIC_ACQUIRE);
    if (s1 != s2 || s2 == 0) {
      partial = 1;
      continue;
    }
    if (tmp.pid != p->pid)
      continue;
    last[n % 32] = tmp;
    n++;
  }

  if (n == 0)
    return;

  shown = n < 32 ? n : 32;
  printk("trace: last %d records for pid %d\n", shown, p->pid);
  oldest = (uint64)(n - shown);
  for (i = 0; i < (uint64)shown; i++)
    trace_printk(&last[(oldest + i) % 32]);
  if (partial)
    printk("trace: partial\n");
}

int
ktracectl(int op, int pid)
{
  struct proc *p, *cur = myproc();

  if (op == TRACE_CLEAR) {
    int i;

    if (cur->uid != 0)
      return -1;
    // The write lock waits for writers already inside trace_record(), so no
    // one can publish an index from before the clear afterwards.  Zeroing
    // the sequences also makes an in-flight reader skip every old slot
    // instead of returning records that the clear has just discarded.
    acquire(&trace_lock);
    for (i = 0; i < TRACE_NENT; i++)
      __atomic_store_n(&tracebuf[i].seq, 0, __ATOMIC_RELEASE);
    __atomic_store_n(&trace_w, 0, __ATOMIC_RELEASE);
    release(&trace_lock);
    return 0;
  }
  if (op != TRACE_ON && op != TRACE_OFF)
    return -1;

  // pid 0 means the caller itself, as with setpgid(0, ...).
  if (pid == 0) {
    acquire(&cur->lock);
    cur->trace = (op == TRACE_ON);
    release(&cur->lock);
    return 0;
  }

  // Same rule as signal(): root or the owner may control another process.
  for (p = proc; p < &proc[NPROC]; p++) {
    acquire(&p->lock);
    if (p->pid == pid && p->state != UNUSED &&
        (cur->uid == 0 || cur->uid == p->uid)) {
      p->trace = (op == TRACE_ON);
      release(&p->lock);
      return 0;
    }
    release(&p->lock);
  }
  return -1;
}

// Copy up to max records, oldest to newest, to user address uaddr.  A
// non-root caller only ever receives records with its own uid: filtering
// here, rather than trusting the reader, keeps other users' paths in the
// kernel.  *lost receives the number of records overwritten since CLEAR.
// No lock is held across copyout.
int
ktraceread(pagetable_t pagetable, uint64 psz, uint64 uaddr, int max,
           uint64 lostaddr)
{
  struct proc *cur = myproc();
  uint64 w, avail, start, lost, i;
  int n = 0;

  if (max < 0)
    return -1;

  w = __atomic_load_n(&trace_w, __ATOMIC_ACQUIRE);
  avail = w < TRACE_NENT ? w : TRACE_NENT;
  lost = w > TRACE_NENT ? w - TRACE_NENT : 0;

  if ((uint64)max > avail)
    max = (int)avail;
  start = w - (uint64)max;

  for (i = 0; i < (uint64)max; i++) {
    struct trace_entry *e = &tracebuf[(start + i) % TRACE_NENT];
    struct trace_entry tmp;
    uint32 s1, s2;

    s1 = __atomic_load_n(&e->seq, __ATOMIC_ACQUIRE);
    if (s1 == 0)
      continue;
    tmp = *e;
    s2 = __atomic_load_n(&e->seq, __ATOMIC_ACQUIRE);
    if (s1 != s2 || s2 == 0)
      continue;
    if (cur->uid != 0 && tmp.uid != cur->uid)
      continue;
    if (copyout(pagetable, psz, uaddr + (uint64)n * sizeof(tmp), (char *)&tmp,
                sizeof(tmp)) < 0)
      return -1;
    n++;
  }

  if (copyout(pagetable, psz, lostaddr, (char *)&lost, sizeof(lost)) < 0)
    return -1;
  return n;
}
