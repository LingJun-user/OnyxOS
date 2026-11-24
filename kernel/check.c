// Kernel invariant checker (batch 16).
//
// check() answers "is the kernel's own bookkeeping still self-consistent",
// not "did some test print FAIL".  It reads the process table, the page
// mappings a process owns, its open files, the inode table on disk, the
// block bitmap, the log header and the page allocator, compares each
// against the rule it is supposed to satisfy, and writes a text report.
//
// It never repairs anything: a diagnostic path that writes is a
// diagnostic path that can destroy the evidence.  It also never holds
// more than one lock at a time while touching process state (the one
// exception is wait_lock, which is only ever held to read p->parent) and
// never holds a lock across copyout.
//
// The report is a best-effort snapshot.  Other harts, or another process
// on this hart, can change everything between two lines of the scan, so a
// single violation can be a race rather than a bug.  Run it while the
// system is idle, which is what the dedicated tests do.

#include <stdarg.h>

#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "proc.h"
#include "fs.h"
#include "file.h"
#include "buf.h"
#include "stat.h"
#include "defs.h"

extern struct proc proc[NPROC];
extern struct spinlock wait_lock;
extern char end[]; // first address after the kernel image

#define CHECK_REPORT_MAX 4096
#define CHECK_MAX_VIOL   16 // recorded violations; the rest only counted
#define CHECK_MAX_ORPHAN 8  // orphan lines; the rest only counted

// The report buffer and the per-inode tables are static because a kernel
// stack page is too small for them.  One scan runs at a time, so a second
// caller is refused instead of corrupting the first caller's output.
static char rbuf[CHECK_REPORT_MAX];
static int rlen;
static int busy;

static int viol;    // violations found, including ones not recorded
static int shown;   // violations written to the report
static int orphans; // inodes with nlink 0 still in the table
static int orphan_shown;

// Counters for the `stats' line, filled in while scanning.
static int proc_live, proc_zombie, vma_live, fd_open;
static int inode_used, dir_count;
static uint64 bitmap_blocks, bitmap_inodes;
static uint64 kmem_nfree, kmem_walk, pages_live, pages_total, pages_kernel;

// Per-inode bookkeeping, indexed by inode number.  Only inodes below
// sb.ninodes are used, which mkfs keeps at NINODES.
static ushort dcount[NINODES];     // directory entries that name the inode
static short nlink_tab[NINODES];   // its nlink, or 0 for an orphan
static uchar itype[NINODES];       // its type, 0 for an unused slot
static ushort dir_up[NINODES];     // ".." of the directory
static ushort dir_from[NINODES];   // directory holding its non-dot entry
static ushort childcount[NINODES]; // subdirectories of each directory
static uchar have_dot[NINODES];
static uchar have_dotdot[NINODES];

// Data blocks start after the metadata: boot, superblock, log, inode and
// bitmap blocks.  mkfs computes nblocks = size - nmeta, so this is the
// boundary the kernel and the image already agree on.
static uint check_nmeta;

// -- report formatting ----------------------------------------------------

static void
rputc(int c)
{
  if (rlen < CHECK_REPORT_MAX - 1)
    rbuf[rlen++] = c;
}

static void
rputs(const char *s)
{
  while (*s)
    rputc(*s++);
}

static void
rnum(uint64 x, int base, int sign)
{
  static char digits[] = "0123456789abcdef";
  char tmp[20];
  int i = 0;

  if (sign && (long long)x < 0) {
    rputc('-');
    x = -(long long)x;
  }
  do {
    tmp[i++] = digits[x % base];
  } while ((x /= base) != 0);
  while (i > 0)
    rputc(tmp[--i]);
}

// A deliberately small subset of printk's formatter: %s, %d, %u, %x,
// %ld, %lu, %lx, %p and %%.  The report is bounded, so unknown
// conversions are copied through rather than interpreted.
static void
rvprintf(const char *fmt, va_list ap)
{
  int c, c0, c1;
  const char *s;

  for (int i = 0; fmt[i]; i++) {
    if (fmt[i] != '%') {
      rputc(fmt[i]);
      continue;
    }
    c0 = fmt[++i] & 0xff;
    c1 = fmt[i] ? fmt[i + 1] & 0xff : 0;
    if (c0 == 's') {
      s = va_arg(ap, const char *);
      rputs(s ? s : "(null)");
    } else if (c0 == 'd') {
      rnum(va_arg(ap, int), 10, 1);
    } else if (c0 == 'l' && c1 == 'd') {
      rnum(va_arg(ap, uint64), 10, 1);
      i++;
    } else if (c0 == 'u') {
      rnum(va_arg(ap, uint32), 10, 0);
    } else if (c0 == 'l' && c1 == 'u') {
      rnum(va_arg(ap, uint64), 10, 0);
      i++;
    } else if (c0 == 'x') {
      rnum(va_arg(ap, uint32), 16, 0);
    } else if (c0 == 'l' && c1 == 'x') {
      rnum(va_arg(ap, uint64), 16, 0);
      i++;
    } else if (c0 == 'p') {
      rputs("0x");
      rnum((uint64)va_arg(ap, void *), 16, 0);
    } else if (c0 == '%') {
      rputc('%');
    } else if (c0 == 0) {
      break;
    } else {
      c = c0;
      rputc('%');
      rputc(c);
    }
  }
}

__attribute__((format(printf, 1, 2))) static void
rprintf(const char *fmt, ...)
{
  va_list ap;

  va_start(ap, fmt);
  rvprintf(fmt, ap);
  va_end(ap);
}

// Record one violation.  Every violation counts, but only the first
// CHECK_MAX_VIOL are written: the point is to see several problems in one
// run, not to fill the buffer with one problem repeated.
__attribute__((format(printf, 1, 2))) static void
violation(const char *fmt, ...)
{
  va_list ap;

  viol++;
  if (shown >= CHECK_MAX_VIOL)
    return;
  shown++;
  rputs("violation: ");
  va_start(ap, fmt);
  rvprintf(fmt, ap);
  va_end(ap);
  rputc('\n');
}

static void
orphan(uint inum)
{
  orphans++;
  if (orphan_shown >= CHECK_MAX_ORPHAN)
    return;
  orphan_shown++;
  rprintf("orphan: inode %u has 0 links but still holds blocks\n", inum);
}

// -- read-only inode and directory access --------------------------------

static int
blk_ok(uint b)
{
  return b >= check_nmeta && b < sb.size;
}

static void
read_dinode(uint inum, struct dinode *d)
{
  struct buf *bp = bread(ROOTDEV, IBLOCK(inum, sb));

  memmove(d, bp->data + (inum % IPB) * sizeof(struct dinode), sizeof(*d));
  brelse(bp);
}

// The block holding logical block bn, without allocating and without
// trusting an address that is outside the image.  bmap() would allocate;
// check() must not.
static uint
bmap_raw(struct dinode *d, uint bn)
{
  struct buf *bp;
  uint addr, *a;

  if (bn < NDIRECT)
    return d->addrs[bn];
  bn -= NDIRECT;
  if (bn >= NINDIRECT)
    return 0;
  if (d->addrs[NDIRECT] == 0 || !blk_ok(d->addrs[NDIRECT]))
    return 0;
  bp = bread(ROOTDEV, d->addrs[NDIRECT]);
  a = (uint *)bp->data;
  addr = a[bn];
  brelse(bp);
  return addr;
}

// Walk one directory's blocks and account for every entry.  Reading the
// raw blocks rather than going through iget()/ilock() keeps this strictly
// read-only: locking an inode whose nlink has just dropped to zero would
// let iput() truncate it, and a checker that repairs is a checker whose
// evidence is gone.
static void
scan_dir(uint inum, struct dinode *d)
{
  struct buf *bp;
  struct dirent de;
  uint nblk, l, off;
  int self;

  nblk = (d->size + BSIZE - 1) / BSIZE;
  for (l = 0; l < nblk; l++) {
    uint addr = bmap_raw(d, l);

    // A hole reads as zero; a bad address is already a violation.
    if (addr == 0 || !blk_ok(addr))
      continue;
    bp = bread(ROOTDEV, addr);
    for (off = 0; off + sizeof(de) <= BSIZE; off += sizeof(de)) {
      uint pos = l * BSIZE + off;

      if (pos + sizeof(de) > d->size)
        break;
      memmove(&de, bp->data + off, sizeof(de));
      if (de.inum == 0)
        continue;
      if (de.inum >= sb.ninodes || de.inum >= NINODES) {
        violation("inode %u: directory entry names inode %u, outside the "
                  "inode table",
                  inum, de.inum);
        continue;
      }
      dcount[de.inum]++;
      self = (de.inum == inum);
      if (namecmp(de.name, ".") == 0) {
        have_dot[inum] = 1;
        if (!self)
          violation("inode %u: \".\" points at inode %u", inum, de.inum);
      } else if (namecmp(de.name, "..") == 0) {
        have_dotdot[inum] = 1;
        dir_up[inum] = de.inum;
      } else {
        dir_from[de.inum] = inum;
      }
    }
    brelse(bp);
  }
  if (!have_dot[inum])
    violation("inode %u: directory has no \".\" entry", inum);
  if (!have_dotdot[inum])
    violation("inode %u: directory has no \"..\" entry", inum);
}

// Every stored block address must land in the data area.  The indirect
// block is checked before it is read, so a bad pointer is reported instead
// of being followed.
static void
check_addrs(uint inum, struct dinode *d)
{
  struct buf *bp;
  uint *a;
  int i;

  if (d->size > MAXFILE * BSIZE) {
    violation("inode %u: size %u exceeds MAXFILE*BSIZE=%lu", inum, d->size,
              (uint64)(MAXFILE * BSIZE));
    return;
  }
  for (i = 0; i < NDIRECT; i++)
    if (d->addrs[i] && !blk_ok(d->addrs[i]))
      violation("inode %u: block %u is outside the data area [%u,%u)", inum,
                d->addrs[i], check_nmeta, sb.size);
  if (d->addrs[NDIRECT] == 0)
    return;
  if (!blk_ok(d->addrs[NDIRECT])) {
    violation("inode %u: indirect block %u is outside the data area", inum,
              d->addrs[NDIRECT]);
    return;
  }
  bp = bread(ROOTDEV, d->addrs[NDIRECT]);
  a = (uint *)bp->data;
  for (i = 0; i < NINDIRECT; i++)
    if (a[i] && !blk_ok(a[i]))
      violation("inode %u: indirect entry %d is block %u, outside the data "
                "area",
                inum, i, a[i]);
  brelse(bp);
}

static void
check_inodes(void)
{
  struct dinode d;
  uint inum;

  if (sb.ninodes > NINODES)
    violation("superblock ninodes=%u exceeds the kernel's NINODES=%u",
              sb.ninodes, NINODES);

  for (inum = 1; inum < sb.ninodes && inum < NINODES; inum++) {
    read_dinode(inum, &d);
    itype[inum] = (uchar)d.type;
    nlink_tab[inum] = d.nlink;
    if (d.type == 0)
      continue;

    inode_used++;
    if (d.type < T_DIR || d.type > T_DEVICE)
      violation("inode %u: type %d is not T_DIR, T_FILE or T_DEVICE", inum,
                d.type);
    if (d.nlink < 0)
      violation("inode %u: nlink %d is negative", inum, d.nlink);
    check_addrs(inum, &d);
    if (d.type == T_DIR) {
      dir_count++;
      scan_dir(inum, &d);
    }
  }

  // A directory's subdirectories are the inodes whose non-dot entry sits
  // in it; that is what its nlink counts.
  for (inum = 1; inum < sb.ninodes && inum < NINODES; inum++)
    if (itype[inum] == T_DIR && dir_from[inum] != 0)
      childcount[dir_from[inum]]++;

  // Second pass: compare the link counts and parent links once every
  // directory has been visited, so inode order does not matter.
  for (inum = 1; inum < sb.ninodes && inum < NINODES; inum++) {
    if (itype[inum] == 0) {
      if (dcount[inum])
        violation("inode %u is unallocated but %u directory entries name it",
                  inum, (uint)dcount[inum]);
      continue;
    }
    if (nlink_tab[inum] <= 0) {
      orphan(inum);
      continue;
    }
    if (itype[inum] == T_DIR) {
      // A directory's link count is not "every entry naming it": it is
      // "." once, plus one per subdirectory's "..".  mkfs and mkdir both
      // maintain it that way, and a directory's own ".." does not add a
      // second reference to its parent.
      uint expected = 1 + childcount[inum];

      if ((uint)nlink_tab[inum] != expected)
        violation("inode %u: nlink %d but 1 + %u subdirectories=%u", inum,
                  nlink_tab[inum], childcount[inum], expected);
    } else if ((uint)nlink_tab[inum] != dcount[inum]) {
      violation("inode %u: nlink %d but %u directory entries name it", inum,
                nlink_tab[inum], dcount[inum]);
    }
    if (itype[inum] != T_DIR)
      continue;
    if (inum == ROOTINO) {
      if (have_dotdot[inum] && dir_up[inum] != ROOTINO)
        violation("inode %u: root's \"..\" is inode %u, not itself", inum,
                  dir_up[inum]);
      continue;
    }
    if (dir_from[inum] == 0)
      violation("inode %u: directory has no entry in any parent", inum);
    else if (have_dotdot[inum] && dir_up[inum] != dir_from[inum])
      violation("inode %u: \"..\" is inode %u but its entry is in inode %u",
                inum, dir_up[inum], dir_from[inum]);
  }
}

// -- file system and allocator -------------------------------------------

static void
check_fs(void)
{
  struct buf *bp;
  uint64 nb, ni, wb, wi;
  uint b, bmap_blocks, inode_blocks;
  int set;

  fscount_get(&nb, &ni);
  fscount_walk(ROOTDEV, &wb, &wi);
  bitmap_blocks = nb;
  bitmap_inodes = ni;
  if (nb != wb)
    violation("bitmap holds %lu allocated blocks but fs_nused_blocks is %lu",
              wb, nb);
  if (ni != wi)
    violation("inode table holds %lu allocated inodes but fs_nused_inodes is "
              "%lu",
              wi, ni);

  if (sb.size != FSSIZE)
    violation("superblock size=%u but FSSIZE=%u", sb.size, FSSIZE);
  if (sb.nlog != LOGBLOCKS + 1)
    violation("superblock nlog=%u but LOGBLOCKS+1=%u", sb.nlog, LOGBLOCKS + 1);
  if (sb.logstart != 2)
    violation("superblock logstart=%u, expected 2", sb.logstart);
  if (sb.inodestart != sb.logstart + sb.nlog)
    violation("superblock inodestart=%u, expected %u", sb.inodestart,
              sb.logstart + sb.nlog);
  if (sb.nblocks > sb.size) {
    violation("superblock nblocks=%u exceeds size=%u", sb.nblocks, sb.size);
    return;
  }

  inode_blocks = sb.ninodes / IPB + 1;
  bmap_blocks = sb.size / BPB + 1;
  if (sb.inodestart + inode_blocks > sb.bmapstart)
    violation("inode table [%u,%u) overlaps the bitmap at %u", sb.inodestart,
              sb.inodestart + inode_blocks, sb.bmapstart);
  if (sb.bmapstart + bmap_blocks > sb.size) {
    violation("bitmap [%u,%u) runs past the image (%u blocks)", sb.bmapstart,
              sb.bmapstart + bmap_blocks, sb.size);
    return;
  }

  // Metadata must stay allocated.  Counting alone cannot see this: the
  // O(1) counters are recalibrated from the bitmap at boot, so clearing a
  // metadata bit silently lowers both.  The allocator would then hand out
  // the superblock or the inode table.
  for (b = 0; b < check_nmeta; b++) {
    bp = bread(ROOTDEV, BBLOCK(b, sb));
    set = ((uchar)bp->data[(b % BPB) / 8] >> (b % 8)) & 1;
    brelse(bp);
    if (!set)
      violation("metadata block %u is marked free in the bitmap", b);
  }
}

static void
check_kmem(void)
{
  kmem_snapshot(&pages_total, &kmem_nfree, &kmem_walk, &pages_live);
  // NPAGE covers all of RAM, including the pages the kernel image itself
  // occupies.  kinit() only ever frees the pages after `end`, so those
  // image pages are neither on the free list nor "handed out": the
  // conservation law has to account for them or it is off by the image.
  pages_kernel = (PGROUNDUP((uint64)end) - KERNBASE) / PGSIZE;
  if (kmem_nfree != kmem_walk)
    violation("kmem.nfree=%lu but the free list holds %lu pages", kmem_nfree,
              kmem_walk);
  if (kmem_nfree + pages_live + pages_kernel != pages_total)
    violation("pages do not add up: free=%lu + live=%lu + kernel=%lu != "
              "total=%lu",
              kmem_nfree, pages_live, pages_kernel, pages_total);
}

static void
check_log(void)
{
  int n;
  uint bad;

  if (log_check(&n, &bad) < 0) {
    if (bad)
      violation("log header names block %u, outside the image", bad);
    else
      violation("log header length %d is outside 0..%d", n, LOGBLOCKS);
  }
}

// -- process table -------------------------------------------------------

static void
check_procs(void)
{
  struct proc *p;
  struct file *f;
  struct vma vs[NVMA];
  struct file *ofile[NOFILE];
  struct proc *par;
  enum procstate st;
  int i, j, k, pid, type, ref, npids = 0, dup;
  int pids[NPROC];

  acquire(&wait_lock);
  for (i = 0; i < NPROC; i++) {
    p = &proc[i];
    acquire(&p->lock);
    st = p->state;
    pid = p->pid;
    par = p->parent;
    memmove(vs, p->vmas, sizeof(vs));
    memmove(ofile, p->ofile, sizeof(ofile));
    release(&p->lock);

    if (st == UNUSED)
      continue;
    if (st == ZOMBIE)
      proc_zombie++;
    else
      proc_live++;

    if (st < UNUSED || st > ZOMBIE)
      violation("process slot %d: state %d is not a valid procstate", i, st);
    if (pid <= 0) {
      violation("process slot %d: pid %d is not positive", i, pid);
    } else {
      for (j = 0, dup = 0; j < npids; j++)
        if (pids[j] == pid)
          dup = 1;
      if (dup)
        violation("process slot %d: pid %d appears twice", i, pid);
      else if (npids < NPROC)
        pids[npids++] = pid;
    }
    // wait_lock is held, so the pointer is stable; only its range is a
    // property of the table itself, not of another process's state.
    if (par != 0 && (par < proc || par >= &proc[NPROC]))
      violation("process pid %d: parent pointer %p is outside the process "
                "table",
                pid, (void *)par);

    for (j = 0; j < NVMA; j++) {
      struct vma *v = &vs[j];

      if (v->end == 0)
        continue;
      vma_live++;
      if (v->start >= v->end)
        violation("process pid %d vma %d: start %lx >= end %lx", pid, j,
                  v->start, v->end);
      else {
        if (v->start < MMAPBASE || v->end > MMAPEND)
          violation("process pid %d vma %d: [%lx,%lx) is outside the mmap "
                    "arena",
                    pid, j, v->start, v->end);
        if (v->start % PGSIZE || v->end % PGSIZE)
          violation("process pid %d vma %d: [%lx,%lx) is not page aligned", pid,
                    j, v->start, v->end);
      }
      if (v->prot != PROT_READ && v->prot != (PROT_READ | PROT_WRITE))
        violation("process pid %d vma %d: prot %d is not a legal mapping", pid,
                  j, v->prot);
      if (v->offset % PGSIZE)
        violation("process pid %d vma %d: offset %lx is not page aligned", pid,
                  j, v->offset);
      if (v->file == 0 && v->offset != 0)
        violation("process pid %d vma %d: anonymous mapping has offset %lx",
                  pid, j, v->offset);
      if (v->file != 0) {
        ref = file_snapshot(v->file, &type);
        if (ref <= 0)
          violation("process pid %d vma %d: file reference count is %d", pid, j,
                    ref);
      }
      for (k = j + 1; k < NVMA; k++) {
        struct vma *w = &vs[k];

        if (w->end == 0)
          continue;
        if (v->start < w->end && w->start < v->end)
          violation("process pid %d: vma %d [%lx,%lx) overlaps vma %d "
                    "[%lx,%lx)",
                    pid, j, v->start, v->end, k, w->start, w->end);
      }
    }

    for (j = 0; j < NOFILE; j++) {
      if ((f = ofile[j]) == 0)
        continue;
      fd_open++;
      ref = file_snapshot(f, &type);
      if (ref == -1) {
        violation("process pid %d fd %d: %p is not a file-table entry", pid, j,
                  (void *)f);
        continue;
      }
      if (ref <= 0)
        violation("process pid %d fd %d: reference count is %d", pid, j, ref);
      if (type <= FD_NONE || type > FD_DEVICE)
        violation("process pid %d fd %d: type %d is not a legal file type", pid,
                  j, type);
    }
  }
  release(&wait_lock);
}

static int
check_run(void)
{
  memset(dcount, 0, sizeof(dcount));
  memset(nlink_tab, 0, sizeof(nlink_tab));
  memset(itype, 0, sizeof(itype));
  memset(dir_up, 0, sizeof(dir_up));
  memset(dir_from, 0, sizeof(dir_from));
  memset(childcount, 0, sizeof(childcount));
  memset(have_dot, 0, sizeof(have_dot));
  memset(have_dotdot, 0, sizeof(have_dotdot));
  rlen = 0;
  viol = 0;
  shown = 0;
  orphans = 0;
  orphan_shown = 0;
  proc_live = proc_zombie = vma_live = fd_open = 0;
  inode_used = dir_count = 0;
  bitmap_blocks = bitmap_inodes = 0;
  kmem_nfree = kmem_walk = pages_live = pages_total = pages_kernel = 0;

  // Set before anything consults it so a corrupt superblock reports a
  // violation instead of wrapping the data-block range.
  check_nmeta = sb.nblocks <= sb.size ? sb.size - sb.nblocks : sb.size;

  rprintf("check: best-effort snapshot; state may change during the scan\n");
  check_procs();
  check_inodes();
  check_fs();
  check_kmem();
  check_log();

  rprintf("stats: proc_live=%d proc_zombie=%d vma=%d fd=%d inode_used=%d "
          "dirs=%d orphan=%d blocks_used=%lu inodes_used=%lu kmem_nfree=%lu "
          "kmem_walk=%lu pages_live=%lu pages_kernel=%lu pages_total=%lu\n",
          proc_live, proc_zombie, vma_live, fd_open, inode_used, dir_count,
          orphans, bitmap_blocks, bitmap_inodes, kmem_nfree, kmem_walk,
          pages_live, pages_kernel, pages_total);
  rprintf("violations=%d\n", viol);
  return viol;
}

// Syscall entry point: root only, one scan at a time, copyout outside any
// lock.  Returns the number of violations found, or -1 if the check itself
// could not run (not root, bad buffer, copyout failure, scan already busy).
int
kcheck(pagetable_t pagetable, uint64 psz, uint64 uaddr, int max)
{
  struct proc *cur = myproc();
  int n, r;

  if (cur == 0 || cur->uid != 0)
    return -1;
  if (max <= 0 || uaddr >= MAXVA)
    return -1;
  if (__atomic_exchange_n(&busy, 1, __ATOMIC_ACQ_REL) != 0)
    return -1;
  if (max > CHECK_REPORT_MAX)
    max = CHECK_REPORT_MAX;

  r = check_run();
  n = rlen < max ? rlen : max;
  if (copyout(pagetable, psz, uaddr, rbuf, n) < 0)
    r = -1;

  __atomic_store_n(&busy, 0, __ATOMIC_RELEASE);
  return r;
}
