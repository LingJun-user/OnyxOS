// trace: print the syscall flight recorder for a command or a process.
//
// Usage:
//   trace [-o FILE] [-e CALL,...] COMMAND [ARG...]
//   trace [-o FILE] [-e CALL,...] -p PID
//
// Only the target and the processes it forks are printed, not this polling
// loop: the flag is turned on in the child just before exec, or on the
// attached pid.  fork() inherits the flag, so a target's descendants are
// recorded too; the tree below is rebuilt from the ppid of each record so
// that two trace commands on the same machine do not mix their output.
// -f names that behaviour explicitly; it changes nothing because
// inheritance is a kernel rule, not an option of this tool.
//
// Output is one line per completed syscall:
//
//   pid ppid name(args) = ret
//
// For path-taking calls the first argument is shown as the quoted path
// instead of the raw user pointer.

#include "kernel/types.h"
#include "kernel/param.h"
#include "kernel/fcntl.h"
#include "kernel/stat.h"
#include "kernel/trace.h"
#include "user/user.h"

#define MAXONLY  8
#define MAXTRACK 1024

static struct trace_entry records[TRACE_NENT];
static struct psinfo psnap[NPROC];
static char only[MAXONLY][16];
static int nonly;
static int tracked[MAXTRACK];
static int ntracked;
static uint32 last_seq;
static uint64 last_lost;
static int outfd = 1;

static const char *
trace_name(int num)
{
  switch (num) {
#define NAME_CASE(n, s)                                                        \
  case n:                                                                      \
    return s;
    TRACE_SYSCALLS(NAME_CASE)
#undef NAME_CASE
  default:
    return "unknown";
  }
}

static void
usage(void)
{
  fprintf(2, "usage: trace [-f] [-o file] [-e call,...] command [args...]\n");
  fprintf(2, "       trace [-f] [-o file] [-e call,...] -p pid\n");
  exit(1);
}

static void
parse_only(char *s)
{
  nonly = 0;
  while (*s && nonly < MAXONLY) {
    int n = 0;

    while (*s && *s != ',' && n < 15)
      only[nonly][n++] = *s++;
    only[nonly][n] = 0;
    if (n > 0)
      nonly++;
    if (*s == ',')
      s++;
  }
}

static int
wanted(int num)
{
  int i;

  if (nonly == 0)
    return 1;
  for (i = 0; i < nonly; i++)
    if (strcmp(only[i], trace_name(num)) == 0)
      return 1;
  return 0;
}

static int
tracked_pid(int pid)
{
  int i;

  if (pid <= 0)
    return 0;
  for (i = 0; i < ntracked; i++)
    if (tracked[i] == pid)
      return 1;
  return 0;
}

static void
track(int pid)
{
  if (pid <= 0 || tracked_pid(pid) || ntracked >= MAXTRACK)
    return;
  tracked[ntracked++] = pid;
}

// A record belongs to the target or to a process whose parent is already
// known to belong to it.  Records arrive in sequence order, so one pass
// grows the tree: once a parent is known, the children it forks join on
// their next record (their ppid is the parent's pid).
static int
in_target_tree(struct trace_entry *e)
{
  if (tracked_pid(e->pid))
    return 1;
  if (tracked_pid(e->ppid)) {
    track(e->pid);
    return 1;
  }
  return 0;
}

static void
emit(struct trace_entry *e)
{
  fprintf(outfd, "%d %d %s(", e->pid, e->ppid, trace_name(e->syscall));
  if (e->path[0])
    fprintf(outfd, "\"%s\"", e->path);
  else
    fprintf(outfd, "0x%lx", e->args[0]);
  fprintf(outfd, ",0x%lx,0x%lx) = %ld\n", e->args[1], e->args[2], e->ret);
}

// Read the ring and print the target's exit records that are newer than
// anything already seen.  The kernel returns the newest window, so seq is
// the cursor: records below it were printed or skipped in an earlier round.
static int
drain(void)
{
  uint64 lost = 0;
  int i, n;

  n = traceread(records, TRACE_NENT, &lost);
  if (n < 0) {
    fprintf(2, "trace: traceread failed\n");
    exit(1);
  }
  if (lost > last_lost)
    fprintf(outfd, "[trace: %ld older records lost]\n", lost - last_lost);
  last_lost = lost;

  for (i = 0; i < n; i++) {
    struct trace_entry *e = &records[i];

    if (e->seq <= last_seq)
      continue;
    last_seq = e->seq;
    if (!in_target_tree(e))
      continue;
    if (!(e->flags & TRACE_EXIT))
      continue;
    if (e->syscall == SYS_fork && (int)e->ret > 0)
      track((int)e->ret);
    if (!wanted(e->syscall))
      continue;
    emit(e);
  }
  return n;
}

// Everything already in the ring belongs to someone else; start after it.
static void
baseline(void)
{
  uint64 lost = 0;
  int i, n;

  n = traceread(records, TRACE_NENT, &lost);
  if (n < 0) {
    fprintf(2, "trace: traceread failed\n");
    exit(1);
  }
  last_seq = 0;
  last_lost = lost;
  for (i = 0; i < n; i++)
    if (records[i].seq > last_seq)
      last_seq = records[i].seq;
}

static int
tree_alive(void)
{
  int i, n;

  n = psinfo(psnap, NPROC);
  if (n < 0) {
    fprintf(2, "trace: psinfo failed\n");
    exit(1);
  }
  for (i = 0; i < n; i++)
    if (tracked_pid(psnap[i].pid) && psnap[i].state != PSTATE_UNUSED &&
        psnap[i].state != PSTATE_ZOMBIE)
      return 1;
  return 0;
}

static void
follow_tree(void)
{
  for (;;) {
    drain();
    if (!tree_alive()) {
      // A parent may have forked and exited between drain and psinfo.
      // Once all known processes are gone their fork records are final.
      int known = ntracked;
      drain();
      if (ntracked == known)
        return;
      continue;
    }
    pause(1);
  }
}

int
main(int argc, char **argv)
{
  int attach = 0, pid = 0, status = 0, i = 1;
  char *outfile = 0;

  while (i < argc && argv[i][0] == '-' && argv[i][1] != 0) {
    if (strcmp(argv[i], "-f") == 0) {
      // Descendants are always traced; accepted for readable command lines.
    } else if (strcmp(argv[i], "-p") == 0 && i + 1 < argc) {
      attach = 1;
      pid = atoi(argv[++i]);
    } else if (strcmp(argv[i], "-e") == 0 && i + 1 < argc) {
      parse_only(argv[++i]);
    } else if (strcmp(argv[i], "-o") == 0 && i + 1 < argc) {
      outfile = argv[++i];
    } else {
      usage();
    }
    i++;
  }

  if (attach ? (i < argc || pid <= 0) : i >= argc)
    usage();

  if (outfile) {
    outfd = open(outfile, O_CREATE | O_TRUNC | O_WRONLY);
    if (outfd < 0) {
      fprintf(2, "trace: cannot open %s\n", outfile);
      exit(1);
    }
  }

  baseline();

  if (attach) {
    track(pid);
    if (tracectl(TRACE_ON, pid) != 0) {
      fprintf(2, "trace: cannot trace pid %d\n", pid);
      exit(1);
    }
    follow_tree();
    exit(0);
  }

  int child = fork();
  if (child < 0) {
    fprintf(2, "trace: fork failed\n");
    exit(1);
  }
  if (child == 0) {
    if (tracectl(TRACE_ON, 0) != 0) {
      fprintf(2, "trace: cannot enable tracing\n");
      exit(1);
    }
    exec(argv[i], argv + i);
    fprintf(2, "trace: exec %s failed\n", argv[i]);
    exit(127);
  }

  track(child);
  follow_tree();
  wait(&status);
  exit(status);
}
