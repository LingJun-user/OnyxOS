// tracetest: prove that the syscall flight recorder records the right
// process, path, arguments and return value, that concurrent writers do
// not lose or mix records, that two trace commands keep their output
// separate, and that it does not leak one user's records to another.
//
// Run as a dedicated test (testrun tracetest) on a single-use QEMU session.
// It clears the ring before each check, so a previous run in the same image
// cannot affect the result.

#include "kernel/types.h"
#include "kernel/param.h"
#include "kernel/fcntl.h"
#include "kernel/stat.h"
#include "kernel/syscall.h"
#include "kernel/trace.h"
#include "user/user.h"

static struct trace_entry buf[TRACE_NENT];
static int checks;

static int file_has(char *path, char *needle);

static void
expect(int ok, const char *what)
{
  if (ok) {
    checks++;
    return;
  }
  printf("tracetest: BAD %s\n", what);
  exit(1);
}

static int
read_all(uint64 *lost)
{
  int n = traceread(buf, TRACE_NENT, lost);

  if (n < 0) {
    printf("tracetest: BAD traceread\n");
    exit(1);
  }
  return n;
}

static struct trace_entry *
find_exit(int n, int pid, int num)
{
  struct trace_entry *found = 0;
  int i;

  for (i = 0; i < n; i++)
    if (buf[i].flags == TRACE_EXIT && buf[i].pid == pid &&
        buf[i].syscall == num)
      found = &buf[i];
  return found;
}

// 1. A failed open records the caller, its parent, the path and the value.
static void
test_open(void)
{
  uint64 lost;
  int pid, st, n;
  struct trace_entry *e;

  expect(tracectl(TRACE_CLEAR, 0) == 0, "root can clear the ring");
  pid = fork();
  if (pid == 0) {
    if (tracectl(TRACE_ON, 0) != 0)
      exit(2);
    if (open("/0123456789012345678901234567890123456789", O_RDONLY) >= 0)
      exit(3);
    if (open("/no/such/file", O_RDONLY) >= 0)
      exit(3);
    exit(0);
  }
  expect(pid > 0, "fork the traced child");
  expect(wait(&st) == pid && st == 0, "the traced child exits cleanly");

  n = read_all(&lost);
  e = find_exit(n, pid, SYS_open);
  expect(e != 0, "the failed open is recorded");
  expect(e->ret == (uint64)-1, "the recorded open failed");
  expect(strcmp(e->path, "/no/such/file") == 0, "the path is recorded");
  expect(e->ppid == getpid(), "the parent pid is recorded");
  expect(e->uid == 0, "the uid is recorded");
  int saw_prefix = 0;
  for (int i = 0; i < n; i++) {
    if (buf[i].syscall == SYS_open && buf[i].flags == TRACE_EXIT &&
        strcmp(buf[i].path, "/012345678901234567890123456789") == 0)
      saw_prefix = 1;
  }
  expect(saw_prefix, "long path keeps its first 31 bytes");
}

// 2. Attaching by pid records another process, which is what trace -p uses.
static void
test_attach(void)
{
  uint64 lost;
  int fds[2], pid, st, n;
  char c;
  struct trace_entry *e;

  expect(tracectl(TRACE_CLEAR, 0) == 0, "clear before the attach test");
  expect(pipe(fds) == 0, "pipe for the attach test");
  pid = fork();
  if (pid == 0) {
    close(fds[1]);
    if (read(fds[0], &c, 1) != 1)
      exit(2);
    if (open("/no/such/file", O_RDONLY) >= 0)
      exit(3);
    exit(0);
  }
  expect(pid > 0, "fork the attach target");
  close(fds[0]);
  expect(tracectl(TRACE_ON, pid) == 0, "attach to another process");
  expect(write(fds[1], "x", 1) == 1, "release the attach target");
  close(fds[1]);
  expect(wait(&st) == pid && st == 0, "the attach target exits");

  n = read_all(&lost);
  e = find_exit(n, pid, SYS_open);
  expect(e != 0, "the attached process is recorded");
  expect(e->ret == (uint64)-1, "the attached open failed");
  expect(strcmp(e->path, "/no/such/file") == 0,
         "the attached path is recorded");
}

// 3. Turning tracing off stops new records.
static void
test_disable(void)
{
  uint64 lost;
  uint32 before = 0, after = 0;
  int i, n, me;

  expect(tracectl(TRACE_CLEAR, 0) == 0, "clear before the disable test");
  expect(tracectl(TRACE_ON, 0) == 0, "enable tracing on self");
  me = getpid();
  expect(tracectl(TRACE_OFF, 0) == 0, "disable tracing on self");

  n = read_all(&lost);
  for (i = 0; i < n; i++)
    if (buf[i].flags == TRACE_EXIT && buf[i].pid == me && buf[i].seq > before)
      before = buf[i].seq;
  expect(before != 0, "the getpid was recorded");

  for (i = 0; i < 5; i++)
    getpid();
  n = read_all(&lost);
  for (i = 0; i < n; i++)
    if (buf[i].flags == TRACE_EXIT && buf[i].pid == me && buf[i].seq > after)
      after = buf[i].seq;
  expect(after == before, "the ring stops growing while tracing is off");
}

// 4. trace -f covers a grandchild: the record's pid and ppid place it one
//    level below the process that trace itself started.
static void
test_follow(void)
{
  uint64 lost;
  int i, pid, st, n, helper, seen;
  struct trace_entry *e;

  expect(tracectl(TRACE_CLEAR, 0) == 0, "clear before the follow test");
  pid = fork();
  if (pid == 0) {
    char *args[] = {"/trace", "-f", "/tracetest", "child", 0};
    exec("/trace", args);
    exit(127);
  }
  expect(pid > 0, "fork the trace command");
  expect(wait(&st) == pid && st == 0, "trace -f finishes the target");

  n = read_all(&lost);
  e = 0;
  for (i = 0; i < n; i++)
    if (buf[i].flags == TRACE_EXIT && buf[i].syscall == SYS_open &&
        strcmp(buf[i].path, "/no/such/file") == 0)
      e = &buf[i];
  expect(e != 0, "the grandchild's failed open is recorded");
  expect(e->pid != pid, "the record is not from the direct child");
  expect(e->ppid != getpid(), "the record is not from a child of the test");
  expect(e->ppid != pid, "the record comes from a grandchild");

  helper = e->ppid;
  seen = 0;
  for (i = 0; i < n; i++)
    if (buf[i].pid == helper && buf[i].flags == TRACE_EXIT)
      seen = 1;
  expect(seen, "the intermediate process was traced");
}

// 5. Permissions: a non-root process may trace itself, not clear the ring,
//    not attach to root, and never sees root's records.
static void
test_permissions(void)
{
  uint64 lost;
  int i, parent, pid, st, n;

  expect(tracectl(TRACE_CLEAR, 0) == 0, "clear before the permission test");
  parent = getpid();
  pid = fork();
  if (pid == 0) {
    if (setuid(1) != 0)
      exit(10);
    if (tracectl(TRACE_CLEAR, 0) != -1)
      exit(11);
    if (tracectl(TRACE_ON, parent) != -1)
      exit(12);
    if (tracectl(TRACE_ON, 0) != 0)
      exit(13);
    getpid();
    n = traceread(buf, 16, &lost);
    if (n <= 0)
      exit(14);
    for (i = 0; i < n; i++)
      if (buf[i].uid != 1)
        exit(15);
    if (tracectl(TRACE_OFF, 0) != 0)
      exit(16);
    exit(0);
  }
  expect(wait(&st) == pid && st == 0, "non-root tracing rules");

  expect(tracectl(TRACE_CLEAR, 0) == 0, "clear before the filter test");
  expect(tracectl(TRACE_ON, 0) == 0, "trace root on self");
  getpid();
  expect(tracectl(TRACE_OFF, 0) == 0, "trace root off self");

  pid = fork();
  if (pid == 0) {
    if (setuid(1) != 0)
      exit(20);
    n = traceread(buf, 64, &lost);
    if (n != 0)
      exit(21);
    exit(0);
  }
  expect(wait(&st) == pid && st == 0, "other-uid records are filtered");
}

// 6. Wrap-around: the newest window is still contiguous and lost grows.
static void
test_wrap(void)
{
  uint64 lost1 = 0, lost2 = 0;
  uint32 first, last;
  int i, n;

  expect(tracectl(TRACE_CLEAR, 0) == 0, "clear before the wrap test");
  expect(tracectl(TRACE_ON, 0) == 0, "trace self for the wrap test");
  open("/tracetest/missing", O_RDONLY);
  for (i = 0; i < 1300; i++)
    getpid();

  n = traceread(buf, TRACE_NENT, &lost1);
  expect(n == TRACE_NENT, "a full ring is returned");
  expect(lost1 > 0, "the ring wrapped");
  char empty_path[TRACE_PATH] = {0};
  for (i = 0; i < n; i++)
    expect(memcmp(buf[i].path, empty_path, sizeof(empty_path)) == 0,
           "reused slots clear the whole path field");
  first = buf[0].seq;
  last = buf[n - 1].seq;
  expect(last > first, "records are in write order");
  expect(last - first + 1 == (uint32)n, "the window is contiguous");

  for (i = 0; i < 20; i++)
    getpid();
  n = traceread(buf, TRACE_NENT, &lost2);
  expect(n == TRACE_NENT, "the ring stays full");
  expect(lost2 > lost1, "lost records keep increasing");
  expect(tracectl(TRACE_OFF, 0) == 0, "stop tracing after the wrap test");
}

// 7. Two processes on different harts write at the same time.  Every
//    record claims its own slot, so the published count is exactly the
//    number of traced syscalls, and no record combines one process's pid
//    with another process's fields.
static void
test_concurrent(void)
{
  enum { ITER = 50000 };
  uint64 lost = 0;
  uint32 prev;
  int fds[2], pid1, pid2, st = 0, w, n, i, j, got1, got2, bad;
  char c;

  expect(tracectl(TRACE_CLEAR, 0) == 0, "clear before the concurrent test");
  expect(pipe(fds) == 0, "pipe for the concurrent test");

  pid1 = fork();
  if (pid1 == 0) {
    close(fds[1]);
    if (read(fds[0], &c, 1) != 1)
      exit(2);
    close(fds[0]);
    if (tracectl(TRACE_ON, 0) != 0)
      exit(3);
    for (i = 0; i < ITER; i++)
      getpid();
    if (tracectl(TRACE_OFF, 0) != 0)
      exit(4);
    exit(0);
  }
  expect(pid1 > 0, "fork the first concurrent writer");

  pid2 = fork();
  if (pid2 == 0) {
    close(fds[1]);
    if (read(fds[0], &c, 1) != 1)
      exit(5);
    close(fds[0]);
    if (tracectl(TRACE_ON, 0) != 0)
      exit(6);
    for (i = 0; i < ITER; i++)
      getpid();
    if (tracectl(TRACE_OFF, 0) != 0)
      exit(7);
    exit(0);
  }
  expect(pid2 > 0, "fork the second concurrent writer");

  close(fds[0]);
  expect(write(fds[1], "xx", 2) == 2, "release both writers");
  close(fds[1]);

  // Read while they write: each snapshot must be ordered and contain no
  // record whose return value belongs to another pid.
  bad = 0;
  for (j = 0; j < 50; j++) {
    n = traceread(buf, TRACE_NENT, &lost);
    if (n < 0)
      exit(1);
    for (i = 0; i < n; i++) {
      if ((i && buf[i].seq <= buf[i - 1].seq) ||
          buf[i].seq > lost + TRACE_NENT || buf[i].seq <= lost ||
          buf[i].uid != 0)
        bad = 1;
      if (buf[i].pid != pid1 && buf[i].pid != pid2)
        bad = 1;
      if (buf[i].flags == TRACE_EXIT && buf[i].syscall == SYS_getpid &&
          buf[i].ret != (uint64)buf[i].pid)
        bad = 1;
    }
  }
  expect(bad == 0, "concurrent snapshots are self-consistent");

  got1 = got2 = 0;
  for (i = 0; i < 2; i++) {
    w = wait(&st);
    expect(st == 0, "a concurrent writer exits cleanly");
    if (w == pid1)
      got1 = 1;
    else if (w == pid2)
      got2 = 1;
    else
      expect(0, "wait returns a concurrent writer");
  }
  expect(got1 && got2, "both concurrent writers were reaped");

  // Each writer publishes 2*ITER getpid records plus the TRACE_OFF entry;
  // TRACE_ON itself is not recorded.  With correct slot claiming this is
  // exactly lost + n, however often the ring wrapped.
  n = read_all(&lost);
  expect(lost + (uint64)n == 2 * (2 * ITER + 1),
         "concurrent writers publish every record");
  expect(n == TRACE_NENT, "the ring is full after the concurrent test");
  prev = buf[0].seq;
  bad = 0;
  for (i = 1; i < n; i++) {
    if (buf[i].seq != prev + 1)
      bad = 1;
    prev = buf[i].seq;
  }
  expect(bad == 0, "the settled window is contiguous");
}

// 8. CLEAR while another process is writing.  The write lock makes the
//    reset atomic, so the first record after it is numbered 1 and none of
//    the erased history comes back.
static void
test_clear_race(void)
{
  uint64 lost = 0;
  int fds[2], pid, st, n, i;
  char c;

  expect(tracectl(TRACE_CLEAR, 0) == 0, "clear before the CLEAR race test");
  expect(pipe(fds) == 0, "pipe for the CLEAR race test");
  pid = fork();
  if (pid == 0) {
    close(fds[0]);
    if (tracectl(TRACE_ON, 0) != 0)
      exit(2);
    if (write(fds[1], "x", 1) != 1)
      exit(3);
    close(fds[1]);
    for (i = 0; i < 100; i++)
      pause(1);
    if (tracectl(TRACE_OFF, 0) != 0)
      exit(4);
    exit(0);
  }
  expect(pid > 0, "fork the CLEAR race writer");
  close(fds[1]);
  expect(read(fds[0], &c, 1) == 1, "the writer is already tracing");
  close(fds[0]);

  expect(tracectl(TRACE_CLEAR, 0) == 0, "clear while the writer runs");
  expect(wait(&st) == pid && st == 0, "the CLEAR race writer exits cleanly");

  n = read_all(&lost);
  expect(n > 0, "records after CLEAR are visible");
  expect(lost == 0, "CLEAR reset the lost count");
  expect(buf[0].seq == 1, "numbering restarts after CLEAR");
  expect(buf[n - 1].seq - buf[0].seq + 1 == (uint32)n,
         "the post-CLEAR window is contiguous");
}

// 9. Two trace commands on the same machine: each prints only its own
//    target and the target's descendants, not the other target's records.
static void
test_two_targets(void)
{
  int p1, p2, st, w, i, got1, got2, has_a, has_b;

  expect(tracectl(TRACE_CLEAR, 0) == 0, "clear before the isolation test");

  p1 = fork();
  if (p1 == 0) {
    char *args[] = {"/trace",    "-e",         "open",     "-o",
                    "/tr-out-a", "/tracetest", "target-a", 0};
    exec("/trace", args);
    exit(127);
  }
  expect(p1 > 0, "start the first trace command");
  p2 = fork();
  if (p2 == 0) {
    char *args[] = {"/trace",    "-e",         "open",     "-o",
                    "/tr-out-b", "/tracetest", "target-b", 0};
    exec("/trace", args);
    exit(127);
  }
  expect(p2 > 0, "start the second trace command");

  got1 = got2 = 0;
  for (i = 0; i < 2; i++) {
    w = wait(&st);
    expect(st == 0, "a trace command finishes");
    if (w == p1)
      got1 = 1;
    else if (w == p2)
      got2 = 1;
    else
      expect(0, "wait returns a trace command");
  }
  expect(got1 && got2, "both trace commands were reaped");

  has_a = file_has("/tr-out-a", "tr-a");
  has_b = file_has("/tr-out-a", "tr-b");
  expect(has_a == 1, "the first target's path is in its own output");
  expect(has_b == 0, "the first output excludes the other target");
  has_a = file_has("/tr-out-b", "tr-b");
  has_b = file_has("/tr-out-b", "tr-a");
  expect(has_a == 1, "the second target's path is in its own output");
  expect(has_b == 0, "the second output excludes the other target");

  unlink("/tr-out-a");
  unlink("/tr-out-b");
}

// Helper mode for test_follow: run under trace, then fork one more level so
// the failed open comes from a grandchild of the trace command.
static void
child_mode(void)
{
  int pid, st;

  pid = fork();
  if (pid == 0) {
    if (open("/no/such/file", O_RDONLY) >= 0)
      exit(1);
    exit(0);
  }
  if (pid < 0 || wait(&st) != pid || st != 0)
    exit(1);
  exit(0);
}

// Helper mode for test_two_targets: keep opening a path long enough for
// the other trace command to be running at the same time.
static void
target_mode(char *path)
{
  int i;

  for (i = 0; i < 20; i++) {
    open(path, O_RDONLY);
    pause(1);
  }
  exit(0);
}

// Search a file for a substring; returns -1 if it cannot be opened.
static int
file_has(char *path, char *needle)
{
  char data[256];
  int fd, n, i, j, len;

  fd = open(path, O_RDONLY);
  if (fd < 0)
    return -1;
  len = strlen(needle);
  while ((n = read(fd, data, sizeof(data))) > 0) {
    for (i = 0; i + len <= n; i++) {
      for (j = 0; j < len && data[i + j] == needle[j]; j++)
        ;
      if (j == len) {
        close(fd);
        return 1;
      }
    }
  }
  close(fd);
  return 0;
}

int
main(int argc, char **argv)
{
  if (argc > 1 && strcmp(argv[1], "child") == 0)
    child_mode();
  if (argc > 1 && strcmp(argv[1], "target-a") == 0) {
    // The tracer must keep collecting after its direct target exits.
    int child = fork();
    if (child != 0)
      exit(child < 0);
    pause(5);
    target_mode("/tr-a");
  }
  if (argc > 1 && strcmp(argv[1], "target-b") == 0)
    target_mode("/tr-b");

  test_open();
  test_attach();
  test_disable();
  test_follow();
  test_permissions();
  test_wrap();
  test_concurrent();
  test_clear_race();
  test_two_targets();

  printf("tracetest: OK (%d checks)\n", checks);
  exit(0);
}
