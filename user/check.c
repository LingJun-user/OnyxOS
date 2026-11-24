// check: ask the kernel whether its own invariants still hold.
//
// Usage:
//   check            print the full report
//   check --stats    print only the counters and the violation total
//
// The kernel does the scanning; this program only prints what it wrote and
// turns the result into an exit status.  --stats exists for before/after
// comparison from a script: take the counters, run a stress case, take
// them again, and look for growth in fd, vma or inode_used.

#include "kernel/types.h"
#include "kernel/param.h"
#include "user/user.h"

#define REPORTSZ 4096

static char report[REPORTSZ];

static int
has_prefix(char *line, char *prefix)
{
  while (*prefix)
    if (*line++ != *prefix++)
      return 0;
  return 1;
}

// Print one line (NUL-terminated within the buffer), optionally only when
// it is a counter line.  Returns 1 if anything was printed.
static int
printline(char *line, int stats)
{
  int counter = has_prefix(line, "stats:") || has_prefix(line, "violations=");
  char *p;

  if (stats && !counter)
    return 0;
  for (p = line; *p; p++)
    write(1, p, 1);
  write(1, "\n", 1);
  return 1;
}

int
main(int argc, char **argv)
{
  int stats = 0, n, start, i;

  if (argc == 2 &&
      (strcmp(argv[1], "--stats") == 0 || strcmp(argv[1], "-s") == 0)) {
    stats = 1;
  } else if (argc != 1) {
    fprintf(2, "usage: check [--stats]\n");
    exit(1);
  }

  n = kcheck(report, REPORTSZ - 1);
  if (n < 0) {
    fprintf(2, "check: cannot run (root only, one scan at a time)\n");
    exit(1);
  }
  report[REPORTSZ - 1] = 0;

  // The kernel ends every complete line with '\n'; a truncated report may
  // leave one without it, which the tail below still prints.
  start = 0;
  for (i = 0; report[i]; i++) {
    if (report[i] == '\n') {
      report[i] = 0;
      printline(report + start, stats);
      start = i + 1;
    }
  }
  if (report[start])
    printline(report + start, stats);

  if (n == 0) {
    printf("check: OK\n");
    exit(0);
  }
  printf("check: FAIL %d violation(s)\n", n);
  exit(1);
}
