// init: The initial user-level program

#include "kernel/types.h"
#include "kernel/stat.h"
#include "kernel/spinlock.h"
#include "kernel/sleeplock.h"
#include "kernel/fs.h"
#include "kernel/file.h"
#include "user/user.h"
#include "kernel/fcntl.h"

char *argv[] = {"login", 0};
char *agentargv[] = {"agent", 0};

// DevLink (batch 17): /dev/agent is backed by the virtio-serial port that
// only `make dev' creates.  The node is made on every boot, but if the
// device is absent the agent's first read fails and it exits, so the
// normal boot path is unchanged.
static void
start_agent(void)
{
  int pid;

  mkdir("/dev");                 // fails harmlessly when it exists
  mknod("/dev/agent", AGENT, 0); // same
  chmod("/dev/agent", 0600);     // every boot: the device is root-only

  pid = fork();
  if (pid == 0) {
    exec("/agent", agentargv);
    exit(1);
  }
}

int
main(void)
{
  int pid, wpid;

  if (open("console", O_RDWR) < 0) {
    mknod("console", CONSOLE, 0);
    open("console", O_RDWR);
  }
  dup(0); // stdout
  dup(0); // stderr

  start_agent();

  for (;;) {
    printf("init: starting login\n");
    pid = fork();
    if (pid < 0) {
      printf("init: fork failed\n");
      exit(1);
    }
    if (pid == 0) {
      exec("/login", argv);
      printf("init: exec login failed\n");
      exit(1);
    }

    for (;;) {
      // this call to wait() returns if the shell exits,
      // or if a parentless process exits.
      wpid = wait((int *)0);
      if (wpid == pid) {
        // the shell exited; restart it.
        break;
      } else if (wpid < 0) {
        printf("init: wait returned an error\n");
        exit(1);
      } else {
        // it was a parentless process; do nothing.
      }
    }
  }
}
