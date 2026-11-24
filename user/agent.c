// agent: the guest half of DevLink (batch 17).
//
// init starts this program at boot.  It opens /dev/agent, the character
// device backed by the virtio-serial port that only `make dev' provides,
// and serves framed requests from tools/onyxctl.py on the host.
//
// Without the device the first read fails and this program exits
// silently, which is why plain `make qemu' is unaffected.
//
// Frame layout (little endian throughout):
//
//   magic   u32   0x58594e4f, the bytes "ONYX"
//   type    u8    1 ping, 2 exec, 3 put, 4 get, 5 stat, 6 klog
//   flags   u8    bit 0: more frames follow for this request id
//   length  u16   payload bytes in this frame, at most 4000
//   id      u32   request id, echoed by the response
//
// Responses use the request type with bit 7 set.  A body larger than one
// frame is split the same way.  The protocol only moves bytes; all file
// access still goes through the kernel's permission checks, and the
// device node itself is 0600 root.

#include "kernel/types.h"
#include "kernel/stat.h"
#include "kernel/fcntl.h"
#include "kernel/fs.h"
#include "kernel/param.h"
#include "user/user.h"

#define MAGIC      0x58594e4f
#define HDRSZ      12
#define MAXPAYLOAD 4000
#define REQMAX     (64 * 1024)
#define OUTMAX     (32 * 1024)
#define ARGMAX     32
#define KLOGMAX    (16 * 1024)

#define T_PING 1
#define T_EXEC 2
#define T_PUT  3
#define T_GET  4
#define T_STAT 5
#define T_KLOG 6
#define R_MASK 0x80
#define F_MORE 1

static int fd = -1;
static char req[REQMAX];
static int reqlen;

static uint32
get32(uchar *p)
{
  return p[0] | (p[1] << 8) | (p[2] << 16) | ((uint32)p[3] << 24);
}

static uint16
get16(uchar *p)
{
  return p[0] | (p[1] << 8);
}

static void
put32(uchar *p, uint32 v)
{
  p[0] = v;
  p[1] = v >> 8;
  p[2] = v >> 16;
  p[3] = v >> 24;
}

static void
put64(uchar *p, uint64 v)
{
  put32(p, v);
  put32(p + 4, v >> 32);
}

static int
read_full(void *dst, int n)
{
  char *p = dst;
  int got = 0;

  while (got < n) {
    int r = read(fd, p + got, n - got);

    if (r <= 0)
      return -1;
    got += r;
  }
  return 0;
}

static int
write_full(void *src, int n)
{
  char *p = src;
  int sent = 0;

  while (sent < n) {
    int r = write(fd, p + sent, n - sent);

    if (r <= 0)
      return -1;
    sent += r;
  }
  return 0;
}

// Send one response, splitting payloads over MAXPAYLOAD.  An empty
// response is still one frame, otherwise the host would wait forever.
static int
send_frame(int type, uint32 id, uchar *payload, int len)
{
  uchar hdr[HDRSZ];
  int off = 0;

  do {
    int chunk = len - off;

    if (chunk > MAXPAYLOAD)
      chunk = MAXPAYLOAD;
    put32(hdr, MAGIC);
    hdr[4] = type;
    hdr[5] = off + chunk < len ? F_MORE : 0;
    hdr[6] = chunk;
    hdr[7] = chunk >> 8;
    put32(hdr + 8, id);
    if (write_full(hdr, sizeof(hdr)) < 0)
      return -1;
    if (chunk > 0 && write_full(payload + off, chunk) < 0)
      return -1;
    off += chunk;
  } while (off < len);
  return 0;
}

// -- requests -------------------------------------------------------------

static void
do_ping(uint32 id)
{
  uchar p[4];

  put32(p, 1); // protocol version
  send_frame(T_PING | R_MASK, id, p, sizeof(p));
}

// Read a whole file into a malloc'd buffer.  Returns the size, or -1.
static int
slurp(char *path, char **out, int cap)
{
  struct stat st;
  char *buf;
  int f, n, got = 0;

  if ((f = open(path, O_RDONLY)) < 0)
    return -1;
  if (fstat(f, &st) < 0) {
    close(f);
    return -1;
  }
  if (st.size > cap)
    st.size = cap;
  buf = malloc(st.size + 1);
  if (buf == 0) {
    close(f);
    return -1;
  }
  while (got < st.size) {
    n = read(f, buf + got, st.size - got);
    if (n <= 0)
      break;
    got += n;
  }
  close(f);
  *out = buf;
  return got;
}

static void
do_exec(uint32 id, uchar *p, int len)
{
  char *errname = "/dev/ag-output/stderr", *outname = "/dev/ag-output/stdout";
  static char argstore[1024];
  char *argv[ARGMAX + 1];
  char fallback[64];
  char *out = 0, *err = 0;
  uchar *resp;
  int argc, off = 0, i, outlen = 0, errlen = 0, used = 0;
  uint64 t0, ticks;
  int pid, st;

  if (len < 2)
    goto fail;
  argc = get16(p);
  off = 2;
  if (argc < 1 || argc > ARGMAX)
    goto fail;
  // Arguments are length-prefixed slices of the frame, not C strings.
  for (i = 0; i < argc; i++) {
    int alen;

    if (off + 2 > len)
      goto fail;
    alen = get16(p + off);
    off += 2;
    if (alen <= 0 || off + alen > len ||
        used + alen + 1 > (int)sizeof(argstore))
      goto fail;
    memmove(argstore + used, p + off, alen);
    argstore[used + alen] = 0;
    argv[i] = argstore + used;
    used += alen + 1;
    off += alen;
  }
  argv[argc] = 0;

  t0 = uptime();
  pid = fork();
  if (pid < 0)
    goto fail;
  if (pid == 0) {
    close(fd);
    close(1);
    if (open(outname, O_CREATE | O_TRUNC | O_WRONLY) < 0)
      exit(126);
    close(2);
    if (open(errname, O_CREATE | O_TRUNC | O_WRONLY) < 0)
      exit(126);
    exec(argv[0], argv);
    if (argv[0][0] != '/') {
      char *q = fallback;
      *q++ = '/';
      for (char *s = argv[0]; *s && q < fallback + sizeof(fallback) - 1; s++)
        *q++ = *s;
      *q = 0;
      exec(fallback, argv);
    }
    fprintf(2, "agent: exec %s failed\n", argv[0]);
    exit(127);
  }
  st = -1;
  if (wait(&st) < 0)
    st = -1;
  ticks = uptime() - t0;

  outlen = slurp(outname, &out, OUTMAX);
  errlen = slurp(errname, &err,
                 REQMAX - 16 - outlen < OUTMAX ? REQMAX - 16 - outlen : OUTMAX);
  if (outlen < 0)
    outlen = 0;
  if (errlen < 0)
    errlen = 0;
  unlink(outname);
  unlink(errname);

  resp = malloc(16 + outlen + errlen);
  if (resp == 0) {
    if (out)
      free(out);
    if (err)
      free(err);
    goto fail;
  }
  put32(resp, st);
  put32(resp + 4, ticks);
  put32(resp + 8, outlen);
  put32(resp + 12, errlen);
  if (outlen)
    memmove(resp + 16, out, outlen);
  if (errlen)
    memmove(resp + 16 + outlen, err, errlen);
  send_frame(T_EXEC | R_MASK, id, resp, 16 + outlen + errlen);
  free(resp);
  if (out)
    free(out);
  if (err)
    free(err);
  return;

fail:
  resp = malloc(16);
  if (resp) {
    put32(resp, -1);
    put32(resp + 4, 0);
    put32(resp + 8, 0);
    put32(resp + 12, 0);
    send_frame(T_EXEC | R_MASK, id, resp, 16);
    free(resp);
  }
}

static void
do_put(uint32 id, uchar *p, int len)
{
  uchar resp[4];
  char path[MAXPATH];
  int plen, body, f, n, off;
  uint32 mode;

  if (len < 2)
    goto fail;
  plen = get16(p);
  if (plen <= 0 || plen >= MAXPATH || 2 + plen + 4 > len)
    goto fail;
  memmove(path, p + 2, plen);
  path[plen] = 0;
  mode = get32(p + 2 + plen);
  body = len - 2 - plen - 4;
  off = 2 + plen + 4;

  f = open(path, O_CREATE | O_TRUNC | O_WRONLY);
  if (f < 0)
    goto fail;
  while (body > 0) {
    n = write(f, p + off, body);
    if (n <= 0) {
      close(f);
      unlink(path);
      goto fail;
    }
    off += n;
    body -= n;
  }
  close(f);
  if (chmod(path, mode) < 0) {
    unlink(path);
    goto fail;
  }
  put32(resp, 0);
  send_frame(T_PUT | R_MASK, id, resp, 4);
  return;

fail:
  put32(resp, -1);
  send_frame(T_PUT | R_MASK, id, resp, 4);
}

static void
do_get(uint32 id, uchar *p, int len)
{
  char path[MAXPATH];
  char *data = 0;
  uchar *resp;
  int plen, n;
  struct stat st;
  int f;

  if (len < 2)
    goto fail;
  plen = get16(p);
  if (plen <= 0 || plen >= MAXPATH || 2 + plen > len)
    goto fail;
  memmove(path, p + 2, plen);
  path[plen] = 0;

  f = open(path, O_RDONLY);
  if (f < 0)
    goto fail;
  if (fstat(f, &st) < 0 || st.size > REQMAX - 8) {
    close(f);
    goto fail;
  }
  data = malloc(st.size + 1);
  if (data == 0) {
    close(f);
    goto fail;
  }
  n = 0;
  while (n < st.size) {
    int r = read(f, data + n, st.size - n);
    if (r <= 0)
      break;
    n += r;
  }
  close(f);

  resp = malloc(8 + n);
  if (resp == 0) {
    free(data);
    goto fail;
  }
  put32(resp, 0);
  put32(resp + 4, n);
  if (n)
    memmove(resp + 8, data, n);
  send_frame(T_GET | R_MASK, id, resp, 8 + n);
  free(resp);
  free(data);
  return;

fail:
  resp = malloc(8);
  if (resp) {
    put32(resp, -1);
    put32(resp + 4, 0);
    send_frame(T_GET | R_MASK, id, resp, 8);
    free(resp);
  }
}

static void
do_stat(uint32 id, uchar *p, int len)
{
  char path[MAXPATH];
  uchar resp[16];
  struct stat st;
  int plen;

  put32(resp, -1);
  put32(resp + 4, 0);
  put32(resp + 8, 0);
  put32(resp + 12, 0);
  if (len >= 2 && (plen = get16(p)) > 0 && plen < MAXPATH && 2 + plen <= len) {
    memmove(path, p + 2, plen);
    path[plen] = 0;
    if (stat(path, &st) == 0) {
      put32(resp, 0);
      put32(resp + 4, st.type);
      put32(resp + 8, st.mode);
      put32(resp + 12, st.size);
    }
  }
  send_frame(T_STAT | R_MASK, id, resp, sizeof(resp));
}

static void
do_klog(uint32 id, uchar *p, int len)
{
  char *buf;
  uchar *resp;
  uint64 seq, lost = 0;
  int max = KLOGMAX;
  int n;

  if (len >= 8)
    seq = get32(p) | ((uint64)get32(p + 4) << 32);
  else
    seq = 0;
  if (len >= 12) {
    uint32 m = get32(p + 8);
    if (m < KLOGMAX)
      max = m;
  }
  buf = malloc(max);
  if (buf == 0)
    return;
  n = klog(buf, max, &seq, &lost);
  if (n < 0)
    n = 0;
  resp = malloc(20 + n);
  if (resp == 0) {
    free(buf);
    return;
  }
  put64(resp, seq);
  put64(resp + 8, lost);
  put32(resp + 16, n);
  if (n)
    memmove(resp + 20, buf, n);
  send_frame(T_KLOG | R_MASK, id, resp, 20 + n);
  free(resp);
  free(buf);
}

static void
dispatch(int type, uint32 id, uchar *p, int len)
{
  switch (type) {
  case T_PING:
    do_ping(id);
    break;
  case T_EXEC:
    do_exec(id, p, len);
    break;
  case T_PUT:
    do_put(id, p, len);
    break;
  case T_GET:
    do_get(id, p, len);
    break;
  case T_STAT:
    do_stat(id, p, len);
    break;
  case T_KLOG:
    do_klog(id, p, len);
    break;
  default:
    break;
  }
}

// Read one header, sliding forward until the magic matches.  A timeout on
// the host side makes it reconnect and resend; the guest may then be in
// the middle of the old frame, so a desynchronised stream is expected and
// must not kill the agent.  Resyncing costs at most one wasted request.
static int
read_header(uchar *hdr)
{
  if (read_full(hdr, 4) < 0)
    return -1;
  while (get32(hdr) != MAGIC) {
    memmove(hdr, hdr + 1, 3);
    if (read_full(hdr + 3, 1) < 0)
      return -1;
  }
  return read_full(hdr + 4, HDRSZ - 4);
}

int
main(void)
{
  uchar hdr[HDRSZ];
  int assembling = 0, dropping = 0, type = 0;
  uint32 id = 0;

  fd = open("/dev/agent", O_RDWR);
  if (fd < 0)
    exit(1);
  mkdir("/tmp");
  mkdir("/dev/ag-output");
  if (chmod("/dev/ag-output", 0700) < 0)
    exit(1);

  for (;;) {
    if (read_header(hdr) < 0)
      exit(0);
    int frame_type = hdr[4];
    int flags = hdr[5];
    int len = get16(hdr + 6);
    uint32 rid = get32(hdr + 8);

    if (len > MAXPAYLOAD) {
      assembling = 0;
      continue;
    }
    if (!assembling || rid != id || frame_type != type) {
      reqlen = 0;
      dropping = 0;
      id = rid;
      type = frame_type;
    }
    if ((flags & ~F_MORE) || reqlen + len > REQMAX)
      dropping = 1;
    if (dropping) {
      static uchar discard[MAXPAYLOAD];
      if (read_full(discard, len) < 0)
        exit(0);
    } else {
      if (read_full(req + reqlen, len) < 0)
        exit(0);
      reqlen += len;
    }
    assembling = (flags & F_MORE) != 0;
    if (!assembling && !dropping) {
      dispatch(type, id, (uchar *)req, reqlen);
      reqlen = 0;
    }
  }
}
