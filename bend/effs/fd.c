// Fd
// ==
//
// Sockets as plain descriptors (U32), for the attack's single event loop:
// it waits on every connection at once (Fd.wait) and steps every ready
// connection's pure client machine in parallel. A descriptor is not an
// affine handle, so nothing stops a double close: the shell owns that.
// Bytes are one Chr per byte, as in bytes.c (whose helpers this reuses).

#include <netinet/tcp.h>
#ifdef __APPLE__
#include <sys/event.h>
#else
#include <sys/epoll.h>
#endif

// the event queue every connection is registered with, tagged with its
// worker (kqueue on macOS, epoll elsewhere); a closed descriptor leaves
// it by itself
static int fd_q = -1;

static int fd_queue(void) {
  if (fd_q < 0) {
#ifdef __APPLE__
    fd_q = kqueue();
#else
    fd_q = epoll_create1(0);
#endif
  }
  return fd_q;
}

static int fd_watch(int fd, u32 tag) {
#ifdef __APPLE__
  struct kevent ev;
  EV_SET(&ev, fd, EVFILT_READ, EV_ADD, 0, 0, (void*)(uintptr_t)tag);
  return kevent(fd_queue(), &ev, 1, NULL, 0, NULL);
#else
  struct epoll_event ev;
  ev.events   = EPOLLIN | EPOLLRDHUP;
  ev.data.u64 = ((u64)tag << 32) | (u32)fd;
  return epoll_ctl(fd_queue(), EPOLL_CTL_ADD, fd, &ev);
#endif
}

#ifdef CID_FD_CONNECT

// a non-blocking connect, parked until the socket is writable; SO_ERROR
// then says how it ended
static Term fd_connect_more(Env e, IoWork* w) {
  int       fd  = (int)w->made;
  int       err = (int)w->code;
  socklen_t len = sizeof(err);
  if (err == EINPROGRESS && getsockopt(fd, SOL_SOCKET, SO_ERROR, &err, &len)) {
    err = errno;
  }
  if (err == 0 && fd_watch(fd, (u32)w->hand) != 0) {
    err = errno;
  }
  if (err != 0 && fd >= 0) {
    close(fd);
  }
  free(w->data);
  return err != 0 ? io_fail(e, (u32)err, NULL) : io_done(e, (Term)(u32)fd);
}

Term fd_connect_run(Env e, Term* f, IoWork* w) {
  struct sockaddr_in at;
  w->data = bytes_cstr(e, f[0], &w->size);
  w->hand = (intptr_t)(u32)f[2];
  int fd  = -1;
  errno   = EINVAL;
  if (!io_nul(w->data, w->size) && io_sys_addr(w->data, (u32)f[1], &at) == 0) {
    fd = socket(AF_INET, SOCK_STREAM, 0);
  }
  if (fd >= 0 && fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK) < 0) {
    close(fd);
    fd = -1;
  }
  if (fd >= 0) {
    int one = 1;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
  }
  w->made = fd;
  io_sys_end(w, fd < 0 ? fd : connect(fd, (struct sockaddr*)&at, sizeof(at)));
  return w->code == EINPROGRESS
    ? io_wait_on(w, fd, POLLOUT, 0, fd_connect_more) : fd_connect_more(e, w);
}

static void __attribute__((constructor)) fd_connect_use(void) {
  io_eff(CID_FD_CONNECT, fd_connect_run, 0);
}

#endif

#ifdef CID_FD_SEND

static Term fd_send_more(Env e, IoWork* w) {
  int fd = (int)w->hand;
  while (w->code == 0 && (u64)w->made < w->size) {
    ssize_t n = send(fd, w->data + w->made, w->size - (u64)w->made, 0);
    if (n < 0 && errno == EAGAIN) {
      return io_wait_on(w, fd, POLLOUT, 0, fd_send_more);
    }
    if (n < 0 && errno == EINTR) {
      continue;
    }
    w->made += io_sys_end(w, n);
  }
  Term r = w->code != 0 ? io_fail(e, w->code, NULL)
    : io_done(e, term_pak(CID_UNIT, 0));
  free(w->data);
  return r;
}

Term fd_send_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)(u32)f[0];
  w->data = bytes_cstr(e, f[1], &w->size);
  w->made = 0;
  w->code = 0;
  return fd_send_more(e, w);
}

static void __attribute__((constructor)) fd_send_use(void) {
  io_eff(CID_FD_SEND, fd_send_run, 0);
}

#endif

#ifdef CID_FD_CLOSE

Term fd_close_run(Env e, Term* f, IoWork* w) {
  close((int)(u32)f[0]);
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) fd_close_use(void) {
  io_eff(CID_FD_CLOSE, fd_close_run, 0);
}

#endif

#ifdef CID_FD_WAIT

// what a wait found: per descriptor, the bytes read ("" at a close or an
// error), or nothing when it was not ready
typedef struct {
  int            n;
  int            ms;
  u64            max;
  struct pollfd* p;
  char**         buf;
  ssize_t*       len;
} FdWait;

// on a helper thread: one poll over every descriptor, then one recv from
// each ready one
static void fd_wait_call(IoWork* w) {
  FdWait* x = (FdWait*)w->data;
  int     r;
  do {
    r = poll(x->p, (nfds_t)x->n, x->ms);
  } while (r < 0 && errno == EINTR);
  for (int i = 0; i < x->n; i += 1) {
    x->len[i] = -2;
    if (r > 0 && (x->p[i].revents & (POLLIN | POLLHUP | POLLERR))) {
      x->buf[i] = malloc(x->max);
      ssize_t k;
      do {
        k = recv(x->p[i].fd, x->buf[i], x->max, 0);
      } while (k < 0 && errno == EINTR);
      x->len[i] = k < 0 && errno == EAGAIN ? -2 : (k < 0 ? 0 : k);
    }
  }
}

static Term fd_wait_pack(Env e, IoWork* w) {
  FdWait* x  = (FdWait*)w->data;
  Term    xs = term_pak(CID_NIL, 0);
  for (int i = x->n; i > 0; i -= 1) {
    int j = i - 1;
    if (x->len[j] >= 0) {
      Term s = bytes_str(e, x->buf[j], (u64)x->len[j]);
      xs = io_node(e, CID_CON, io_tup(e, (Term)(u32)x->p[j].fd, s), xs);
    }
    if (x->len[j] != -2) {
      free(x->buf[j]);
    }
  }
  free(x->p);
  free(x->buf);
  free(x->len);
  free(x);
  return xs;
}

Term fd_wait_run(Env e, Term* f, IoWork* w) {
  FdWait* x = io_mem(calloc(1, sizeof(FdWait)));
  int     cap = 16;
  x->p   = io_mem(malloc(sizeof(struct pollfd) * cap));
  x->ms  = (int)(u32)f[2];
  x->max = (u64)(u32)f[1];
  Term s = f[0];
  while (term_aux(s) == CID_CON) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, s, 2, fb));
    if (x->n == cap) {
      cap *= 2;
      x->p = io_mem(realloc(x->p, sizeof(struct pollfd) * cap));
    }
    x->p[x->n].fd      = (int)(u32)fb[0];
    x->p[x->n].events  = POLLIN;
    x->p[x->n].revents = 0;
    x->n += 1;
    s = fb[1];
  }
  x->buf = io_mem(calloc((size_t)(x->n + 1), sizeof(char*)));
  x->len = io_mem(calloc((size_t)(x->n + 1), sizeof(ssize_t)));
  w->data = (char*)x;
  // a zero-timeout poll first, on the loop: when something is already
  // ready (the busy case) there is no helper-thread round trip
  int ms = x->ms;
  x->ms  = 0;
  fd_wait_call(w);
  for (int i = 0; i < x->n; i += 1) {
    if (x->len[i] != -2) {
      return fd_wait_pack(e, w);
    }
  }
  x->ms = ms;
  return ms == 0 ? fd_wait_pack(e, w) : io_work(w, fd_wait_call, fd_wait_pack);
}

static void __attribute__((constructor)) fd_wait_use(void) {
  io_eff(CID_FD_WAIT, fd_wait_run, 0);
}

#endif

#ifdef CID_FD_NEXT

// what a queue wait found: per ready descriptor its tag and the bytes read
// ("" at a close or an error)
typedef struct {
  int   n;
  u64   ns;
  u64   max;
  int   fd[256];
  u32   tag[256];
  char* buf[256];
  long  len[256];
} FdNext;

static void fd_next_call(IoWork* w) {
  FdNext* x = (FdNext*)w->data;
  int     r;
#ifdef __APPLE__
  struct kevent   evs[256];
  struct timespec ts = { (time_t)(x->ns / 1000000000ull), (long)(x->ns % 1000000000ull) };
  do {
    r = kevent(fd_queue(), NULL, 0, evs, 256, &ts);
  } while (r < 0 && errno == EINTR);
  for (int i = 0; i < r; i += 1) {
    x->fd[i]  = (int)evs[i].ident;
    x->tag[i] = (u32)(uintptr_t)evs[i].udata;
  }
#else
  struct epoll_event evs[256];
  int ms = (int)((x->ns + 999999ull) / 1000000ull);
  do {
    r = epoll_wait(fd_queue(), evs, 256, ms);
  } while (r < 0 && errno == EINTR);
  for (int i = 0; i < r; i += 1) {
    x->fd[i]  = (int)(u32)evs[i].data.u64;
    x->tag[i] = (u32)(evs[i].data.u64 >> 32);
  }
#endif
  x->n = r < 0 ? 0 : r;
  for (int i = 0; i < x->n; i += 1) {
    x->buf[i] = malloc(x->max);
    ssize_t k;
    do {
      k = recv(x->fd[i], x->buf[i], x->max, 0);
    } while (k < 0 && errno == EINTR);
    x->len[i] = k < 0 && errno == EAGAIN ? -2 : (k < 0 ? 0 : k);
  }
}

static Term fd_next_pack(Env e, IoWork* w) {
  FdNext* x  = (FdNext*)w->data;
  Term    xs = term_pak(CID_NIL, 0);
  for (int i = x->n; i > 0; i -= 1) {
    int j = i - 1;
    if (x->len[j] >= 0) {
      Term s = bytes_str(e, x->buf[j], (u64)x->len[j]);
      xs = io_node(e, CID_CON, io_tup(e, (Term)x->tag[j], s), xs);
    }
    free(x->buf[j]);
  }
  free(x);
  return xs;
}

// waits up to ns for registered connections; a zero-timeout look first,
// on the loop, so a busy loop skips the helper-thread round trip
Term fd_next_run(Env e, Term* f, IoWork* w) {
  FdNext* x = io_mem(calloc(1, sizeof(FdNext)));
  x->max  = (u64)(u32)f[0];
  x->ns   = 0;
  w->data = (char*)x;
  u64 ns  = (u64)f[1];
  fd_next_call(w);
  if (x->n > 0 || ns == 0) {
    return fd_next_pack(e, w);
  }
  x->ns = ns;
  return io_work(w, fd_next_call, fd_next_pack);
}

static void __attribute__((constructor)) fd_next_use(void) {
  io_eff(CID_FD_NEXT, fd_next_run, 0);
}

#endif
