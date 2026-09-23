// Bytes
// =====
//
// Byte-faithful IO. Base's io_str decodes UTF-8 and io_cstr encodes it:
// its strings are code points. The port's strings are bytes, one Chr per
// byte (0..255), so these effects copy Base's (tcp_*.c, write.c,
// file_*.c) with the text edge replaced: bytes in become one Chr each,
// and each Chr out is written as its low byte. One file for every def
// (spliced once; each def's part is behind its CID, as Base's
// file_read.c does).

#include <netdb.h>

// one Chr per byte, no decoding (io_str without the UTF-8 step)
static __attribute__((unused)) Term bytes_str(Env e, const char* p, u64 n) {
  Term s    = term_pak(CID_SNIL, 0);
  Loc  hole = 0;
  for (u64 i = 0; i < n; i += 1) {
    Loc  l = heap_alloc(e, 1);
    Term t = term_ctr(CID_SCON, l);
    e.mem[l] = (u64)(uint8_t)p[i];
    if (hole == 0) {
      s = t;
    } else {
      e.mem[hole] = io_seal(e, t, CID_SCON);
    }
    hole = l + 1;
  }
  if (hole != 0) {
    e.mem[hole] = io_seal(e, term_pak(CID_SNIL, 0), CID_SCON);
  }
  return s;
}

// each Chr's low byte, no encoding (io_cstr without the UTF-8 step); a
// malloc'ed, NUL-terminated copy the caller frees
static __attribute__((unused)) char* bytes_cstr(Env e, Term s, u64* len) {
  u64   cap = 64;
  u64   n   = 0;
  char* buf = io_mem(malloc(cap));
  while (term_aux(s) == CID_SCON) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, s, 2, fb));
    if (n + 2 > cap) {
      cap *= 2;
      buf = io_mem(realloc(buf, cap));
    }
    buf[n] = (char)(fb[0] & 0xFF);
    n += 1;
    s = fb[1];
  }
  buf[n] = 0;
  *len = n;
  return buf;
}

// Net
// ---

#ifdef CID_NET_SEND

static Term net_send_more(Env e, IoWork* w) {
  int fd = (int)w->hand;
  while (w->code == 0 && (u64)w->made < w->size) {
    ssize_t n = send(fd, w->data + w->made, w->size - (u64)w->made, 0);
    if (n < 0 && errno == EAGAIN) {
      return io_wait_on(w, fd, POLLOUT, 0, net_send_more);
    }
    if (n < 0 && errno == EINTR) {
      continue;
    }
    w->made += io_sys_end(w, n);
  }
  Term r = w->code != 0 ? io_fail(e, w->code, NULL)
    : io_done(e, term_pak(CID_UNIT, 0));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

Term net_send_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->data = bytes_cstr(e, f[1], &w->size);
  w->made = 0;
  w->code = 0;
  return net_send_more(e, w);
}

static void __attribute__((constructor)) net_send_use(void) {
  io_eff(CID_NET_SEND, net_send_run, 0);
}

#endif

#ifdef CID_NET_RECV

static Term net_recv_pack(Env e, IoWork* w) {
  Term r = w->code ? io_fail(e, w->code, NULL)
    : io_done(e, bytes_str(e, w->data, w->size));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

// parked until readable; a recv that still finds nothing parks again
static Term net_recv_more(Env e, IoWork* w) {
  int fd  = (int)w->hand;
  w->size = io_sys_end(w, recv(fd, w->data, (size_t)w->made, 0));
  return w->code == EAGAIN || w->code == EINTR
    ? io_wait_on(w, fd, POLLIN, 0, net_recv_more) : net_recv_pack(e, w);
}

Term net_recv_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->made = f[1] < INT32_MAX ? (intptr_t)f[1] : INT32_MAX;
  w->data = io_mem(malloc((size_t)w->made + 1));
  return net_recv_more(e, w);
}

static void __attribute__((constructor)) net_recv_use(void) {
  io_eff(CID_NET_RECV, net_recv_run, IO_READ);
}

#endif

#ifdef CID_NET_POLL

// recv with a deadline: Some{bytes} ("" at the peer's close), or None{}
// once ms pass with nothing to read
static Term net_poll_end(Env e, IoWork* w, Term r) {
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

static Term net_poll_more(Env e, IoWork* w) {
  int fd  = (int)w->hand;
  u64 at  = io_wait_time(w);
  w->size = io_sys_end(w, recv(fd, w->data, (size_t)w->made, 0));
  if (w->code == EAGAIN || w->code == EINTR) {
    return io_tick() < at ? io_wait_on(w, fd, POLLIN, at, net_poll_more)
      : net_poll_end(e, w, io_done(e, term_pak(CID_NONE, 0)));
  }
  return net_poll_end(e, w, w->code ? io_fail(e, w->code, NULL) : io_done(e,
    io_box(e, CID_SOME, bytes_str(e, w->data, w->size))));
}

Term net_poll_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->made = f[1] < INT32_MAX ? (intptr_t)f[1] : INT32_MAX;
  w->data = io_mem(malloc((size_t)w->made + 1));
  return io_wait_on(w, (int)w->hand, POLLIN,
    io_tick() + (u64)(u32)f[2] * 1000000ull, net_poll_more);
}

static void __attribute__((constructor)) net_poll_use(void) {
  io_eff(CID_NET_POLL, net_poll_run, 0);
}

#endif

// Out
// ---

#ifdef CID_OUT_WRITE

Term out_write_run(Env e, Term* f, IoWork* w) {
  u64   n    = 0;
  char* data = bytes_cstr(e, f[0], &n);
  io_out(stdout, data, n);
  free(data);
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) out_write_use(void) {
  io_eff(CID_OUT_WRITE, out_write_run, 0);
}

#endif

#ifdef CID_OUT_WRITE_ERR

// stdout is flushed first, as IO.print_err does, so the two interleave in
// program order
Term out_write_err_run(Env e, Term* f, IoWork* w) {
  u64   n    = 0;
  char* data = bytes_cstr(e, f[0], &n);
  io_sync();
  io_out(stderr, data, n);
  fflush(stderr);
  free(data);
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) out_write_err_use(void) {
  io_eff(CID_OUT_WRITE_ERR, out_write_err_run, 0);
}

#endif

#ifdef CID_OUT_TO_FILE

// points stdout at path (created or truncated): Out.write then streams
// there. Pending output is flushed to the old stdout first.
Term out_to_file_run(Env e, Term* f, IoWork* w) {
  u64   n    = 0;
  char* path = bytes_cstr(e, f[0], &n);
  if (io_nul(path, n)) {
    free(path);
    return io_fail(e, EILSEQ, NULL);
  }
  io_sync();
  fflush(stdout);
  int fd;
  do {
    fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  } while (fd < 0 && errno == EINTR);
  free(path);
  if (fd < 0) {
    return io_fail(e, (u32)errno, NULL);
  }
  int ok = dup2(fd, fileno(stdout));
  u32 code = ok < 0 ? (u32)errno : 0;
  close(fd);
  return code ? io_fail(e, code, NULL) : io_done(e, term_pak(CID_UNIT, 0));
}

static void __attribute__((constructor)) out_to_file_use(void) {
  io_eff(CID_OUT_TO_FILE, out_to_file_run, 0);
}

#endif

// Stdin
// -----

#ifdef CID_STDIN_READ

static void stdin_read_call(IoWork* w) {
  ssize_t n;
  do {
    n = read(0, w->data, w->word);
  } while (n < 0 && errno == EINTR);
  w->size = io_sys_end(w, n);
}

static Term stdin_read_pack(Env e, IoWork* w) {
  Term r = w->code ? io_fail(e, w->code, NULL)
    : io_done(e, bytes_str(e, w->data, w->size));
  free(w->data);
  return r;
}

// up to max bytes ("" at EOF), read on a helper thread
Term stdin_read_run(Env e, Term* f, IoWork* w) {
  u32 max = (u32)f[0];
  w->word = max < INT32_MAX ? max : INT32_MAX;
  w->data = io_mem(malloc(w->word + 1));
  return io_work(w, stdin_read_call, stdin_read_pack);
}

static void __attribute__((constructor)) stdin_read_use(void) {
  io_eff(CID_STDIN_READ, stdin_read_run, 0);
}

#endif

// Files
// -----

#ifdef CID_FILES_READ

// the whole file into w->data; the path arrives in w->text
static void files_read_call(IoWork* w) {
  int fd;
  do {
    fd = open(w->text, O_RDONLY);
  } while (fd < 0 && errno == EINTR);
  if (fd < 0) {
    w->code = (u32)errno;
    return;
  }
  u64 cap = 65536;
  w->size = 0;
  w->data = malloc(cap);
  w->code = w->data == NULL ? ENOMEM : 0;
  while (w->code == 0) {
    if (w->size == cap) {
      char* more = realloc(w->data, cap * 2);
      if (more == NULL) {
        w->code = ENOMEM;
        break;
      }
      w->data = more;
      cap *= 2;
    }
    ssize_t n = read(fd, w->data + w->size, cap - w->size);
    if (n < 0 && errno == EINTR) {
      continue;
    }
    if (n <= 0) {
      w->code = n < 0 ? (u32)errno : 0;
      break;
    }
    w->size += (u64)n;
  }
  close(fd);
}

static Term files_read_pack(Env e, IoWork* w) {
  Term r = w->code ? io_fail(e, w->code, NULL)
    : io_done(e, bytes_str(e, w->data, w->size));
  free(w->data);
  free(w->text);
  return r;
}

Term files_read_run(Env e, Term* f, IoWork* w) {
  u64 n   = 0;
  w->text = bytes_cstr(e, f[0], &n);
  w->data = NULL;
  w->size = 0;
  w->code = 0;
  if (io_nul(w->text, n)) {
    w->code = EILSEQ;
    return files_read_pack(e, w);
  }
  return io_work(w, files_read_call, files_read_pack);
}

static void __attribute__((constructor)) files_read_use(void) {
  io_eff(CID_FILES_READ, files_read_run, 0);
}

#endif

#ifdef CID_FILES_WRITE

// create or truncate w->text, then write all of w->data
static void files_write_call(IoWork* w) {
  int fd;
  do {
    fd = open(w->text, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  } while (fd < 0 && errno == EINTR);
  if (fd < 0) {
    w->code = (u32)errno;
    return;
  }
  w->code = 0;
  for (u64 at = 0; at < w->size;) {
    ssize_t n = write(fd, w->data + at, w->size - at);
    if (n < 0 && errno == EINTR) {
      continue;
    }
    if (n < 0) {
      w->code = (u32)errno;
      break;
    }
    at += (u64)n;
  }
  if (close(fd) != 0 && w->code == 0) {
    w->code = (u32)errno;
  }
}

static Term files_write_pack(Env e, IoWork* w) {
  Term r = w->code ? io_fail(e, w->code, NULL)
    : io_done(e, term_pak(CID_UNIT, 0));
  free(w->data);
  free(w->text);
  return r;
}

Term files_write_run(Env e, Term* f, IoWork* w) {
  u64 n   = 0;
  w->text = bytes_cstr(e, f[0], &n);
  w->data = bytes_cstr(e, f[1], &w->size);
  w->code = 0;
  if (io_nul(w->text, n)) {
    w->code = EILSEQ;
    return files_write_pack(e, w);
  }
  return io_work(w, files_write_call, files_write_pack);
}

static void __attribute__((constructor)) files_write_use(void) {
  io_eff(CID_FILES_WRITE, files_write_run, 0);
}

#endif

// Dns
// ---

#ifdef CID_DNS_RESOLVE

// the first IPv4 address of w->text, dotted, into w->data; a failure is
// getaddrinfo's code in w->code
static void dns_resolve_call(IoWork* w) {
  struct addrinfo hints, *res = NULL;
  memset(&hints, 0, sizeof(hints));
  hints.ai_family   = AF_INET;
  hints.ai_socktype = SOCK_STREAM;
  int rc = getaddrinfo(w->text, NULL, &hints, &res);
  if (rc != 0 || res == NULL) {
    w->code = rc != 0 ? (u32)rc : (u32)EAI_NONAME;
    return;
  }
  w->data = malloc(INET_ADDRSTRLEN);
  if (w->data == NULL || inet_ntop(AF_INET,
      &((struct sockaddr_in*)res->ai_addr)->sin_addr, w->data,
      INET_ADDRSTRLEN) == NULL) {
    w->code = (u32)EAI_MEMORY;
  } else {
    w->size = strlen(w->data);
    w->code = 0;
  }
  freeaddrinfo(res);
}

static Term dns_resolve_pack(Env e, IoWork* w) {
  Term r = w->code == 0 ? io_done(e, bytes_str(e, w->data, w->size))
    : w->code == (u32)-1 ? io_fail(e, EILSEQ, NULL)
    : io_fail(e, w->code, gai_strerror((int)w->code));
  free(w->data);
  free(w->text);
  return r;
}

Term dns_resolve_run(Env e, Term* f, IoWork* w) {
  u64 n   = 0;
  w->text = bytes_cstr(e, f[0], &n);
  w->data = NULL;
  w->size = 0;
  w->code = 0;
  if (io_nul(w->text, n) || n == 0) {
    w->code = (u32)-1;
    return dns_resolve_pack(e, w);
  }
  return io_work(w, dns_resolve_call, dns_resolve_pack);
}

static void __attribute__((constructor)) dns_resolve_use(void) {
  io_eff(CID_DNS_RESOLVE, dns_resolve_run, 0);
}

#endif
