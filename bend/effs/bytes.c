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

#ifdef CID_OUT_LINES

// writes each string of a list, last first: the attack keeps its result
// lines newest first, so no joined copy is built. Each string is read
// straight into one buffer.
Term out_lines_run(Env e, Term* f, IoWork* w) {
  u64    cap = 0;
  u64    k   = 0;
  Term*  xs  = NULL;
  Term   l   = f[0];
  while (term_aux(l) == CID_CON) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, l, 2, fb));
    if (k == cap) {
      cap = cap ? cap * 2 : 64;
      xs  = io_mem(realloc(xs, sizeof(Term) * cap));
    }
    xs[k] = fb[0];
    k += 1;
    l = fb[1];
  }
  for (u64 i = k; i > 0; i -= 1) {
    u64   n    = 0;
    char* data = bytes_cstr(e, xs[i - 1], &n);
    io_out(stdout, data, n);
    free(data);
  }
  free(xs);
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) out_lines_use(void) {
  io_eff(CID_OUT_LINES, out_lines_run, 0);
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

// Pieces
// ------
//
// Input read in batches and cut into pieces for decoding in parallel:
// each piece runs through the last LF in its first `size` bytes, or
// through the first LF after them (the report's own rule), so no record
// is ever cut by a piece unless it holds a raw LF. A piece comes as its
// lines, each packed (see lib/sys.bend). The last two batches stay here,
// for Pieces.again; the bytes after a batch's last LF wait for the next.

#if defined(CID_PIECES_READ) || defined(CID_PIECES_AGAIN) || defined(CID_PIECES_LINES) || defined(CID_PIECES_OPEN) || defined(CID_PIECES_CLOSE)

// a batch: its bytes, and where each piece it was cut into ends
typedef struct {
  char* data;
  u64*  ends;
  u64   k;
} PiecesBatch;

static PiecesBatch pieces_prev  = {NULL, NULL, 0};
static PiecesBatch pieces_cur   = {NULL, NULL, 0};
static char*       pieces_carry = NULL;
static u64         pieces_carry_n = 0;

// the length of the piece p[0..n) starts with, or 0 without a LF
static u64 piece_len(const char* p, u64 n, u64 size) {
  u64 lim = n < size ? n : size;
  for (u64 i = lim; i > 0; i -= 1) {
    if (p[i - 1] == '\n') {
      return i;
    }
  }
  const char* q = lim < n ? memchr(p + lim, '\n', n - lim) : NULL;
  return q ? (u64)(q - p) + 1 : 0;
}

// the bytes p[0..n) packed for the Bend side to unpack in parallel: the
// count of bytes in the last word (0 for none), then the words, last
// first, four bytes each, the first byte lowest
static Term packed(Env e, const uint8_t* p, u64 n) {
  Term xs = term_pak(CID_NIL, 0);
  u64  w  = n / 4;
  for (u64 i = 0; i < w; i += 1) {
    const uint8_t* q = p + 4 * i;
    u32 v = (u32)q[0] | (u32)q[1] << 8 | (u32)q[2] << 16 | (u32)q[3] << 24;
    xs = io_node(e, CID_CON, (Term)v, xs);
  }
  u64 k = n % 4;
  if (k > 0) {
    const uint8_t* q = p + 4 * w;
    u32 v = 0;
    for (u64 j = 0; j < k; j += 1) {
      v |= (u32)q[j] << (8 * j);
    }
    xs = io_node(e, CID_CON, (Term)v, xs);
  } else if (w > 0) {
    k = 4;
  }
  return io_node(e, CID_CON, (Term)k, xs);
}

// the lines of p[0..n) (each with its LF; the last maybe without), each
// packed
static Term packed_lines(Env e, const uint8_t* p, u64 n) {
  Term xs  = term_pak(CID_NIL, 0);
  u64  end = n;
  while (end > 0) {
    u64 start = end - 1;
    while (start > 0 && p[start - 1] != '\n') {
      start -= 1;
    }
    xs  = io_node(e, CID_CON, packed(e, p + start, end - start), xs);
    end = start;
  }
  return xs;
}

// a batch's pieces from the one at index from on, as their lines
static Term batch_from(Env e, PiecesBatch* b, u64 from) {
  Term xs = term_pak(CID_NIL, 0);
  for (u64 i = b->k; i > from; i -= 1) {
    u64 start = i > 1 ? b->ends[i - 2] : 0;
    xs = io_node(e, CID_CON, packed_lines(e, (const uint8_t*)b->data + start, b->ends[i - 1] - start), xs);
  }
  return xs;
}

// p[0..n) (which this takes) cut into pieces, as the new batch: the
// pieces, then the bytes after the last one when tail is set and they
// are not empty; *used is the length they cover
static Term pieces_of(Env e, char* p, u64 n, u64 size, int tail, u64* used) {
  free(pieces_prev.data);
  free(pieces_prev.ends);
  pieces_prev = pieces_cur;
  u64  cap  = 64;
  u64  k    = 0;
  u64* ends = io_mem(malloc(cap * sizeof(u64)));
  u64  at   = 0;
  for (;;) {
    u64 m = piece_len(p + at, n - at, size);
    if (m == 0 && !(tail && at < n)) {
      break;
    }
    if (k == cap) {
      cap *= 2;
      ends = io_mem(realloc(ends, cap * sizeof(u64)));
    }
    if (m == 0) {
      ends[k] = n;
      k += 1;
      break;
    }
    at += m;
    ends[k] = at;
    k += 1;
  }
  *used      = at;
  pieces_cur = (PiecesBatch){p, ends, k};
  return batch_from(e, &pieces_cur, 0);
}

#endif

#ifdef CID_PIECES_AGAIN

// the batch before the last one, from the piece at index from on, again
Term pieces_again_run(Env e, Term* f, IoWork* w) {
  u64 from = (u64)(u32)f[0];
  return batch_from(e, &pieces_prev, from < pieces_prev.k ? from : pieces_prev.k);
}

static void __attribute__((constructor)) pieces_again_use(void) {
  io_eff(CID_PIECES_AGAIN, pieces_again_run, 0);
}

#endif

#ifdef CID_PIECES_LINES

// the batch before the last one: the piece at index i, from its line at
// index j on
Term pieces_lines_run(Env e, Term* f, IoWork* w) {
  u64 i = (u64)(u32)f[0];
  u64 j = (u64)(u32)f[1];
  if (i >= pieces_prev.k) {
    return term_pak(CID_NIL, 0);
  }
  const uint8_t* p     = (const uint8_t*)pieces_prev.data;
  u64            start = i > 0 ? pieces_prev.ends[i - 1] : 0;
  u64            end   = pieces_prev.ends[i];
  for (u64 l = 0; l < j && start < end; l += 1) {
    const uint8_t* q = memchr(p + start, '\n', end - start);
    start = q ? (u64)(q - p) + 1 : end;
  }
  return packed_lines(e, p + start, end - start);
}

static void __attribute__((constructor)) pieces_lines_use(void) {
  io_eff(CID_PIECES_LINES, pieces_lines_run, 0);
}

#endif

#ifdef CID_PIECES_OPEN

// path opened for reading, as a descriptor; nothing waits from before
Term pieces_open_run(Env e, Term* f, IoWork* w) {
  u64   n    = 0;
  char* path = bytes_cstr(e, f[0], &n);
  if (io_nul(path, n)) {
    free(path);
    return io_fail(e, EILSEQ, NULL);
  }
  int fd;
  do {
    fd = open(path, O_RDONLY);
  } while (fd < 0 && errno == EINTR);
  free(path);
  if (fd < 0) {
    return io_fail(e, (u32)errno, NULL);
  }
  free(pieces_carry);
  pieces_carry   = NULL;
  pieces_carry_n = 0;
  return io_done(e, (Term)(u32)fd);
}

static void __attribute__((constructor)) pieces_open_use(void) {
  io_eff(CID_PIECES_OPEN, pieces_open_run, 0);
}

#endif

#ifdef CID_PIECES_CLOSE

Term pieces_close_run(Env e, Term* f, IoWork* w) {
  int fd = (int)(u32)f[0];
  if (fd > 2) {
    close(fd);
  }
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) pieces_close_use(void) {
  io_eff(CID_PIECES_CLOSE, pieces_close_run, 0);
}

#endif

#ifdef CID_PIECES_READ

// reads fd (w->made) onto the carry (w->data, w->size) until max bytes
// and a LF past the carry, or EOF (then w->made = -1)
static void pieces_read_call(IoWork* w) {
  int   fd  = (int)w->made;
  u64   cap = w->size + (u64)w->word + 65536;
  int   nl  = 0;
  char* d   = realloc(w->data, cap);
  if (d == NULL) {
    w->code = ENOMEM;
    return;
  }
  w->data = d;
  while (!(nl && w->size >= (u64)w->word)) {
    if (w->size == cap) {
      char* more = realloc(w->data, cap * 2);
      if (more == NULL) {
        w->code = ENOMEM;
        return;
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
      w->made = -1;
      return;
    }
    if (!nl && memchr(w->data + w->size, '\n', (size_t)n) != NULL) {
      nl = 1;
    }
    w->size += (u64)n;
  }
}

static Term pieces_read_pack(Env e, IoWork* w) {
  if (w->code) {
    free(w->data);
    return io_fail(e, w->code, NULL);
  }
  u64  used = 0;
  int  eof  = w->made == -1;
  Term xs   = pieces_of(e, w->data, w->size, (u64)w->hand, eof, &used);
  if (!eof && used < w->size) {
    pieces_carry_n = w->size - used;
    pieces_carry   = io_mem(malloc(pieces_carry_n));
    memcpy(pieces_carry, w->data + used, pieces_carry_n);
  }
  return io_done(e, xs);
}

// at least max bytes of fd (or all that is left) cut into pieces of
// about size bytes; a line not ended yet waits for the next call, and
// the last line, ended or not, comes at EOF; [] only at EOF
Term pieces_read_run(Env e, Term* f, IoWork* w) {
  w->made = (intptr_t)(u32)f[0];
  w->word = (u32)f[1] < INT32_MAX ? (u32)f[1] : INT32_MAX;
  w->hand = (intptr_t)((u32)f[2] > 0 ? (u32)f[2] : 1);
  w->data = pieces_carry;
  w->size = pieces_carry_n;
  w->code = 0;
  pieces_carry   = NULL;
  pieces_carry_n = 0;
  return io_work(w, pieces_read_call, pieces_read_pack);
}

static void __attribute__((constructor)) pieces_read_use(void) {
  io_eff(CID_PIECES_READ, pieces_read_run, 0);
}

#endif
