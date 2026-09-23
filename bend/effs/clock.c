// Clock
// =====
//
// One file for every Clock.* def (spliced once; each def's part is behind
// its CID, as Base's file_read.c does). Nats are raw words: callers keep
// them under 2^48 (mono_ns: about 78 hours of uptime).

#include <time.h>

// local UTC offset at t, plus 86400 so it is never negative
static u64 clock_offset(time_t t) {
  struct tm lt;
  if (localtime_r(&t, &lt) == NULL) {
    return 86400;
  }
  return (u64)(lt.tm_gmtoff + 86400);
}

#ifdef CID_CLOCK_MONO_NS

// macOS's CLOCK_MONOTONIC (the runtime's io_tick) counts whole µs;
// CLOCK_UPTIME_RAW counts ns (mach_absolute_time, Go's darwin clock)
static u64 clock_mono_now(void) {
#ifdef __APPLE__
  return clock_gettime_nsec_np(CLOCK_UPTIME_RAW);
#else
  return io_tick();
#endif
}

static u64 clock_mono_ns_t0;

// ns since the process started
Term clock_mono_ns_run(Env e, Term* f, IoWork* w) {
  return (Term)(clock_mono_now() - clock_mono_ns_t0);
}

static void __attribute__((constructor)) clock_mono_ns_use(void) {
  clock_mono_ns_t0 = clock_mono_now();
  io_eff(CID_CLOCK_MONO_NS, clock_mono_ns_run, 0);
}

#endif

#ifdef CID_CLOCK_WALL

// (unix seconds, nanoseconds, local offset + 86400)
Term clock_wall_run(Env e, Term* f, IoWork* w) {
  struct timespec ts;
  clock_gettime(CLOCK_REALTIME, &ts);
  u32 off = (u32)clock_offset(ts.tv_sec);
  return io_tup(e, (Term)(u64)ts.tv_sec,
    io_tup(e, (Term)(u64)ts.tv_nsec, (Term)off));
}

static void __attribute__((constructor)) clock_wall_use(void) {
  io_eff(CID_CLOCK_WALL, clock_wall_run, 0);
}

#endif

#ifdef CID_CLOCK_OFFSET_AT

// local offset + 86400 at a unix second (for report timestamps)
Term clock_offset_at_run(Env e, Term* f, IoWork* w) {
  return (Term)clock_offset((time_t)(u64)f[0]);
}

static void __attribute__((constructor)) clock_offset_at_use(void) {
  io_eff(CID_CLOCK_OFFSET_AT, clock_offset_at_run, 0);
}

#endif

#ifdef CID_CLOCK_SLEEP_NS

// nanosleep on a helper thread, so the loop keeps serving the other
// computations; the loop's own timer (select) only has ms resolution.
// w->word is 32 bits, so the ns ride in w->size.
static void clock_sleep_ns_call(IoWork* w) {
  struct timespec ts = { (time_t)(w->size / 1000000000ull),
    (long)(w->size % 1000000000ull) };
  while (nanosleep(&ts, &ts) != 0 && errno == EINTR) {
  }
}

static Term clock_sleep_ns_pack(Env e, IoWork* w) {
  return term_pak(CID_UNIT, 0);
}

Term clock_sleep_ns_run(Env e, Term* f, IoWork* w) {
  w->size = (u64)f[0];
  if (w->size == 0) {
    return term_pak(CID_UNIT, 0);
  }
  return io_work(w, clock_sleep_ns_call, clock_sleep_ns_pack);
}

static void __attribute__((constructor)) clock_sleep_ns_use(void) {
  io_eff(CID_CLOCK_SLEEP_NS, clock_sleep_ns_run, 0);
}

#endif
