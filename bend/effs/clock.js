// Clock
// =====
//
// The port targets the native lane only; these twins exist because every
// effect def needs a .js import.

function clock_mono_ns() {
  throw new Error("Clock.mono_ns: unsupported on the JS lane");
}

function clock_wall() {
  throw new Error("Clock.wall: unsupported on the JS lane");
}

function clock_offset_at(sec) {
  throw new Error("Clock.offset_at: unsupported on the JS lane");
}

function clock_sleep_ns(ns) {
  throw new Error("Clock.sleep_ns: unsupported on the JS lane");
}
