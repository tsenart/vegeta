// Bytes
// =====
//
// The port targets the native lane only; these twins exist because every
// effect def needs a .js import. Each fails as its type allows: a Result
// answers Fail (95, EOPNOTSUPP), a handle is handed back beside it, and a
// Unit effect throws.

function bytes_unsupported() {
  return { $: "Fail", error: io_tup(95, "unsupported on the JS lane") };
}

function net_send(sock, data) {
  return io_tup(sock, bytes_unsupported());
}

function net_recv(sock, max) {
  return io_tup(sock, bytes_unsupported());
}

function net_poll(sock, max, ms) {
  return io_tup(sock, bytes_unsupported());
}

function out_write(data) {
  throw new Error("Out.write: unsupported on the JS lane");
}

function out_to_file(path) {
  throw new Error("Out.to_file: unsupported on the JS lane");
}

function out_write_err(data) {
  throw new Error("Out.write_err: unsupported on the JS lane");
}

function stdin_read(max) {
  return bytes_unsupported();
}

function files_read(path) {
  return bytes_unsupported();
}

function files_write(path, data) {
  return bytes_unsupported();
}

function dns_resolve(host) {
  return bytes_unsupported();
}

function pieces_open(path) {
  return bytes_unsupported();
}

function pieces_read(fd, max, size) {
  return bytes_unsupported();
}

function pieces_lines(i, j) {
  return { $: "Nil" };
}

function pieces_close(fd) {
  return { $: "Unit" };
}

function pieces_again(from) {
  return { $: "Nil" };
}

function out_lines(xs) {
  throw new Error("Out.lines: unsupported on the JS lane");
}
