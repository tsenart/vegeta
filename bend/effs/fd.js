function fd_connect(ip, port) {
  throw new Error("Fd.connect: unsupported on the JS lane");
}

function fd_send(fd, data) {
  throw new Error("Fd.send: unsupported on the JS lane");
}

function fd_close(fd) {
  throw new Error("Fd.close: unsupported on the JS lane");
}

function fd_wait(fds, max, ms) {
  throw new Error("Fd.wait: unsupported on the JS lane");
}

function fd_next(max, ns) {
  throw new Error("Fd.next: unsupported on the JS lane");
}
