package vegeta

import (
	"fmt"
	"net"
	"os"
	"strconv"
	"strings"
)

// Used to adjust the max-workers while vegeta is running
func readMaxWorkerFromSocket(socketPath string, attacker *Attacker) {
	// Create a Unix domain socket and listen for incoming connections.
	socket, err := net.Listen("unix", socketPath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "socket err1: %s\n", err)
		return
	}

	// Wait for stopch to close and then shutdown socket
	go func(attacker *Attacker, socket net.Listener) {
		<-attacker.stopch
		_ = socket.Close()
		_ = os.Remove(socketPath)
	}(attacker, socket)

	for {
		// Accept an incoming connection.
		conn, err := socket.Accept()
		if err != nil {
			fmt.Fprintf(os.Stderr, "socket err2: %v\n", err)
			return
		}

		// Handle the connection in a separate goroutine.
		go func(conn net.Conn) {
			defer conn.Close()
			// Create a buffer for incoming data.
			buf := make([]byte, 4096)

			// Read data from the connection.
			n, err := conn.Read(buf)
			if err != nil {
				fmt.Fprintf(os.Stderr, "socket err3: %v\n", err)
				return
			}

			input := string(buf[:n])
			input = strings.TrimSpace(input)
			input = strings.Trim(input, "\n\r")
			i, err := strconv.ParseUint(input, 10, 64)
			if err != nil {
				fmt.Fprintf(os.Stderr, "socket err4: %v\n", err)
			}
			attacker.AdjustMaxWokers(i)
			fmt.Fprintf(os.Stderr, "worker update: %v\n", attacker.maxWorkers)
		}(conn)
	}
}
