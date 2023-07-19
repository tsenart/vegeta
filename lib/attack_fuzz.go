//go:build gofuzz
// +build gofuzz

package vegeta

import (
	"encoding/binary"
	"fmt"
	"net"
	"net/http"
	"os"
	"time"
)

// FuzzAttackerTCP fuzzes binary responses to attacker.
func FuzzAttackerTCP(fuzz []byte) int {
	// Ignore empty fuzz
	if len(fuzz) == 0 {
		return -1
	}

	// Start server
	directory, err := os.MkdirTemp("/tmp", "fuzz")
	if err != nil {
		panic(err.Error())
	}
	socket := fmt.Sprintf("%s/attacker.sock", directory)
	listener, err := net.Listen("unix", socket)
	if err != nil {
		panic(err.Error())
	}
	go func() {
		connection, err := listener.Accept()
		if err != nil {
			panic(err.Error())
		}
		_, err = connection.Write(fuzz)
		if err != nil {
			panic(err.Error())
		}
		err = connection.Close()
		if err != nil {
			panic(err.Error())
		}
	}()
	defer listener.Close()
	defer os.RemoveAll(directory)

	// Setup targeter
	targeter := Targeter(func(target *Target) error {
		target.Method = "GET"
		target.URL = "http://vegeta.test"
		return nil
	})

	// Deliver a single hit
	attacker := NewAttacker(
		UnixSocket(socket),
		Workers(1),
		MaxWorkers(1),
		Timeout(time.Second),
		KeepAlive(false),
	)
	result := attacker.hit(targeter, "fuzz")
	if result.Error != "" {
		return 0
	}
	return 1
}

// FuzzAttackerHTTP fuzzes valid HTTP responses to attacker.
func FuzzAttackerHTTP(fuzz []byte) int {
	// Decode response
	code, headers, body, ok := decodeFuzzResponse(fuzz)
	if !ok {
		return -1
	}

	// Start server
	directory, err := os.MkdirTemp("/tmp", "fuzz")
	if err != nil {
		panic(err.Error())
	}
	socket := fmt.Sprintf("%s/attacker.sock", directory)
	listener, err := net.Listen("unix", socket)
	if err != nil {
		panic(err.Error())
	}
	handler := func(response http.ResponseWriter, request *http.Request) {
		for name, values := range headers {
			for _, value := range values {
				response.Header().Add(name, value)
			}
		}
		response.WriteHeader(int(code))
		_, err := response.Write(body)
		if err != nil {
			panic(err.Error())
		}
	}
	server := http.Server{
		Handler: http.HandlerFunc(handler),
	}
	defer server.Close()
	defer listener.Close()
	defer os.RemoveAll(directory)
	go server.Serve(listener)

	// Setup targeter
	targeter := Targeter(func(target *Target) error {
		target.Method = "GET"
		target.URL = "http://vegeta.test"
		return nil
	})

	// Deliver a single hit
	attacker := NewAttacker(
		UnixSocket(socket),
		Workers(1),
		MaxWorkers(1),
		Timeout(time.Second),
		KeepAlive(false),
	)
	result := attacker.hit(targeter, "fuzz")
	if result.Error != "" {
		return 0
	}
	return 1
}

func decodeFuzzResponse(fuzz []byte) (
	code int,
	headers map[string][]string,
	body []byte,
	ok bool,
) {
	if len(fuzz) < 2 {
		return
	}
	headers = make(map[string][]string)
	body = []byte{}
	code = int(binary.LittleEndian.Uint16(fuzz[0:2]))
	if len(fuzz) == 2 {
		ok = true
		return
	}
	fuzz, ok = decodeFuzzHeaders(fuzz[2:], headers)
	if !ok {
		return
	}
	body = fuzz
	ok = true
	return
}
