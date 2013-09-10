package main

import (
	"flag"
	"log"
	"runtime"
)

// command is a closure function which each command constructor
// builds and returns
type command func() error

func main() {
	commands := map[string]func([]string) command{
		"attack": attackCmd,
		"report": reportCmd,
	}
	// Global flags
	cpus := flag.Int("cpus", runtime.NumCPU(), "Number of CPUs to use")
	flag.Parse()
	args := flag.Args()

	runtime.GOMAXPROCS(*cpus)

	if cmd, ok := commands[args[0]]; !ok {
		log.Fatalf("Unknown command: %s", args[0])
	} else if err := cmd(args[1:])(); err != nil {
		log.Fatal(err)
	}
}
