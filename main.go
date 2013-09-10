package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"runtime"
)

// command is a closure function which each command constructor
// builds and returns
type command func() error

var usage = fmt.Sprintf(
	`Usage: vegeta [globals] <command> [options]

Commands:
  attack  Hit the targets
  report  Report the results

Globals:
  -cpus=%d Number of CPUs to use
`, runtime.NumCPU())

func init() {
	flag.Usage = func() { fmt.Print(usage) }
	cpus := flag.Int("cpus", runtime.NumCPU(), "Number of CPUs to use")
	flag.Parse()
	runtime.GOMAXPROCS(*cpus)
}

func main() {
	commands := map[string]func([]string) command{
		"attack": attackCmd,
		"report": reportCmd,
	}

	args := flag.Args()
	if len(args) == 0 {
		flag.Usage()
		os.Exit(1)
	}

	if cmd, ok := commands[args[0]]; !ok {
		log.Fatalf("Unknown command: %s", args[0])
	} else if err := cmd(args[1:])(); err != nil {
		log.Fatal(err)
	}
}
