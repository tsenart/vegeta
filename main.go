package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"runtime"
)

func main() {
	commands := map[string]command{"attack": attackCmd(), "report": reportCmd()}

	flag.Usage = func() {
		fmt.Println("Usage: vegeta [globals] <command> [options]")
		for name, cmd := range commands {
			fmt.Printf("\n%s command:\n", name)
			cmd.fs.PrintDefaults()
		}
		fmt.Printf("\nglobal flags:\n  -cpus=%d Number of CPUs to use\n", runtime.NumCPU())
		fmt.Println(examples)
	}

	cpus := flag.Int("cpus", runtime.NumCPU(), "Number of CPUs to use")
	flag.Parse()

	runtime.GOMAXPROCS(*cpus)

	args := flag.Args()
	if len(args) == 0 {
		flag.Usage()
		os.Exit(1)
	}

	if cmd, ok := commands[args[0]]; !ok {
		log.Fatalf("Unknown command: %s", args[0])
	} else if err := cmd.fn(args[1:]); err != nil {
		log.Fatal(err)
	}
}

const examples = `
examples:
  echo "GET http://localhost/" | vegeta attack -duration=5s | tee results.bin | vegeta report
  vegeta attack -targets=targets.txt > results.bin
  vegeta report -input=results.bin -reporter=json > metrics.json
  cat results.bin | vegeta report -reporter=plot > plot.html
`

type command struct {
	fs *flag.FlagSet
	fn func(args []string) error
}
