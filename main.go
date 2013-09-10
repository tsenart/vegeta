package main

import (
	"flag"
	"log"
	"runtime"
	"time"
)

func main() {
	// Global flags
	cpus := flag.Int("cpus", runtime.NumCPU(), "Number of CPUs to use")
	flag.Parse()
	runtime.GOMAXPROCS(*cpus)

	args := flag.Args()
	if len(args) < 1 {
		log.Fatal("Unspecified command")
	}
	cmd, cmdf := args[0], flag.NewFlagSet(args[0], flag.ExitOnError)

	switch cmd {
	case "attack":
		rate := cmdf.Uint64("rate", 50, "Requests per second")
		targetsf := cmdf.String("targets", "targets.txt", "Targets file")
		ordering := cmdf.String("ordering", "random", "Attack ordering [sequential, random]")
		duration := cmdf.Duration("duration", 10*time.Second, "Duration of the test")
		output := cmdf.String("output", "stdout", "Vegeta Results file")

		if err := cmdf.Parse(args[1:]); err != nil {
			log.Fatal(err)
		}
		if err := attack(*rate, *duration, *targetsf, *ordering, *output); err != nil {
			log.Fatal(err)
		}
	case "report":
		reporter := cmdf.String("reporter", "text", "Reporter [text, json, plot:timings]")
		input := cmdf.String("input", "stdin", "Vegeta Results file")
		output := cmdf.String("output", "stdout", "Output file")

		if err := cmdf.Parse(args[1:]); err != nil {
			log.Fatal(err)
		}
		if err := report(*reporter, *input, *output); err != nil {
			log.Fatal(err)
		}
	default:
		log.Fatalf("Unknown command: %s", cmd)
	}
}
