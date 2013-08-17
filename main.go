package main

import (
	"flag"
	vegeta "github.com/tsenart/vegeta/lib"
	"io"
	"log"
	"os"
	"runtime"
	"time"
)

func init() {
	runtime.GOMAXPROCS(runtime.NumCPU())
}

func main() {
	var (
		rate     = flag.Uint64("rate", 50, "Requests per second")
		targetsf = flag.String("targets", "targets.txt", "Targets file")
		ordering = flag.String("ordering", "random", "Attack ordering [sequential, random]")
		duration = flag.Duration("duration", 10*time.Second, "Duration of the test")
		reporter = flag.String("reporter", "text", "Reporter to use [text]")
		output   = flag.String("output", "stdout", "Reporter output file")
	)
	flag.Parse()

	if flag.NFlag() == 0 {
		flag.Usage()
		return
	}

	if *rate == 0 {
		log.Fatal("rate can't be zero")
	}

	targets, err := vegeta.NewTargetsFromFile(*targetsf)
	if err != nil {
		log.Fatal(err)
	}

	switch *ordering {
	case "random":
		targets.Shuffle(time.Now().UnixNano())
	case "sequential":
		break
	default:
		log.Fatalf("Unknown ordering %s", *ordering)
	}

	if *duration == 0 {
		log.Fatal("Duration provided is invalid")
	}

	var rep vegeta.Reporter
	switch *reporter {
	case "text":
		rep = vegeta.NewTextReporter()
	default:
		log.Println("reporter provided is not supported. using text")
		rep = vegeta.NewTextReporter()
	}

	var out io.Writer
	switch *output {
	case "stdout":
		out = os.Stdout
	default:
		file, err := os.Create(*output)
		if err != nil {
			log.Fatalf("Couldn't open `%s` for writing report: %s", *output, err)
		}
		defer file.Close()
		out = file
	}

	log.Printf("Vegeta is attacking %d targets in %s order for %s...\n", len(targets), *ordering, *duration)
	vegeta.Attack(targets, *rate, *duration, rep)
	log.Println("Done!")

	log.Printf("Writing report to '%s'...", *output)
	if rep.Report(out) != nil {
		log.Println("Failed to report!")
	}
}
