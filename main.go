package main

import (
	"flag"
	"fmt"
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
		reporter = flag.String("reporter", "text", "Reporter to use [text, plot:timings]")
		output   = flag.String("output", "stdout", "Reporter output file")
	)
	flag.Parse()

	if flag.NFlag() == 0 {
		flag.Usage()
		return
	}

	if err := run(*rate, *duration, *targetsf, *ordering, *reporter, *output); err != nil {
		log.Fatal(err)
	}
}

const (
	errRatePrefix        = "Rate: "
	errDurationPrefix    = "Duration: "
	errOutputFilePrefix  = "Output file: "
	errTargetsFilePrefix = "Targets file: "
	errOrderingPrefix    = "Ordering: "
	errReportingPrefix   = "Reporting: "
)

// run is an utility function that validates the attack arguments, sets up the
// required resources, launches the attack and reports the results
func run(rate uint64, duration time.Duration, targetsf, ordering, reporter, output string) error {
	if rate == 0 {
		return fmt.Errorf(errRatePrefix + "can't be zero")
	}

	if duration == 0 {
		return fmt.Errorf(errDurationPrefix + "can't be zero")
	}

	var out io.Writer
	switch output {
	case "stdout":
		out = os.Stdout
	default:
		file, err := os.Create(output)
		if err != nil {
			return fmt.Errorf(errOutputFilePrefix+"(%s): %s", output, err)
		}
		defer file.Close()
		out = file
	}

	var rep vegeta.Reporter
	switch reporter {
	case "text":
		rep = vegeta.NewTextReporter()
	case "plot:timings":
		rep = vegeta.NewTimingsPlotReporter()
	default:
		log.Println("Reporter provided is not supported. Using text")
		rep = vegeta.NewTextReporter()
	}

	targets, err := vegeta.NewTargetsFromFile(targetsf)
	if err != nil {
		return fmt.Errorf(errTargetsFilePrefix+"(%s): %s", targetsf, err)
	}

	switch ordering {
	case "random":
		targets.Shuffle(time.Now().UnixNano())
	case "sequential":
		break
	default:
		return fmt.Errorf(errOrderingPrefix+"`%s` is invalid", ordering)
	}

	log.Printf("Vegeta is attacking %d targets in %s order for %s...\n", len(targets), ordering, duration)
	vegeta.Attack(targets, rate, duration, rep)
	log.Println("Done!")

	log.Printf("Writing report to '%s'...", output)
	if err = rep.Report(out); err != nil {
		return fmt.Errorf(errReportingPrefix+"%s", err)
	}
	return nil
}
