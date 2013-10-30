package main

import (
	"flag"
	"fmt"
	vegeta "github.com/tsenart/vegeta/lib"
	"log"
	"time"
)

func attackCmd(args []string) command {
	fs := flag.NewFlagSet("attack", flag.ExitOnError)
	rate := fs.Uint64("rate", 50, "Requests per second")
	targetsf := fs.String("targets", "stdin", "Targets file")
	ordering := fs.String("ordering", "random", "Attack ordering [sequential, random]")
	duration := fs.Duration("duration", 10*time.Second, "Duration of the test")
	output := fs.String("output", "stdout", "Output file")
	hdrs := new(vegeta.Headers)
	fs.Var(hdrs, "header", "Targets request header")
	fs.Parse(args)

	return func() error {
		return attack(*rate, *duration, *targetsf, *ordering, *output, hdrs)
	}
}

// attack validates the attack arguments, sets up the
// required resources, launches the attack and writes the results
func attack(rate uint64, duration time.Duration, targetsf, ordering, output string, hdrs *vegeta.Headers) error {
	if rate == 0 {
		return fmt.Errorf(errRatePrefix + "can't be zero")
	}

	if duration == 0 {
		return fmt.Errorf(errDurationPrefix + "can't be zero")
	}

	in, err := file(targetsf, false)
	if err != nil {
		return fmt.Errorf(errTargetsFilePrefix+"(%s): %s", targetsf, err)
	}
	defer in.Close()
	targets, err := vegeta.NewTargetsFrom(in)
	if err != nil {
		return fmt.Errorf(errTargetsFilePrefix+"(%s): %s", targetsf, err)
	}
	targets.SetHeaders(hdrs)

	switch ordering {
	case "random":
		targets.Shuffle(time.Now().UnixNano())
	case "sequential":
		break
	default:
		return fmt.Errorf(errOrderingPrefix+"`%s` is invalid", ordering)
	}

	out, err := file(output, true)
	if err != nil {
		return fmt.Errorf(errOutputFilePrefix+"(%s): %s", output, err)
	}
	defer out.Close()

	log.Printf("Vegeta is attacking %d targets in %s order for %s...\n", len(targets), ordering, duration)
	results := vegeta.Attack(targets, rate, duration)
	log.Println("Done!")
	log.Printf("Writing results to '%s'...", output)
	if err := results.Encode(out); err != nil {
		return err
	}
	return nil
}

const (
	errRatePrefix        = "Rate: "
	errDurationPrefix    = "Duration: "
	errOutputFilePrefix  = "Output file: "
	errTargetsFilePrefix = "Targets file: "
	errOrderingPrefix    = "Ordering: "
	errReportingPrefix   = "Reporting: "
)
