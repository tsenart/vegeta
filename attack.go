package main

import (
	"fmt"
	vegeta "github.com/tsenart/vegeta/lib"
	"io"
	"log"
	"os"
	"time"
)

const (
	errRatePrefix        = "Rate: "
	errDurationPrefix    = "Duration: "
	errOutputFilePrefix  = "Output file: "
	errTargetsFilePrefix = "Targets file: "
	errOrderingPrefix    = "Ordering: "
	errReportingPrefix   = "Reporting: "
)

// attack is the command function that validates the attack arguments, sets up the
// required resources, launches the attack and reports the results
func attack(rate uint64, duration time.Duration, targetsf, ordering, output string) error {
	if rate == 0 {
		return fmt.Errorf(errRatePrefix + "can't be zero")
	}

	if duration == 0 {
		return fmt.Errorf(errDurationPrefix + "can't be zero")
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

	log.Printf("Vegeta is attacking %d targets in %s order for %s...\n", len(targets), ordering, duration)
	results := vegeta.Attack(targets, rate, duration)
	log.Println("Done!")
	log.Printf("Writing results to '%s'...", output)
	if err := results.WriteTo(out); err != nil {
		return err
	}
	return nil
}
