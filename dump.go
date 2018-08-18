package main

import (
	"flag"
	"fmt"
)

func dumpCmd() command {
	fs := flag.NewFlagSet("vegeta dump", flag.ExitOnError)
	return command{fs, func([]string) error {
		return fmt.Errorf("vegeta dump has been deprecated and succeeded by the vegeta encode command.")
	}}
}
