package main

import (
	"fmt"
)

func dumpCmd() command {
	return command{fn: func([]string) error {
		return fmt.Errorf("vegeta dump has been deprecated and succeeded by the vegeta encode command")
	}}
}
