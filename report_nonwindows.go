// +build !windows

package main

import (
	"os"
)

var escCodes = []byte("\033[2J\033[0;0H")

func clearScreen() error {
	_, err := os.Stdout.Write(escCodes)
	return err
}
