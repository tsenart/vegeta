//go:build windows
// +build windows

package main

import (
	"os"
	"os/exec"
)

func clearScreen() error {
	cmd := exec.Command("cmd", "/c", "cls")
	cmd.Stdout = os.Stdout
	return cmd.Run()
}
