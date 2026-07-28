package main

import (
	"io"
	"os"
	"strings"
	"testing"
)

func TestAttackCmdLegacyBooleanStyleUsesNormalizedBooleanParsing(t *testing.T) {
	t.Parallel()

	cmd := attackCmd()
	err := cmd.fn([]string{"-keepalive", "false", "-rate", "0", "-duration", "1s"})
	if err == nil {
		t.Fatal("expected command parsing to fail for -rate=0")
	}
	if !strings.Contains(err.Error(), "-rate=0 requires setting -max-workers") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestAttackCmdAttachedBooleanStyleUsesNormalizedBooleanParsing(t *testing.T) {
	t.Parallel()

	cmd := attackCmd()
	err := cmd.fn([]string{"-keepalive=false", "-rate", "0", "-duration", "1s"})
	if err == nil {
		t.Fatal("expected command parsing to fail for -rate=0")
	}
	if !strings.Contains(err.Error(), "-rate=0 requires setting -max-workers") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestMainVersionPrintsBuildMetadata(t *testing.T) {
	origArgs := os.Args
	origStdout := os.Stdout
	origVersion := Version
	origCommit := Commit
	origDate := Date
	defer func() {
		os.Args = origArgs
		os.Stdout = origStdout
		Version = origVersion
		Commit = origCommit
		Date = origDate
	}()

	Version = "v0.0.0-test"
	Commit = "commit-test"
	Date = "2026-07-28"

	r, w, err := os.Pipe()
	if err != nil {
		t.Fatalf("os.Pipe() error: %v", err)
	}
	os.Stdout = w
	os.Args = []string{"vegeta", "--version"}

	main()

	if err := w.Close(); err != nil {
		t.Fatalf("pipe close error: %v", err)
	}
	output, err := io.ReadAll(r)
	if err != nil {
		t.Fatalf("read output error: %v", err)
	}
	if err := r.Close(); err != nil {
		t.Fatalf("pipe close error: %v", err)
	}

	if got := string(output); !strings.Contains(got, "Version: v0.0.0-test") {
		t.Fatalf("missing version value: %q", got)
	}
	if got := string(output); !strings.Contains(got, "Commit: commit-test") {
		t.Fatalf("missing commit value: %q", got)
	}
	if got := string(output); !strings.Contains(got, "Date: 2026-07-28") {
		t.Fatalf("missing date value: %q", got)
	}
}
