package main

import (
	"flag"
	"reflect"
	"testing"
)

func TestNormalizeBooleanFlagArgs(t *testing.T) {
	t.Parallel()

	fs := flag.NewFlagSet("normalize", flag.ContinueOnError)
	var keepalive bool
	var http2 bool
	fs.BoolVar(&keepalive, "keepalive", false, "use keepalive")
	fs.BoolVar(&http2, "http2", false, "use http2")

	got := normalizeBooleanFlagArgs(fs, []string{
		"-keepalive", "false",
		"-http2", "true",
		"false",
	})
	want := []string{
		"-keepalive=false",
		"-http2=true",
		"false",
	}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("normalized args = %#v, want %#v", got, want)
	}

	if err := fs.Parse(got); err != nil {
		t.Fatal(err)
	}
	if keepalive {
		t.Fatal("keepalive should be false")
	}
	if !http2 {
		t.Fatal("http2 should be true")
	}
}

func TestNormalizeBooleanFlagArgsStopsAtDoubleDash(t *testing.T) {
	t.Parallel()

	fs := flag.NewFlagSet("normalize", flag.ContinueOnError)
	var keepalive bool
	fs.BoolVar(&keepalive, "keepalive", true, "use keepalive")

	got := normalizeBooleanFlagArgs(fs, []string{"-keepalive", "--", "false"})
	want := []string{"-keepalive", "--", "false"}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("normalized args = %#v, want %#v", got, want)
	}
}

func TestNormalizeBooleanFlagArgsSkipsNonBooleanValues(t *testing.T) {
	t.Parallel()

	fs := flag.NewFlagSet("normalize", flag.ContinueOnError)
	var keepalive bool
	fs.BoolVar(&keepalive, "keepalive", true, "use keepalive")

	got := normalizeBooleanFlagArgs(fs, []string{"-keepalive", "maybe", "foo"})
	want := []string{"-keepalive", "maybe", "foo"}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("normalized args = %#v, want %#v", got, want)
	}

	if err := fs.Parse(got); err != nil {
		t.Fatal(err)
	}
	if !keepalive {
		t.Fatal("keepalive should remain true when value is not boolean")
	}
}

func TestNormalizeBooleanFlagArgsForUnknownFlags(t *testing.T) {
	t.Parallel()

	fs := flag.NewFlagSet("normalize", flag.ContinueOnError)
	var header string
	var keepalive bool
	fs.StringVar(&header, "header", "", "request header")
	fs.BoolVar(&keepalive, "keepalive", false, "use keepalive")

	got := normalizeBooleanFlagArgs(fs, []string{"-header", "false", "-keepalive", "false"})
	want := []string{"-header", "false", "-keepalive=false"}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("normalized args = %#v, want %#v", got, want)
	}

	if err := fs.Parse(got); err != nil {
		t.Fatal(err)
	}
	if keepalive {
		t.Fatal("keepalive should be false")
	}
}
