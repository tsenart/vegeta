package main

import (
	"os"
)

func file(filename string, create bool) (*os.File, error) {
	switch filename {
	case "stdin":
		return os.Stdin, nil
	case "stdout":
		return os.Stdout, nil
	default:
		var file *os.File
		var err error
		if create {
			file, err = os.Create(filename)
		} else {
			file, err = os.Open(filename)
		}
		if err != nil {
			return nil, err
		}
		return file, nil
	}
}
