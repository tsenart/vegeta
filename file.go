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
			file, err = os.OpenFile(filename, os.O_RDWR|os.O_APPEND, 0660)
		} else {
			file, err = os.Open(filename)
		}
		if err != nil {
			return nil, err
		}
		return file, nil
	}
}
