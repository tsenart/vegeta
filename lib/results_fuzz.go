//go:build gofuzz
// +build gofuzz

package vegeta

import (
	"bytes"
	"io"
)

// FuzzResultsFormatDetection tests result list format detection.
func FuzzResultsFormatDetection(fuzz []byte) int {
	decoder := DecoderFor(bytes.NewReader(fuzz))
	if decoder == nil {
		return 0
	}
	ok := readAllResults(decoder)
	if !ok {
		return 0
	}
	return 1
}

// FuzzGobDecoder tests decoding a gob format result list.
func FuzzGobDecoder(fuzz []byte) int {
	decoder := NewDecoder(bytes.NewReader(fuzz))
	ok := readAllResults(decoder)
	if !ok {
		return 0
	}
	return 1
}

// FuzzCSVDecoder tests decoding a CSV format result list.
func FuzzCSVDecoder(fuzz []byte) int {
	decoder := NewCSVDecoder(bytes.NewReader(fuzz))
	ok := readAllResults(decoder)
	if !ok {
		return 0
	}
	return 1
}

// FuzzJSONDecoder tests decoding a JSON format result list.
func FuzzJSONDecoder(fuzz []byte) int {
	decoder := NewJSONDecoder(bytes.NewReader(fuzz))
	ok := readAllResults(decoder)
	if !ok {
		return 0
	}
	return 1
}

func readAllResults(decoder Decoder) (ok bool) {
	for {
		result := &Result{}
		err := decoder.Decode(result)
		if err == io.EOF {
			return true
		} else if err != nil {
			return false
		}
	}
}
