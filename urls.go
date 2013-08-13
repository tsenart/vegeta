package main

import (
	"bytes"
	"fmt"
	"io/ioutil"
	"math/rand"
	"net/url"
)

type URLs []*url.URL

func NewURLsFromFile(filename string) (urls URLs, err error) {
	lines, err := ioutil.ReadFile(filename)
	if err != nil {
		return URLs{}, err
	}

	for _, line := range bytes.Split(lines, []byte("\n")) {
		uri, err := url.Parse(string(line))
		if err != nil {
			return URLs{}, fmt.Errorf("Failed to parse URI (%s): %s", line, err)
		}
		urls = append(urls, uri)
	}
	return urls, nil
}

func (urls URLs) Iter(random bool) []int {
	if random {
		return rand.Perm(len(urls))
	}
	iter := make([]int, len(urls))
	for i := 0; i < len(urls); i++ {
		iter[i] = i
	}
	return iter
}
