package main

import (
	"bufio"
	"fmt"
	"io"
	"math/rand"
	"net/http"
	"os"
	"strings"
)

type Targets []*http.Request

func NewTargetsFromFile(filename string) (Targets, error) {
	file, err := os.Open(filename)
	if err != nil {
		return Targets{}, err
	}
	defer file.Close()
	return NewTargets(file)
}

func NewTargets(source io.Reader) (Targets, error) {
	reader := bufio.NewReader(source)
	targets := make([]*http.Request, 0)

	for {
		line, err := reader.ReadString('\n')
		if err != nil && err == io.EOF {
			break
		} else if err != nil {
			return targets, err
		}
		if line = strings.TrimSpace(line); line == "" { // Empty line
			continue
		}
		parts := strings.SplitN(line, " ", 2)
		if len(parts) != 2 {
			return targets, fmt.Errorf("Invalid request format: `%s`", line)
		}
		// Build request
		req, err := http.NewRequest(parts[0], parts[1], nil)
		if err != nil {
			return targets, fmt.Errorf("Failed to build request: %s", err)
		}
		targets = append(targets, req)
	}
	return targets, nil
}

func (t Targets) Iter(ordering string) []int {
	if ordering == "random" {
		return rand.Perm(len(t))
	}
	iter := make([]int, len(t))
	for i := 0; i < len(t); i++ {
		iter[i] = i
	}
	return iter
}
