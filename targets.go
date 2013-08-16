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
	targets := make([]*http.Request, 0)
	scanner := bufio.NewScanner(source)

	for scanner.Scan() {
		line := scanner.Text()
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
	if err := scanner.Err(); err != nil {
		return targets, err
	}
	return targets, nil
}

func (t Targets) Shuffle(seed int64) {
	rand.Seed(seed)
	for i, rnd := range rand.Perm(len(t)) {
		tmp := t[i]
		t[i] = t[rnd]
		t[rnd] = tmp
	}
}
