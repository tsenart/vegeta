package vegeta

import (
	"bufio"
	"fmt"
	"io"
	"math/rand"
	"net/http"
	"os"
	"strings"
)

// Targets represents the http.Requests which will be issued during the test
type Targets []*http.Request

// NewTargetsFromFile reads and parses targets from a text file
func NewTargetsFromFile(filename string) (Targets, error) {
	file, err := os.Open(filename)
	if err != nil {
		return Targets{}, err
	}
	defer file.Close()
	return readTargets(file)
}

// readTargets reads targets out of a line separated source skipping empty lines
func readTargets(source io.Reader) (Targets, error) {
	scanner := bufio.NewScanner(source)
	lines := make([]string, 0)
	for scanner.Scan() {
		line := scanner.Text()

		if line = strings.TrimSpace(line); line != "" && line[0:2] != "//" { // A comment or blank line
			lines = append(lines, line)
		}
	}
	if err := scanner.Err(); err != nil {
		return Targets{}, err
	}

	return NewTargets(lines)
}

// NewTargets instantiates Targets from a slice of strings
func NewTargets(lines []string) (Targets, error) {
	targets := make([]*http.Request, 0)
	for _, line := range lines {
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

// Shuffle randomly alters the order of Targets with the provided seed
func (t Targets) Shuffle(seed int64) {
	rand.Seed(seed)
	for i, rnd := range rand.Perm(len(t)) {
		tmp := t[i]
		t[i] = t[rnd]
		t[rnd] = tmp
	}
}
