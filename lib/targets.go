package vegeta

import (
	"bufio"
	"fmt"
	"io"
	"math/rand"
	"net/http"
	"strings"
)

// Targets represents the http.Requests which will be issued during the test
type Targets []*http.Request

// NewTargetsFrom reads targets out of a line separated source skipping empty lines
func NewTargetsFrom(source io.Reader) (Targets, error) {
	scanner := bufio.NewScanner(source)
	lines := make([]string, 0)
	for scanner.Scan() {
		line := scanner.Text()

		if line = strings.TrimSpace(line); line != "" && line[0:2] != "//" {
			// Skipping comments or blank lines
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
		t[i], t[rnd] = t[rnd], t[i]
	}
}

// SetHeader sets the passed request header in all Targets
// by making a copy for each
func (t Targets) SetHeader(header http.Header) {
	for _, target := range t {
		target.Header = make(http.Header, len(header))
		for k, vs := range header {
			target.Header[k] = make([]string, len(vs))
			copy(target.Header[k], vs)
		}
	}
}
