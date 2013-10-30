package vegeta

import (
	"bufio"
	"fmt"
	"io"
	"math/rand"
	"strings"
)

type Target struct {
	Method	string
	URL	string
	Headers *Headers
}

// Targets represents a list of strings that we'll build http.Requests later
type Targets []*Target

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
	targets := make([]*Target, 0)
	for _, line := range lines {
		parts := strings.SplitN(line, " ", 2)
		if len(parts) != 2 {
			return targets, fmt.Errorf("Invalid request format: `%s`", line)
		}
		
		targets = append(targets, NewTarget(parts[0], parts[1]))
	}
	return targets, nil
}

func NewTarget(method string, url string) *Target {
	target := new(Target)
	target.Method = method
	target.URL = url
	return target
}

// Shuffle randomly alters the order of Targets with the provided seed
func (t Targets) Shuffle(seed int64) {
	rand.Seed(seed)
	for i, rnd := range rand.Perm(len(t)) {
		t[i], t[rnd] = t[rnd], t[i]
	}
}

// SetHeader sets the passed request header in all Targets
func (t Targets) SetHeaders(hdrs *Headers) {
	for _, target := range t {
		target.Headers = hdrs
	}
}
