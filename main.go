package main

import (
	"bytes"
	"flag"
	"fmt"
	"io/ioutil"
	"log"
	"math"
	"math/rand"
	"net/http"
	"net/url"
	"time"
)

// -qps=10 -urls=xxx.txt -mode={sequential,random} {-requests=N,-duration=T}

func main() {
	var (
		// Flags
		qps      = flag.Uint("qps", 50, "Queries Per Second")
		urlsFile = flag.String("urls", "urls.txt", "URLs file")
		mode     = flag.String("mode", "random", "sequential or random")
		requests = flag.Uint("requests", 5000, "Number of requests to do")
		duration = flag.Duration("duration", 10*time.Second, "Maximum duration of execution")
	)

	var (
		urls    []*url.URL
		clients []*http.Client
		err     error
	)

	flag.Parse()

	// Validate QPS argument
	if *qps == 0 {
		log.Fatal("qps can't be zero")
	}
	// Magic formula that assumes each client can
	// sustain 500 QPS under normal circumstances
	clients = make([]*http.Client, int(math.Ceil(float64(*qps)/500.0)))

	// Parse URLs file
	if urls, err = readURLsFromFile(*urlsFile); err != nil {
		log.Fatal(err)
	}

	// Parse mode argument
	if *mode == "random" {
		rand.Seed(time.Now().UnixNano())
	} else if *mode != "sequential" {
		log.Fatal("Unknown mode %s", *mode)
	}

	// Parse number of requests and duration
	if *requests == 0 && *duration == 0 {
		log.Fatal("Neither requests or duration was provided")
	}

	fmt.Printf("Hitting %d URLs in %s mode for %s with %d requests and %d clients.",
		len(urls), *mode, duration.String(), *requests, len(clients))
}

func readURLsFromFile(filename string) ([]*url.URL, error) {
	lines, err := ioutil.ReadFile(filename)
	if err != nil {
		return []*url.URL{}, err
	}

	var urls []*url.URL
	for _, line := range bytes.Split(lines, []byte("\n")) {
		uri, err := url.Parse(string(line))
		if err != nil {
			return []*url.URL{}, fmt.Errorf("Failed to parse URI (%s): %s", line, err)
		}
		urls = append(urls, uri)
	}
	return urls, nil
}
