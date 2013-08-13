package main

import (
	"flag"
	"fmt"
	"log"
	"math"
	"math/rand"
	"net/http"
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
	flag.Parse()

	// Validate QPS argument
	if *qps == 0 {
		log.Fatal("qps can't be zero")
	}
	// Magic formula that assumes each client can
	// sustain 500 QPS under normal circumstances
	clients := make([]*Client, int(math.Ceil(float64(*qps)/500.0)))
	qpsClient := *qps / uint(len(clients))
	for i := 0; i < len(clients); i++ {
		clients[i] = NewClient(qpsClient)
	}

	// Parse URLs file
	urls, err := NewURLsFromFile(*urlsFile)
	if err != nil {
		log.Fatal(err)
	}

	// Parse mode argument
	random := false
	if *mode == "random" {
		rand.Seed(time.Now().UnixNano())
		random = true
	} else if *mode != "sequential" {
		log.Fatal("Unknown mode %s", *mode)
	}

	// Parse number of requests and duration
	if *requests == 0 && *duration == 0 {
		log.Fatal("Neither requests or duration was provided")
	}

	fmt.Printf("Hitting %d URLs in %s mode for %s with %d requests and %d clients.",
		len(urls), *mode, duration.String(), *requests, len(clients))

	reqs := make(chan *http.Request, *requests)
	for _, client := range clients {
		go client.Drill(reqs)
	}
	for _, index := range urls.Iter(random) {
		url := urls[index]
		req, err := http.NewRequest("GET", url.String(), nil)
		if err != nil {
			log.Fatal("Bad request: %s", err)
		}
		reqs <- req
	}
}
