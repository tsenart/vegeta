package main

import (
	"flag"
	"log"
	"math"
	"math/rand"
	"net/http"
	"os"
	"time"
)

func main() {
	var (
		// Flags
		rate     = flag.Uint("rate", 50, "Requests per second")
		targetsf = flag.String("targets", "targets.txt", "Targets file")
		ordering = flag.String("ordering", "random", "Attack ordering [sequential, random]")
		duration = flag.Duration("duration", 10*time.Second, "Duration of the test")
		reporter = flag.String("reporter", "text", "Reporter to use [text]")
	)
	flag.Parse()

	if flag.NFlag() == 0 {
		flag.Usage()
		return
	}

	// Validate rate argument
	if *rate == 0 {
		log.Fatal("rate can't be zero")
	}
	// Parse targets file
	targets, err := NewTargetsFromFile(*targetsf)
	if err != nil {
		log.Fatal(err)
	}

	// Parse ordering argument
	if *ordering == "random" {
		rand.Seed(time.Now().UnixNano())
	} else if *ordering != "sequential" {
		log.Fatalf("Unknown ordering %s", *ordering)
	}

	// Parse duration
	if *duration == 0 {
		log.Fatal("Duration provided is invalid")
	}

	// Parse reporter
	var rep Reporter
	switch *reporter {
	case "text":
		rep = NewTextReporter()
	default:
		log.Println("reporter provided is not supported. using text")
		rep = NewTextReporter()
	}

	log.Printf("Vegeta is attacking %d targets in %s order for %s\n", len(targets), *ordering, *duration)
	attack(targets, *ordering, *rate, *duration, rep)

	// Report results!
	if rep.Report(os.Stdout) != nil {
		log.Fatal("Failed to report!")
	}
}

func attack(targets Targets, ordering string, rate uint, duration time.Duration, rep Reporter) {
	// Magic formula that assumes each client can
	// sustain 200 RPS under normal circumstances
	clients := make([]*Client, int(math.Ceil(float64(rate)/200.0)))
	ratePerClient := rate / uint(len(clients))
	for i := 0; i < len(clients); i++ {
		clients[i] = NewClient(ratePerClient)
	}

	hits := make(chan *http.Request, rate*uint((duration).Seconds()))
	defer close(hits)
	for i, idxs := 0, targets.Iter(ordering); i < cap(hits); i++ {
		hits <- targets[idxs[i%len(idxs)]]
	}
	responses := make(chan *Response, cap(hits))
	defer close(responses)
	for _, client := range clients {
		go client.Drill(hits, responses) // Attack!
	}
	// Wait for all requests to finish
	for i := 0; i < cap(responses); i++ {
		rep.Add(<-responses)
	}
}
