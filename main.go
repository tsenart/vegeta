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
	// Magic formula that assumes each client can
	// sustain 200 RPS under normal circumstances
	clients := make([]*Client, int(math.Ceil(float64(*rate)/200.0)))
	ratePerClient := *rate / uint(len(clients))
	for i := 0; i < len(clients); i++ {
		clients[i] = NewClient(ratePerClient)
	}

	// Parse targets file
	targets, err := NewTargetsFromFile(*targetsf)
	if err != nil {
		log.Fatal(err)
	}

	// Parse ordering argument
	random := false
	if *ordering == "random" {
		rand.Seed(time.Now().UnixNano())
		random = true
	} else if *ordering != "sequential" {
		log.Fatalf("Unknown ordering %s", *ordering)
	}

	// Parse duration
	if *duration == 0 {
		log.Fatal("Duration provided is invalid")
	}

	hits := make(chan *http.Request, *rate*uint((*duration).Seconds()))
	for i, idxs := 0, targets.Iter(random); i < cap(hits); i++ {
		hits <- targets[idxs[i%len(idxs)]]
	}
	// Attack!
	responses := make(chan *Response, cap(hits))
	for _, client := range clients {
		go client.Drill(hits, responses)
	}
	log.Printf("Vegeta is attacking ")
	log.Printf("%d targets in %s order for %s with %d clients.\n", len(targets), *ordering, duration, len(clients))

	var rep Reporter
	switch *reporter {
	case "text":
		rep = NewTextReporter(len(responses))
	default:
		log.Println("reporter provided is not supported. using text")
		rep = NewTextReporter(len(responses))
	}
	// Wait for all requests to finish
	for i := 0; i < cap(responses); i++ {
		rep.Add(<-responses)
	}
	close(hits)
	close(responses)

	if rep.Report(os.Stdout) != nil {
		log.Fatal("Failed to report!")
	}
}
