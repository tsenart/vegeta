package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"runtime"
	"runtime/pprof"
	"sort"
	"strings"
)

func main() {
	commands := map[string]command{
		"attack": attackCmd(),
		"report": reportCmd(),
		"plot":   plotCmd(),
		"encode": encodeCmd(),
		"dump":   dumpCmd(),
	}

	fs := flag.NewFlagSet("vegeta", flag.ExitOnError)
	cpus := fs.Int("cpus", runtime.NumCPU(), "Number of CPUs to use")
	profile := fs.String("profile", "", "Enable profiling of [cpu, heap]")
	version := fs.Bool("version", false, "Print version and exit")

	fs.Usage = func() {
		fmt.Fprintln(fs.Output(), "Usage: vegeta [global flags] <command> [command flags]")
		fmt.Fprintf(fs.Output(), "\nglobal flags:\n")
		fs.PrintDefaults()

		names := make([]string, 0, len(commands))
		for name := range commands {
			names = append(names, name)
		}

		sort.Strings(names)
		for _, name := range names {
			if cmd := commands[name]; cmd.fs != nil {
				fmt.Fprintf(fs.Output(), "\n%s command:\n", name)
				cmd.fs.SetOutput(fs.Output())
				cmd.fs.PrintDefaults()
			}
		}

		fmt.Fprintln(fs.Output(), examples)
	}

	fs.Parse(os.Args[1:])

	if *version {
		fmt.Printf("Version: %s\nCommit: %s\nRuntime: %s %s/%s\nDate: %s\n",
			Version,
			Commit,
			runtime.Version(),
			runtime.GOOS,
			runtime.GOARCH,
			Date,
		)
		return
	}

	runtime.GOMAXPROCS(*cpus)

	for _, prof := range strings.Split(*profile, ",") {
		if prof = strings.TrimSpace(prof); prof == "" {
			continue
		}

		f, err := os.Create(prof + ".pprof")
		if err != nil {
			log.Fatal(err)
		}
		defer f.Close()

		switch {
		case strings.HasPrefix(prof, "cpu"):
			pprof.StartCPUProfile(f)
			defer pprof.StopCPUProfile()
		case strings.HasPrefix(prof, "heap"):
			defer pprof.Lookup("heap").WriteTo(f, 0)
		}
	}

	args := fs.Args()
	if len(args) == 0 {
		fs.Usage()
		os.Exit(1)
	}

	if cmd, ok := commands[args[0]]; !ok {
		log.Fatalf("Unknown command: %s", args[0])
	} else if err := cmd.fn(args[1:]); err != nil {
		log.Fatal(err)
	}
}

// Set at linking time
var (
	Commit  string
	Date    string
	Version string
)

const examples = `
examples:
  echo "GET http://localhost/" | vegeta attack -duration=5s | tee results.bin | vegeta report
  vegeta report -type=json results.bin > metrics.json
  cat results.bin | vegeta plot > plot.html
  cat results.bin | vegeta report -type="hist[0,100ms,200ms,300ms]"
`

type command struct {
	fs *flag.FlagSet
	fn func(args []string) error
}
