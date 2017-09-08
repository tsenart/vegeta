# Vegeta [![Build Status](https://secure.travis-ci.org/tsenart/vegeta.svg)](http://travis-ci.org/tsenart/vegeta) [![Go Report Card](https://goreportcard.com/badge/github.com/tsenart/vegeta)](https://goreportcard.com/report/github.com/tsenart/vegeta) [![GoDoc](https://godoc.org/github.com/tsenart/vegeta?status.svg)](https://godoc.org/github.com/tsenart/vegeta) [![Gitter](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/tsenart/vegeta?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge) [![Donate](https://img.shields.io/badge/donate-bitcoin-yellow.svg)](#donate)

Vegeta is a versatile HTTP load testing tool built out of a need to drill
HTTP services with a constant request rate.
It can be used both as a command line utility and a library.

![Vegeta](http://fc09.deviantart.net/fs49/i/2009/198/c/c/ssj2_vegeta_by_trunks24.jpg)

## Install
### Pre-compiled executables
Get them [here](http://github.com/tsenart/vegeta/releases).

### Homebrew on Mac OS X
You can install Vegeta using the [Homebrew](https://github.com/Homebrew/homebrew/) package manager on Mac OS X:
```shell
$ brew update && brew install vegeta
```

### Source
You need `go` installed and `GOBIN` in your `PATH`. Once that is done, run the
command:
```shell
$ go get -u github.com/tsenart/vegeta
```

## Contributing
See [CONTRIBUTING.md](CONTRIBUTING.md).

## Usage manual
```console
Usage: vegeta [global flags] <command> [command flags]

global flags:
  -cpus int
      Number of CPUs to use (default 8)
  -profile string
      Enable profiling of [cpu, heap]
  -version
      Print version and exit

attack command:
  -body string
      Requests body file
  -cert string
      TLS client PEM encoded certificate file
  -connections int
      Max open idle connections per target host (default 10000)
  -duration duration
      Duration of the test [0 = forever]
  -header value
      Request header
  -http2
      Send HTTP/2 requests when supported by the server (default true)
  -insecure
      Ignore invalid server TLS certificates
  -keepalive
      Use persistent connections (default true)
  -key string
      TLS client PEM encoded private key file
  -laddr value
      Local IP address (default 0.0.0.0)
  -lazy
      Read targets lazily
  -output string
      Output file (default "stdout")
  -rate uint
      Requests per second (default 50)
  -redirects int
      Number of redirects to follow. -1 will not follow but marks as success (default 10)
  -root-certs value
      TLS root certificate files (comma separated list)
  -targets string
      Targets file (default "stdin")
  -timeout duration
      Requests timeout (default 30s)
  -workers uint
      Initial number of workers (default 10)

report command:
  -inputs string
      Input files (comma separated) (default "stdin")
  -output string
      Output file (default "stdout")
  -reporter string
      Reporter [text, json, plot, hist[buckets]] (default "text")

dump command:
  -dumper string
      Dumper [json, csv] (default "json")
  -inputs string
      Input files (comma separated) (default "stdin")
  -output string
      Output file (default "stdout")

examples:
  echo "GET http://localhost/" | vegeta attack -duration=5s | tee results.bin | vegeta report
  vegeta attack -targets=targets.txt > results.bin
  vegeta report -inputs=results.bin -reporter=json > metrics.json
  cat results.bin | vegeta report -reporter=plot > plot.html
  cat results.bin | vegeta report -reporter="hist[0,100ms,200ms,300ms]"
```

#### `-cpus`
Specifies the number of CPUs to be used internally.
It defaults to the amount of CPUs available in the system.

#### `-profile`
Specifies which profiler to enable during execution. Both *cpu* and
*heap* profiles are supported. It defaults to none.

#### `-version`
Prints the version and exits.

### `attack`
```console
$ vegeta attack -h
Usage of vegeta attack:
  -body string
      Requests body file
  -cert string
      TLS client PEM encoded certificate file
  -connections int
      Max open idle connections per target host (default 10000)
  -duration duration
      Duration of the test [0 = forever]
  -header value
      Request header
  -http2
      Send HTTP/2 requests when supported by the server (default true)
  -insecure
      Ignore invalid server TLS certificates
  -keepalive
      Use persistent connections (default true)
  -key string
      TLS client PEM encoded private key file
  -laddr value
      Local IP address (default 0.0.0.0)
  -lazy
      Read targets lazily
  -output string
      Output file (default "stdout")
  -rate uint
      Requests per second (default 50)
  -redirects int
      Number of redirects to follow. -1 will not follow but marks as success (default 10)
  -root-certs value
      TLS root certificate files (comma separated list)
  -targets string
      Targets file (default "stdin")
  -timeout duration
      Requests timeout (default 30s)
  -workers uint
      Initial number of workers (default 10)
```

#### `-body`
Specifies the file whose content will be set as the body of every
request unless overridden per attack target, see `-targets`.

#### `-cert`
Specifies the PEM encoded TLS client certificate file to be used with HTTPS requests.
If `-key` isn't specified, it will be set to the value of this flag.

#### `-connections`
Specifies the maximum number of idle open connections per target host.

#### `-duration`
Specifies the amount of time to issue request to the targets.
The internal concurrency structure's setup has this value as a variable.
The actual run time of the test can be longer than specified due to the
responses delay. Use 0 for an infinite attack.

#### `-header`
Specifies a request header to be used in all targets defined, see `-targets`.
You can specify as many as needed by repeating the flag.

#### `-http2`
Specifies whether to enable HTTP/2 requests to servers which support it.

#### `-insecure`
Specifies whether to ignore invalid server TLS certificates.

#### `-keepalive`
Specifies whether to reuse TCP connections between HTTP requests.

#### `-key`
Specifies the PEM encoded TLS client certificate private key file to be
used with HTTPS requests.

#### `-laddr`
Specifies the local IP address to be used.

#### `-lazy`
Specifies whether to read the input targets lazily instead of eagerly.
This allows streaming targets into the attack command and reduces memory
footprint.
The trade-off is one of added latency in each hit against the targets.

#### `-output`
Specifies the output file to which the binary results will be written
to. Made to be piped to the report command input. Defaults to stdout.

####  `-rate`
Specifies the requests per second rate to issue against
the targets. The actual request rate can vary slightly due to things like
garbage collection, but overall it should stay very close to the specified.

#### `-redirects`
Specifies the max number of redirects followed on each request. The
default is 10. When the value is -1, redirects are not followed but
the response is marked as successful.

#### `-root-certs`
Specifies the trusted TLS root CAs certificate files as a comma separated
list. If unspecified, the default system CAs certificates will be used.

#### `-targets`
Specifies the attack targets in a line separated file, defaulting to stdin.
The format should be as follows, combining any or all of the following:

Simple targets
```
GET http://goku:9090/path/to/dragon?item=balls
GET http://user:password@goku:9090/path/to
HEAD http://goku:9090/path/to/success
```

Targets with custom headers
```
GET http://user:password@goku:9090/path/to
X-Account-ID: 8675309

DELETE http://goku:9090/path/to/remove
Confirmation-Token: 90215
Authorization: Token DEADBEEF
```

Targets with custom bodies
```
POST http://goku:9090/things
@/path/to/newthing.json

PATCH http://goku:9090/thing/71988591
@/path/to/thing-71988591.json
```

Targets with custom bodies and headers
```
POST http://goku:9090/things
X-Account-ID: 99
@/path/to/newthing.json
```

#### `-timeout`
Specifies the timeout for each request. The default is 0 which disables
timeouts.

#### `-workers`
Specifies the initial number of workers used in the attack. The actual
number of workers will increase if necessary in order to sustain the
requested rate.

### report
```console
$ vegeta report -h
Usage of vegeta report:
  -inputs string
      Input files (comma separated) (default "stdin")
  -output string
      Output file (default "stdout")
  -reporter string
      Reporter [text, json, plot, hist[buckets]] (default "text")
```

#### `-inputs`
Specifies the input files to generate the report of, defaulting to stdin.
These are the output of vegeta attack. You can specify more than one (comma
separated) and they will be merged and sorted before being used by the
reports.

#### `-output`
Specifies the output file to which the report will be written to.

#### `-reporter`
Specifies the kind of report to be generated. It defaults to text.

##### `text`
```console
Requests      [total, rate]             1200, 120.00
Duration      [total, attack, wait]     10.094965987s, 9.949883921s, 145.082066ms
Latencies     [mean, 50, 95, 99, max]   113.172398ms, 108.272568ms, 140.18235ms, 247.771566ms, 264.815246ms
Bytes In      [total, mean]             3714690, 3095.57
Bytes Out     [total, mean]             0, 0.00
Success       [ratio]                   55.42%
Status Codes  [code:count]              0:535  200:665
Error Set:
Get http://localhost:6060: dial tcp 127.0.0.1:6060: connection refused
Get http://localhost:6060: read tcp 127.0.0.1:6060: connection reset by peer
Get http://localhost:6060: dial tcp 127.0.0.1:6060: connection reset by peer
Get http://localhost:6060: write tcp 127.0.0.1:6060: broken pipe
Get http://localhost:6060: net/http: transport closed before response was received
Get http://localhost:6060: http: can't write HTTP request on broken connection
```

##### `json`
```json
{
  "latencies": {
    "total": 237119463,
    "mean": 2371194,
    "50th": 2854306,
    "95th": 3478629,
    "99th": 3530000,
    "max": 3660505
  },
  "bytes_in": {
    "total": 606700,
    "mean": 6067
  },
  "bytes_out": {
    "total": 0,
    "mean": 0
  },
  "earliest": "2015-09-19T14:45:50.645818631+02:00",
  "latest": "2015-09-19T14:45:51.635818575+02:00",
  "end": "2015-09-19T14:45:51.639325797+02:00",
  "duration": 989999944,
  "wait": 3507222,
  "requests": 100,
  "rate": 101.01010672380401,
  "success": 1,
  "status_codes": {
    "200": 100
  },
  "errors": []
}
```
##### `plot`
Generates an HTML5 page with an interactive plot based on
[Dygraphs](http://dygraphs.com).
Click and drag to select a region to zoom into. Double click to zoom
out.
Input a different number on the bottom left corner input field
to change the moving average window size (in data points).

Each point on the plot shows a request, the X axis represents the time
at the start of the request and the Y axis represents the time taken
to complete that request.

![Plot](http://i.imgur.com/oi0cgGq.png)

##### `hist`
Computes and prints a text based histogram for the given buckets.
Each bucket upper bound is non-inclusive.
```console
cat results.bin | vegeta report -reporter='hist[0,2ms,4ms,6ms]'
Bucket         #     %       Histogram
[0,     2ms]   6007  32.65%  ########################
[2ms,   4ms]   5505  29.92%  ######################
[4ms,   6ms]   2117  11.51%  ########
[6ms,   +Inf]  4771  25.93%  ###################
```

### `dump`
```console
$ vegeta dump -h
Usage of vegeta dump:
  -dumper string
      Dumper [json, csv] (default "json")
  -inputs string
      Input files (comma separated) (default "stdin")
  -output string
      Output file (default "stdout")
```

#### `-inputs`
Specifies the input files containing attack results to be dumped. You can specify more than one (comma separated).

#### `-output`
Specifies the output file to which the dump will be written to.

#### `-dumper`
Specifies the dump format.

##### `json`
Dumps attack results as JSON objects.

##### `csv`
Dumps attack results as CSV records with six columns.
The columns are: unix timestamp in ns since epoch, http status code,
request latency in ns, bytes out, bytes in, and lastly the error.

## Usage: Distributed attacks
Whenever your load test can't be conducted due to Vegeta hitting machine limits
such as open files, memory, CPU or network bandwidth, it's a good idea to use Vegeta in a distributed manner.

In a hypothetical scenario where the desired attack rate is 60k requests per second,
let's assume we have 3 machines with `vegeta` installed.

Make sure open file descriptor and process limits are set to a high number for your user **on each machine**
using the `ulimit` command.

We're ready to start the attack. All we need to do is to divide the intended rate by the number of machines,
and use that number on each attack. Here we'll use [pdsh](https://code.google.com/p/pdsh/) for orchestration.

```shell
$ pdsh -b -w '10.0.1.1,10.0.2.1,10.0.3.1' \
    'echo "GET http://target/" | vegeta attack -rate=20000 -duration=60s > result.bin'
```

After the previous command finishes, we can gather the result files to use on our report.

```shell
$ for machine in "10.0.1.1 10.0.2.1 10.0.3.1"; do
    scp $machine:~/result.bin $machine.bin &
  done
```

The `report` command accepts multiple result files in a comma separated list.
It'll read and sort them by timestamp before generating reports.

```console
$ vegeta report -inputs="10.0.1.1.bin,10.0.2.1.bin,10.0.3.1.bin"
Requests      [total, rate]         3600000, 60000.00
Latencies     [mean, 95, 99, max]   223.340085ms, 326.913687ms, 416.537743ms, 7.788103259s
Bytes In      [total, mean]         3714690, 3095.57
Bytes Out     [total, mean]         0, 0.00
Success       [ratio]               100.0%
Status Codes  [code:count]          200:3600000
Error Set:
```

## Usage (Library)
```go
package main

import (
  "fmt"
  "time"

  vegeta "github.com/tsenart/vegeta/lib"
)

func main() {
  rate := uint64(100) // per second
  duration := 4 * time.Second
  targeter := vegeta.NewStaticTargeter(vegeta.Target{
    Method: "GET",
    URL:    "http://localhost:9100/",
  })
  attacker := vegeta.NewAttacker()

  var metrics vegeta.Metrics
  for res := range attacker.Attack(targeter, rate, duration) {
    metrics.Add(res)
  }
  metrics.Close()

  fmt.Printf("99th percentile: %s\n", metrics.Latencies.P99)
}
```

#### Limitations
There will be an upper bound of the supported `rate` which varies on the
machine being used.
You could be CPU bound (unlikely), memory bound (more likely) or
have system resource limits being reached which ought to be tuned for
the process execution. The important limits for us are file descriptors
and processes. On a UNIX system you can get and set the current
soft-limit values for a user.
```shell
$ ulimit -n # file descriptors
2560
$ ulimit -u # processes / threads
709
```
Just pass a new number as the argument to change it.

## License
See [LICENSE](LICENSE).

## Donate

If you use and love Vegeta, please consider sending some Satoshi to
`1MDmKC51ve7Upxt75KoNM6x1qdXHFK6iW2`. In case you want to be mentioned as a
sponsor, let me know!

[![Donate Bitcoin](https://i.imgur.com/W9Vc51d.png)](#donate)
