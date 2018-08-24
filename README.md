# Vegeta [![Build Status](https://secure.travis-ci.org/tsenart/vegeta.svg?branch=master)](http://travis-ci.org/tsenart/vegeta) [![Go Report Card](https://goreportcard.com/badge/github.com/tsenart/vegeta)](https://goreportcard.com/report/github.com/tsenart/vegeta) [![GoDoc](https://godoc.org/github.com/tsenart/vegeta?status.svg)](https://godoc.org/github.com/tsenart/vegeta) [![Gitter](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/tsenart/vegeta?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge) [![Donate](https://img.shields.io/badge/donate-bitcoin-yellow.svg)](#donate)

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

## Versioning
Both the library and the CLI are versioned with [SemVer v2.0.0](https://semver.org/spec/v2.0.0.html).

After [v8.0.0](https://github.com/tsenart/vegeta/tree/v8.0.0), the two components
are versioned separately to better isolate breaking changes to each.

CLI releases are tagged with `cli/vMAJOR.MINOR.PATCH` and published on the [Github releases page](https://github.com/tsenart/vegeta/releases).
As for the library, new versions are tagged with `lib/vMAJOR.MINOR.PATCH` but not published as a release.

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
  -format string
    	Targets format [http, json] (default "http")
  -h2c
    	Send HTTP/2 requests without TLS encryption
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
  -max-body value
	Maximum number of bytes to be read from response bodies. [-1 = no limit] (default -1)
  -name string
    	Attack name
  -output string
    	Output file (default "stdout")
  -rate value
    	Number of requests per time unit (default 50/1s)
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

encode command:
  -output string
    	Output file (default "stdout")
  -to string
    	Output encoding [csv, gob, json] (default "json")

plot command:
  -output string
    	Output file (default "stdout")
  -threshold int
    	Threshold of data points above which series are downsampled. (default 4000)
  -title string
    	Title and header of the resulting HTML page (default "Vegeta Plot")

report command:
  -output string
    	Output file (default "stdout")
  -type string
    	Report type to generate [text, json, hist[buckets]] (default "text")

examples:
  echo "GET http://localhost/" | vegeta attack -duration=5s | tee results.bin | vegeta report
  vegeta report -type=json results.bin > metrics.json
  cat results.bin | vegeta plot > plot.html
  cat results.bin | vegeta report -type="hist[0,100ms,200ms,300ms]"
```

#### `-cpus`
Specifies the number of CPUs to be used internally.
It defaults to the amount of CPUs available in the system.

#### `-profile`
Specifies which profiler to enable during execution. Both *cpu* and
*heap* profiles are supported. It defaults to none.

#### `-version`
Prints the version and exits.

### `attack` command

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

#### `-format`
Specifies the targets format to decode.

##### `json` format

The JSON format makes integration with programs that produce targets dynamically easier.
Each target is one JSON object in its own line. The method and url fields are required.
If present, the body field must be base64 encoded. The generated [JSON Schema](lib/target.schema.json)
defines the format in detail.

```bash
jq -ncM '{method: "GET", url: "http://goku", body: "Punch!" | @base64, header: {"Content-Type": ["text/plain"]}}' |
  vegeta attack -format=json -rate=100 | vegeta encode
```

##### `http` format

The http format almost resembles the plain-text HTTP message format defined in
[RFC 2616](https://www.w3.org/Protocols/rfc2616/rfc2616-sec5.html) but it
doesn't support in-line HTTP bodies, only references to files that are loaded and used
as request bodies (as exemplified below).

Although targets in this format can be produced by other programs, it was originally
meant to be used by people writing targets by hand for simple use cases.

Here are a few examples of valid targets files in the http format:

###### Simple targets
```
GET http://goku:9090/path/to/dragon?item=ball
GET http://user:password@goku:9090/path/to
HEAD http://goku:9090/path/to/success
```

###### Targets with custom headers
```
GET http://user:password@goku:9090/path/to
X-Account-ID: 8675309

DELETE http://goku:9090/path/to/remove
Confirmation-Token: 90215
Authorization: Token DEADBEEF
```

###### Targets with custom bodies
```
POST http://goku:9090/things
@/path/to/newthing.json

PATCH http://goku:9090/thing/71988591
@/path/to/thing-71988591.json
```

###### Targets with custom bodies and headers
```
POST http://goku:9090/things
X-Account-ID: 99
@/path/to/newthing.json
```

#### `-h2c`
Specifies that HTTP2 requests are to be sent over TCP without TLS encryption.

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

#### `-max-body`
Specifies the maximum number of bytes to be read from the body of each
response. Set to -1 for no limit. It knows how to intepret values like these:

* `"10 MB"` -> `10MB`
* `"10240 g"` -> `10TB`
* `"2000"` -> `2000B`
* `"1tB"` -> `1TB`
* `"5 peta"` -> `5PB`
* `"28 kilobytes"` -> `28KB`
* `"1 gigabyte"` -> `1GB`

#### `-name`

Specifies the name of the attack to be recorded in responses.

#### `-output`
Specifies the output file to which the binary results will be written
to. Made to be piped to the report command input. Defaults to stdout.

####  `-rate`
Specifies the request rate per time unit to issue against
the targets. The actual request rate can vary slightly due to things like
garbage collection, but overall it should stay very close to the specified.
If no time unit is provided, 1s is used.

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

#### `-timeout`
Specifies the timeout for each request. The default is 0 which disables
timeouts.

#### `-workers`
Specifies the initial number of workers used in the attack. The actual
number of workers will increase if necessary in order to sustain the
requested rate.

### `report` command

```
Usage: vegeta report [options] [<file>...]

Outputs a report of attack results.

Arguments:
  <file>  A file with vegeta attack results encoded with one of
          the supported encodings (gob | json | csv) [default: stdin]

Options:
  --type    Which report type to generate (text | json | hist[buckets]).
            [default: text]
  --output  Output file [default: stdout]

Examples:
  echo "GET http://:80" | vegeta attack -rate=10/s > results.gob
  echo "GET http://:80" | vegeta attack -rate=100/s | vegeta encode > results.json
  vegeta report results.*
```

#### `report -type=text`
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

#### `report -type=json`
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

#### `report -type=hist`
Computes and prints a text based histogram for the given buckets.
Each bucket upper bound is non-inclusive.
```console
cat results.bin | vegeta report -type='hist[0,2ms,4ms,6ms]'
Bucket         #     %       Histogram
[0,     2ms]   6007  32.65%  ########################
[2ms,   4ms]   5505  29.92%  ######################
[4ms,   6ms]   2117  11.51%  ########
[6ms,   +Inf]  4771  25.93%  ###################
```

### `encode` command

```
Usage: vegeta encode [options] [<file>...]

Encodes vegeta attack results from one encoding to another.
The supported encodings are Gob (binary), CSV and JSON.
Each input file may have a different encoding which is detected
automatically.

The CSV encoder doesn't write a header. The columns written by it are:

  1. Unix timestamp in nanoseconds since epoch
  2. HTTP status code
  3. Request latency in nanoseconds
  4. Bytes out
  5. Bytes in
  6. Error
  7. Base64 encoded response body
  8. Attack name
  9. Sequence number of request

Arguments:
  <file>  A file with vegeta attack results encoded with one of
          the supported encodings (gob | json | csv) [default: stdin]

Options:
  --to      Output encoding (gob | json | csv) [default: json]
  --output  Output file [default: stdout]

Examples:
  echo "GET http://:80" | vegeta attack -rate=1/s > results.gob
  cat results.gob | vegeta encode | jq -c 'del(.body)' | vegeta encode -to gob
```

### `plot` command

![Plot](https://i.imgur.com/Jra1sNH.png)

```
Usage: vegeta plot [options] [<file>...]

Outputs an HTML time series plot of request latencies over time.
The X axis represents elapsed time in seconds from the beginning
of the earliest attack in all input files. The Y axis represents
request latency in milliseconds.

Click and drag to select a region to zoom into. Double click to zoom out.
Choose a different number on the bottom left corner input field
to change the moving average window size (in data points).

Arguments:
  <file>  A file output by running vegeta attack [default: stdin]

Options:
  --title      Title and header of the resulting HTML page.
               [default: Vegeta Plot]
  --threshold  Threshold of data points to downsample series to.
               Series with less than --threshold number of data
               points are not downsampled. [default: 4000]

Examples:
  echo "GET http://:80" | vegeta attack -name=50qps -rate=50 -duration=5s > results.50qps.bin
  cat results.50qps.bin | vegeta plot > plot.50qps.html
  echo "GET http://:80" | vegeta attack -name=100qps -rate=100 -duration=5s > results.100qps.bin
  vegeta plot results.50qps.bin results.100qps.bin > plot.html
```

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
$ PDSH_RCMD_TYPE=ssh pdsh -b -w '10.0.1.1,10.0.2.1,10.0.3.1' \
    'echo "GET http://target/" | vegeta attack -rate=20000 -duration=60s > result.bin'
```

After the previous command finishes, we can gather the result files to use on our report.

```shell
$ for machine in 10.0.1.1 10.0.2.1 10.0.3.1; do
    scp $machine:~/result.bin $machine.bin &
  done
```

The `report` command accepts multiple result files.
It'll read and sort them by timestamp before generating reports.

```console
$ vegeta report 10.0.1.1.bin 10.0.2.1.bin 10.0.3.1.bin
Requests      [total, rate]         3600000, 60000.00
Latencies     [mean, 95, 99, max]   223.340085ms, 326.913687ms, 416.537743ms, 7.788103259s
Bytes In      [total, mean]         3714690, 3095.57
Bytes Out     [total, mean]         0, 0.00
Success       [ratio]               100.0%
Status Codes  [code:count]          200:3600000
Error Set:
```

## Usage: Real-time Analysis
If you are a happy user of iTerm, you can integrate vegeta with [jplot](https://github.com/rs/jplot) using [jaggr](https://github.com/rs/jaggr) to plot a vegeta report in real-time in the comfort of you terminal:

```
echo 'GET http://localhost:8080' | \
    vegeta attack -rate 5000 -duration 10m | vegeta encode | \
    jaggr @count=rps \
          hist\[100,200,300,400,500\]:code \
          p25,p50,p95:latency \
          sum:bytes_in \
          sum:bytes_out | \
    jplot rps+code.hist.100+code.hist.200+code.hist.300+code.hist.400+code.hist.500 \
          latency.p95+latency.p50+latency.p25 \
          bytes_in.sum+bytes_out.sum
```

![](https://i.imgur.com/ttBDsQS.gif)

## Usage (Library)

The library versioning follows [SemVer v2.0.0](https://semver.org/spec/v2.0.0.html).
Since [lib/v9.0.0](https://github.com/tsenart/vegeta/tree/lib/v9.0.0), the library and cli
are versioned separately to better isolate breaking changes to each component.

```go
package main

import (
  "fmt"
  "time"

  vegeta "github.com/tsenart/vegeta/lib"
)

func main() {
  rate := vegeta.Rate{Freq: 100, Per: time.Second}
  duration := 4 * time.Second
  targeter := vegeta.NewStaticTargeter(vegeta.Target{
    Method: "GET",
    URL:    "http://localhost:9100/",
  })
  attacker := vegeta.NewAttacker()

  var metrics vegeta.Metrics
  for res := range attacker.Attack(targeter, rate, duration, "Big Bang!") {
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
