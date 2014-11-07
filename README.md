# Vegeta [![Build Status](https://secure.travis-ci.org/tsenart/vegeta.png)](http://travis-ci.org/tsenart/vegeta)

Vegeta is a versatile HTTP load testing tool built out of need to drill
HTTP services with a constant request rate.
It can be used both as a command line utility and a library.

![Vegeta](http://fc09.deviantart.net/fs49/i/2009/198/c/c/ssj2_vegeta_by_trunks24.jpg)

## Install
### Pre-compiled executables
Get them [here](http://github.com/tsenart/vegeta/releases).

### Source
You need go installed and `GOBIN` in your `PATH`. Once that is done, run the
command:
```shell
$ go get github.com/tsenart/vegeta
$ go install github.com/tsenart/vegeta
```

## Usage manual
```shell
$ vegeta -h
Usage: vegeta [globals] <command> [options]

attack command:
  -body="": Requests body file
  -cert="": x509 Certificate file
  -duration=10s: Duration of the test
  -header=: Request header
  -keepalive=true: Use persistent connections
  -laddr=0.0.0.0: Local IP address
  -lazy=false: Read targets lazily
  -ordering="random": Attack ordering [sequential, random]
  -output="stdout": Output file
  -rate=50: Requests per second
  -redirects=10: Number of redirects to follow
  -targets="stdin": Targets file
  -timeout=0: Requests timeout
  -workers=0: Number of workers

report command:
  -inputs="stdin": Input files (comma separated)
  -output="stdout": Output file
  -reporter="text": Reporter [text, json, plot]

global flags:
  -cpus=8 Number of CPUs to use

examples:
  echo "GET http://localhost/" | vegeta attack -duration=5s | tee results.bin | vegeta report
  vegeta attack -targets=targets.txt > results.bin
  vegeta report -inputs=results.bin -reporter=json > metrics.json
  cat results.bin | vegeta report -reporter=plot > plot.html
```

#### -cpus
Specifies the number of CPUs to be used internally.
It defaults to the amount of CPUs available in the system.

### attack
```shell
$ vegeta attack -h
Usage of vegeta attack:
  -body="": Requests body file
  -cert="": x509 Certificate file
  -duration=10s: Duration of the test
  -header=: Request header
  -keepalive=true: Use persistent connections
  -laddr=0.0.0.0: Local IP address
  -lazy=false: Read targets lazily
  -output="stdout": Output file
  -rate=50: Requests per second
  -redirects=10: Number of redirects to follow
  -targets="stdin": Targets file
  -timeout=30s: Requests timeout
  -workers=0: Number of workers
```

#### -body
Specifies the file whose content will be set as the body of every request.

#### -cert
Specifies the x509 TLS certificate to be used with HTTPS requests.

#### -duration
Specifies the amount of time to issue request to the targets.
The internal concurrency structure's setup has this value as a variable.
The actual run time of the test can be longer than specified due to the
responses delay.

#### -header
Specifies a request header to be used in all targets defined.
You can specify as many as needed by repeating the flag.

#### -keepalive
Specifies whether to reuse TCP connections between HTTP requests.

#### -laddr
Specifies the local IP address to be used.

#### -lazy
Specifies whether to read the input targets lazily instead of eagerly.
This allows streaming targets into the attack command and reduces memory
footprint.
The trade-off is one of added latency in each hit against the targets.

#### -output
Specifies the output file to which the binary results will be written
to. Made to be piped to the report command input. Defaults to stdout.

####  -rate
Specifies the requests per second rate to issue against
the targets. The actual request rate can vary slightly due to things like
garbage collection, but overall it should stay very close to the specified.

#### -redirects
Specifies the max number of redirects followed on each request. The
default is 10.

#### -targets
Specifies the attack targets in a line separated file, defaulting to stdin.
The format should be as follows.
```
GET http://goku:9090/path/to/dragon?item=balls
GET http://user:password@goku:9090/path/to
HEAD http://goku:9090/path/to/success
...
```

#### -timeout
Specifies the timeout for each request. The default is 0 which disables
timeouts.

#### -workers
Specifies the number of workers used in the attack. The default 0
means every single hit runs in its own worker.

### report
```
$ vegeta report -h
Usage of vegeta report:
  -input="stdin": Input files (comma separated)
  -output="stdout": Output file
  -reporter="text": Reporter [text, json, plot]
```

#### -input
Specifies the input files to generate the report of, defaulting to stdin.
These are the output of vegeta attack. You can specify more than one (comma
separated) and they will be merged and sorted before being used by the
reports.

#### -output
Specifies the output file to which the report will be written to.

#### -reporter
Specifies the kind of report to be generated. It defaults to text.

##### text
```
Requests      [total]                   1200
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

##### json
```json
{
  "latencies": {
    "mean": 9093653647,
    "50th": 2401223400,
    "95th": 12553709381,
    "99th": 12604629125,
    "max": 12604629125
  },
  "bytes_in": {
    "total": 782040,
    "mean": 651.7
  },
  "bytes_out": {
    "total": 0,
    "mean": 0
  },
  "duration": 9949883921,
  "wait": 145082066,
  "requests": 1200,
  "success": 0.11666666666666667,
  "status_codes": {
    "0": 1060,
    "200": 140
  },
  "errors": [
    "Get http://localhost:6060: dial tcp 127.0.0.1:6060: operation timed out"
  ]
}
```
##### plot
Generates an HTML5 page with an interactive plot based on
[Dygraphs](http://dygraphs.com).
Click and drag to select a region to zoom into. Double click to zoom
out.
Input a different number on the bottom left corner input field
to change the moving average window size (in data points).

![Plot](http://i.imgur.com/oi0cgGq.png)


## Usage (Library)
```go
package main

import (
  "time"
  "fmt"

  vegeta "github.com/tsenart/vegeta/lib"
)

func main() {

  rate := uint64(100) // per second
  duration := 4 * time.Second
  targeter := vegeta.NewStaticTargeter(&vegeta.Target{
    Method: "GET",
    URL:    "http://localhost:9100/",
  })
  attacker := vegeta.NewAttacker()

  var results vegeta.Results
  for res := range attacker.Attack(targeter, rate, duration) {
    results = append(results, res)
  }

  metrics := vegeta.NewMetrics(results)
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

## Licence
```
The MIT License (MIT)

Copyright (c) 2013, 2014 Tomás Senart

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
