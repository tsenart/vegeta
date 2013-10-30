# Vegeta [![Build Status](https://secure.travis-ci.org/tsenart/vegeta.png)](http://travis-ci.org/tsenart/vegeta)

Vegeta is a versatile HTTP load testing tool built out of need to drill
HTTP services with a constant request rate.
It can be used both as a command line utility and a library.

![Vegeta](http://fc09.deviantart.net/fs49/i/2009/198/c/c/ssj2_vegeta_by_trunks24.jpg)

## Install
### Pre-compiled executables
* [Mac OSX 64 bit](https://dl.dropboxusercontent.com/u/83217940/vegeta-darwin-amd64-1517f2d.tar.gz)
* [Mac OSX 32 bit](https://dl.dropboxusercontent.com/u/83217940/vegeta-darwin-386-1517f2d.tar.gz)
* [Linux 64 bit](https://dl.dropboxusercontent.com/u/83217940/vegeta-linux-amd64-1517f2d.tar.gz)
* [Linux 32 bit](https://dl.dropboxusercontent.com/u/83217940/vegeta-linux-386-1517f2d.tar.gz)

### Source
You need go installed and `GOBIN` in your `PATH`. Once that is done, run the
command:
```shell
$ go get github.com/tsenart/vegeta
$ go install github.com/tsenart/vegeta
```

## Usage examples
```shell
$ echo "GET http://localhost/" | vegeta attack -rate=100 -duration=5s | vegeta report
$ vegeta attack -targets=targets.txt > results.vr
$ vegeta report -input=results.vr -reporter=json > metrics.json
$ cat results.vr | vegeta report -reporter=plot > plot.html
```

## Usage manual
```shell
$ vegeta -h
Usage: vegeta [globals] <command> [options]

Commands:
  attack  Hit the targets
  report  Report the results

Globals:
  -cpus=8 Number of CPUs to use
```

#### -cpus
Specifies the number of CPUs to be used internally.
It defaults to the amount of CPUs available in the system.

### attack
```shell
$ vegeta attack -h
Usage of attack:
  -duration=10s: Duration of the test
  -header=: Targets request header
  -ordering="random": Attack ordering [sequential, random]
  -output="stdout": Output file
  -rate=50: Requests per second
  -targets="stdin": Targets file
```

#### -duration
Specifies the amount of time to issue request to the targets.
The internal concurrency structure's setup has this value as a variable.
The actual run time of the test can be longer than specified due to the
responses delay.

#### -header
Specifies a request header to be used in all targets defined.
You can specify as many as needed by repeating the flag.

#### -ordering
Specifies the ordering of target attack. The default is `random` and
it will randomly pick one of the targets per request without ever choosing
that target again.
The other option is `sequential` and it does what you would expect it to
do.

#### -output
Specifies the output file to which the binary results will be written
to. Made to be piped to the report command input. Defaults to stdout.

####  -rate
Specifies the requests per second rate to issue against
the targets. The actual request rate can vary slightly due to things like
garbage collection, but overall it should stay very close to the specified.

#### -targets
Specifies the attack targets in a line separated file, defaulting to stdin.
The format should be as follows.
```
GET http://goku:9090/path/to/dragon?item=balls
GET http://user:password@goku:9090/path/to
HEAD http://goku:9090/path/to/success
...
```

### report
```
$ vegeta report -h
Usage of report:
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
Requests      [total]               1200
Duration      [total]               1.998307684s
Latencies     [mean, 95, 99, max]   223.340085ms, 326.913687ms, 416.537743ms, 7.788103259s
Bytes In      [total, mean]         3714690, 3095.57
Bytes Out     [total, mean]         0, 0.00
Success       [ratio]               55.42%
Status Codes  [code:count]          0:535  200:665
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
  "duration": 1998307684,
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

![Plot](https://dl.dropboxusercontent.com/u/83217940/plot.png)


## Usage (Library)
```go
package main

import (
  vegeta "github.com/tsenart/vegeta/lib"
  "time"
  "fmt"
)

func main() {
  targets, _ := vegeta.NewTargets([]string{"GET http://localhost:9100/"})
  rate := uint64(100) // per second
  duration := 4 * time.Second

  results := vegeta.Attack(targets, rate, duration)
  metrics := vegeta.NewMetrics(results)

  fmt.Printf("Mean latency: %s", metrics.Latencies.Mean)
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

Copyright (c) 2013 Tomás Senart

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
