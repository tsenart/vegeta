# Vegeta

Vegeta is a versatile HTTP load testing tool built out of need to drill
HTTP services with a constant request rate.
It can be used both as a command line utility and a library.

![Vegeta](http://fc09.deviantart.net/fs49/i/2009/198/c/c/ssj2_vegeta_by_trunks24.jpg)

## Install
### Pre-compiled executables
You can download already compiled executables for Linux and Mac OS X.
```
Linux 64 bit
URL: https://dl.dropboxusercontent.com/u/83217940/vegeta-linux-amd64.tar.gz
SHA256 of the executable:
a9c5f41e44465c28dcbc58813b3868ffefd6c8a050a12e6a7d19ec1cba021518

Linux 32 bit
URL: https://dl.dropboxusercontent.com/u/83217940/vegeta-linux-386.tar.gz
SHA256 of the executable:
af185355cfe405e8cb554459a27b8e502ba1bb77011cab1c676315b55a3a49b7

Mac OS X 64 bit
URL: https://dl.dropboxusercontent.com/u/83217940/vegeta-darwin-amd64.tar.gz
SHA256 of the executable:
3144ba0fe80ec7ea7b735718599d9fbda95eda8ecc6f6be2ac57b3cedb2f21df

Mac OS X 32 bit
URL: https://dl.dropboxusercontent.com/u/83217940/vegeta-darwin-386.tar.gz
SHA256 of the executable:
40a5bc50c3f9516fa01c903a0d5a1662478ac9c3da0bf00ed4a7920ffd2633ab
```

### Source
You need go installed and `GOBIN` in your `PATH`. Once that is done, run the
command:
```shell
$ go get github.com/tsenart/vegeta
$ go install github.com/tsenart/vegeta
```

## Usage (CLI)
```shell
$ vegeta -h
Usage of vegeta:
  -duration=10s: Duration of the test
  -ordering="random": Attack ordering [sequential, random]
  -output="stdout": Reporter output file
  -rate=50: Requests per second
  -reporter="text": Reporter to use [text, plot:timings]
  -targets="targets.txt": Targets file
```

#### -duration
Specifies the amount of time to issue request to the targets.
The internal concurrency structure's setup has this value as a variable.
The actual run time of the test can be longer than specified due to the
responses delay.

#### -ordering
Specifies the ordering of target attack. The default is `random` and
it will randomly pick one of the targets per request without ever choosing
that target again.
The other option is `sequential` and it does what you would expect it to
do.

#### -output
Specifies the output file to which the report will be written to.
The default is stdout.

####  -rate
Specifies the requests per second rate to issue against
the targets. The actual request rate can vary slightly due to things like
garbage collection, but overall it should stay very close to the specified.

#### -reporter
Specifies the reporting type to display the results with.
The default is the text report printed to stdout.
##### -reporter=text
```
Time(avg)	Requests	Success		Bytes(rx/tx)
152.341ms	200		    17.00%		251.00/0.00

Count:		49	30	39	48	34
Status:		500	404	409	503	200

Error Set:
Server Timeout
Page Not Found
```
##### -reporter=plot:timings
Plots the request timings in SVG format.
![plot](https://dl.dropboxusercontent.com/u/83217940/plot.svg)

#### -targets
Specifies the attack targets in a line sepated file. The format should
be as follows:
```
GET http://goku:9090/path/to/dragon?item=balls
GET http://user:password@goku:9090/path/to
HEAD http://goku:9090/path/to/success
...
```

## Usage (Library)
```go
package main

import (
  vegeta "github.com/tsenart/vegeta/lib"
  "time"
  "os"
)

func main() {
  targets, _ := vegeta.NewTargets([]string{"GET http://localhost:9100/"})
  rate := uint64(100) // per second
  duration := 4 * time.Second
  reporter := vegeta.NewTextReporter()

  vegeta.Attack(targets, rate, duration, reporter)

  reporter.Report(os.Stdout)
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

## TODO
* Add timeout options to the requests
* Cluster mode (to overcome single machine limits)

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
