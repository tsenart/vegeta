# Vegeta

Vegeta is a versatile HTTP load testing tool built out of need to drill
HTTP services with a relatively constant request rate.

## Install
You need go installed and `GOBIN` in your `PATH`. Once that is done, run the
command:
```shell
$ go install github.com/tsenart/vegeta
```

## Usage
```shell
$ vegeta -h
Usage of vegeta:
  -duration=10s: Duration of the test
  -ordering="random": sequential or random
  -rate=50: Requests per second
  -reporter="text": Reporter to use [text]
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

####  -rate
Specifies the requests per second rate to issue requests with against
the targets

#### -reporter
Specifies the reporting type to display the results with.
The default is a text report printed to stdout.

#### -targets
Specifies the attack targets in a line sepated file. The format should
be as follows:
```
GET http://goku:9090/path/to/dragon?item=balls
HEAD http://goku:9090/path/to/success
...
```


## TODO
* Add timeout options to the requests
* Graphical reports
* Test

## Licence
See the `LICENSE` file.




