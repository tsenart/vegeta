# Load ramping

This script will automatically run vegeta against a target with different request
rates and graph the latency distribution and success rate at each request rate.

Usage:

```
echo GET http://localhost:8080/ | python3 ramp-requests.py
```

Dependencies:

* Python 3
* Gnuplot

For more documentation, see https://github.com/tsenart/vegeta/wiki/Load-ramping
