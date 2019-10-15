#!/usr/bin/env python3

import json
import os
import subprocess
import sys
import time


if '-h' in sys.argv or '--help' in sys.argv:
    print('usage:', file=sys.stderr)
    print('echo GET http://localhost:8080/ | %s' % sys.argv[0], file=sys.stderr)
    sys.exit(1)

target = sys.stdin.read().strip()


# Log-spaced rates (each ca. +25% (+1dB) of the previous, covering 1/sec to 100k/sec)
rates = [10.0 ** (i / 10.0) for i in range(50)]

# Log-spaced buckets (each ca. +25% (+1dB) of the previous, covering <1us to >10s)
buckets = [0] + [1e3 * 10.0 ** (i / 10.0) for i in range(71)]


# Run vegeta attack
for rate in rates:
    filename='results_%i.bin' % (1000*rate)
    if not os.path.exists(filename):
        cmd = 'vegeta attack -duration 5s -rate %i/1000s -output %s' % (1000*rate, filename)
        print(cmd, file=sys.stderr)
        subprocess.run(cmd, shell=True, input=target, encoding='utf-8')
        time.sleep(5)


# Run vegeta report, and extract data for gnuplot
with open('results_latency.txt', 'w') as out_latency, \
     open('results_success.txt', 'w') as out_success:

    for rate in rates:
        cmd = 'vegeta report -type=json -buckets \'%s\' results_%i.bin' \
            % ("[%s]" % ",".join("%ins" % bucket for bucket in buckets), 1000*rate)
        print(cmd, file=sys.stderr)
        result = json.loads(subprocess.check_output(cmd, shell=True))

        # (Request rate, Response latency) -> (Fraction of responses)
        for latency, count in result['buckets'].items():
            latency_nsec = float(latency)
            fraction = count / sum(result['buckets'].values()) * result['success']
            print(rate, latency_nsec, fraction, file=out_latency)
        print(file=out_latency)

        # (Request rate) -> (Success rate)
        print(rate, result['success'], file=out_success)

print('# wrote results_latency.txt and results_success.txt', file=sys.stderr)


# Visualize with gnuplot (PNG)
cmd = 'gnuplot -e "set term png size 1280, 800" ramp-requests.plt > result.png'
print(cmd, file=sys.stderr)
subprocess.run(cmd, shell=True)

# Visualize with gnuplot (default, likely a UI)
cmd = 'gnuplot -persist ramp-requests.plt'
print(cmd, file=sys.stderr)
subprocess.run(cmd, shell=True)
