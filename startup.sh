#!/bin/sh

if [ "$TARGET_URL" == "" ]; then
    echo "ENV TARGET_URL is required"
    exit 1
fi

echo "Starting attack to $TARGET_URL for $DURATION at $REQUESTS_PER_SECOND requests/s"

echo "GET $TARGET_URL" | vegeta attack -duration=$DURATION -rate=$REQUESTS_PER_SECOND -prom-enable=true > /dev/null 2>&1
# | vegeta report -every=1s

