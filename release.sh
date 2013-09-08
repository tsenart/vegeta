#!/bin/sh

for OS in "linux" "darwin"; do
	for ARCH in "386" "amd64"; do
		GOOS=$OS  CGO_ENABLED=0 GOARCH=$ARCH go build -o vegeta
		REV=$(git rev-parse HEAD)
		ARCHIVE=vegeta-$OS-$ARCH-${REV:0:7}.tar.gz
		tar -czf $ARCHIVE vegeta
		echo $ARCHIVE
	done
done
