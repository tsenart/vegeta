#!/bin/sh

for OS in "freebsd" "linux" "darwin" "windows"; do
	for ARCH in "386" "amd64"; do
		GOOS=$OS  CGO_ENABLED=0 GOARCH=$ARCH go build -o vegeta
		ARCHIVE=vegeta-$OS-$ARCH.tar.gz
		tar -czf $ARCHIVE vegeta
		echo $ARCHIVE
	done
done
