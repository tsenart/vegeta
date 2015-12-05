#!/bin/sh

for OS in "freebsd" "linux" "darwin" "windows"; do
  for ARCH in "386" "amd64"; do
    VERSION="$(git describe --tags $1)"
    GOOS=$OS CGO_ENABLED=0 GOARCH=$ARCH go build -ldflags "-X main.Version=$VERSION" -o vegeta
    ARCHIVE="vegeta-$VERSION-$OS-$ARCH.tar.gz"
    tar -czf $ARCHIVE vegeta
    echo $ARCHIVE
  done
done
