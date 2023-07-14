COMMIT=$(shell git rev-parse HEAD)
VERSION=$(shell git describe --tags --exact-match --always)
DATE=$(shell date +'%FT%TZ%z')

vegeta: generate
	CGO_ENABLED=0 go build -v -a -tags=netgo \
  	-ldflags '-s -w -extldflags "-static" -X main.Version=$(VERSION) -X main.Commit=$(COMMIT) -X main.Date=$(DATE)'

generate: GOARCH := $(shell go env GOHOSTARCH)
generate: GOOS := $(shell go env GOHOSTOS)
generate:
	go install github.com/mailru/easyjson/...@latest
	go get github.com/shurcooL/vfsgen
	go install github.com/shurcooL/vfsgen/...@latest
	go generate ./...
