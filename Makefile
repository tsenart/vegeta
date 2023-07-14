COMMIT=$(shell git rev-parse HEAD)
VERSION=$(shell git describe --tags --exact-match --always)
DATE=$(shell date +'%FT%TZ%z')

vegeta: generate
	CGO_ENABLED=0 go build -v -a -tags=netgo \
  	-ldflags '-s -w -extldflags "-static" -X main.Version=$(VERSION) -X main.Commit=$(COMMIT) -X main.Date=$(DATE)'

clean-vegeta:
	rm vegeta

generate: GOOS=$(GOHOSTOS) GOARCH=$(GOHOSTARCH)
generate:
	go install github.com/mailru/easyjson/...@latest
	go get github.com/shurcooL/vfsgen
	go install github.com/shurcooL/vfsgen/...@latest
	go generate ./...
