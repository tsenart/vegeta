COMMIT=$(shell git rev-parse HEAD)
VERSION=$(shell git describe --tags --exact-match --always)
DATE=$(shell date +'%FT%TZ%z')

vegeta: vendor generate
	CGO_ENABLED=0 go build -v -a -tags=netgo \
  	-ldflags '-s -w -extldflags "-static" -X main.Version=$(VERSION) -X main.Commit=$(COMMIT) -X main.Date=$(DATE)'

clean-vegeta:
	rm vegeta

generate: vendor
	go generate ./...

vendor:
	dep ensure -v

clean-vendor:
	rm -rf vendor

dist:
	goreleaser release --debug --skip-validate

clean-dist:
	rm -rf dist
