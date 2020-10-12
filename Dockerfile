FROM golang:1.14.4-alpine3.12 AS BUILD

RUN apk add make build-base

WORKDIR /vegeta

# cache dependencies
ADD go.mod /vegeta
ADD go.sum /vegeta
RUN go mod download

# now build source code
ADD / /vegeta

RUN make vegeta

FROM alpine:3.12.0

COPY --from=BUILD /vegeta/vegeta /bin/vegeta

ENTRYPOINT [ "" ]
