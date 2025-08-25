FROM golang:1.22-alpine3.21 AS build

RUN apk add make build-base git

WORKDIR /vegeta

# cache dependencies
ADD go.mod /vegeta
ADD go.sum /vegeta
RUN go mod download

ADD . /vegeta

RUN make generate
RUN make vegeta

FROM alpine:3.22.1

COPY --from=build /vegeta/vegeta /bin/vegeta

ENTRYPOINT ["vegeta"]
