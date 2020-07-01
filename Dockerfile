FROM golang:1.14.4-alpine3.12 AS BUILD

RUN apk add make

WORKDIR /vegeta

# cache dependencies
ADD go.mod /vegeta
ADD go.sum /vegeta
RUN go mod download

#now build source code
ADD / /vegeta
RUN make vegeta
# RUN go build -v -o /bin/vegeta

FROM alpine:3.12.0

ENV TARGET_URL ''
ENV DURATION '5'
ENV REQUESTS_PER_SECOND '5'

COPY --from=BUILD /vegeta/vegeta /bin/vegeta
ADD startup.sh /
CMD [ "/startup.sh" ]

