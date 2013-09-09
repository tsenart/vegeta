package vegeta

import (
	"io"
)

// Reporter represents any reporter of the results of the test
type Reporter interface {
	Report(io.Writer) error
	Add(res *Result)
}
