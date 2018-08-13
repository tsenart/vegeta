// +build dev

package plot

import (
	"net/http"
)

// Assets contains assets required to render the Plot.
var Assets http.FileSystem = http.Dir("assets")
