package vegeta

import "net/http"

// NewController returns an http.Handler which exposes a REST interface to
// control the provided Attacker.
func NewController(path string, atk *Attacker) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch action := r.URL.Path[len(path):]; action {
		case "stop":
			atk.Stop()
		}
	})
}
