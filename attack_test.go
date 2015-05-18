package main

import (
	"net/http"
	"reflect"
	"testing"
)

func TestHeadersSet(t *testing.T) {
	h := headers{
		Header: make(http.Header),
	}
	for i, tt := range []struct {
		key, val string
		want     []string
	}{
		{"key", "value", []string{"value"}},
		{"key", "value", []string{"value", "value"}},
		{"Key", "Value", []string{"Value"}},
		{"KEY", "VALUE", []string{"VALUE"}},
	} {
		if err := h.Set(tt.key + ": " + tt.val); err != nil {
			t.Error(err)
		} else if got := h.Header[tt.key]; !reflect.DeepEqual(got, tt.want) {
			t.Errorf("test #%d, '%s: %s': got: %+v, want: %+v", i, tt.key, tt.val, got, tt.want)
		}
	}
}
