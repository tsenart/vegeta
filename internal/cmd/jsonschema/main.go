package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io/ioutil"
	"os"
	"strings"

	"github.com/alecthomas/jsonschema"

	vegeta "github.com/tsenart/vegeta/v12/lib"
)

func main() {
	types := map[string]interface{}{
		"Target": &vegeta.Target{},
	}

	valid := strings.Join(keys(types), ", ")

	fs := flag.NewFlagSet("jsonschema", flag.ContinueOnError)
	typ := fs.String("type", "", fmt.Sprintf("Vegeta type to generate a JSON schema for [%s]", valid))
	out := fs.String("output", "stdout", "Output file")

	if err := fs.Parse(os.Args[1:]); err != nil {
		die("%s", err)
	}

	t, ok := types[*typ]
	if !ok {
		die("invalid type %q not in [%s]", *typ, valid)
	}

	schema, err := json.MarshalIndent(jsonschema.Reflect(t), "", "  ")
	if err != nil {
		die("%s", err)
	}

	switch *out {
	case "stdout":
		_, err = os.Stdout.Write(schema)
	default:
		err = ioutil.WriteFile(*out, schema, 0644)
	}

	if err != nil {
		die("%s", err)
	}
}

func die(s string, args ...interface{}) {
	fmt.Fprintf(os.Stderr, s, args...)
	os.Exit(1)
}

func keys(types map[string]interface{}) (ks []string) {
	for k := range types {
		ks = append(ks, k)
	}
	return ks
}
