// +build !windows

package main

import "flag"

func systemSpecificFlags(fs *flag.FlagSet, opts *attackOpts) {
	fs.Var(&opts.resolvers, "resolvers", "Override system dns resolution (comma separated list)")
}
