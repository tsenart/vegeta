// +build !windows

package main

import "flag"

func systemSpecificFlags(fs *flag.FlagSet, opts *attackOpts) {
	fs.Var(&opts.resolvers, "resolvers", "List of addresses (ip:port) to use for DNS resolution. Disables use of local system DNS. (comma separated list)")
}
