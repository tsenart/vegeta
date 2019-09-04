// +build gofuzz

package vegeta

func decodeFuzzHeaders(fuzz []byte, headers map[string][]string) (
	rest []byte,
	ok bool,
) {
	rest = fuzz
	for {
		if len(rest) == 0 {
			// Consumed all fuzz
			ok = true
			return
		}
		if fuzz[0] == 0 {
			// Headers terminated
			if len(rest) == 1 {
				rest = []byte{}
			} else {
				rest = rest[1:]
			}
			ok = true
			return
		}
		if len(fuzz) == 1 {
			// Invalid headers encoding
			return
		}
		rest, ok = decodeFuzzHeader(rest[1:], headers)
		if !ok {
			return
		}
	}
}

func decodeFuzzHeader(fuzz []byte, headers map[string][]string) (
	rest []byte,
	ok bool,
) {
	if len(fuzz) == 0 {
		ok = true
		return
	}
	name, rest, ok := extractFuzzString(fuzz)
	if !ok {
		return
	}
	value, rest, ok := extractFuzzString(rest)
	if !ok {
		return
	}
	if header, ok := headers[name]; ok {
		headers[name] = append(header, value)
	} else {
		headers[name] = []string{value}
	}
	ok = true
	return
}

func extractFuzzString(fuzz []byte) (
	value string,
	rest []byte,
	ok bool,
) {
	if len(fuzz) < 2 {
		// Invalid string encoding
		return
	}
	length := int(fuzz[0])
	if length == 0 {
		// Invalid length
		return
	}
	if len(fuzz) < (length + 1) {
		// Insufficient fuzz
		return
	}
	value = string(fuzz[1 : length+1])
	if len(fuzz) == (length + 1) {
		// Consumed all fuzz
		rest = []byte{}
	} else {
		// More fuzz
		rest = fuzz[length+1:]
	}
	ok = true
	return
}

func extractFuzzByteString(fuzz []byte) (
	value []byte,
	rest []byte,
	ok bool,
) {
	if len(fuzz) < 2 {
		// Invalid byte string encoding
		return
	}
	length := int(fuzz[0])
	if length == 0 {
		// Invalid length
		return
	}
	if len(fuzz) < (length + 1) {
		// Insufficient fuzz
		return
	}
	value = fuzz[1 : length+1]
	if len(fuzz) == (length + 1) {
		// Consumed all fuzz
		rest = []byte{}
	} else {
		// More fuzz
		rest = fuzz[length+1:]
	}
	ok = true
	return
}
