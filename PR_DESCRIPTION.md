# Add --csv-header option to encode command

#### Background

This PR addresses issue #588 where users requested a way to include headers in CSV output for better readability and easier processing with downstream tools. Currently, `vegeta encode` outputs raw CSV data without headers, requiring manual workarounds.

**What type of PR is this?**
/kind feature

**What this PR does / why we need it**:
This PR adds a `--csv-header` flag to the `vegeta encode` command, allowing users to output CSV files with a header row.

**Implementation Details**:
- Refactored `lib/results.go`:
  - Exposed `CSVHeader` (lowercase) for consistency.
  - Added `WriteCSVHeader(w io.Writer) error` helper function.
- Updated `encode.go`:
  - Added `--csv-header` flag.
  - Integrated `WriteCSVHeader` in the encoding loop.
- Updated `lib/results_test.go`:
  - Added `TestWriteCSVHeader` to verify the header content matches expectations.

**Which issue(s) this PR fixes**:
Fixes #588

**Special notes for your reviewer**:
**Verification Results**

**Automated Tests**
Ran `go test ./...` and `make test` (implicit via go test):
- `TestWriteCSVHeader` passed.
- Regression tests passed.

**Manual Verification**
Executed:
```bash
echo "GET http://:80" | go run . attack -rate=1 -duration=1s | go run . encode -to csv -csv-header
```
Output:
```csv
timestamp,code,latency,bytes_out,bytes_in,error,body,attack,seq,method,url,headers
1769322193920100568,0,209402,0,0,"Get ""http://:80"": lookup : no such host",,,0,GET,http://:80,
```

**Does this PR introduce a user-facing change?**:
```release-note
Added --csv-header flag to encode command to output CSV headers.
```

#### Checklist

- [x] Git commit messages conform to [community standards](http://tbaggery.com/2008/04/19/a-note-about-git-commit-messages.html).
- [x] Each Git commit represents meaningful milestones or atomic units of work.
- [x] Changed or added code is covered by appropriate tests.
