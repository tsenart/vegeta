# Flags.parse_attack and Flags.parse_report: Go Vegeta's defaults, forms
# and error texts (checked by hand against Go Vegeta's attack and report
# commands, Go 1.26), the port's refusals, and a round trip through the
# canonical command line (LAWS attack_args).
import Base
import ../lib/dec.bend as Dec
import ../lib/dur.bend as Dur
import ../lib/pacer.bend as Pace
import ../lib/hdr.bend as Hdr
import ../lib/flags.bend as Flags

def opt(+m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "-"
    case Some{n}:
      Dec.show(n)

def vals(vs: List<&2, String>) -> String:
  match vs:
    case Nil{}:
      ""
    case Con{+v, +rest}:
      "[" ++ v ++ "]" ++ vals(rest)

def hdrs(hs: List<&2, Hdr.Header>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{+h, +rest}:
      Hdr.Header{k, vs} = h
      " " ++ k ++ "=" ++ vals(vs) ++ hdrs(rest)

def body(+b: Maybe<&2, String>) -> String:
  match b:
    case None{}:
      "-"
    case Some{p}:
      p

def attack(+a: Flags.Attack) -> String:
  Flags.Attack{rate, du, tg, fm, out, name, w, mw, to, hs, b, ka, mb, rd, enc} = a
  Pace.Rate{f, p} = rate
  "rate=" ++ Dec.show(f) ++ "/" ++ Dec.show(p) ++ " duration=" ++ Dec.show(du) ++ " targets=" ++ tg ++ " format=" ++ fm
  ++ " output=" ++ out ++ " name=" ++ name ++ " workers=" ++ Dec.show(w) ++ " max-workers=" ++ opt(mw) ++ " timeout=" ++ opt(to)
  ++ " headers=" ++ hdrs(hs) ++ " body=" ++ body(b) ++ " keepalive=" ++ Flags.pick(String, ka, "true", "false")
  ++ " max-body=" ++ opt(mb) ++ " redirects=" ++ opt(rd) ++ " encoding=" ++ enc

def show_a(+r: Result<&2, &2, String, Flags.Attack>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ e
    case Done{a}:
      attack(a)

def nats(bs: List<&2, Nat>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, +rest}:
      " " ++ Dec.show(b) ++ nats(rest)

def kind(+k: Flags.RKind) -> String:
  match k:
    case Flags.AsText{}:
      "text"
    case Flags.AsJson{bs}:
      "json[" ++ nats(bs) ++ " ]"
    case Flags.AsHist{bs}:
      "hist[" ++ nats(bs) ++ " ]"

def show_r(+r: Result<&2, &2, String, Flags.Report>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ e
    case Done{x}:
      Flags.Report{k, out, files} = x
      kind(k) ++ " output=" ++ out ++ " files=" ++ vals(files)

def a(+args: List<&2, String>) -> String:
  show_a(Flags.parse_attack(args))

def r(+args: List<&2, String>) -> String:
  show_r(Flags.parse_report(args))

# LAWS attack_args, for the round trip
def opt_nat(+flag: String, +none: String, +m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      flag ++ none
    case Some{n}:
      flag ++ Dec.show(n)

def hdr_val_flags(+k: String, vs: List<&2, String>) -> List<&2, String>:
  match vs:
    case Nil{}:
      []
    case Con{+v, +rest}:
      Con{"-header=" ++ k ++ ": " ++ v, hdr_val_flags(k, rest)}

def hdr_flags(hs: List<&2, Hdr.Header>) -> List<&2, String>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      Hdr.Header{k, vs} = h
      List.append(&2, String, hdr_val_flags(k, vs), hdr_flags(rest))

def one(+flag: String, +m: Maybe<&2, Nat>, +d: Bool) -> List<&2, String>:
  match m:
    case None{}:
      []
    case Some{n}:
      [flag ++ Flags.pick(String, d, Dur.show(n), Dec.show(n))]

def args_of(+x: Flags.Attack) -> List<&2, String>:
  Flags.Attack{rate, du, tg, fm, out, name, w, mw, to, hs, b, ka, mb, rd, enc} = x
  Pace.Rate{f, p} = rate
  List.concat(&2, String, [
    ["-rate=" ++ Dec.show(f) ++ "/" ++ Dur.show(p), "-duration=" ++ Dur.show(du), "-targets=" ++ tg, "-format=" ++ fm, "-output=" ++ out,
     "-name=" ++ name, "-workers=" ++ Dec.show(w)],
    one("-max-workers=", mw, False{}), one("-timeout=", to, True{}), hdr_flags(hs), ["-body=" ++ body(b)],
    ["-keepalive=" ++ Flags.pick(String, ka, "true", "false"), opt_nat("-max-body=", "-1", mb), opt_nat("-redirects=", "-1", rd), "-encoding=" ++ enc]])

def trip() -> Flags.Attack:
  Flags.Attack{Pace.Rate{3n, 1500000000n}, Nat.mul(90n, 1000000000n), "t.txt", "http", "o.csv", "my attack", 4n, Some{9n}, Some{250000000n},
    [Hdr.Header{"X-A", ["1", "a b"]}, Hdr.Header{"x-b", ["2"]}], Some{"body.txt"}, False{}, Some{512n}, None{}, "json"}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(a([]))
    IO.print(a(["-rate=100/1s", "-duration", "2s", "-header", "A: 1", "-header", "B: 2", "-keepalive=false", "-encoding", "json"]))
    IO.print(a(["-http2"]))
    IO.print(a(["--http2=false"]))
    IO.print(a(["-max-connections", "5"]))
    IO.print(a(["-foo"]))
    IO.print(a(["-rate=infinity"]))
    IO.print(a(["-rate=0"]))
    IO.print(a(["-rate=0", "-max-workers=5"]))
    IO.print(a(["-rate", "abc"]))
    IO.print(a(["-rate", "5/x"]))
    IO.print(a(["--rate", "7/m"]))
    IO.print(a(["-duration=5"]))
    IO.print(a(["-header", "A: 1", "-header", "A:2", "-header", " B :  x y "]))
    IO.print(a(["-header", "nocolon"]))
    IO.print(a(["-header=A:"]))
    IO.print(a(["-workers"]))
    IO.print(a(["-workers=x"]))
    IO.print(a(["-keepalive", "false"]))
    IO.print(a(["-keepalive=maybe"]))
    IO.print(a(["-keepalive=0"]))
    IO.print(a(["-max-body=1KB", "-redirects=-1", "-timeout=1.5s", "-body", "b.txt", "-name", "x", "-targets=t.txt", "-output=o.bin", "-workers=3", "-max-workers", "7"]))
    IO.print(a(["-max-body=-1", "-redirects", "0"]))
    IO.print(a(["-max-body=zz"]))
    IO.print(a(["-redirects=x"]))
    IO.print(a(["-format=json"]))
    IO.print(a(["-format=xml"]))
    IO.print(a(["-encoding=gob"]))
    IO.print(a(["---x"]))
    IO.print(a(["-=x"]))
    IO.print(a(["-h"]))
    IO.print(a(["x", "-foo"]))
    IO.print(a(["--", "-foo"]))
    IO.print(a(["-", "-foo"]))
    IO.print(a(["-name=a=b", "-body="]))
    IO.print(attack(trip()))
    IO.print(a(args_of(trip())))
    IO.print(r([]))
    IO.print(r(["a.csv", "b.csv"]))
    IO.print(r(["-type=json", "-output=o.json", "f"]))
    IO.print(r(["-type=json", "-buckets=[1ms, 10ms]", "f"]))
    IO.print(r(["-type=json", "-buckets", "[0,2s]"]))
    IO.print(r(["-type=hist[1ms,10ms]"]))
    IO.print(r(["-type", "hist", "-buckets=[0,1ms]", "x"]))
    IO.print(r(["-type=hist[1ms]", "-buckets=[5ms]"]))
    IO.print(r(["-type=hist"]))
    IO.print(r(["-type=hist[]"]))
    IO.print(r(["-type=hist[1ms,x]"]))
    IO.print(r(["-type=hist1ms"]))
    IO.print(r(["-type=hdrplot"]))
    IO.print(r(["-type=plot"]))
    IO.print(r(["-type=xml"]))
    IO.print(r(["-type=xmlx"]))
    IO.print(r(["-every=1s", "f"]))
    IO.print(r(["-every", "1s"]))
    IO.print(r(["-type", "json", "--", "-f"]))
    IO.print(r(["-foo"]))
    IO.print(r(["-output"]))
    IO.print(r(["f", "-type=json"]))
#|rate=50/1000000000 duration=0 targets=stdin format=http output=stdout name= workers=10 max-workers=- timeout=- headers= body=- keepalive=true max-body=- redirects=10 encoding=csv
#|rate=100/1000000000 duration=2000000000 targets=stdin format=http output=stdout name= workers=10 max-workers=- timeout=- headers= A=[1] B=[2] body=- keepalive=false max-body=- redirects=10 encoding=json
#|error: flag not supported in the Bend port: -http2
#|error: flag not supported in the Bend port: -http2
#|error: flag not supported in the Bend port: -max-connections
#|error: flag provided but not defined: -foo
#|rate=50/1000000000 duration=0 targets=stdin format=http output=stdout name= workers=10 max-workers=- timeout=- headers= body=- keepalive=true max-body=- redirects=10 encoding=csv
#|error: -rate=0 requires setting -max-workers
#|rate=0/0 duration=0 targets=stdin format=http output=stdout name= workers=10 max-workers=5 timeout=- headers= body=- keepalive=true max-body=- redirects=10 encoding=csv
#|error: invalid value "abc" for flag -rate: strconv.Atoi: parsing "abc": invalid syntax
#|error: invalid value "5/x" for flag -rate: time: invalid duration "x"
#|rate=7/60000000000 duration=0 targets=stdin format=http output=stdout name= workers=10 max-workers=- timeout=- headers= body=- keepalive=true max-body=- redirects=10 encoding=csv
#|error: invalid value "5" for flag -duration: parse error
#|rate=50/1000000000 duration=0 targets=stdin format=http output=stdout name= workers=10 max-workers=- timeout=- headers= A=[1][2] B=[x y] body=- keepalive=true max-body=- redirects=10 encoding=csv
#|error: invalid value "nocolon" for flag -header: header 'nocolon' has a wrong format
#|error: invalid value "A:" for flag -header: header 'A:' has a wrong format
#|error: flag needs an argument: -workers
#|error: invalid value "x" for flag -workers: parse error
#|rate=50/1000000000 duration=0 targets=stdin format=http output=stdout name= workers=10 max-workers=- timeout=- headers= body=- keepalive=true max-body=- redirects=10 encoding=csv
#|error: invalid boolean value "maybe" for -keepalive: parse error
#|rate=50/1000000000 duration=0 targets=stdin format=http output=stdout name= workers=10 max-workers=- timeout=- headers= body=- keepalive=false max-body=- redirects=10 encoding=csv
#|rate=50/1000000000 duration=0 targets=t.txt format=http output=o.bin name=x workers=3 max-workers=7 timeout=1500000000 headers= body=b.txt keepalive=true max-body=1024 redirects=- encoding=csv
#|rate=50/1000000000 duration=0 targets=stdin format=http output=stdout name= workers=10 max-workers=- timeout=- headers= body=- keepalive=true max-body=- redirects=0 encoding=csv
#|error: invalid value "zz" for flag -max-body: strconv.UnmarshalText: parsing "zz": invalid syntax
#|error: invalid value "x" for flag -redirects: parse error
#|error: target format not supported in the Bend port: json
#|error: format "xml" isn't one of [http, json]
#|error: invalid value "gob" for flag -encoding: want csv or json (gob is not supported in the Bend port)
#|error: bad flag syntax: ---x
#|error: bad flag syntax: -=x
#|error: flag: help requested
#|rate=50/1000000000 duration=0 targets=stdin format=http output=stdout name= workers=10 max-workers=- timeout=- headers= body=- keepalive=true max-body=- redirects=10 encoding=csv
#|rate=50/1000000000 duration=0 targets=stdin format=http output=stdout name= workers=10 max-workers=- timeout=- headers= body=- keepalive=true max-body=- redirects=10 encoding=csv
#|rate=50/1000000000 duration=0 targets=stdin format=http output=stdout name= workers=10 max-workers=- timeout=- headers= body=- keepalive=true max-body=- redirects=10 encoding=csv
#|rate=50/1000000000 duration=0 targets=stdin format=http output=stdout name=a=b workers=10 max-workers=- timeout=- headers= body=- keepalive=true max-body=- redirects=10 encoding=csv
#|rate=3/1500000000 duration=90000000000 targets=t.txt format=http output=o.csv name=my attack workers=4 max-workers=9 timeout=250000000 headers= X-A=[1][a b] x-b=[2] body=body.txt keepalive=false max-body=512 redirects=- encoding=json
#|rate=3/1500000000 duration=90000000000 targets=t.txt format=http output=o.csv name=my attack workers=4 max-workers=9 timeout=250000000 headers= X-A=[1][a b] x-b=[2] body=body.txt keepalive=false max-body=512 redirects=- encoding=json
#|text output=stdout files=
#|text output=stdout files=[a.csv][b.csv]
#|json[ ] output=o.json files=[f]
#|json[ 0 1000000 10000000 ] output=stdout files=[f]
#|json[ 0 2000000000 ] output=stdout files=
#|hist[ 0 1000000 10000000 ] output=stdout files=
#|hist[ 0 1000000 ] output=stdout files=[x]
#|hist[ 0 5000000 ] output=stdout files=
#|error: bad buckets: ''
#|error: time: invalid duration ""
#|error: time: invalid duration "x"
#|error: bad buckets: 1ms
#|error: report type not supported in the Bend port: hdrplot
#|error: The plot reporter has been deprecated and succeeded by the vegeta plot command
#|error: invalid report type: xml
#|error: unknown report type: "xmlx"
#|error: flag not supported in the Bend port: -every
#|error: flag not supported in the Bend port: -every
#|json[ ] output=stdout files=[-f]
#|error: flag provided but not defined: -foo
#|error: flag needs an argument: -output
#|text output=stdout files=[f][-type=json]
