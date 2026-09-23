# vegeta, in Bend: `attack` and `report`. Arguments arrive as code points
# and are turned into UTF-8 bytes, as every String in the port is bytes.
import Base
import ./lib/sys.bend as Sys
import ./lib/text.bend as Text
import ./attack.bend as Attack
import ./report.bend as Report

def usage() -> String:
  "Usage: vegeta [global flags] <command> [command flags]\n\nCommands:\n  attack  Hit targets\n  report  Report the results\n"

def bytes_of(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Con{Text.utf8(x), bytes_of(rest)}

def unknown(+cmd: String) -> IO(Unit):
  do IO<Unit>:
    Sys.Out.write_err("vegeta: unknown command " ++ cmd ++ "\n" ++ usage())
    IO.die(Unit, 1, "")

def dispatch.report(yes: Bool, +cmd: String, rest: List<&2, String>) -> IO(Unit):
  match yes:
    case True{}:
      Report.run(rest)
    case False{}:
      unknown(cmd)

def dispatch.attack(yes: Bool, +cmd: String, rest: List<&2, String>) -> IO(Unit):
  match yes:
    case True{}:
      Attack.run(rest)
    case False{}:
      dispatch.report(String.eq(cmd, "report"), cmd, rest)

def dispatch(args: List<&2, String>) -> IO(Unit):
  match args:
    case Nil{}:
      do IO<Unit>:
        Sys.Out.write_err(usage())
        IO.die(Unit, 1, "")
    case Con{+cmd, rest}:
      dispatch.attack(String.eq(cmd, "attack"), cmd, rest)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    dispatch(bytes_of(args))
