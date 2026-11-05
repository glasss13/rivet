import Verification.Parser
open Verification

def main (args : List String) : IO UInt32 := do
  let source ← IO.FS.readFile args[0]!
  match parse source with
  | .ok _ => IO.println "accepted"; return 0
  | .error e => IO.println e; return 1
