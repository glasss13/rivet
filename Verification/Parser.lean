module
public import Verification.Syntax
@[expose] public section
deriving instance DecidableEq for Except
namespace Verification

-- A deliberately closed Intel-syntax grammar; no assembler preprocessing.
def splitChars (sep : Char) (cs : List Char) : List (List Char) :=
  cs.foldr (fun c acc => if c = sep then [] :: acc else
    match acc with | [] => [[c]] | h::t => (c::h)::t) [[]]
def strip (cs : List Char) : List Char :=
  ((cs.dropWhile (fun c => c == ' ' || c == '\t' || c == '\r')).reverse.dropWhile
    (fun c => c == ' ' || c == '\t' || c == '\r')).reverse
def clean (s : String) : String := String.ofList (strip (s.toList.takeWhile (· != '#')))
def tokens (s : String) : List String :=
  let cs := s.toList.flatMap (fun c => if c == ',' then [' ', ',', ' ']
    else if c == '\t' then [' '] else [c])
  (splitChars ' ' cs).filterMap (fun cs => if cs.isEmpty then none else some (String.ofList cs))
def identifier (s : String) : Bool :=
  !s.toList.isEmpty && s.toList.all (fun c => c.isAlpha || c.isDigit || c == '_') &&
    !(s.toList.head!).isDigit
-- GNU as treats these Intel expression operators and type names specially,
-- regardless of case or whether a label with that spelling exists.
def assemblyIdentifier (s : String) : Bool :=
  identifier s && !([
    "and", "eq", "ge", "gt", "le", "lt", "mod", "ne", "not", "offset", "or",
    "shl", "short", "shr", "xor", "byte", "word", "dword", "fword", "qword",
    "mmword", "tbyte", "oword", "xmmword", "ymmword", "zmmword", "near", "far",
    "ptr"] : List String).contains (String.ofList (s.toList.map Char.toLower))
abbrev Labels := List (String × Nat)
def target (ls : Labels) (s : String) : Except String Nat :=
  match ls.lookup s with
  | some n => .ok n
  | none => .error ("unresolved label: " ++ s)
def parseOp (ls : Labels) (s : String) : Except String Op := do
  match tokens s with
  | ["xor", "eax", ",", "eax"] => pure (.xor .eax .eax)
  | ["test", "rsi", ",", "rsi"] => pure (.test .rsi .rsi)
  | ["movzx", "edx", ",", "BYTE", "PTR", "[rdi]"] => pure (.movzx .edx (.bytePtr .rdi))
  | ["add", "rax", ",", "rdx"] => pure (.add .rax .rdx)
  | ["inc", "rdi"] => pure (.inc .rdi)
  | ["dec", "rsi"] => pure (.dec .rsi)
  | ["jz", l] => pure (.jz (← target ls l))
  | ["jnz", l] => pure (.jnz (← target ls l))
  | ["ret"] => pure .ret
  | _ => .error ("unsupported instruction: " ++ s)

structure Scan where
  functionName : Option String := none
  labels : Labels := []
  lines : List (Nat × String) := []
  count : Nat := 0
  entrySeen : Bool := false

def scanLine (st : Scan) (line : Nat) (raw : String) : Except String Scan := do
  let s := clean raw
  if s.toList.isEmpty then return st
  if s.toList.contains ';' then throw "semicolon is forbidden"
  if s.toList.head? == some '.' then
    match tokens s with
    | [".globl", name] =>
      if st.functionName.isSome || !assemblyIdentifier name || st.count != 0 || !st.labels.isEmpty then
        throw "expected one initial .globl declaration"
      return { st with functionName := some name }
    | _ => throw "unsupported directive"
  if s.toList.getLast? == some ':' then
    let name := String.ofList (s.toList.reverse.drop 1).reverse
    if !assemblyIdentifier name || (st.labels.lookup name).isSome then
      throw "invalid, reserved, or duplicate label"
    if !st.entrySeen then
      if st.functionName != some name then throw "first label must name the function"
    return { st with labels := st.labels ++ [(name, st.count)], entrySeen := true }
  if !st.entrySeen then throw "instruction before function entry"
  return { st with lines := st.lines ++ [(line,s)], count := st.count+1 }

def parse (source : String) : Except String Program := do
  let numbered := ((splitChars '\n' source.toList).map String.ofList).zipIdx 1
  let st ← numbered.foldlM (fun st (s,n) =>
    match scanLine st n s with
    | .ok st => pure st
    | .error e => .error ("line " ++ toString n ++ ": " ++ e)) {}
  if st.count == 0 then throw "empty function"
  let p ← st.lines.mapM (fun (n,s) => do
    match parseOp st.labels s with
    | .ok op => pure (Instruction.mk op n)
    | .error e => .error ("line " ++ toString n ++ ": " ++ e))
  if p.any (fun i => match i.op with
      | .jz t | .jnz t => t ≥ p.length
      | _ => false) then throw "branch target outside function"
  return p
end Verification
