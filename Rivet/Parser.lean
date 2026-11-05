module
public import Rivet.Syntax
@[expose] public section
deriving instance DecidableEq for Except
namespace Rivet

-- A deliberately closed Intel-syntax grammar; no assembler preprocessing.
def splitChars (separator : Char) (characters : List Char) : List (List Char) :=
  characters.foldr (fun character groups => if character = separator then [] :: groups else
    match groups with | [] => [[character]] | head::tail => (character::head)::tail) [[]]
def strip (characters : List Char) : List Char :=
  ((characters.dropWhile (fun character => character == ' ' || character == '\t' || character == '\r')).reverse.dropWhile
    (fun character => character == ' ' || character == '\t' || character == '\r')).reverse
def clean (source : String) : String := String.ofList (strip (source.toList.takeWhile (· != '#')))
def tokens (source : String) : List String :=
  let characters := source.toList.flatMap (fun character => if character == ',' then [' ', ',', ' ']
    else if character == '\t' then [' '] else [character])
  (splitChars ' ' characters).filterMap (fun characters => if characters.isEmpty then none else some (String.ofList characters))
def identifier (source : String) : Bool :=
  !source.toList.isEmpty && source.toList.all (fun character => character.isAlpha || character.isDigit || character == '_') &&
    !(source.toList.head!).isDigit
-- GNU as treats these Intel expression operators and type names specially,
-- regardless of case or whether a label with that spelling exists.
def assemblyIdentifier (source : String) : Bool :=
  identifier source && !([
    "and", "eq", "ge", "gt", "le", "lt", "mod", "ne", "not", "offset", "or",
    "shl", "short", "shr", "xor", "byte", "word", "dword", "fword", "qword",
    "mmword", "tbyte", "oword", "xmmword", "ymmword", "zmmword", "near", "far",
    "ptr"] : List String).contains (String.ofList (source.toList.map Char.toLower))
abbrev Labels := List (String × Nat)
def target (labels : Labels) (labelName : String) : Except String Nat :=
  match labels.lookup labelName with
  | some instructionIndex => .ok instructionIndex
  | none => .error ("unresolved label: " ++ labelName)
def parseOp (labels : Labels) (source : String) : Except String Op := do
  match tokens source with
  | ["xor", "eax", ",", "eax"] => pure (.xor .eax .eax)
  | ["test", "rsi", ",", "rsi"] => pure (.test .rsi .rsi)
  | ["movzx", "edx", ",", "BYTE", "PTR", "[rdi]"] => pure (.movzx .edx (.bytePtr .rdi))
  | ["add", "rax", ",", "rdx"] => pure (.add .rax .rdx)
  | ["inc", "rdi"] => pure (.inc .rdi)
  | ["dec", "rsi"] => pure (.dec .rsi)
  | ["jz", labelName] => pure (.jz (← target labels labelName))
  | ["jnz", labelName] => pure (.jnz (← target labels labelName))
  | ["ret"] => pure .ret
  | _ => .error ("unsupported instruction: " ++ source)

structure Scan where
  functionName : Option String := none
  labels : Labels := []
  lines : List (Nat × String) := []
  count : Nat := 0
  entrySeen : Bool := false

def scanLine (scan : Scan) (lineNumber : Nat) (rawLine : String) : Except String Scan := do
  let lineSource := clean rawLine
  if lineSource.toList.isEmpty then return scan
  if lineSource.toList.contains ';' then throw "semicolon is forbidden"
  if lineSource.toList.head? == some '.' then
    match tokens lineSource with
    | [".globl", name] =>
      if scan.functionName.isSome || !assemblyIdentifier name || scan.count != 0 || !scan.labels.isEmpty then
        throw "expected one initial .globl declaration"
      return { scan with functionName := some name }
    | _ => throw "unsupported directive"
  if lineSource.toList.getLast? == some ':' then
    let name := String.ofList (lineSource.toList.reverse.drop 1).reverse
    if !assemblyIdentifier name || (scan.labels.lookup name).isSome then
      throw "invalid, reserved, or duplicate label"
    if !scan.entrySeen then
      if scan.functionName != some name then throw "first label must name the function"
    return { scan with labels := scan.labels ++ [(name, scan.count)], entrySeen := true }
  if !scan.entrySeen then throw "instruction before function entry"
  return { scan with lines := scan.lines ++ [(lineNumber,lineSource)], count := scan.count+1 }

def parse (source : String) : Except String Program := do
  let numberedLines := ((splitChars '\n' source.toList).map String.ofList).zipIdx 1
  let scan ← numberedLines.foldlM (fun scan (lineSource,lineNumber) =>
    match scanLine scan lineNumber lineSource with
    | .ok scan => pure scan
    | .error message => .error ("line " ++ toString lineNumber ++ ": " ++ message)) {}
  if scan.count == 0 then throw "empty function"
  let program ← scan.lines.mapM (fun (lineNumber,lineSource) => do
    match parseOp scan.labels lineSource with
    | .ok operation => pure (Instruction.mk operation lineNumber)
    | .error message => .error ("line " ++ toString lineNumber ++ ": " ++ message))
  if program.any (fun instruction => match instruction.op with
      | .jz targetIndex | .jnz targetIndex => targetIndex ≥ program.length
      | _ => false) then throw "branch target outside function"
  return program
end Rivet
