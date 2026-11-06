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
def parseRegister : String → Except String Reg
  | "rax" => .ok .rax
  | "rbx" => .ok .rbx
  | "rcx" => .ok .rcx
  | "rdx" => .ok .rdx
  | "rsi" => .ok .rsi
  | "rdi" => .ok .rdi
  | "rbp" => .ok .rbp
  | "rsp" => .ok .rsp
  | "r8" => .ok .r8
  | "r9" => .ok .r9
  | "r10" => .ok .r10
  | "r11" => .ok .r11
  | "r12" => .ok .r12
  | "r13" => .ok .r13
  | "r14" => .ok .r14
  | "r15" => .ok .r15
  | name => .error ("unsupported register: " ++ name)

def parseRegister32 : String → Except String Reg32
  | "eax" => .ok .eax
  | "ebx" => .ok .ebx
  | "ecx" => .ok .ecx
  | "edx" => .ok .edx
  | "esi" => .ok .esi
  | "edi" => .ok .edi
  | "ebp" => .ok .ebp
  | "esp" => .ok .esp
  | "r8d" => .ok .r8d
  | "r9d" => .ok .r9d
  | "r10d" => .ok .r10d
  | "r11d" => .ok .r11d
  | "r12d" => .ok .r12d
  | "r13d" => .ok .r13d
  | "r14d" => .ok .r14d
  | "r15d" => .ok .r15d
  | name => .error ("unsupported register: " ++ name)

def parseRegister8 : String → Except String Reg8
  | "al" => .ok .al
  | "bl" => .ok .bl
  | "cl" => .ok .cl
  | "dl" => .ok .dl
  | "sil" => .ok .sil
  | "dil" => .ok .dil
  | "bpl" => .ok .bpl
  | "spl" => .ok .spl
  | "r8b" => .ok .r8b
  | "r9b" => .ok .r9b
  | "r10b" => .ok .r10b
  | "r11b" => .ok .r11b
  | "r12b" => .ok .r12b
  | "r13b" => .ok .r13b
  | "r14b" => .ok .r14b
  | "r15b" => .ok .r15b
  | name => .error ("unsupported register: " ++ name)

def parseMemory8 (source : String) : Except String Mem8 := do
  match source.toList with
  | '[' :: rest =>
    match rest.reverse with
    | ']' :: name => return ⟨← parseRegister (String.ofList name.reverse)⟩
    | _ => throw "expected [register]"
  | _ => throw "expected [register]"

def parseOp (labels : Labels) (source : String) : Except String Op := do
  match tokens source with
  | ["xor", destination, ",", operand] => return .xor (← parseRegister32 destination) (← parseRegister32 operand)
  | ["test", left, ",", right] => return .test (← parseRegister left) (← parseRegister right)
  | ["movzx", destination, ",", "BYTE", "PTR", memory] =>
    return .movzx (← parseRegister32 destination) (← parseMemory8 memory)
  | ["mov", "BYTE", "PTR", memory, ",", operand] =>
    return .store8 (← parseMemory8 memory) (← parseRegister8 operand)
  | ["mov", destination, ",", operand] => return .mov (← parseRegister destination) (← parseRegister operand)
  | ["cmp", left, ",", right] => return .cmp (← parseRegister left) (← parseRegister right)
  | ["add", destination, ",", operand] => return .add (← parseRegister destination) (← parseRegister operand)
  | ["inc", destination] => return .inc (← parseRegister destination)
  | ["dec", destination] => return .dec (← parseRegister destination)
  | ["jb", labelName] => return .jb (← target labels labelName)
  | ["jz", labelName] => return .jz (← target labels labelName)
  | ["jnz", labelName] => return .jnz (← target labels labelName)
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
      | .jb targetIndex | .jz targetIndex | .jnz targetIndex => targetIndex ≥ program.length
      | _ => false) then throw "branch target outside function"
  return program
end Rivet
