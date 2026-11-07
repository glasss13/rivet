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
  !source.toList.isEmpty && source.toList.all (fun character =>
    character.isAlpha || character.isDigit || character == '_' || character == '.') &&
    !(source.toList.head!).isDigit
-- GNU as reserves the current-location symbol and these Intel expression
-- operators and type names, regardless of case or existing label declarations.
def assemblyIdentifier (source : String) : Bool :=
  identifier source && !([
    ".", "and", "eq", "ge", "gt", "le", "lt", "mod", "ne", "not", "offset", "or",
    "shl", "short", "shr", "xor", "byte", "word", "dword", "fword", "qword",
    "mmword", "tbyte", "oword", "xmmword", "ymmword", "zmmword", "near", "far",
    "ptr"] : List String).contains (String.ofList (source.toList.map Char.toLower))
abbrev Labels := List (String × Nat)
def target (labels : Labels) (labelName : String) : Except String Nat := do
  unless assemblyIdentifier labelName do throw "invalid or reserved label reference"
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

def parseRegister16 : String → Except String Reg16
  | "ax" => .ok .ax
  | "bx" => .ok .bx
  | "cx" => .ok .cx
  | "dx" => .ok .dx
  | "si" => .ok .si
  | "di" => .ok .di
  | "bp" => .ok .bp
  | "sp" => .ok .sp
  | "r8w" => .ok .r8w
  | "r9w" => .ok .r9w
  | "r10w" => .ok .r10w
  | "r11w" => .ok .r11w
  | "r12w" => .ok .r12w
  | "r13w" => .ok .r13w
  | "r14w" => .ok .r14w
  | "r15w" => .ok .r15w
  | name => .error ("unsupported register: " ++ name)

def joinTokens (parts : List String) : String :=
  String.ofList (List.intercalate [' '] (parts.map String.toList))

def startsInteger (source : String) : Bool :=
  source.toList.head?.any (fun character => character.isDigit || character == '-' || character == '+')

/-- Decimal or hexadecimal integer literals, with an optional sign. -/
def parseInteger (source : String) : Except String Int := do
  let (negative, characters) := match source.toList with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | rest => (false, rest)
  if characters.head? == some '0' && characters.length > 1 &&
      characters[1]? != some 'x' && characters[1]? != some 'X' then
    throw "use decimal without leading zeroes, or hexadecimal with 0x"
  let (radix, digits) := match characters with
    | '0' :: 'x' :: rest | '0' :: 'X' :: rest => (16, rest)
    | rest => (10, rest)
  if digits.isEmpty then throw "expected integer"
  let value ← digits.foldlM (fun value character => do
    let digit := if '0' ≤ character && character ≤ '9' then character.toNat - '0'.toNat
      else if 'a' ≤ character.toLower && character.toLower ≤ 'f' then character.toLower.toNat - 'a'.toNat + 10
      else radix
    if digit ≥ radix then throw ("invalid integer: " ++ source)
    pure (value * radix + digit)) 0
  return if negative then -(Int.ofNat value) else Int.ofNat value

def parseScale : Int → Except String Scale
  | 1 => .ok .one | 2 => .ok .two | 4 => .ok .four | 8 => .ok .eight
  | _ => .error "address scale must be 1, 2, 4, or 8"

def parseAddress (source : String) : Except String Address := do
  let words := (splitChars ' ' (source.toList.map (fun character =>
    if character == '\t' then ' ' else character))).filter (!·.isEmpty)
  for (left, right) in words.zip (words.drop 1) do
    let isName := fun character : Char => character.isAlpha || character.isDigit
    if left.getLast?.any isName && right.head?.any isName then
      throw "whitespace inside an address term"
  let compact := String.ofList words.flatten
  let inner ← match compact.toList with
    | '[' :: rest => match rest.reverse with
      | ']' :: characters => pure (String.ofList characters.reverse)
      | _ => throw "expected [address]"
    | _ => throw "expected [address]"
  let expanded := inner.toList.flatMap (fun character => if character == '-' then ['+', '-'] else [character])
  let groups := (splitChars '+' expanded).map String.ofList
  let terms := if inner.toList.head? == some '-' then groups.drop 1 else groups
  let address ← terms.foldlM (fun (address : Address) term => do
    if term.toList.isEmpty then throw "empty address term"
    match (splitChars '*' term.toList).map String.ofList with
    | [left, right] =>
      if address.index.isSome then throw "multiple index registers"
      let (register, scale) ← if startsInteger left then
        pure (← parseRegister right, ← parseScale (← parseInteger left))
      else pure (← parseRegister left, ← parseScale (← parseInteger right))
      if register == .rsp then throw "rsp cannot be an index register"
      return { address with index := some register, scale }
    | [single] =>
      if startsInteger single then
        return { address with displacement := address.displacement + (← parseInteger single) }
      let register ← parseRegister single
      if address.base.isNone then return { address with base := some register }
      if address.index.isSome then throw "too many address registers"
      if register == .rsp then
        return { address with base := some register, index := address.base }
      return { address with index := some register }
    | _ => throw "invalid address term") {}
  if address.index == some .rsp then throw "rsp cannot be an index register"
  unless -(2^31) ≤ address.displacement && address.displacement < 2^31 do
    throw "address displacement exceeds signed 32 bits"
  return address

def parseOperand (source : String) : Except String Operand := do
  let source := String.ofList ((clean source).toList.map Char.toLower)
  match tokens source with
  | size :: "ptr" :: address =>
    let width ← match size with
      | "byte" => pure Width.byte | "word" => pure Width.word
      | "dword" => pure Width.dword | "qword" => pure Width.qword
      | _ => throw "unsupported memory width"
    return .memory width (← parseAddress (joinTokens address))
  | [name] =>
    if startsInteger name then
      return .immediate (← parseInteger name)
    if let .ok register := parseRegister name then return .reg64 register
    if let .ok register := parseRegister32 name then return .reg32 register
    if let .ok register := parseRegister16 name then return .reg16 register
    if let .ok register := parseRegister8 name then return .reg8 register
    throw ("unsupported operand: " ++ name)
  | _ => throw "expected register, integer, or sized memory operand"

def parseMove (operands : String) : Except String Op := do
  match (splitChars ',' operands.toList).map String.ofList with
  | [destination, source] =>
    let destination ← parseOperand destination
    let source ← parseOperand source
    unless validMove destination source do throw "invalid MOV operands or immediate"
    return .mov destination source
  | _ => throw "MOV requires two operands"

def parseCondition : String → Except String Condition
  | "e" | "z" => .ok .equal
  | "ne" | "nz" => .ok .notEqual
  | "b" => .ok .below
  | "ae" => .ok .aboveOrEqual
  | "be" => .ok .belowOrEqual
  | "a" => .ok .above
  | "s" => .ok .sign
  | suffix => .error ("unsupported condition: " ++ suffix)

def parseOp (labels : Labels) (source : String) : Except String Op := do
  let parts := tokens source
  let mnemonic := parts.headD ""
  let operation : Option BinaryOp := match mnemonic with
    | "add" => some .add | "sub" => some .sub | "cmp" => some .cmp | "test" => some .test
    | "sbb" => some .sbb
    | "and" => some .and | "or" => some .or | "xor" => some .xor | _ => none
  if let some operation := operation then
    match (splitChars ',' (joinTokens parts.tail).toList).map String.ofList with
    | [destination, source] =>
      let destination ← parseOperand destination
      let source ← parseOperand source
      unless validBinary operation destination source do throw "invalid scalar operands or immediate"
      return .binary operation destination source
    | _ => throw "scalar instruction requires two operands"
  else if mnemonic == "imul" then
    let operands := (splitChars ',' (joinTokens parts.tail).toList).map String.ofList
    let (destination, source, immediate) ← match operands with
      | [destination, source] => pure (destination, source, none)
      | [destination, source, immediate] => pure (destination, source, some (← parseInteger (clean immediate)))
      | _ => throw "IMUL requires two operands or three with an immediate multiplier"
    let destination ← parseOperand destination
    let source ← parseOperand source
    let (source, immediate) := match source, immediate with
      | .immediate value, none => (destination, some value)
      | _, _ => (source, immediate)
    unless validImul destination source immediate do throw "invalid IMUL operands or immediate"
    return .imul destination source immediate
  else if mnemonic.toList.take 4 == ['c', 'm', 'o', 'v'] then
    let condition ← parseCondition (String.ofList (mnemonic.toList.drop 4))
    match (splitChars ',' (joinTokens parts.tail).toList).map String.ofList with
    | [destination, source] =>
      let destination ← parseOperand destination
      let source ← parseOperand source
      unless validConditionalMove destination source do throw "CMOV requires a 16/32/64-bit register and matching register or memory source"
      return .cmovcc condition destination source
    | _ => throw "CMOV requires two operands"
  else if mnemonic.toList.take 3 == ['s', 'e', 't'] then
    let condition ← parseCondition (String.ofList (mnemonic.toList.drop 3))
    let destination ← parseOperand (joinTokens parts.tail)
    unless destination.width == some .byte do throw "SET requires a byte register or memory destination"
    return .setcc condition destination
  else if mnemonic.toList.head? == some 'j' then
    match parts with
    | [_, labelName] =>
      let destination ← target labels labelName
      if mnemonic == "jmp" then return .jmp destination
      return .jcc (← parseCondition (String.ofList (mnemonic.toList.drop 1))) destination
    | _ => throw "jump requires a label"
  else match parts with
  | "lea" :: destination :: "," :: address =>
    return .lea (← parseRegister destination) (← parseAddress (joinTokens address))
  | "movzx" :: destination :: "," :: source =>
    let source ← parseOperand (joinTokens source)
    unless source.width == some .byte || source.width == some .word do
      throw "MOVZX requires a byte or word register or memory source"
    return .movzx (← parseRegister32 destination) source
  | "movsxd" :: destination :: "," :: source =>
    let source ← parseOperand (joinTokens source)
    unless source.width == some .dword do
      throw "MOVSXD requires a dword register or memory source"
    return .movsxd (← parseRegister destination) source
  | "mov" :: operands => parseMove (joinTokens operands)
  | "movabs" :: operands =>
    match ← parseMove (joinTokens operands) with
    | .mov (.reg64 destination) (.immediate value) => return .mov (.reg64 destination) (.immediate value)
    | _ => throw "MOVABS requires a 64-bit register and immediate"
  | "not" :: operands =>
    let destination ← parseOperand (joinTokens operands)
    unless destination.width.isSome do throw "NOT requires a register or sized memory operand"
    return .not destination
  | ["inc", destination] => return .inc (← parseRegister destination)
  | ["dec", destination] => return .dec (← parseRegister destination)
  | ["push", source] => return .push (← parseRegister source)
  | ["pop", destination] => return .pop (← parseRegister destination)
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
  if lineSource.toList.getLast? == some ':' then
    let name := String.ofList (lineSource.toList.reverse.drop 1).reverse
    if !assemblyIdentifier name || (scan.labels.lookup name).isSome then
      throw "invalid, reserved, or duplicate label"
    if !scan.entrySeen then
      if scan.functionName != some name then throw "first label must name the function"
    return { scan with labels := scan.labels ++ [(name, scan.count)], entrySeen := true }
  if lineSource.toList.head? == some '.' then
    match tokens lineSource with
    | [".globl", name] =>
      if scan.functionName.isSome || !assemblyIdentifier name || scan.count != 0 || !scan.labels.isEmpty then
        throw "expected one initial .globl declaration"
      return { scan with functionName := some name }
    | _ => throw "unsupported directive"
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
      | .jmp targetIndex | .jcc _ targetIndex => targetIndex ≥ program.length
      | _ => false) then throw "branch target outside function"
  return program
end Rivet
