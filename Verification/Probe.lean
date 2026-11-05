import Verification.Model
open Verification

def main (args : List String) : IO Unit := do
  let op := args[0]!
  let a := args[1]!.toNat!
  let b := args[2]!.toNat!
  let z := args[3]!.toNat! != 0
  let s : State := { regs := fun r => if r = .rdx then b else if r = .rdi then 1024 else a, zf := z, mem := fun _ => ⟨b%256, Nat.mod_lt _ (by decide)⟩, readable := fun _ => true, pc := 5, status := .running, reads := [] }
  let instr := match op with
    | "xor" => Op.xor .eax .eax | "test" => .test .rax .rax
    | "movzx" => .movzx .eax (.bytePtr .rdi) | "add" => .add .rax .rdx
    | "inc" => .inc .rax | "dec" => .dec .rax
    | "jz" => .jz 17 | "jnz" => .jnz 17 | _ => .ret
  let t := stepOp instr s
  if op == "ret" then
    IO.println (t.regs .rsp - s.regs .rsp)
    return
  IO.println s!"{t.regs .rax} {if t.zf then 1 else 0} {t.pc}"
