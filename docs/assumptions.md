# Assumptions and trust boundary

The success claim is conditional: under `Preconditions`, the exact certified assembly always returns the exact byte sum and obeys its memory-access contract in the shared model. Native correspondence relies on the reviewed interpretation of this subset and the platform assumptions below. Machine code and the assembler are not verified.

Trusted foundations:

- Lean 4.30.0, its kernel and logical infrastructure.
- The small shared reference parser and execution definitions, including their interpretation of the supported Intel syntax and x86 operations.
- GNU assembler correctly assembling the accepted source inside the fixed wrapper; the linker and loader place that function correctly.
- The processor implements the modeled instruction behavior. Ordinary readable memory accesses succeed, and the caller supplies a valid continuation address. There are no asynchronous interference, concurrency, signals, or hardware failures within the modeled execution.
- The caller establishes the input, memory, stack and ABI conditions. The model stops when RET transfers control to the supplied address; it does not prove the caller's continuation correct.

Caller conditions (`Preconditions`):

- Entry is instruction zero with running status. RDI is the input address, RSI the length, and the length is at most 4096.
- All register values are canonical natural-number encodings of 64-bit words: `0 <= value < 2^64`. Other registers and ZF are arbitrary. `Registers64` formalizes this representation, and `run_registers64` proves preservation. Register writes explicitly reduce modulo 2^64; the supported 32-bit writes replace the entire register with a zero-extended result.
- Every byte in the buffer is readable. `address + length < 2^64` ensures that the one-past-buffer pointer reached by the final increment does not wrap. For length zero, readability is vacuous.
- The eight bytes starting at RSP are readable, do not cross the address-space boundary, and are disjoint from the buffer. The return address is their little-endian value. RSP becomes `(old RSP + 8) mod 2^64`, including the boundary case.
- Memory and its readability map remain fixed. Memory bytes have type `Fin 256`. Architectural mapping/canonical-address requirements are included in the interpretation of readable memory and a valid return continuation; page tables and exception delivery are outside this model.

The instruction pointer is an index, justified by excluding code-address inspection, self-modification, indirect control flow and external calls. Reading missing code or unreadable memory faults explicitly. Rejected source has no program semantics. ZF is the only modeled flag; no accepted instruction or specification observes any omitted flag. Timing, caches, speculation, syscalls, process startup, allocation, SIMD and floating point are outside the claim.

Successful reads append `(address, size)` events. A byte load appends one size-1 event. RET appends one size-8 event, after checking all eight bytes. Failed accesses fault before appending a successful read event. The out-of-buffer counterexample therefore identifies the offending PC and address and proves the resulting fault. There are no memory-write operations or write events. Existing trace history is allowed at entry; all guarantees about the invocation concern appended events. With an empty entry trace, every event is permitted.

Proof dependencies are printed by the build and independently audited by `scripts/verify.py`. The only allowed dependencies are Lean's standard `propext` (propositional extensionality), `Quot.sound` (quotient soundness), and `Classical.choice`. The parsing certificate and access-safety proofs use these standard dependencies; the functional proof also uses those three standard dependencies. There are no project-specific axioms, unfinished proofs, or native-evaluation proof shortcuts. The audit rejects them. Native test execution is evidence about the implementation, not a logical premise of the proofs.

The Lean and native tool versions are pinned in `lean-toolchain` and `tools.lock.json`; the latter records the tested Linux and Rust toolchains and is enforced by the acceptance script. These tools must be provisioned by the environment. There are no fetched project libraries or Rust crates. The Rust SHA-256 routine supplies provenance metadata only and is tested against known vectors and Python `hashlib`; it is outside the proof foundation. This repository does not promise bit-for-bit identical native binaries across differing OS/linker environments; deterministic generated Lean content is the reproducibility contract.
