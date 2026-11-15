module
public import Rivet.Tactics.Registers
-- `rivet_arith (only)? [facts]`: proves an arithmetic goal about words and numbers with `lia`, within
-- a fixed budget that `maxHeartbeats` does not change. The goal and the facts it uses are read back to
-- the block's start first, registers and memory. General (`∀`) facts in scope are hidden, and with
-- `only`, every other hypothesis. Its syntax is here; it is defined after the read-back.
public meta import Lean
public section
namespace Rivet
open Lean Meta Elab Tactic

meta def arithBudget : Nat := 20000

-- `lia`'s report without `grind`'s restatements of the goal's facts (asserted facts, equivalence
-- classes): on a large context they are nearly all of it.
meta partial def withoutRestatements : MessageData → MessageData
  | .trace data header children =>
    .trace data header <| (children.filter fun
      | .trace part _ _ => part.cls != `facts && part.cls != `eqc
      | _ => true).map withoutRestatements
  | .withContext context message => .withContext context (withoutRestatements message)
  | .withNamingContext naming message => .withNamingContext naming (withoutRestatements message)
  | .nest indent message => .nest indent (withoutRestatements message)
  | .group message => .group (withoutRestatements message)
  | .compose first second => .compose (withoutRestatements first) (withoutRestatements second)
  | .tagged tag message => .tagged tag (withoutRestatements message)
  | message => message

syntax (name := rivetArith) "rivet_arith" (&" only")? (" [" term,* "]")? : tactic

end Rivet
