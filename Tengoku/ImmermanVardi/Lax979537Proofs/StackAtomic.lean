import Tengoku.ImmermanVardi.Lax979537Proofs.StackBoolean
import Tengoku.ImmermanVardi.Lax979537Proofs.StackCheckBound

namespace Lax979537Proofs.StackAtomic

open StackProgram StackTransfer StackBoolean

variable {K Aux : Type} [DecidableEq K]

def less (left right copyLeft copyRight tmp : K) : EvalProgram K Aux :=
  .seq (answer true) (StackCheckBound.checkBound left right copyLeft copyRight tmp)

def equal (left right copyLeft copyRight tmp savedPort : K) : EvalProgram K Aux :=
  .seq (binary savedPort (· || ·) (less left right copyLeft copyRight tmp)
    (less right left copyLeft copyRight tmp)) negate

theorem not_less_both (a b : Nat) : (!(decide (a < b) || decide (b < a))) = decide (a = b) := by
  by_cases h : a = b
  · subst b; simp
  · rcases lt_or_gt_of_ne h with hlt | hlt <;> simp [h, hlt]

/-- Port equality is decided when compiling the fixed syntax, so repeated
variables such as x = x require no dynamic counter comparison. -/
def equalValue (left right copyLeft copyRight tmp savedPort : K) : EvalProgram K Aux :=
  if left = right then answer true else equal left right copyLeft copyRight tmp savedPort

def lessValue (left right copyLeft copyRight tmp : K) : EvalProgram K Aux :=
  if left = right then answer false else less left right copyLeft copyRight tmp

end Lax979537Proofs.StackAtomic
