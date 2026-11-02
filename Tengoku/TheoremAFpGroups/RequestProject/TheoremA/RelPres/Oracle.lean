module

public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closure facts for Mathlib's `RecursiveIn`

The encoded relative presentations use Mathlib's natural-number relation `Nat.RecursiveIn O`
(on `ℕ →. ℕ`), kept under the local name `RecursiveIn`. We derive the closure properties
needed for relative presentations from its constructors:

* `RecursiveIn.of_partrec` — every oracle-free partial recursive function is recursive in `O`;
* `RecursiveIn.comp_primrec` — precomposition with a primitive recursive function;
* `RecursiveIn.guard` — the guarded call `pair a 0 ↦ 0`, `pair a 1 ↦ f a`, which does not
  evaluate `f` on the `0` branch (built from `prec`);
* `RecursiveIn.cond` — branching on a primitive recursive Boolean test **before** evaluating
  either branch, so that divergence of the unused branch is irrelevant.
-/

@[expose] public section

namespace TheoremA.RelPres

/-- The natural-number oracle relation used by the encoded relative presentations.-/
abbrev RecursiveIn (O : Set (ℕ →. ℕ)) (f : ℕ →. ℕ) : Prop := Nat.RecursiveIn O f

namespace RecursiveIn
export Nat.RecursiveIn (zero succ left right oracle pair comp prec rfind)
end RecursiveIn

open Nat.Partrec

variable {O : Set (ℕ →. ℕ)}

/-- Every partial recursive function is recursive relative to any set of oracles.-/
theorem RecursiveIn.of_partrec {f : ℕ →. ℕ} (hf : Nat.Partrec f) : RecursiveIn O f := by
  induction hf with
  | zero => exact RecursiveIn.zero
  | succ => exact RecursiveIn.succ
  | left => exact RecursiveIn.left
  | right => exact RecursiveIn.right
  | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
  | rfind _ ih => exact RecursiveIn.rfind ih

end TheoremA.RelPres
