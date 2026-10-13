/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Circuits.BarringtonConverse.Internal

/-!
# The converse direction of Barrington's theorem

Polynomial-length width-`5` permutation branching programs are evaluated by
balanced Boolean formulas of logarithmic depth. Together with the existing
formula-to-program construction, this proves the full nonuniform Barrington
equivalence under the library's total-assignment family convention.

## Main results

- `BP.eval_reachesFormula` -- correctness of balanced state-to-state evaluation
- `BP.depth_reachesFormula_le` -- depth at most `(w + 1) * d + 1`
- `BP.eval_decisionFormula_eq_true` -- the decision formula detects movement
- `BP.depth_decisionFormula_le` -- logarithmic depth in program length
- `BP.vars_decisionFormula_lt` -- conversion preserves an arity bound
- `BPFamily.toFormulaFamily_logDepth` -- polynomial-length families give
  logarithmic-depth formula families
- `barrington_equivalence_onTotalAssignments` -- the explicitly named
  total-assignment equivalence
-/

public section

namespace Complexity

/-- Taking a binary ceiling logarithm of a polynomial bound yields an affine
bound in `log₂ n`. This arithmetic bridge is shared by total-assignment and
fixed-arity Barrington converses.
@isnad1 id=le.1h4v.s6.7e109b1d8c1e from=translated src=- shape=f1e9344d vocab=aa5a54b4
-/
theorem clog_le_of_polynomial_bound
    (C p n m : ℕ) (h : m ≤ C * (n + 1) ^ p) :
    Nat.clog 2 m ≤ Nat.clog 2 C + p * (Nat.log 2 n + 1) :=
  clog_le_of_polynomial_bound_internal C p n m h

namespace BP

/-- The balanced state-to-state formula correctly evaluates every program of
length at most `2 ^ d`.
@isnad1 id=iff.1h6v.s6.801ffccb8ecc from=translated src=- shape=7f2287b7 vocab=a44654a6
-/
theorem eval_reachesFormula {w : ℕ} (α : ℕ → Bool) (d : ℕ) (p : BP w)
    (x y : Fin w) (h : p.length ≤ 2 ^ d) :
    BoolFormula.eval α (reachesFormula d p x y) = true ↔ BP.eval α p x = y :=
  eval_reachesFormula_internal α d p x y h

/-- Balanced state-to-state evaluation has depth at most
`(w + 1) * d + 1`.
@isnad1 id=le.0h5v.s5.f73b8fd3e294 from=translated src=- shape=cf1ff78b vocab=bda9b828
-/
theorem depth_reachesFormula_le {w : ℕ} (d : ℕ) (p : BP w)
    (x y : Fin w) :
    (reachesFormula d p x y).depth ≤ (w + 1) * d + 1 :=
  depth_reachesFormula_le_internal d p x y

/-- The canonical decision formula is true exactly when the program moves its
designated query point.
@isnad1 id=iff.0h4v.s5.baefba7db7a9 from=translated src=- shape=b966bbd4 vocab=cb1b3a64
-/
theorem eval_decisionFormula_eq_true {w : ℕ} (α : ℕ → Bool)
    (p : BP w) (x : Fin w) :
    BoolFormula.eval α (decisionFormula p x) = true ↔ BP.eval α p x ≠ x :=
  eval_decisionFormula_eq_true_internal α p x

/-- The canonical decision formula has logarithmic depth in program length.
@isnad1 id=le.0h3v.s5.7197fac98d63 from=translated src=- shape=08335116 vocab=51f28efd
-/
theorem depth_decisionFormula_le {w : ℕ} (p : BP w) (x : Fin w) :
    (decisionFormula p x).depth ≤ (w + 1) * Nat.clog 2 p.length + 2 :=
  depth_decisionFormula_le_internal p x

/-- The balanced decision formula introduces no new input variables.
@isnad1 id=lt.2h5v.s5.3101b2b6caa4 from=translated src=- shape=3c6d4cb2 vocab=d9054274
-/
theorem vars_decisionFormula_lt {w n : ℕ}
    (p : BP w) (x : Fin w)
    (hvars : ∀ instruction ∈ p, instruction.var < n) :
    ∀ index ∈ (decisionFormula p x).vars, index < n :=
  vars_decisionFormula_lt_internal p x hvars

end BP

namespace BPFamily

/-- The balanced formula family computes every function family decided by the
source branching-program family.
@isnad1 id=computes.1h4v.s4.d62ea557c60e from=translated src=- shape=577b166b vocab=67b0c9d0
-/
theorem toFormulaFamily_computes {w : ℕ} {R : BPFamily w}
    {x : ℕ → Fin w} {f : ℕ → (ℕ → Bool) → Bool}
    (h : R.DecidesOnTotalAssignments x f) :
    (R.toFormulaFamily x).ComputesOnTotalAssignments f :=
  toFormulaFamily_computes_internal h

/-- A polynomial-length width-`5` branching-program family becomes a
logarithmic-depth Boolean-formula family.
@isnad1 id=logdepth.1h2v.s5.419bba841077 from=translated src=- shape=1c8c7a56 vocab=69933211
-/
theorem toFormulaFamily_logDepth {R : BPFamily 5} {x : ℕ → Fin 5}
    (h : R.PolynomialLength) :
    (R.toFormulaFamily x).LogDepth :=
  toFormulaFamily_logDepth_internal h

end BPFamily

/-- Every logarithmic-depth total-assignment formula family has a
polynomial-length width-`5` permutation branching-program family.
@isnad1 id=le.0h0v.s4.53bae9992f1d from=translated src=- shape=d8d79b04 vocab=f48e34ac
-/
theorem formulaNC1OnTotalAssignments_subset_width5BPOnTotalAssignments :
    FormulaNC1OnTotalAssignments ⊆ Width5BPOnTotalAssignments :=
  formulaNC1OnTotalAssignments_subset_width5BPOnTotalAssignments_internal

/-- Every polynomial-length width-`5` total-assignment branching-program
family has an equivalent logarithmic-depth formula family.
@isnad1 id=le.0h0v.s4.814c0a65e1e1 from=translated src=- shape=d8d79b04 vocab=f48e34ac
-/
theorem width5BPOnTotalAssignments_subset_formulaNC1OnTotalAssignments :
    Width5BPOnTotalAssignments ⊆ FormulaNC1OnTotalAssignments :=
  width5BPOnTotalAssignments_subset_formulaNC1OnTotalAssignments_internal

/-- **Barrington's theorem on total assignments.** Logarithmic-depth Boolean
formula families are exactly polynomial-length width-`5` permutation
branching-program families over assignments `ℕ → Bool`.

This theorem does not claim that the length-`n` objects only read the first
`n` variables; the typed fixed-arity theorem is a separate statement.
@isnad1 id=eq.0h0v.s3.fae36633834a from=translated src=- shape=d8d79b04 vocab=1c97eff4
-/
theorem barrington_equivalence_onTotalAssignments :
    FormulaNC1OnTotalAssignments = Width5BPOnTotalAssignments :=
  Set.Subset.antisymm
    formulaNC1OnTotalAssignments_subset_width5BPOnTotalAssignments
    width5BPOnTotalAssignments_subset_formulaNC1OnTotalAssignments

end Complexity
