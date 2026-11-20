/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Relational.PatternCounts
import Tengoku.RegularityLemmata.RegularityLemmata.Relational.UniformPatternCounts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms RegularityLemmata.DiagonalLoopRegression.induced_count_changes_on_loops` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms RegularityLemmata.DiagonalLoopRegression.injective_hom_count_ignores_added_loops` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms RegularityLemmata.DiagonalLoopRegression.hom_count_collision_difference` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms RegularityLemmata.DiagonalLoopRegression.edge_isSimplePattern` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms RegularityLemmata.DiagonalLoopRegression.hosts_not_diagonalAgreement` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms RegularityLemmata.DiagonalLoopRegression.restricted_hom_regression` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Named diagonal-loop regression

Adding only loops changes induced embeddings of a simple pattern, but not its
injective preservation-only count. These are the existing model-level counts,
not substitute counting definitions. The small finite instance is kernel-checked.
-/

namespace RegularityLemmata.DiagonalLoopRegression

open FirstOrder FiniteRelModel

def language : Language.{0, 0} := ⟨fun _ ↦ Empty, fun n ↦ if n = 2 then Unit else Empty⟩

instance : FiniteRelational language where
  arityBound := 2
  functionsEmpty := fun _ ↦ inferInstanceAs (IsEmpty Empty)
  relationsFintype := fun n ↦ by
    by_cases h : n = 2 <;> simp only [language, h, ite_true, ite_false] <;> infer_instance
  relationsDecidableEq := fun n ↦ by
    by_cases h : n = 2 <;> simp only [language, h, ite_true, ite_false] <;> infer_instance
  relationsEmptyAbove := fun n hn ↦ by
    have h : n ≠ 2 := by omega
    simp only [language, h, ite_false]
    infer_instance

/-- Complete binary relation, optionally including loops.-/
def complete (n : ℕ) (loops : Bool) : FiniteRelModel language (Fin n) where
  rel := fun {r} _ x ↦ match r, x with
    | 2, x => loops || decide (x 0 ≠ x 1)
    | _, _ => false

/-- The two models agree on every off-diagonal binary tuple.
@isnad1 id=iff.1h2v.s6.01dbe915b2c9 from=translated src=- shape=c6593174 vocab=8db88e31
-/
theorem offDiagonal_agreement (n : ℕ) (x : Fin 2 → Fin n) (hx : x 0 ≠ x 1) :
    (complete n false).Holds (n := 2) () x ↔ (complete n true).Holds (n := 2) () x := by
  change (false || decide (x 0 ≠ x 1)) = true ↔ (true || decide (x 0 ≠ x 1)) = true
  simp [hx]

/-- The irreflexive two-vertex pattern has six induced embeddings into the
irreflexive three-vertex complete relation, and none after only loops are added.
@isnad1 id=and.0h0v.s6.9a5c30670e62 from=translated src=- shape=1ac4f421 vocab=4dca9e6a
-/
theorem induced_count_changes_on_loops :
    inducedEmbeddingCount (complete 2 false) (complete 3 false) = 6 ∧
      inducedEmbeddingCount (complete 2 false) (complete 3 true) = 0 := by decide

/-- Injective homomorphisms do not test the pattern's absent loops.
@isnad1 id=and.0h0v.s6.8d9baa47c3fb from=translated src=- shape=1ac4f421 vocab=ee2a3dec
-/
theorem injective_hom_count_ignores_added_loops :
    injectiveHomCount (complete 2 false) (complete 3 false) = 6 ∧
      injectiveHomCount (complete 2 false) (complete 3 true) = 6 := by decide

/-- All homomorphisms may change through collisions; here the three constant
maps are added, exactly the two-vertex collision charge.
@isnad1 id=and.0h0v.s6.a775331fd485 from=translated src=- shape=1ac4f421 vocab=358c59f8
-/
theorem hom_count_collision_difference :
    homCount (complete 2 false) (complete 3 false) = 6 ∧
      homCount (complete 2 false) (complete 3 true) = 9 := by decide

/-- The positive edge pattern meets the new simplicity hypothesis.
@isnad1 id=simplepa.0h0v.s3.a56625cff409 from=translated src=- shape=af010f2d vocab=a51b9dd2
-/
theorem edge_isSimplePattern : SimplePattern (complete 2 false) := by
  unfold SimplePattern
  decide

/-- The two hosts in the regression do not meet diagonal agreement. This is
the explicit missing premise of the induced-count corollary.
@isnad1 id=not.0h0v.s5.ba355542ebda from=translated src=- shape=754bc602 vocab=3b55cf52
-/
theorem hosts_not_diagonalAgreement :
    ¬ DiagonalAgreementOn (complete 3 false) (complete 3 true) Finset.univ := by
  intro h
  have hi : ¬ Function.Injective (fun _ : Fin 2 ↦ (0 : Fin 3)) := by
    intro hinj
    exact (by decide : (0 : Fin 2) ≠ 1) (hinj (a₁ := 0) (a₂ := 1) rfl)
  have hh := h (RelSymbol.mk' (n := 2) (() : language.Relations 2)) (fun _ ↦ 0)
    (fun _ ↦ Finset.mem_univ _) hi
  change (false = true ↔ true = true) at hh
  exact Bool.false_ne_true (hh.mpr rfl)

/-- The set-restricted homomorphism API agrees with the original count used
by this regression, including its three colliding maps.
@isnad1 id=eq.0h0v.s5.7ba299bbba40 from=translated src=- shape=3451d1f3 vocab=6cc46dd2
-/
theorem restricted_hom_regression :
    homCountOn (complete 2 false) (complete 3 true) Finset.univ = 9 := by
  rw [homCountOn_univ]
  exact hom_count_collision_difference.2

end RegularityLemmata.DiagonalLoopRegression

