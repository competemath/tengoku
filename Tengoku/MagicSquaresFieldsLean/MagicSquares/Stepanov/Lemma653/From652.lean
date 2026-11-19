import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.DegreeSystem
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.Core
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Passing directly from Lemma 6.52 data to the first estimate of 6.53

This file connects the two halves of the current development.

For a constraint system whose good points form a finite subset of the
field, `S < A` gives an auxiliary polynomial.  If `M > 0`, summing its
root multiplicities immediately bounds the number of good points by its
degree, exactly as at the beginning of LN97 Theorem 6.53.

Version 2 avoids requiring a `DecidablePred sys.good` instance in theorem
statements.  The finite set of good points is packaged as a noncomputable
definition using classical decidability.
-/

/-- The finite set of points satisfying the `good` predicate of a
Stepanov constraint system.-/
noncomputable def constraintSystemGoodFinset
    {m q D M : ℕ} {f g : Polynomial F}
    (sys : StepanovConstraintSystem F m q D M f g) :
    Finset F := by
  classical
  exact Finset.univ.filter sys.good

omit [DecidableEq F] in
@[simp]
theorem mem_constraintSystemGoodFinset
    {m q D M : ℕ} {f g : Polynomial F}
    (sys : StepanovConstraintSystem F m q D M f g)
    (c : F) :
    c ∈ constraintSystemGoodFinset sys ↔ sys.good c := by
  classical
  simp [constraintSystemGoodFinset]

/-- Direct multiplicity-count consequence of the abstract Lemma 6.52
constraint system.-/
theorem constraintSystem_good_card_mul_le
    {m q D M u K G : ℕ} {f g : Polynomial F}
    (hf0 : f ≠ 0)
    (hfdeg : f.natDegree ≤ K)
    (hgdeg : g.natDegree ≤ G)
    (hind : QuotientPowerIndependent (F := F) m q D g)
    (sys : StepanovConstraintSystem F m q D M f g)
    (houter : ∀ v i, (sys.decode v i).natDegree ≤ u)
    (hSA : sys.S < sys.A)
    (hM : 0 < M) :
    ∃ E : Fin m → Polynomial (Polynomial F),
      (∃ i, E i ≠ 0) ∧
      stepanovAuxiliary q M f g E ≠ 0 ∧
      M * (constraintSystemGoodFinset sys).card
        ≤ M * K + (D + q * u + (m - 1) * G) := by
  obtain ⟨E, hEne, hE0, hmult, hdeg⟩ :=
    stepanovAuxiliary_exists_of_constraintSystem_with_degree
      (F := F) hf0 hfdeg hgdeg hind sys houter hSA
  refine ⟨E, hEne, hE0, ?_⟩
  apply card_mul_le_of_multiplicity_and_degree
    (F := F)
    (h := stepanovAuxiliary q M f g E)
    (T := constraintSystemGoodFinset sys)
    (M := M)
    (D := M * K + (D + q * u + (m - 1) * G))
    hM
  · intro c hc
    exact hmult c ((mem_constraintSystemGoodFinset sys c).mp hc)
  · exact hdeg

/-- Division form of the same estimate.-/
theorem constraintSystem_good_card_le
    {m q D M u K G : ℕ} {f g : Polynomial F}
    (hf0 : f ≠ 0)
    (hfdeg : f.natDegree ≤ K)
    (hgdeg : g.natDegree ≤ G)
    (hind : QuotientPowerIndependent (F := F) m q D g)
    (sys : StepanovConstraintSystem F m q D M f g)
    (houter : ∀ v i, (sys.decode v i).natDegree ≤ u)
    (hSA : sys.S < sys.A)
    (hM : 0 < M) :
    ∃ E : Fin m → Polynomial (Polynomial F),
      (∃ i, E i ≠ 0) ∧
      stepanovAuxiliary q M f g E ≠ 0 ∧
      (constraintSystemGoodFinset sys).card
        ≤ (M * K + (D + q * u + (m - 1) * G)) / M := by
  obtain ⟨E, hEne, hE0, hmul⟩ :=
    constraintSystem_good_card_mul_le
      (F := F) hf0 hfdeg hgdeg hind sys houter hSA hM
  refine ⟨E, hEne, hE0, ?_⟩
  exact (Nat.le_div_iff_mul_le hM).2 (by
    simpa [Nat.mul_comm] using hmul)

end LN97
end MagicSquares
