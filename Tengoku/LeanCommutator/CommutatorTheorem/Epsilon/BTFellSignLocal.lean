import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTFellCountParity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two-sided sign refinement for real-rooted polynomials

Exact Descartes makes the positive-root count lower semicontinuous when all
old nonzero coefficient signs are preserved.  Reflection gives the same
inequality for negative roots.  Away from zero their sum is the fixed degree,
so both inequalities are equalities.
-/

open scoped Polynomial

namespace CommutatorTheorem.BTFellSignLocal

open Polynomial
open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTFellDescartes
open CommutatorTheorem.BTFellExactDescartes

/-- The monic normalization of `p(-X)`.-/
noncomputable def reflectPolynomial (p : ℝ[X]) : ℝ[X] :=
  C ((-1 : ℝ) ^ p.natDegree) * p.comp (-X)

/-- The positive and negative root counts exhaust the degree when zero is
not a root.-/
theorem positive_add_negativeRootsCount_eq_natDegree
    {p : ℝ[X]} (hp : p.Monic) (hreal : RealRooted p)
    (hzero : ¬p.IsRoot 0) :
    p.roots.countP (0 < ·) + p.roots.countP (· < 0) = p.natDegree := by
  have hpartition := Multiset.card_eq_countP_add_countP (0 < ·) p.roots
  have hnonpos : p.roots.countP (fun r : ℝ => ¬ 0 < r) =
      p.roots.countP (· < 0) := by
    apply Multiset.countP_congr rfl
    intro r hr
    have hrne : r ≠ 0 := by
      intro hre
      subst r
      exact hzero ((mem_roots hp.ne_zero).mp hr)
    apply propext
    constructor <;> intro h
    · exact lt_of_le_of_ne (le_of_not_gt h) hrne
    · exact not_lt_of_ge h.le
  rw [hnonpos] at hpartition
  exact hpartition.symm.trans hreal.natDegree_eq_card_roots.symm

end CommutatorTheorem.BTFellSignLocal
