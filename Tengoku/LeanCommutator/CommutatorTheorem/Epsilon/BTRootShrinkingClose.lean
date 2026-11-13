import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTRootShrinking
import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTRootMoment

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closing the one-step derivative barrier

This file turns the finite reciprocal-gap inequality from `BTRootShrinking` into the
logarithmic-derivative identity used by the root-shrinking argument.
-/

namespace CommutatorTheorem

open scoped Polynomial BigOperators
open Polynomial Finset

/-- If a point is strictly to the right of every root of a split polynomial, its barrier
potential is positive.-/
lemma rootBarrierPotential_pos_of_strictRootUpperBound
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 0 < p.natDegree) {x : ℝ}
    (hx : IsStrictRootUpperBound p x) : 0 < rootBarrierPotential p x := by
  have hp0 : p ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  have heval : p.eval x ≠ 0 := by
    intro hzero
    exact (lt_irrefl x) (hx x hzero)
  rw [rootBarrierPotential_eq_sum_roots hp heval]
  rw [multiset_map_sum_eq_fin_sum_sort]
  let l := p.roots.sort (· ≤ ·)
  have hlen : 0 < l.length := by
    simpa [l, hp.natDegree_eq_card_roots] using hdeg
  haveI : Nonempty (Fin l.length) := Fin.pos_iff_nonempty.mp hlen
  apply Finset.sum_pos (s := (Finset.univ : Finset (Fin l.length)))
  · intro i _
    have hmem : l.get i ∈ p.roots := by
      exact (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mp (l.get_mem i)
    exact one_div_pos.mpr (sub_pos.mpr (hx _ ((mem_roots hp0).mp hmem)))
  · exact Finset.univ_nonempty

/-- A strict upper bound for the roots of `p` is also a strict upper bound for the roots of
`p'`, provided `p` is split and has positive degree.  The proof uses positivity of the
logarithmic derivative to the right of all roots.-/
lemma RealRooted.derivative_strictRootUpperBound
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 0 < p.natDegree) {x : ℝ}
    (hx : IsStrictRootUpperBound p x) : IsStrictRootUpperBound p.derivative x := by
  have hp0 : p ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  intro r hr
  by_contra hnot
  have hxr : x ≤ r := le_of_not_gt hnot
  have hstrict_r : IsStrictRootUpperBound p r := by
    intro y hy
    exact lt_of_lt_of_le (hx y hy) hxr
  have hpeval : p.eval r ≠ 0 := by
    intro hzero
    exact (lt_irrefl r) (hstrict_r r hzero)
  have hbarrier_pos := rootBarrierPotential_pos_of_strictRootUpperBound hp hdeg hstrict_r
  rw [rootBarrierPotential] at hbarrier_pos
  have hderiv_ne : p.derivative.eval r ≠ 0 := by
    intro hzero
    simp [hzero] at hbarrier_pos
  exact hderiv_ne hr

/-- Elementary reciprocal-gap algebra, kept separate so that root-list accessors do not obscure
the field normalization.-/
lemma reciprocal_gap_at_shift {b r A : ℝ} (hA : A ≠ 0) (hgap : b - r ≠ 0) :
    1 / (b - 1 / A - r) =
      (1 / (b - r)) * A / (A - 1 / (b - r)) := by
  field_simp [hA, hgap]
  ring

/-- The barrier potential is antitone as its argument moves right while staying beyond all
roots.-/
lemma rootBarrierPotential_antitone
    {p : ℝ[X]} (hp : RealRooted p) (hdeg : 0 < p.natDegree) {x y : ℝ}
    (hx : IsStrictRootUpperBound p x) (hxy : x ≤ y) :
    rootBarrierPotential p y ≤ rootBarrierPotential p x := by
  have hp0 : p ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  have hy : IsStrictRootUpperBound p y := by
    intro r hr
    exact lt_of_lt_of_le (hx r hr) hxy
  have hxeval : p.eval x ≠ 0 := by
    intro hzero
    exact (lt_irrefl x) (hx x hzero)
  have hyeval : p.eval y ≠ 0 := by
    intro hzero
    exact (lt_irrefl y) (hy y hzero)
  rw [rootBarrierPotential_eq_sum_roots hp hyeval,
    rootBarrierPotential_eq_sum_roots hp hxeval]
  rw [multiset_map_sum_eq_fin_sum_sort, multiset_map_sum_eq_fin_sum_sort]
  apply Finset.sum_le_sum
  intro i _
  have hmem : (p.roots.sort (· ≤ ·)).get i ∈ p.roots := by
    exact (Multiset.mem_sort (s := p.roots) (r := (· ≤ ·))).mp
      ((p.roots.sort (· ≤ ·)).get_mem i)
  have hroot := (mem_roots hp0).mp hmem
  apply one_div_le_one_div_of_le (sub_pos.mpr (hx _ hroot))
  linarith

/-- Strict admissibility puts the optimized moment barrier strictly to the right of `1`.
The non-strict endpoint is available as `one_le_optimal_rootMoment_barrier`; the strict form is
what lets the barrier proof avoid evaluating at a possible root equal to `1`.-/
lemma one_lt_optimal_rootMoment_barrier
    {c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hcα : c < (1 + α)⁻¹) :
    1 < 1 - α + Real.sqrt ((1 - c) * α / c) := by
  have h1α : 0 < 1 + α := by linarith
  have hcineq : c * (1 + α) < 1 := by
    apply (lt_div_iff₀ h1α).mp
    simpa [one_div] using hcα
  have hsquare : α ^ 2 < (1 - c) * α / c := by
    rw [lt_div_iff₀ hc]
    nlinarith [mul_pos hα (sub_pos.mpr hcineq)]
  have hsqrt : α < Real.sqrt ((1 - c) * α / c) := by
    calc
      α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα.le).symm
      _ < Real.sqrt ((1 - c) * α / c) := Real.sqrt_lt_sqrt (sq_nonneg α) hsquare
  linarith

end CommutatorTheorem
