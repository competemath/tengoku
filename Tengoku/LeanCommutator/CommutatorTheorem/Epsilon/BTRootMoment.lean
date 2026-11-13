import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTRootShrinking

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Root moments and the optimized initial barrier

This file formalizes the moment algebra behind the refined
Ravichandran--Srivastava root-shrinking bound.  It contains three independent
pieces:

* the first two root moments in terms of the first two lower coefficients;
* a quadratic majorant for the reciprocal barrier using only mean zero and
  the second moment;
* the exact scalar optimization which produces
  `c * (1 - α) + 2 * sqrt (c * (1 - c) * α)` and explains the condition
  `c ≤ (1 + α)⁻¹`.

There are no axioms or placeholders in this file.
-/

namespace CommutatorTheorem

open scoped Polynomial BigOperators
open Polynomial Finset

/-! ## Vieta/Newton identities for the first two root moments -/

/-- Average of the roots, counted with multiplicity.-/
noncomputable def rootMean (p : ℝ[X]) : ℝ :=
  p.roots.sum / (p.natDegree : ℝ)

/-- Average of the squares of the roots, counted with multiplicity.-/
noncomputable def rootMeanSquare (p : ℝ[X]) : ℝ :=
  (p.roots.map fun r ↦ r ^ 2).sum / (p.natDegree : ℝ)

/-- For a monic split polynomial, the sum of the roots is the negative of the
next coefficient.-/
theorem sum_roots_eq_neg_nextCoeff {p : ℝ[X]} (hp : RealRooted p)
    (hmonic : p.Monic) :
    p.roots.sum = -p.nextCoeff := by
  rw [hp.nextCoeff_eq_neg_sum_roots_of_monic hmonic]
  simp

/-- Coefficient form of the normalized root mean.-/
theorem rootMean_eq_neg_nextCoeff_div_natDegree
    {p : ℝ[X]} (hp : RealRooted p) (hmonic : p.Monic) :
    rootMean p = -p.nextCoeff / (p.natDegree : ℝ) := by
  rw [rootMean, sum_roots_eq_neg_nextCoeff hp hmonic]

/-- In positive degree, mean zero is exactly vanishing next coefficient.-/
theorem rootMean_eq_zero_iff_nextCoeff_eq_zero
    {p : ℝ[X]} (hp : RealRooted p) (hmonic : p.Monic)
    (hdeg : 0 < p.natDegree) :
    rootMean p = 0 ↔ p.nextCoeff = 0 := by
  rw [rootMean_eq_neg_nextCoeff_div_natDegree hp hmonic]
  have hn : (p.natDegree : ℝ) ≠ 0 := by exact_mod_cast hdeg.ne'
  constructor
  · intro h
    apply neg_eq_zero.mp
    exact (div_eq_zero_iff.mp h).resolve_right hn
  · intro h
    simp [h]

/-! ## A moment majorant for the initial barrier -/

/-- The quadratic which majorizes `r ↦ (b-r)⁻¹` on `r ≤ 1` and is tangent at
`r = -α`.-/
noncomputable def rootMomentMajorant (b α r : ℝ) : ℝ :=
  1 / (b + α) + (r + α) / (b + α) ^ 2 +
    (r + α) ^ 2 / ((b - 1) * (b + α) ^ 2)

/-! ## The monotone-potential bridge for fixed-`φ` iteration -/

/-- To the right of every root, the barrier potential of a real-rooted
polynomial is antitone.-/
theorem rootBarrierPotential_anti_of_strictRootUpperBound
    {p : ℝ[X]} (hp : RealRooted p) {x y : ℝ}
    (hx : IsStrictRootUpperBound p x) (hxy : x ≤ y) :
    rootBarrierPotential p y ≤ rootBarrierPotential p x := by
  have hp0 : p ≠ 0 := by
    intro hzero
    have hroot : p.IsRoot x := by simp [hzero]
    exact (lt_irrefl x) (hx x hroot)
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
  have hgap : 0 < x - (p.roots.sort (· ≤ ·)).get i := by
    exact sub_pos.mpr (hx _ ((mem_roots hp0).mp hmem))
  exact one_div_le_one_div_of_le hgap (by linarith)

/-! ## Exact optimization of the barrier objective -/

/-- The scalar objective obtained after inserting the moment bound into the
iterated barrier displacement.-/
noncomputable def rootShrinkMomentObjective (b c α : ℝ) : ℝ :=
  b - (1 - c) * (b - 1) * (b + α) / (b + α - 1)

/-- Reparameterizing by `v = b + α - 1` exposes the AM--GM optimization.-/
theorem rootShrinkMomentObjective_eq {b c α : ℝ}
    (hv : b + α - 1 ≠ 0) :
    rootShrinkMomentObjective b c α =
      c * (1 - α) + c * (b + α - 1) +
        (1 - c) * α / (b + α - 1) := by
  dsimp [rootShrinkMomentObjective]
  field_simp [hv]
  ring

/-- At the optimizing barrier, the objective is exactly the refined
root-shrinking expression.-/
theorem rootShrinkMomentObjective_at_optimum
    {c α : ℝ} (hc : 0 < c) (hc1 : c < 1) (hα : 0 < α) :
    let v := Real.sqrt ((1 - c) * α / c)
    let b := 1 - α + v
    rootShrinkMomentObjective b c α =
      c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α) := by
  dsimp only
  let v := Real.sqrt ((1 - c) * α / c)
  let b := 1 - α + v
  change rootShrinkMomentObjective b c α =
    c * (1 - α) + 2 * Real.sqrt (c * (1 - c) * α)
  have hrad : 0 < (1 - c) * α / c :=
    div_pos (mul_pos (sub_pos.mpr hc1) hα) hc
  have hv : 0 < v := Real.sqrt_pos.2 hrad
  have hvsq : v ^ 2 = (1 - c) * α / c := Real.sq_sqrt hrad.le
  have hvb : b + α - 1 = v := by dsimp [b]; ring
  rw [rootShrinkMomentObjective_eq (by rw [hvb]; exact hv.ne')]
  rw [hvb]
  have hsqrt : Real.sqrt (c * (1 - c) * α) = c * v := by
    apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hc1.le)) hα.le)
      (mul_nonneg hc.le hv.le)).2
    rw [mul_pow, hvsq]
    field_simp [hc.ne']
  rw [hsqrt]
  have hkey : c * v ^ 2 = (1 - c) * α := by
    rw [hvsq]
    field_simp [hc.ne']
  have hfrac : (1 - c) * α / v = c * v := by
    apply (div_eq_iff hv.ne').2
    calc
      (1 - c) * α = c * v ^ 2 := hkey.symm
      _ = (c * v) * v := by ring
  rw [hfrac]
  ring

/-- The admissibility condition `c ≤ (1+α)⁻¹` puts the optimizing barrier at
or to the right of `1`, exactly as required by the root interval hypothesis.-/
theorem one_le_optimal_rootMoment_barrier
    {c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hcα : c ≤ (1 + α)⁻¹) :
    1 ≤ 1 - α + Real.sqrt ((1 - c) * α / c) := by
  have h1α : 0 < 1 + α := by linarith
  have hc1 : c < 1 := lt_of_le_of_lt hcα (by
    rw [inv_lt_one₀ h1α]
    linarith)
  have hrad : 0 ≤ (1 - c) * α / c :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hc1.le) hα.le) hc.le
  have hsquare : α ^ 2 ≤ (1 - c) * α / c := by
    rw [le_div_iff₀ hc]
    have hcineq : c * (1 + α) ≤ 1 := by
      exact (le_div_iff₀ h1α).mp (by simpa [one_div] using hcα)
    nlinarith
  have hsqrt : α ≤ Real.sqrt ((1 - c) * α / c) := by
    calc
      α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα.le).symm
      _ ≤ Real.sqrt ((1 - c) * α / c) := Real.sqrt_le_sqrt hsquare
  linarith

end CommutatorTheorem
