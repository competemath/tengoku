/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Order
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.ProximityGrowth
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.LogDerivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Minimal-type growth of genus-one canonical products

Inverse-square summability of the zero locations makes the genus-one
canonical product a function of order at most two and minimal type.  The
proof splits the logarithmic majorant into a finite linear head and an
arbitrarily small quadratic tail.  It then adds the finite origin monomial
and converts the resulting pointwise logarithmic bound to a Nevanlinna
characteristic bound.  The results are independent of any particular
completed L-function.
-/

open Filter Metric Real Set Topology
open scoped Real

namespace OverflowResidueRH

open ValueDistribution

/-- A genus-one factor has a global linear exponential bound.-/
lemma norm_hadamardGenus1Factor_le_exp_linear
    (ρ z : ℂ) :
    ‖hadamardGenus1Factor ρ z‖ ≤ Real.exp (2 * ‖z‖ / ‖ρ‖) := by
  let w : ℂ := z / ρ
  have hre : w.re ≤ ‖w‖ := Complex.re_le_norm _
  have hone : ‖(1 : ℂ) - w‖ ≤ 1 + ‖w‖ := by
    calc
      ‖(1 : ℂ) - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ = 1 + ‖w‖ := by simp
  have hone_exp : 1 + ‖w‖ ≤ Real.exp ‖w‖ := by
    simpa [add_comm] using Real.add_one_le_exp ‖w‖
  calc
    ‖hadamardGenus1Factor ρ z‖ = ‖(1 - w) * Complex.exp w‖ := by
      simp only [hadamardGenus1Factor, w]
    _ = ‖1 - w‖ * Real.exp w.re := by rw [norm_mul, Complex.norm_exp]
    _ ≤ Real.exp ‖w‖ * Real.exp ‖w‖ := by
      exact mul_le_mul (hone.trans hone_exp) (Real.exp_le_exp.mpr hre)
        (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (2 * ‖w‖) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (2 * ‖z‖ / ‖ρ‖) := by
      congr 1
      rw [norm_div]
      ring

/-- A genus-one factor has a global quadratic exponential bound.  For
`‖z / ρ‖ ≤ 1` this is the Taylor estimate; outside the unit disk the linear
bound is stronger.-/
lemma norm_hadamardGenus1Factor_le_exp_quadratic
    (ρ z : ℂ) :
    ‖hadamardGenus1Factor ρ z‖ ≤
      Real.exp (4 * ‖z‖ ^ 2 * (‖ρ‖ ^ 2)⁻¹) := by
  let w : ℂ := z / ρ
  have hbound_w : ‖(1 - w) * Complex.exp w‖ ≤ Real.exp (4 * ‖w‖ ^ 2) := by
    by_cases hw : ‖w‖ ≤ 1
    · have hdev := genusOneTaylorBoundData.bound w hw
      have hnorm : ‖(1 - w) * Complex.exp w‖ ≤ 1 + 4 * ‖w‖ ^ 2 := by
        calc
          ‖(1 - w) * Complex.exp w‖ =
              ‖1 - (1 - (1 - w) * Complex.exp w)‖ := by
            congr 1
            ring
          _ ≤ ‖(1 : ℂ)‖ + ‖1 - (1 - w) * Complex.exp w‖ := norm_sub_le _ _
          _ ≤ 1 + 4 * ‖w‖ ^ 2 := by
            simpa using add_le_add_left hdev 1
      exact hnorm.trans (by
        simpa [add_comm] using Real.add_one_le_exp (4 * ‖w‖ ^ 2))
    · have hw_one : 1 ≤ ‖w‖ := le_of_not_ge hw
      have hlin : ‖(1 - w) * Complex.exp w‖ ≤ Real.exp (2 * ‖w‖) := by
        have hre : w.re ≤ ‖w‖ := Complex.re_le_norm _
        have hone : ‖(1 : ℂ) - w‖ ≤ 1 + ‖w‖ := by
          calc
            ‖(1 : ℂ) - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
            _ = 1 + ‖w‖ := by simp
        calc
          ‖(1 - w) * Complex.exp w‖ = ‖1 - w‖ * Real.exp w.re := by
            rw [norm_mul, Complex.norm_exp]
          _ ≤ Real.exp ‖w‖ * Real.exp ‖w‖ := by
            have hone_exp : 1 + ‖w‖ ≤ Real.exp ‖w‖ := by
              simpa [add_comm] using Real.add_one_le_exp ‖w‖
            exact mul_le_mul (hone.trans hone_exp) (Real.exp_le_exp.mpr hre)
              (Real.exp_pos _).le (Real.exp_pos _).le
          _ = Real.exp (2 * ‖w‖) := by
            rw [← Real.exp_add]
            congr 1
            ring
      exact hlin.trans (Real.exp_le_exp.mpr (by
        nlinarith [sq_nonneg ‖w‖]))
  calc
    ‖hadamardGenus1Factor ρ z‖ = ‖(1 - w) * Complex.exp w‖ := by
      simp only [hadamardGenus1Factor, w]
    _ ≤ Real.exp (4 * ‖w‖ ^ 2) := hbound_w
    _ = Real.exp (4 * ‖z‖ ^ 2 * (‖ρ‖ ^ 2)⁻¹) := by
      congr 1
      rw [norm_div, div_pow, div_eq_mul_inv]
      ring

/-- A summable nonnegative exponential majorant controls the norm of a
multipliable complex product.  The proof passes finite-product bounds to the
limit, avoiding an ordered-monoid requirement on `ℝ`.-/
lemma norm_tprod_le_exp_tsum
    {ι : Type*} {f : ι → ℂ} {b : ι → ℝ}
    (hf : Multipliable f) (hb : Summable b)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hfb : ∀ i, ‖f i‖ ≤ Real.exp (b i)) :
    ‖∏' i, f i‖ ≤ Real.exp (∑' i, b i) := by
  have hlim : Tendsto (fun F : Finset ι ↦ ∏ i ∈ F, f i) atTop
      (𝓝 (∏' i, f i)) := hf.hasProd
  have hnormlim : Tendsto (fun F : Finset ι ↦ ‖∏ i ∈ F, f i‖) atTop
      (𝓝 ‖∏' i, f i‖) := hlim.norm
  refine le_of_tendsto' hnormlim (fun F ↦ ?_)
  rw [norm_prod]
  calc
    ∏ i ∈ F, ‖f i‖ ≤ ∏ i ∈ F, Real.exp (b i) := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact norm_nonneg _
      · intro i _hi
        exact hfb i
    _ = Real.exp (∑ i ∈ F, b i) := (Real.exp_sum F b).symm
    _ ≤ Real.exp (∑' i, b i) :=
      Real.exp_le_exp.mpr (hb.sum_le_tsum F fun i _ ↦ hb_nonneg i)

set_option maxHeartbeats 400000 in
-- The full-index `ite` majorant avoids expensive subtype-product reduction,
-- but its finite-head/complement tsum normalization needs extra elaboration.
lemma norm_infiniteHadamardProduct_le_exp_split
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    (F : Finset ι) (z : ℂ) :
    ‖infiniteHadamardProduct zeroLoc z‖ ≤
      Real.exp
        ((∑ i ∈ F, 2 * ‖z‖ / ‖zeroLoc i‖) +
          4 * ‖z‖ ^ 2 *
            ∑' i : {i : ι // i ∉ F}, (‖zeroLoc i.1‖ ^ 2)⁻¹) := by
  classical
  let b : ι → ℝ := fun i ↦
    if i ∈ F then 2 * ‖z‖ / ‖zeroLoc i‖
    else 4 * ‖z‖ ^ 2 * (‖zeroLoc i‖ ^ 2)⁻¹
  have hb : Summable b := by
    apply Summable.add_compl (s := F) Summable.of_finite
    have htail := (H.inv_sq_summable.subtype (fun i ↦ i ∉ F)).mul_left
      (4 * ‖z‖ ^ 2)
    exact htail.congr (fun i ↦ by simp [b, i.2])
  have hb_nonneg : ∀ i, 0 ≤ b i := by
    intro i
    dsimp [b]
    split_ifs <;> positivity
  have hfactor : ∀ i,
      ‖hadamardGenus1Factor (zeroLoc i) z‖ ≤ Real.exp (b i) := by
    intro i
    dsimp [b]
    split_ifs
    · exact norm_hadamardGenus1Factor_le_exp_linear (zeroLoc i) z
    · exact norm_hadamardGenus1Factor_le_exp_quadratic (zeroLoc i) z
  have hmajor := norm_tprod_le_exp_tsum (H.product_multipliable z) hb
    hb_nonneg hfactor
  have hsum_head :
      ∑ i ∈ F, b i = ∑ i ∈ F, 2 * ‖z‖ / ‖zeroLoc i‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [b, hi]
  have hsum_tail :
      ∑' i : {i : ι // i ∉ F}, b i.1 =
        4 * ‖z‖ ^ 2 *
          ∑' i : {i : ι // i ∉ F}, (‖zeroLoc i.1‖ ^ 2)⁻¹ := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    simp [b, i.2]
  have htsum :
      ∑' i, b i =
        (∑ i ∈ F, 2 * ‖z‖ / ‖zeroLoc i‖) +
          4 * ‖z‖ ^ 2 *
            ∑' i : {i : ι // i ∉ F}, (‖zeroLoc i.1‖ ^ 2)⁻¹ := by
    rw [← hb.sum_add_tsum_subtype_compl F, hsum_head, hsum_tail]
  change ‖∏' i, hadamardGenus1Factor (zeroLoc i) z‖ ≤ _
  exact hmajor.trans_eq (congrArg Real.exp htsum)

end OverflowResidueRH
