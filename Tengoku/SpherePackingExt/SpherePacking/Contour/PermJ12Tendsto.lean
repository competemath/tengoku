module

public import Tengoku.Seed.Analysis.Calculus.Deriv.Basic
public import Tengoku.Seed.Analysis.Complex.Basic
public import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
public import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Tengoku.Seed.Analysis.Complex.Exponential
public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
public import Tengoku.Seed.Topology.Algebra.Algebra
public import Tengoku.Seed.Order.Interval.Set.UnorderedInterval
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tendsto for the `Ψ₁'` integrand near `z = 1`

In the `perm_J12` contour deformation, one needs a limit statement of the form
`Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] 1) (𝓝 0)`.

This file isolates that argument in a dimension-agnostic form. We assume:
- a factorization `Ψ₁' r z = ψT' z * cexp (π * I * r * z)`;
- a modular identity expressing `ψT'` in terms of a function `ψS` evaluated at `gAct z`; and
- basic geometric control of `gAct z` on `closure wedgeSet`.

## Main definitions
* `TendstoPsiOneHypotheses`

## Main statements
* `tendsto_Ψ₁'_one_within_closure_wedgeSet_of`
-/

open Set Filter
open scoped Topology Complex

namespace SpherePacking.Contour

noncomputable section

/--
`TendstoPsiOneHypotheses wedgeSet ψS ψT' Ψ₁' gAct k` bundles the hypotheses used to prove
`Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] 1) (𝓝 0)`.

This keeps downstream call sites from having to thread a long list of modular-identity and
geometry hypotheses.-/
public structure TendstoPsiOneHypotheses
    (wedgeSet : Set ℂ)
    (ψS : UpperHalfPlane → ℂ)
    (ψT' : ℂ → ℂ)
    (Ψ₁' : ℝ → ℂ → ℂ)
    (gAct : UpperHalfPlane → UpperHalfPlane)
    (k : ℕ) : Prop where
  hk : (1 : ℕ) ≤ k
  Ψ₁'_eq :
    ∀ r : ℝ, ∀ z : ℂ, Ψ₁' r z = ψT' z * cexp ((Real.pi : ℂ) * Complex.I * (r : ℂ) * z)
  ψT'_one : ψT' (1 : ℂ) = 0
  tendsto_ψS_atImInfty : Tendsto ψS UpperHalfPlane.atImInfty (𝓝 (0 : ℂ))
  gAct_im :
    ∀ {z : ℂ} (hz : 0 < z.im),
      (gAct (⟨z, hz⟩ : UpperHalfPlane)).im = z.im / Complex.normSq (z - 1)
  ψT'_eq_neg_ψS_mul :
    ∀ {z : ℂ} (hz : 0 < z.im),
      ψT' z = -ψS (gAct (⟨z, hz⟩ : UpperHalfPlane)) * (z - 1) ^ k
  mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → z ≠ (1 : ℂ) → z ∈ UpperHalfPlane.upperHalfPlaneSet
  closure_wedgeSet_subset_abs_re_sub_one_le_im :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → |z.re - 1| ≤ z.im

private def expNorm (r : ℝ) : ℂ → ℝ :=
  fun z ↦ ‖cexp (z * (Complex.I * ((r : ℂ) * (Real.pi : ℂ))))‖

private lemma one_div_two_im_le_im_div_normSq_sub_one {z : ℂ}
    (hz_im_pos : 0 < z.im) (hz1 : z ≠ (1 : ℂ)) (habs_re : |z.re - 1| ≤ z.im) :
    (1 : ℝ) / (2 * z.im) ≤ z.im / Complex.normSq (z - 1) := by
  have hz_im_ne : z.im ≠ 0 := ne_of_gt hz_im_pos
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hnormSq_pos : 0 < Complex.normSq (z - 1) := (Complex.normSq_pos).2 hz1'
  have hnormSq_le : Complex.normSq (z - 1) ≤ 2 * z.im ^ 2 := by
    have hre_sq : (z.re - 1) ^ 2 ≤ z.im ^ 2 := by
      have : |z.re - 1| ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs_re 2
      simpa [sq_abs] using this
    have hnormSq : Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
      simp [Complex.normSq, sub_eq_add_neg, pow_two, add_comm]
    nlinarith [hnormSq, hre_sq]
  have hMul :
      z.im * ((1 : ℝ) / (2 * z.im ^ 2)) ≤ z.im * ((1 : ℝ) / Complex.normSq (z - 1)) :=
    mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hnormSq_pos hnormSq_le)
      (le_of_lt hz_im_pos)
  calc
    (1 : ℝ) / (2 * z.im) = z.im * ((1 : ℝ) / (2 * z.im ^ 2)) := by field_simp [hz_im_ne]
    _ ≤ z.im * ((1 : ℝ) / Complex.normSq (z - 1)) := hMul
    _ = z.im / Complex.normSq (z - 1) := by simp [div_eq_mul_inv]

private structure GActImNearOneHyp (wedgeSet : Set ℂ)
    (gAct : UpperHalfPlane → UpperHalfPlane) : Prop where
  gAct_im :
    ∀ {z : ℂ} (hz : 0 < z.im),
      (gAct (⟨z, hz⟩ : UpperHalfPlane)).im = z.im / Complex.normSq (z - 1)
  mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → z ≠ (1 : ℂ) → z ∈ UpperHalfPlane.upperHalfPlaneSet
  closure_wedgeSet_subset_abs_re_sub_one_le_im :
    ∀ {z : ℂ}, z ∈ closure wedgeSet → |z.re - 1| ≤ z.im

private lemma exists_gAct_im_ge_of_dist_lt
    {wedgeSet : Set ℂ}
    {gAct : UpperHalfPlane → UpperHalfPlane}
    (hg : GActImNearOneHyp wedgeSet gAct)
    {A : ℝ} (hApos : 0 < A)
    {z : ℂ} (hzcl : z ∈ closure wedgeSet) (hz1 : z ≠ (1 : ℂ))
    (hdist : dist z (1 : ℂ) < 1 / (2 * A)) :
    ∃ hz_im_pos : 0 < z.im, A ≤ (gAct (⟨z, hz_im_pos⟩ : UpperHalfPlane)).im := by
  have hz_im_pos : 0 < z.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using
      (hg.mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl hz1)
  have hz_im_lt : z.im < 1 / (2 * A) := by
    have hnorm : ‖z - 1‖ < 1 / (2 * A) := by simpa [dist_eq_norm] using hdist
    have hz_im_le : z.im ≤ ‖z - 1‖ := by
      simpa [abs_of_nonneg (le_of_lt hz_im_pos)] using (Complex.abs_im_le_norm (z - 1))
    exact lt_of_le_of_lt hz_im_le hnorm
  have habs_re : |z.re - 1| ≤ z.im := hg.closure_wedgeSet_subset_abs_re_sub_one_le_im hzcl
  have hLower : (1 : ℝ) / (2 * z.im) ≤ z.im / Complex.normSq (z - 1) :=
    one_div_two_im_le_im_div_normSq_sub_one (z := z) hz_im_pos hz1 habs_re
  have hA_lt : A < (1 : ℝ) / (2 * z.im) := by
    have hmul : z.im * (2 * A) < (1 : ℝ) := (lt_div_iff₀ (by positivity)).1 hz_im_lt
    exact (lt_div_iff₀ (by positivity)).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
  refine ⟨hz_im_pos, ?_⟩
  have : A < (gAct (⟨z, hz_im_pos⟩ : UpperHalfPlane)).im := by
    have : A < z.im / Complex.normSq (z - 1) := lt_of_lt_of_le hA_lt hLower
    simpa [hg.gAct_im (z := z) (hz := hz_im_pos)] using this
  exact this.le

end

end SpherePacking.Contour
