import Tengoku.Twinprime.TwinPrime.Analytic.PrimeReciprocalAbel
import Tengoku.Twinprime.TwinPrime.Analytic.ClassicalDistribution
import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeIntegral
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmically scaled reciprocal Mangoldt sums

The finite centered Abel bound is applied to an actual continuously
differentiable test function. The reciprocal Mangoldt input is discharged
by the repository's unconditional classical distribution theorem.
-/

noncomputable section

open Finset MeasureTheory ArithmeticFunction Filter
open scoped Topology

namespace TwinPrime.Analytic

def logScaleTestFunction (g : ℝ → ℝ) (L y : ℝ) : ℝ :=
  g (Real.log y / L) / L

private theorem logScale_mem {L u v y : ℝ} (hL : 0 < L) (_huv : u ≤ v)
    (hy : y ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) :
    Real.log y / L ∈ Set.Icc u v := by
  have hy0 := (Real.exp_pos (u * L)).trans_le hy.1
  constructor
  · apply (le_div_iff₀ hL).mpr
    simpa using Real.log_le_log (Real.exp_pos (u * L)) hy.1
  · apply (div_le_iff₀ hL).mpr
    simpa using Real.log_le_log hy0 hy.2

private theorem hasDerivAt_logScaleTestFunction
    {g : ℝ → ℝ} {L y : ℝ} (hL : L ≠ 0) (hy : 0 < y)
    (hg : DifferentiableAt ℝ g (Real.log y / L)) :
    HasDerivAt (logScaleTestFunction g L)
      (deriv g (Real.log y / L) / L ^ 2 / y) y := by
  have h := (hg.hasDerivAt.comp y ((Real.hasDerivAt_log hy.ne').div_const L)).div_const L
  have heq : deriv g (Real.log y / L) / L ^ 2 / y =
      (deriv g (Real.log y / L) * (y⁻¹ / L)) / L := by
    field_simp
  rw [heq]
  exact h

private theorem continuousOn_logScaleDerivative
    {g : ℝ → ℝ} {L u v : ℝ} (hL : 0 < L) (huv : u ≤ v)
    (hg : ContinuousOn (deriv g) (Set.Icc u v)) :
    ContinuousOn (fun y => deriv g (Real.log y / L) / L ^ 2 / y)
      (Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) := by
  have hypos : ∀ y ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L)), 0 < y :=
    fun y hy => (Real.exp_pos (u * L)).trans_le hy.1
  have hc : ContinuousOn (fun y => Real.log y / L)
      (Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) := by
    have hlog : ContinuousOn Real.log
        (Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) :=
      fun y hy => (Real.continuousAt_log (hypos y hy).ne').continuousWithinAt
    exact hlog.div_const L
  exact ((hg.comp hc (fun y hy => logScale_mem hL huv hy)).div_const _).div
    continuousOn_id (fun y hy => (hypos y hy).ne')

/--
@isnad1 id=eq.3h4v.s6.bec2f9bdefc5 from=translated src=- shape=fa9a92bd vocab=81a8b7c9
-/
theorem integral_logScaleTestFunction_div
    {g : ℝ → ℝ} {L u v : ℝ} (hL : 0 < L) (huv : u ≤ v)
    (hg : ContinuousOn g (Set.Icc u v)) :
    (∫ y in Real.exp (u * L)..Real.exp (v * L), logScaleTestFunction g L y / y) =
      ∫ t in u..v, g t := by
  have hab : Real.exp (u * L) ≤ Real.exp (v * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right huv hL.le)
  have hder : ∀ y ∈ Set.uIcc (Real.exp (u * L)) (Real.exp (v * L)),
      HasDerivAt (fun y => Real.log y / L) (1 / y / L) y := by
    intro y hy
    have hy0 : 0 < y := (Real.exp_pos (u * L)).trans_le ((Set.uIcc_of_le hab ▸ hy).1)
    simpa only [one_div] using (Real.hasDerivAt_log hy0.ne').div_const L
  have hc : ContinuousOn (fun y : ℝ => 1 / y / L)
      (Set.uIcc (Real.exp (u * L)) (Real.exp (v * L))) := by
    apply ContinuousOn.div_const
    apply continuousOn_const.div continuousOn_id
    intro y hy
    exact ((Real.exp_pos (u * L)).trans_le ((Set.uIcc_of_le hab ▸ hy).1)).ne'
  have hgimage : ContinuousOn g ((fun y => Real.log y / L) ''
      Set.uIcc (Real.exp (u * L)) (Real.exp (v * L))) := by
    apply hg.mono
    rintro t ⟨y, hy, rfl⟩
    exact logScale_mem hL huv (Set.uIcc_of_le hab ▸ hy)
  have h := intervalIntegral.integral_comp_mul_deriv' hder hc hgimage
  simp only [Real.log_exp, mul_div_cancel_right₀ _ hL.ne'] at h
  convert h using 1
  congr 1
  ext y
  simp only [Function.comp_apply, logScaleTestFunction]
  ring

/--
@isnad1 id=le.5h5v.s8.76047590810e from=translated src=- shape=579596c5 vocab=16ca3542
-/
theorem abs_logScaleTestFunction_variation_le
    {g : ℝ → ℝ} {L u v K : ℝ} (hL : 0 < L) (huv : u ≤ v)
    (hg_diff : ∀ t ∈ Set.Icc u v, DifferentiableAt ℝ g t)
    (hg_deriv : ContinuousOn (deriv g) (Set.Icc u v))
    (hK : ∀ t ∈ Set.Icc u v, |deriv g t| ≤ K) :
    (∫ y in Real.exp (u * L)..Real.exp (v * L),
      |deriv (logScaleTestFunction g L) y|) ≤ K * (v - u) / L := by
  have hab : Real.exp (u * L) ≤ Real.exp (v * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right huv hL.le)
  have hformula : ∀ y ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L)),
      deriv (logScaleTestFunction g L) y = deriv g (Real.log y / L) / L ^ 2 / y := by
    intro y hy
    exact (hasDerivAt_logScaleTestFunction hL.ne'
      ((Real.exp_pos (u * L)).trans_le hy.1) (hg_diff _ (logScale_mem hL huv hy))).deriv
  have hc := continuousOn_logScaleDerivative hL huv hg_deriv
  have hfcont : ContinuousOn (deriv (logScaleTestFunction g L))
      (Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) := hc.congr hformula
  have hInv : ContinuousOn (fun y : ℝ => 1 / y)
      (Set.uIcc (Real.exp (u * L)) (Real.exp (v * L))) := by
    apply continuousOn_const.div continuousOn_id
    intro y hy
    exact ((Real.exp_pos (u * L)).trans_le ((Set.uIcc_of_le hab ▸ hy).1)).ne'
  have hmain : (∫ y in Real.exp (u * L)..Real.exp (v * L), 1 / y) = (v - u) * L := by
    rw [integral_one_div (by
      rw [Set.uIcc_of_le hab]
      exact fun h => (not_le_of_gt (Real.exp_pos (u * L))) h.1)]
    rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    ring
  calc
    _ ≤ ∫ y in Real.exp (u * L)..Real.exp (v * L), (K / L ^ 2) * (1 / y) := by
      apply intervalIntegral.integral_mono_on hab
        ((Set.uIcc_of_le hab).symm ▸ hfcont.abs).intervalIntegrable
        (hInv.const_mul _).intervalIntegrable
      intro y hy
      have hy0 := (Real.exp_pos (u * L)).trans_le hy.1
      rw [hformula y hy, abs_div, abs_div, abs_of_pos (sq_pos_of_pos hL), abs_of_pos hy0]
      exact (div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (hK _ (logScale_mem hL huv hy)) (sq_nonneg L)) hy0.le).trans_eq (by ring)
    _ = K * (v - u) / L := by
      rw [intervalIntegral.integral_const_mul, hmain]
      field_simp

/-- Finite, exact-floor version of centered Abel summation for a logarithmic
test function. Both signs of the derivative are allowed.
@isnad1 id=le.7h8v.s8.104939fe40e0 from=translated src=- shape=9e549e09 vocab=83abc2b7
-/
theorem abs_logScale_primeReciprocal_error_le
    {g : ℝ → ℝ} {L u v : ℝ} (hL : 0 < L) (huv : u ≤ v)
    (hg_diff : ∀ t ∈ Set.Icc u v, DifferentiableAt ℝ g t)
    (hg_deriv : ContinuousOn (deriv g) (Set.Icc u v)) (K₀ K₁ c M : ℝ)
    (hK₀ : ∀ t ∈ Set.Icc u v, |g t| ≤ K₀)
    (hK₁ : ∀ t ∈ Set.Icc u v, |deriv g t| ≤ K₁)
    (herror : ∀ y ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L)),
      |realPrimeReciprocalSum y - Real.log y - c| ≤ M) :
    |(∑ n ∈ Ioc ⌊Real.exp (u * L)⌋₊ ⌊Real.exp (v * L)⌋₊,
        vonMangoldt n / (n : ℝ) * (g (Real.log n / L) / L)) -
          (∫ t in u..v, g t)| ≤ M * (2 * K₀ + K₁ * (v - u)) / L := by
  have hab : Real.exp (u * L) ≤ Real.exp (v * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right huv hL.le)
  have hdf : ∀ y ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L)),
      HasDerivAt (logScaleTestFunction g L)
        (deriv g (Real.log y / L) / L ^ 2 / y) y := by
    intro y hy
    exact hasDerivAt_logScaleTestFunction hL.ne'
      ((Real.exp_pos (u * L)).trans_le hy.1) (hg_diff _ (logScale_mem hL huv hy))
  have hfcont : ContinuousOn (deriv (logScaleTestFunction g L))
      (Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) :=
    (continuousOn_logScaleDerivative hL huv hg_deriv).congr (fun y hy => (hdf y hy).deriv)
  have hgcont : ContinuousOn g (Set.Icc u v) :=
    fun t ht => (hg_diff t ht).continuousAt.continuousWithinAt
  have h := abs_primeReciprocal_abel_error_le_of_continuous_deriv
    (Real.exp_pos (u * L)) hab (fun y hy => (hdf y hy).differentiableAt)
    hfcont c M herror
  rw [integral_logScaleTestFunction_div hL huv hgcont] at h
  have hM : 0 ≤ M := (abs_nonneg _).trans (herror _ ⟨le_rfl, hab⟩)
  have hend (t : ℝ) (ht : t ∈ Set.Icc u v) :
      |logScaleTestFunction g L (Real.exp (t * L))| ≤ K₀ / L := by
    simp only [logScaleTestFunction, Real.log_exp, mul_div_cancel_right₀ _ hL.ne',
      abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right (hK₀ t ht) hL.le
  exact h.trans <| (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (hend u ⟨le_rfl, huv⟩) (hend v ⟨huv, le_rfl⟩))
      (abs_logScaleTestFunction_variation_le hL huv hg_diff hg_deriv hK₁)) hM).trans_eq (by ring)

/-- The actual reciprocal Mangoldt sum on a fixed logarithmic window.-/
def logScalePrimeReciprocalSum (g : ℝ → ℝ) (u v x : ℝ) : ℝ :=
  ∑ n ∈ Ioc ⌊x ^ u⌋₊ ⌊x ^ v⌋₊,
    vonMangoldt n / (n : ℝ) * (g (Real.log n / Real.log x) / Real.log x)

end TwinPrime.Analytic
