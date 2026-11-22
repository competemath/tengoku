/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Tengoku.Absorptioncutoff.AbsorptionCutoff.Supercritical.ScoreSmoothing
import Tengoku.Absorptioncutoff.AbsorptionCutoff.MeanMap.Dynamics
import Tengoku.Seed.MeasureTheory.Integral.Pi
import Tengoku.Seed.Probability.Moments.MGFAnalytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tensorization of the supercritical score

This module starts from the one-coordinate score calculation and develops the
moment and product-law estimates used in the paper's total-variation smoothing
argument.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The fourth moment of a standard real Gaussian is `3`.
@isnad1 id=eq.0h0v.s5.0928981e36b3 from=translated src=- shape=ed0f2aee vocab=4960fe00
-/
lemma integral_pow_four_gaussianReal :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  let f : ℝ → ℝ := fun t => Real.exp (t ^ 2 / 2)
  have hm :
      iteratedDeriv 4 f 0 =
        ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 := by
    have h := iteratedDeriv_mgf_zero
      (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) 4
    simpa [mgf_fun_id_gaussianReal, f] using h
  have hf (t : ℝ) : HasDerivAt f (t * f t) t := by
    have hg : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      convert ((hasDerivAt_id t).pow 2).div_const 2 using 1 <;>
        first | rfl | norm_num
    simpa only [f, mul_comm] using hg.exp
  have h1 :
      deriv f = fun t => t * f t := by
    funext t
    exact (hf t).deriv
  have h2 :
      deriv (fun t => t * f t) =
        fun t => (1 + t ^ 2) * f t := by
    funext t
    have h := (hasDerivAt_id t).mul (hf t)
    change deriv (id * f) t = _
    rw [h.deriv]
    simp only [id_eq]
    ring
  have h3 :
      deriv (fun t => (1 + t ^ 2) * f t) =
        fun t => (3 * t + t ^ 3) * f t := by
    funext t
    have hp : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
      convert ((hasDerivAt_id t).pow 2).const_add 1 using 1 <;>
        first | rfl | norm_num
    change deriv ((fun s : ℝ => 1 + s ^ 2) * f) t = _
    rw [(hp.mul (hf t)).deriv]
    ring
  have h4 :
      deriv (fun t => (3 * t + t ^ 3) * f t) =
        fun t => (3 + 6 * t ^ 2 + t ^ 4) * f t := by
    funext t
    have hp : HasDerivAt (fun s : ℝ => 3 * s + s ^ 3)
        (3 + 3 * t ^ 2) t := by
      convert ((hasDerivAt_id t).const_mul 3).add
        ((hasDerivAt_id t).pow 3) using 1 <;>
        first | rfl | norm_num
    change deriv ((fun s : ℝ => 3 * s + s ^ 3) * f) t = _
    rw [(hp.mul (hf t)).deriv]
    ring
  rw [← hm, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_one, h1, h2, h3, h4]
  norm_num [f]

/-- Compatibility name for the standard real Gaussian fourth moment.
@isnad1 id=eq.0h0v.s5.0928981e36b3 from=translated src=- shape=ed0f2aee vocab=4960fe00
-/
lemma integral_fourth_gaussian :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 :=
  integral_pow_four_gaussianReal

/-- The fourth power is integrable under the standard real Gaussian law.
@isnad1 id=integrab.0h0v.s5.1547dcd6334b from=translated src=- shape=3a191710 vocab=49f0f850
-/
lemma integrable_pow_four_gaussianReal :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
  have h :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 4).integrable_norm_pow'
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [id_eq, Real.norm_eq_abs]
  rw [← abs_pow, abs_of_nonneg]
  positivity

/-- The evaluated one-coordinate score has Fisher information `1/(2q²)`.
@isnad1 id=and.2h2v.s7.d633fcce9957 from=translated src=- shape=4aab5e33 vocab=a950e3a3
-/
lemma integrable_sq_gaussianOneCoordinateScore_map_and_integral_eq
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    Integrable
        (fun x : ℝ =>
          gaussianOneCoordinateScore A q
            (gaussianOneCoordinateMap A q x) ^ 2)
        (gaussianReal 0 1) ∧
      ∫ x : ℝ,
          gaussianOneCoordinateScore A q
            (gaussianOneCoordinateMap A q x) ^ 2
        ∂gaussianReal 0 1 = 1 / (2 * q ^ 2) := by
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) :=
    integrable_const 1
  have hpoly :
      Integrable (fun x : ℝ => x ^ 4 - 2 * x ^ 2 + 1)
        (gaussianReal 0 1) :=
    (integrable_pow_four_gaussianReal.sub
      (integrable_sq_gaussian.const_mul 2)).add hone
  have hsquare :
      (fun x : ℝ =>
        gaussianOneCoordinateScore A q
          (gaussianOneCoordinateMap A q x) ^ 2) =
        fun x : ℝ =>
          (4 * q ^ 2)⁻¹ * (x ^ 4 - 2 * x ^ 2 + 1) := by
    funext x
    rw [gaussianOneCoordinateScore_map hA hq]
    field_simp [hq.ne']
    ring
  rw [hsquare]
  have hint :=
    hpoly.const_mul (4 * q ^ 2)⁻¹
  refine ⟨hint, ?_⟩
  have hpolyIntegral :
      ∫ x : ℝ, x ^ 4 - 2 * x ^ 2 + 1 ∂gaussianReal 0 1 =
        (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) -
          2 * (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) + 1 := by
    let f4 : ℝ → ℝ := fun x => x ^ 4
    let f2 : ℝ → ℝ := fun x => 2 * x ^ 2
    let f1 : ℝ → ℝ := fun _ => 1
    have heq : (fun x : ℝ => x ^ 4 - 2 * x ^ 2 + 1) =
        (f4 - f2) + f1 := by
      funext x
      simp only [f4, f2, f1, Pi.add_apply, Pi.sub_apply]
    have hf4 : Integrable f4 (gaussianReal 0 1) := by
      simpa only [f4] using integrable_pow_four_gaussianReal
    have hf2 : Integrable f2 (gaussianReal 0 1) := by
      simpa only [f2] using integrable_sq_gaussian.const_mul 2
    have hf1 : Integrable f1 (gaussianReal 0 1) := by
      simpa only [f1] using hone
    rw [heq, integral_add' (hf4.sub hf2) hf1, integral_sub' hf4 hf2]
    simp only [f4, f2, f1, integral_const_mul]
    simp
  rw [integral_const_mul, hpolyIntegral, integral_pow_four_gaussianReal,
    integral_sq_gaussian]
  field_simp [hq.ne']
  ring

/-- Compatibility projection of the exact evaluated score second moment.
@isnad1 id=eq.2h2v.s7.9c672604523e from=translated src=- shape=c0a3eddb vocab=ee58d053
-/
lemma integral_sq_gaussianOneCoordinateScore_map
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    ∫ x : ℝ,
        gaussianOneCoordinateScore A q
          (gaussianOneCoordinateMap A q x) ^ 2
      ∂gaussianReal 0 1 = 1 / (2 * q ^ 2) :=
  (integrable_sq_gaussianOneCoordinateScore_map_and_integral_eq hA hq).2

/-- The score of the `N`-coordinate product law, written as the sum of its
one-coordinate scores. -/
noncomputable def gaussianCoordinateScoreSum
    (A q : ℝ) (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  ∑ i, gaussianOneCoordinateScore A q
    (gaussianOneCoordinateMap A q (g i))

/-- Each evaluated coordinate score is integrable under the product Gaussian
law.
@isnad1 id=integrab.2h4v.s6.f678d70a92e3 from=translated src=- shape=5548d853 vocab=e8c00dd4
-/
lemma integrable_gaussianOneCoordinateScore_map_eval
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) {N : ℕ} (i : Fin N) :
    Integrable
      (fun g : Fin N → ℝ =>
        gaussianOneCoordinateScore A q
          (gaussianOneCoordinateMap A q (g i)))
      (gaussianVec N) := by
  let f : ℝ → ℝ := fun x =>
    gaussianOneCoordinateScore A q (gaussianOneCoordinateMap A q x)
  refine Integrable.comp_measurable
    (f := fun g : Fin N → ℝ => g i) (g := f) ?_
      (measurable_pi_apply i)
  unfold gaussianVec
  rw [Measure.pi_map_eval]
  simpa only [measure_univ, Finset.prod_const_one, one_smul, f] using
    integrable_gaussianOneCoordinateScore_map hA hq

/-- Each evaluated coordinate score remains centered under the product
Gaussian law.
@isnad1 id=eq.2h4v.s6.ee52129bb309 from=translated src=- shape=3298d57c vocab=ad18ce55
-/
lemma integral_gaussianOneCoordinateScore_map_eval_eq_zero
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) {N : ℕ} (i : Fin N) :
    ∫ g : Fin N → ℝ,
        gaussianOneCoordinateScore A q
          (gaussianOneCoordinateMap A q (g i))
      ∂gaussianVec N = 0 := by
  let f : ℝ → ℝ := fun x =>
    gaussianOneCoordinateScore A q (gaussianOneCoordinateMap A q x)
  have hpm :
      (gaussianVec N).map (Function.eval i) = gaussianReal 0 1 := by
    unfold gaussianVec
    rw [Measure.pi_map_eval]
    simp
  have hf : AEStronglyMeasurable f
      ((gaussianVec N).map (Function.eval i)) := by
    rw [hpm]
    exact (integrable_gaussianOneCoordinateScore_map hA hq).1
  have hmap := integral_map
    (μ := gaussianVec N) (φ := Function.eval i) (f := f)
    (measurable_pi_apply i).aemeasurable hf
  rw [hpm] at hmap
  exact hmap.symm.trans
    (integral_gaussianOneCoordinateScore_map_eq_zero hA hq)

/-- The product score is integrable under the standard product Gaussian law.
@isnad1 id=integrab.2h3v.s6.50afa8c926bb from=translated src=- shape=384db00c vocab=cfbddaba
-/
lemma integrable_gaussianCoordinateScoreSum
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    Integrable (gaussianCoordinateScoreSum A q N) (gaussianVec N) := by
  unfold gaussianCoordinateScoreSum
  exact integrable_finsetSum Finset.univ fun i _ =>
    integrable_gaussianOneCoordinateScore_map_eval hA hq i

/-- The finite-coordinate product score has mean zero.
@isnad1 id=eq.2h3v.s6.5617f90fcd5e from=translated src=- shape=8da61331 vocab=a688edfa
-/
lemma integral_gaussianCoordinateScoreSum_eq_zero
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    ∫ g, gaussianCoordinateScoreSum A q N g ∂gaussianVec N = 0 := by
  unfold gaussianCoordinateScoreSum
  rw [integral_finsetSum _ fun i _ =>
    integrable_gaussianOneCoordinateScore_map_eval hA hq i]
  simp_rw [integral_gaussianOneCoordinateScore_map_eval_eq_zero hA hq]
  simp

/-- The square of each evaluated coordinate score is integrable under the
product Gaussian law.
@isnad1 id=integrab.2h4v.s6.9b18664ea10a from=translated src=- shape=37e03c3a vocab=0c6dbd23
-/
lemma integrable_sq_gaussianOneCoordinateScore_map_eval
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) {N : ℕ} (i : Fin N) :
    Integrable
      (fun g : Fin N → ℝ =>
        gaussianOneCoordinateScore A q
          (gaussianOneCoordinateMap A q (g i)) ^ 2)
      (gaussianVec N) := by
  let f : ℝ → ℝ := fun x =>
    gaussianOneCoordinateScore A q
      (gaussianOneCoordinateMap A q x) ^ 2
  refine Integrable.comp_measurable
    (f := fun g : Fin N → ℝ => g i) (g := f) ?_
      (measurable_pi_apply i)
  unfold gaussianVec
  rw [Measure.pi_map_eval]
  simpa only [measure_univ, Finset.prod_const_one, one_smul, f] using
    (integrable_sq_gaussianOneCoordinateScore_map_and_integral_eq hA hq).1

/-- The evaluated one-coordinate score belongs to `L²` under the standard
Gaussian law.
@isnad1 id=memlp.2h2v.s6.4eb16bfc25e0 from=translated src=- shape=132394e3 vocab=26a5eab2
-/
lemma memLp_two_gaussianOneCoordinateScore_map
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    MemLp
      (fun x : ℝ =>
        gaussianOneCoordinateScore A q
          (gaussianOneCoordinateMap A q x))
      2 (gaussianReal 0 1) :=
  (memLp_two_iff_integrable_sq
    (integrable_gaussianOneCoordinateScore_map hA hq).1).2
    (integrable_sq_gaussianOneCoordinateScore_map_and_integral_eq hA hq).1

/-- The variance of one evaluated score equals its Fisher information.
@isnad1 id=eq.2h2v.s6.8cd1ad5ffa73 from=translated src=- shape=a3409e41 vocab=66999a23
-/
lemma variance_gaussianOneCoordinateScore_map
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    Var[fun x : ℝ =>
        gaussianOneCoordinateScore A q
          (gaussianOneCoordinateMap A q x);
      gaussianReal 0 1] = 1 / (2 * q ^ 2) := by
  rw [variance_eq_integral
    (integrable_gaussianOneCoordinateScore_map hA hq).aemeasurable,
    integral_gaussianOneCoordinateScore_map_eq_zero hA hq]
  simpa using integral_sq_gaussianOneCoordinateScore_map hA hq

/-- The square of the finite-coordinate product score is integrable.
@isnad1 id=integrab.2h3v.s6.0b6dacc7716a from=translated src=- shape=7a5dcfe2 vocab=bb093d69
-/
lemma integrable_sq_gaussianCoordinateScoreSum
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    Integrable (fun g => gaussianCoordinateScoreSum A q N g ^ 2)
      (gaussianVec N) := by
  have hi (i : Fin N) :
      MemLp
        (fun g : Fin N → ℝ =>
          gaussianOneCoordinateScore A q
            (gaussianOneCoordinateMap A q (g i)))
        2 (gaussianVec N) :=
    (memLp_two_iff_integrable_sq
      (integrable_gaussianOneCoordinateScore_map_eval hA hq i).1).2
      (integrable_sq_gaussianOneCoordinateScore_map_eval hA hq i)
  unfold gaussianCoordinateScoreSum
  exact (memLp_finsetSum Finset.univ fun i _ => hi i).integrable_sq

/-- The product score has Fisher information `N/(2q²)`.
@isnad1 id=eq.2h3v.s7.b29e06f13b3b from=translated src=- shape=216e5a28 vocab=adb1eae5
-/
lemma integral_sq_gaussianCoordinateScoreSum
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    ∫ g, gaussianCoordinateScoreSum A q N g ^ 2 ∂gaussianVec N =
      N / (2 * q ^ 2) := by
  let f : ℝ → ℝ := fun x =>
    gaussianOneCoordinateScore A q (gaussianOneCoordinateMap A q x)
  have hf : ∀ _ : Fin N, MemLp f 2 (gaussianReal 0 1) :=
    fun _ => memLp_two_gaussianOneCoordinateScore_map hA hq
  have hvariance := variance_sum_pi (μ := fun _ : Fin N => gaussianReal 0 1)
    (X := fun _ => f) hf
  have hsumVariance :
      Var[gaussianCoordinateScoreSum A q N; gaussianVec N] =
        ∑ _ : Fin N, 1 / (2 * q ^ 2) := by
    rw [show gaussianCoordinateScoreSum A q N =
        ∑ i : Fin N, fun g : Fin N → ℝ =>
          gaussianOneCoordinateScore A q
            (gaussianOneCoordinateMap A q (g i)) by
      funext g
      simp only [gaussianCoordinateScoreSum, Finset.sum_apply]]
    simpa only [gaussianVec, f,
      variance_gaussianOneCoordinateScore_map hA hq] using hvariance
  rw [variance_eq_integral
      (integrable_gaussianCoordinateScoreSum hA hq N).aemeasurable,
    integral_gaussianCoordinateScoreSum_eq_zero hA hq N] at hsumVariance
  simpa [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, mul_assoc] using
    hsumVariance

/-- The absolute product score is integrable.
@isnad1 id=integrab.2h3v.s6.b70888575f5e from=translated src=- shape=3133dd2f vocab=095ca0b1
-/
lemma integrable_abs_gaussianCoordinateScoreSum
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    Integrable (fun g => |gaussianCoordinateScoreSum A q N g|)
      (gaussianVec N) :=
  (integrable_gaussianCoordinateScoreSum hA hq N).abs

/-- The product score has the paper's `L¹` bound
`√N / (√2 q)`.
@isnad1 id=le.2h3v.s6.6d74351fa5a1 from=translated src=- shape=fdb385d7 vocab=be146e29
-/
lemma integral_abs_gaussianCoordinateScoreSum_le
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    ∫ g, |gaussianCoordinateScoreSum A q N g| ∂gaussianVec N ≤
      Real.sqrt N / (Real.sqrt 2 * q) := by
  have hmem :
      MemLp (gaussianCoordinateScoreSum A q N) 2 (gaussianVec N) :=
    (memLp_two_iff_integrable_sq
      (integrable_gaussianCoordinateScoreSum hA hq N).1).2
      (integrable_sq_gaussianCoordinateScoreSum hA hq N)
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hmemReal :
      MemLp (gaussianCoordinateScoreSum A q N)
        (ENNReal.ofReal (2 : ℝ)) (gaussianVec N) := by
    simpa only [ENNReal.ofReal_ofNat] using hmem
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (μ := gaussianVec N) hholder hmemReal
      (memLp_const (1 : ℝ))
  have hsqrt :
      ∫ g, |gaussianCoordinateScoreSum A q N g| ∂gaussianVec N ≤
        Real.sqrt
          (∫ g, gaussianCoordinateScoreSum A q N g ^ 2 ∂gaussianVec N) := by
    simpa only [Real.norm_eq_abs, abs_one, mul_one, ENNReal.ofReal_ofNat,
      Real.rpow_two, sq_abs, integral_const, probReal_univ, one_smul,
      one_pow, Real.one_rpow, Real.sqrt_eq_rpow] using hcs
  rw [integral_sq_gaussianCoordinateScoreSum hA hq N] at hsqrt
  calc
    ∫ g, |gaussianCoordinateScoreSum A q N g| ∂gaussianVec N
        ≤ Real.sqrt (N / (2 * q ^ 2)) := hsqrt
    _ = Real.sqrt N / Real.sqrt (2 * q ^ 2) := by
      rw [Real.sqrt_div (by positivity)]
    _ = Real.sqrt N / (Real.sqrt 2 * Real.sqrt (q ^ 2)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = Real.sqrt N / (Real.sqrt 2 * q) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]

/-- The Lebesgue density of the finite product of one-coordinate
observations. -/
noncomputable def gaussianProductDensity
    (A q : ℝ) (N : ℕ) (y : Fin N → ℝ) : ℝ :=
  ∏ i, gaussianOneCoordinateDensity A q (y i)

/-- The score of the finite product density in observation coordinates. -/
noncomputable def gaussianProductScore
    (A q : ℝ) (N : ℕ) (y : Fin N → ℝ) : ℝ :=
  ∑ i, gaussianOneCoordinateScore A q (y i)

/-- The finite product observation density is Borel measurable.
@isnad1 id=measurab.0h3v.s4.fbc3013fb9e3 from=translated src=- shape=30b8ceaa vocab=1f9d4f2e
-/
lemma measurable_gaussianProductDensity (A q : ℝ) (N : ℕ) :
    Measurable (gaussianProductDensity A q N) := by
  classical
  unfold gaussianProductDensity
  exact Finset.measurable_prod Finset.univ fun i _ =>
    (measurable_gaussianOneCoordinateDensity A q).comp
      (measurable_pi_apply i)

/-- The finite product observation score is Borel measurable.
@isnad1 id=measurab.0h3v.s4.4a4b5c89d269 from=translated src=- shape=30b8ceaa vocab=73765df2
-/
lemma measurable_gaussianProductScore (A q : ℝ) (N : ℕ) :
    Measurable (gaussianProductScore A q N) := by
  classical
  unfold gaussianProductScore
  exact Finset.measurable_sum Finset.univ fun i _ =>
    (measurable_gaussianOneCoordinateScore A q).comp
      (measurable_pi_apply i)

/-- Score times product density is jointly Borel measurable in the parameter
and observation vector.
@isnad1 id=measurab.0h2v.s6.deacee7f6ed0 from=translated src=- shape=24bbed33 vocab=1bbfd3af
-/
lemma measurable_gaussianProductScore_mul_density (A : ℝ) (N : ℕ) :
    Measurable
      (fun p : ℝ × (Fin N → ℝ) =>
        gaussianProductScore A p.1 N p.2 *
          gaussianProductDensity A p.1 N p.2) := by
  classical
  apply Measurable.mul
  · unfold gaussianProductScore
    apply Finset.measurable_sum
    intro i _
    unfold gaussianOneCoordinateScore Real.artanh
    fun_prop
  · unfold gaussianProductDensity
    apply Finset.measurable_prod
    intro i _
    unfold gaussianOneCoordinateDensity
    apply Measurable.ite
    · exact measurableSet_Ioo.preimage
        ((measurable_pi_apply i).comp measurable_snd)
    · unfold gaussianOneCoordinateDensityFormula Real.artanh
      fun_prop
    · fun_prop

/-- The `q`-derivative of the globally extended one-coordinate density
factors as score times density. Outside the fixed support `(0,1)`, both sides
vanish identically.
@isnad1 id=hasderiv.2h3v.s6.eae916367a8f from=translated src=- shape=60af9ef6 vocab=388d3174
-/
lemma hasDerivAt_gaussianOneCoordinateDensity_q
    {A q y : ℝ} (hA : 0 < A) (hq : 0 < q) :
    HasDerivAt
      (fun r => gaussianOneCoordinateDensity A r y)
      (gaussianOneCoordinateScore A q y *
        gaussianOneCoordinateDensity A q y) q := by
  by_cases hy : y ∈ Set.Ioo (0 : ℝ) 1
  · have hformula :=
      hasDerivAt_gaussianOneCoordinateDensityFormula_q
        (y := y) hA hq
    have heq :
        (fun r => gaussianOneCoordinateDensity A r y) =ᶠ[nhds q]
          fun r => gaussianOneCoordinateDensityFormula A r y :=
      Filter.Eventually.of_forall fun r =>
        gaussianOneCoordinateDensity_eq_formula A r hy
    have h := hformula.congr_of_eventuallyEq heq
    simpa only [gaussianOneCoordinateDensity_eq_formula A q hy] using h
  · simpa [gaussianOneCoordinateDensity, hy] using
      (hasDerivAt_const (x := q) (0 : ℝ))

/-- The `q`-derivative of the finite product density factors globally as
score times density.
@isnad1 id=hasderiv.2h4v.s6.c8b3ecd27054 from=translated src=- shape=988843d6 vocab=1ed16c39
-/
lemma hasDerivAt_gaussianProductDensity_q
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) {N : ℕ} {y : Fin N → ℝ} :
    HasDerivAt
      (fun r => gaussianProductDensity A r N y)
      (gaussianProductScore A q N y * gaussianProductDensity A q N y) q := by
  classical
  let d : Fin N → ℝ → ℝ :=
    fun i r => gaussianOneCoordinateDensity A r (y i)
  let s : Fin N → ℝ :=
    fun i => gaussianOneCoordinateScore A q (y i)
  have hd (i : Fin N) :
      HasDerivAt (d i) (s i * d i q) q := by
    simpa only [d, s] using
      hasDerivAt_gaussianOneCoordinateDensity_q
        (y := y i) hA hq
  have hprod := HasDerivAt.fun_finsetProd
    (u := Finset.univ) (f := d)
    (f' := fun i => s i * d i q)
    (fun i _ => hd i)
  have hfactor :
      (∑ i ∈ (Finset.univ : Finset (Fin N)),
          (∏ j ∈ Finset.univ.erase i, d j q) • (s i * d i q)) =
        (∑ i, s i) * ∏ i, d i q := by
    simp only [smul_eq_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.prod_erase_mul Finset.univ (fun j => d j q) hi]
    ring
  rw [hfactor] at hprod
  simpa only [gaussianProductDensity, gaussianProductScore, d, s] using hprod

/-- The ordinary parameter derivative of the product density is its score
times density.
@isnad1 id=eq.2h4v.s6.9526808cf202 from=translated src=- shape=42d0c6e1 vocab=01af03b9
-/
lemma deriv_gaussianProductDensity_q
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) (y : Fin N → ℝ) :
    deriv (fun r => gaussianProductDensity A r N y) q =
      gaussianProductScore A q N y * gaussianProductDensity A q N y :=
  (hasDerivAt_gaussianProductDensity_q hA hq).deriv

/-- For a fixed observation vector, score times product density varies
continuously with the positive parameter.
@isnad1 id=continuo.2h4v.s6.ac9d27e73fd5 from=translated src=- shape=f3fccf29 vocab=0cdd1a00
-/
lemma continuousAt_gaussianProductScore_mul_density_q
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) (y : Fin N → ℝ) :
    ContinuousAt
      (fun r => gaussianProductScore A r N y *
        gaussianProductDensity A r N y) q := by
  unfold gaussianProductScore gaussianProductDensity
  apply ContinuousAt.mul
  · apply tendsto_finsetSum
    intro i _
    unfold gaussianOneCoordinateScore
    change ContinuousAt
      (fun r => -(1 / (2 * r)) +
        Real.artanh (Real.sqrt (y i)) ^ 2 / (2 * A ^ 2 * r ^ 2)) q
    fun_prop (disch := positivity)
  · apply tendsto_finsetProd
    intro i _
    by_cases hy : y i ∈ Set.Ioo (0 : ℝ) 1
    · simp only [gaussianOneCoordinateDensity, ite_eq_left hy]
      unfold gaussianOneCoordinateDensityFormula
      change ContinuousAt
        (fun r =>
          (A * Real.sqrt (2 * Real.pi * r))⁻¹ *
            (Real.sqrt (y i) * (1 - y i))⁻¹ *
              Real.exp
                (-(Real.artanh (Real.sqrt (y i))) ^ 2 /
                  (2 * A ^ 2 * r))) q
      fun_prop (disch := positivity)
    · simp [gaussianOneCoordinateDensity, hy]

/-- Coordinatewise transformation from standard Gaussian samples to the
finite product observation. -/
noncomputable def gaussianProductObservationMap
    (A q : ℝ) (N : ℕ) (g : Fin N → ℝ) : Fin N → ℝ :=
  fun i => gaussianOneCoordinateMap A q (g i)

/-- Coordinate averaging on the finite product observation space. -/
noncomputable def gaussianProductAverage
    (N : ℕ) (y : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, y i

/-- The product law of the one-coordinate observation densities. -/
noncomputable def gaussianProductObservationMeasure
    (A q : ℝ) (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ : Fin N =>
    volume.withDensity
      (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y))

/-- The coordinatewise product observation map is Borel measurable.
@isnad1 id=measurab.0h3v.s5.b3b19202ba75 from=translated src=- shape=e793cb3f vocab=3af1930b
-/
lemma measurable_gaussianProductObservationMap (A q : ℝ) (N : ℕ) :
    Measurable (gaussianProductObservationMap A q N) := by
  have hcoord : Measurable (gaussianOneCoordinateMap A q) := by
    unfold gaussianOneCoordinateMap
    simp_rw [Real.tanh_eq]
    fun_prop
  exact measurable_pi_lambda _ fun i =>
    hcoord.comp (measurable_pi_apply i)

/-- Coordinate averaging is Borel measurable.
@isnad1 id=measurab.0h1v.s4.04c4edd970f0 from=translated src=- shape=bbef8654 vocab=46dda61f
-/
lemma measurable_gaussianProductAverage (N : ℕ) :
    Measurable (gaussianProductAverage N) := by
  unfold gaussianProductAverage
  fun_prop

/-- Averaging the transformed observation coordinates is exactly the scalar
Gaussian radius update.
@isnad1 id=eq.0h4v.s4.2253aba3014d from=translated src=- shape=9daec38c vocab=e85c63ef
-/
lemma gaussianProductAverage_observationMap
    (A q : ℝ) (N : ℕ) (g : Fin N → ℝ) :
    gaussianProductAverage N (gaussianProductObservationMap A q N g) =
      Fmap A N q g := by
  rfl

/-- The coordinatewise observation pushforward is the product of the
one-coordinate `withDensity` laws.
@isnad1 id=eq.2h3v.s6.cc336489e357 from=translated src=- shape=6a3f5b13 vocab=aeff2a05
-/
lemma map_gaussianProductObservationMap_eq
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    Measure.map (gaussianProductObservationMap A q N) (gaussianVec N) =
      gaussianProductObservationMeasure A q N := by
  unfold gaussianProductObservationMap gaussianProductObservationMeasure
  unfold gaussianVec
  rw [Measure.pi_map_pi fun _ =>
    (by
      unfold gaussianOneCoordinateMap
      simp_rw [Real.tanh_eq]
      fun_prop :
      Measurable (gaussianOneCoordinateMap A q)).aemeasurable]
  congr 1
  funext i
  exact map_gaussianOneCoordinateMap_eq_withDensity hA hq

/-- Pushing the finite product observation law through coordinate averaging
recovers the scalar squared-radius transition law.
@isnad1 id=eq.2h3v.s6.c931e5bba4f9 from=translated src=- shape=48ccd9a4 vocab=f4263610
-/
lemma map_gaussianProductAverage_observationMeasure_eq_Kchain
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    Measure.map (gaussianProductAverage N)
        (gaussianProductObservationMeasure A q N) =
      Kchain A N q := by
  rw [← map_gaussianProductObservationMap_eq hA hq N,
    Measure.map_map (measurable_gaussianProductAverage N)
      (measurable_gaussianProductObservationMap A q N),
    Kchain_apply]
  congr 1

/-- Evaluating the observation-space product score on transformed Gaussian
coordinates gives the Gaussian-coordinate score sum.
@isnad1 id=eq.0h4v.s4.429bf310022e from=translated src=- shape=5ddc812c vocab=8ab80ee1
-/
lemma gaussianProductScore_observationMap
    (A q : ℝ) (N : ℕ) (g : Fin N → ℝ) :
    gaussianProductScore A q N (gaussianProductObservationMap A q N g) =
      gaussianCoordinateScoreSum A q N g := by
  rfl

/-- The absolute product-score integral under the observation law is the
Gaussian-coordinate absolute-score integral.
@isnad1 id=eq.2h3v.s6.5479d20157a5 from=translated src=- shape=322d7fd9 vocab=b4c984e9
-/
lemma integral_abs_gaussianProductScore_eq
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    ∫ y, |gaussianProductScore A q N y|
        ∂gaussianProductObservationMeasure A q N =
      ∫ g, |gaussianCoordinateScoreSum A q N g| ∂gaussianVec N := by
  rw [← map_gaussianProductObservationMap_eq hA hq N]
  have hmap :=
    integral_map
      (μ := gaussianVec N) (φ := gaussianProductObservationMap A q N)
      (f := fun y => |gaussianProductScore A q N y|)
      (measurable_gaussianProductObservationMap A q N).aemeasurable
      ((measurable_gaussianProductScore A q N).abs.aestronglyMeasurable)
  rw [hmap]
  congr 1

/-- The observation-space product score inherits the sharp `L¹` bound.
@isnad1 id=le.2h3v.s6.79423549ea54 from=translated src=- shape=34ae5c1e vocab=42cd0f71
-/
lemma integral_abs_gaussianProductScore_le
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    ∫ y, |gaussianProductScore A q N y|
        ∂gaussianProductObservationMeasure A q N ≤
      Real.sqrt N / (Real.sqrt 2 * q) := by
  rw [integral_abs_gaussianProductScore_eq hA hq N]
  exact integral_abs_gaussianCoordinateScoreSum_le hA hq N

/-- The one-coordinate observation density is Lebesgue integrable.
@isnad1 id=integrab.2h2v.s5.f2164b457cfc from=translated src=- shape=743a1cb3 vocab=d2f72a4e
-/
lemma integrable_gaussianOneCoordinateDensity
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    Integrable (gaussianOneCoordinateDensity A q) volume := by
  have hmeas : AEStronglyMeasurable
      (gaussianOneCoordinateDensity A q) volume :=
    (measurable_gaussianOneCoordinateDensity A q).aestronglyMeasurable
  have hnonneg :
      0 ≤ᵐ[volume] gaussianOneCoordinateDensity A q :=
    Filter.Eventually.of_forall
      (gaussianOneCoordinateDensity_nonneg hA hq)
  rw [← lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg]
  have hmap : Measurable (gaussianOneCoordinateMap A q) := by
    unfold gaussianOneCoordinateMap
    simp_rw [Real.tanh_eq]
    fun_prop
  have hlin :
      ∫⁻ x, ENNReal.ofReal (gaussianOneCoordinateDensity A q x) ∂volume =
        1 := by
    calc
      _ = (volume.withDensity
          (fun x => ENNReal.ofReal (gaussianOneCoordinateDensity A q x)))
          Set.univ := by
        rw [withDensity_apply _ MeasurableSet.univ]
        simp
      _ = Measure.map (gaussianOneCoordinateMap A q)
          (gaussianReal 0 1) Set.univ := by
        rw [map_gaussianOneCoordinateMap_eq_withDensity hA hq]
      _ = gaussianReal 0 1 Set.univ := by
        rw [Measure.map_apply hmap MeasurableSet.univ]
        simp
      _ = 1 := measure_univ
  rw [hlin]
  exact ENNReal.one_ne_top

/-- The finite product observation density is Lebesgue integrable.
@isnad1 id=integrab.2h3v.s6.399424a11b3e from=translated src=- shape=f7d17228 vocab=28cfe54d
-/
lemma integrable_gaussianProductDensity
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    Integrable (gaussianProductDensity A q N) volume := by
  classical
  unfold gaussianProductDensity
  simpa only [volume_pi] using
    (Integrable.fintype_prod fun _ : Fin N =>
      integrable_gaussianOneCoordinateDensity hA hq)

/-- The product of the one-coordinate observation laws has the product
density with respect to Lebesgue measure on the finite product space.
@isnad1 id=eq.2h3v.s6.fcc3358832d8 from=translated src=- shape=820e98c0 vocab=1455c9c5
-/
lemma gaussianProductObservationMeasure_eq_withDensity
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    gaussianProductObservationMeasure A q N =
      volume.withDensity
        (fun y => ENNReal.ofReal (gaussianProductDensity A q N y)) := by
  classical
  unfold gaussianProductObservationMeasure
  rw [volume_pi]
  apply Measure.pi_eq
  intro s hs
  let f : ℝ → ℝ := gaussianOneCoordinateDensity A q
  let F : (Fin N → ℝ) → ℝ := fun y => ∏ i, f (y i)
  have hf : Integrable f volume := by
    simpa only [f] using integrable_gaussianOneCoordinateDensity hA hq
  have hf_nonneg (x : ℝ) : 0 ≤ f x := by
    exact gaussianOneCoordinateDensity_nonneg hA hq x
  have hF : Integrable F (Measure.pi fun _ : Fin N => (volume : Measure ℝ)) := by
    exact Integrable.fintype_prod fun _ => hf
  have hF_nonneg (y : Fin N → ℝ) : 0 ≤ F y := by
    exact Finset.prod_nonneg fun i _ => hf_nonneg (y i)
  have hrect : MeasurableSet (Set.univ.pi s) :=
    MeasurableSet.univ_pi hs
  have hindicator :
      (Set.univ.pi s).indicator F =
        fun y : Fin N → ℝ => ∏ i, (s i).indicator f (y i) := by
    funext y
    by_cases hy : y ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hy]
      have hmem : ∀ i, y i ∈ s i := by
        simpa only [Set.mem_pi, Set.mem_univ, forall_const] using hy
      apply Finset.prod_congr rfl
      intro i _
      rw [Set.indicator_of_mem (hmem i)]
    · rw [Set.indicator_of_notMem hy]
      have hnot : ∃ i, y i ∉ s i := by
        simpa only [Set.mem_pi, Set.mem_univ, forall_const, not_forall] using hy
      obtain ⟨i, hi⟩ := hnot
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Set.indicator_of_notMem hi]
  have hreal :
      ∫ y in Set.univ.pi s, F y
          ∂(Measure.pi fun _ : Fin N => (volume : Measure ℝ)) =
        ∏ i, ∫ x in s i, f x := by
    rw [← integral_indicator hrect, hindicator,
      integral_fintype_prod_eq_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [integral_indicator (hs i)]
  have hcoord (i : Fin N) :
      ENNReal.ofReal (∫ x in s i, f x) =
        (volume.withDensity
          (fun x => ENNReal.ofReal (gaussianOneCoordinateDensity A q x)))
          (s i) := by
    rw [withDensity_apply _ (hs i),
      ← ofReal_integral_eq_lintegral_ofReal
        (hf.integrableOn) (Filter.Eventually.of_forall hf_nonneg)]
  rw [withDensity_apply _ hrect]
  change (∫⁻ y in Set.univ.pi s, ENNReal.ofReal (F y)
      ∂(Measure.pi fun _ : Fin N => (volume : Measure ℝ))) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hF.integrableOn
      (Filter.Eventually.of_forall hF_nonneg),
    hreal, ENNReal.ofReal_prod_of_nonneg]
  · simp_rw [hcoord]
  · intro i _
    exact integral_nonneg fun x => hf_nonneg x

/-- The finite product observation density is nonnegative.
@isnad1 id=le.2h4v.s5.5006df055e0c from=translated src=- shape=df793d21 vocab=7340419d
-/
lemma gaussianProductDensity_nonneg
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ)
    (y : Fin N → ℝ) :
    0 ≤ gaussianProductDensity A q N y := by
  unfold gaussianProductDensity
  exact Finset.prod_nonneg fun i _ =>
    gaussianOneCoordinateDensity_nonneg hA hq (y i)

/-- The real mass of a measurable set under the finite product observation
law is the restricted integral of its product density.
@isnad1 id=eq.3h4v.s7.3b75cb32f886 from=translated src=- shape=6d127a61 vocab=f2bb90c3
-/
lemma gaussianProductObservationMeasure_apply_toReal
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ)
    {s : Set (Fin N → ℝ)} (hs : MeasurableSet s) :
    (gaussianProductObservationMeasure A q N s).toReal =
      ∫ y in s, gaussianProductDensity A q N y ∂volume := by
  rw [gaussianProductObservationMeasure_eq_withDensity hA hq N,
    withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_gaussianProductDensity hA hq N).integrableOn
      (Filter.Eventually.of_forall
        (gaussianProductDensity_nonneg hA hq N)),
    ENNReal.toReal_ofReal]
  exact integral_nonneg fun y =>
    gaussianProductDensity_nonneg hA hq N y

/-- The product score is integrable under the finite product observation
law.
@isnad1 id=integrab.2h3v.s6.d849f6313399 from=translated src=- shape=811c0ca4 vocab=a633dd9f
-/
lemma integrable_gaussianProductScore_observationMeasure
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    Integrable (gaussianProductScore A q N)
      (gaussianProductObservationMeasure A q N) := by
  rw [← map_gaussianProductObservationMap_eq hA hq N,
    integrable_map_measure
      (measurable_gaussianProductScore A q N).aestronglyMeasurable
      (measurable_gaussianProductObservationMap A q N).aemeasurable]
  exact (integrable_gaussianCoordinateScoreSum hA hq N).congr
    (Filter.Eventually.of_forall fun g =>
      (gaussianProductScore_observationMap A q N g).symm)

/-- The global parameter derivative of the product density is Lebesgue
integrable.
@isnad1 id=integrab.2h3v.s6.1409494e15ef from=translated src=- shape=1777f004 vocab=d43ad19a
-/
lemma integrable_gaussianProductScore_mul_density
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    Integrable
      (fun y => gaussianProductScore A q N y *
        gaussianProductDensity A q N y) volume := by
  have hobs :=
    integrable_gaussianProductScore_observationMeasure hA hq N
  rw [gaussianProductObservationMeasure_eq_withDensity hA hq N] at hobs
  have hsmul :=
    (integrable_withDensity_iff_integrable_smul'
      ((measurable_gaussianProductDensity A q N).ennreal_ofReal)
      (Filter.Eventually.of_forall fun y => by simp)).1 hobs
  apply hsmul.congr
  filter_upwards with y
  rw [ENNReal.toReal_ofReal (gaussianProductDensity_nonneg hA hq N y)]
  simp only [smul_eq_mul, mul_comm]

/-- Integrating the global score derivative recovers the pointwise
difference of product densities at two positive parameters.
@isnad1 id=eq.3h5v.s6.e4e93ec63ddf from=translated src=- shape=ab83cecb vocab=964f9ffa
-/
lemma intervalIntegral_gaussianProductScore_mul_density_eq_sub
    {A q₀ q₁ : ℝ} (hA : 0 < A) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (N : ℕ) (y : Fin N → ℝ) :
    ∫ r in q₀..q₁, gaussianProductScore A r N y *
        gaussianProductDensity A r N y =
      gaussianProductDensity A q₁ N y -
        gaussianProductDensity A q₀ N y := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro r hr
    exact hasDerivAt_gaussianProductDensity_q hA
      (lt_of_lt_of_le (lt_min hq₀ hq₁) hr.1)
  · apply ContinuousOn.intervalIntegrable
    intro r hr
    exact
      (continuousAt_gaussianProductScore_mul_density_q hA
        (lt_of_lt_of_le (lt_min hq₀ hq₁) hr.1) N y).continuousWithinAt

/-- The pointwise density difference is bounded by the absolute parameter
derivative integrated over the unoriented interval between the parameters.
@isnad1 id=le.3h5v.s6.24812fcdc6f2 from=translated src=- shape=988bbcea vocab=cc45b701
-/
lemma abs_gaussianProductDensity_sub_le_integral_abs
    {A q₀ q₁ : ℝ} (hA : 0 < A) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (N : ℕ) (y : Fin N → ℝ) :
    |gaussianProductDensity A q₁ N y -
        gaussianProductDensity A q₀ N y| ≤
      ∫ r in Set.uIoc q₀ q₁,
        |gaussianProductScore A r N y *
          gaussianProductDensity A r N y| := by
  rw [← intervalIntegral_gaussianProductScore_mul_density_eq_sub
    hA hq₀ hq₁ N y]
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_integral_norm_uIoc
      (f := fun r => gaussianProductScore A r N y *
        gaussianProductDensity A r N y)
      (a := q₀) (b := q₁))

/-- The absolute score integral under the observation law is the Lebesgue
integral of absolute score times product density.
@isnad1 id=eq.2h3v.s7.460b66e1fa01 from=translated src=- shape=33606586 vocab=7baaa4da
-/
lemma integral_abs_gaussianProductScore_mul_density_eq
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    ∫ y, |gaussianProductScore A q N y| *
        gaussianProductDensity A q N y ∂volume =
      ∫ y, |gaussianProductScore A q N y|
        ∂gaussianProductObservationMeasure A q N := by
  rw [gaussianProductObservationMeasure_eq_withDensity hA hq N,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_gaussianProductDensity A q N).ennreal_ofReal)
      (Filter.Eventually.of_forall fun y => by simp)
      (fun y => |gaussianProductScore A q N y|)]
  apply integral_congr_ae
  filter_upwards with y
  rw [ENNReal.toReal_ofReal (gaussianProductDensity_nonneg hA hq N y)]
  simp only [smul_eq_mul, mul_comm]

/-- The Lebesgue `L¹` norm of the product-density derivative has the sharp
score bound.
@isnad1 id=le.2h3v.s7.4ceeb4e21693 from=translated src=- shape=8cf580d1 vocab=b24b6ff3
-/
lemma integral_abs_gaussianProductScore_mul_density_le
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (N : ℕ) :
    ∫ y, |gaussianProductScore A q N y *
        gaussianProductDensity A q N y| ∂volume ≤
      Real.sqrt N / (Real.sqrt 2 * q) := by
  have heq :
      (fun y : Fin N → ℝ =>
        |gaussianProductScore A q N y *
          gaussianProductDensity A q N y|) =
        fun y =>
          |gaussianProductScore A q N y| *
            gaussianProductDensity A q N y := by
    funext y
    rw [abs_mul, abs_of_nonneg
      (gaussianProductDensity_nonneg hA hq N y)]
  rw [heq, integral_abs_gaussianProductScore_mul_density_eq hA hq N]
  exact integral_abs_gaussianProductScore_le hA hq N

/-- The derivative `L¹` bound is uniform over the unoriented interval between
two positive parameter values.
@isnad1 id=le.4h5v.s7.dffff9a2dab0 from=translated src=- shape=237eaa6c vocab=0850a409
-/
lemma integral_abs_gaussianProductScore_mul_density_le_uIcc
    {A q₀ q₁ r : ℝ} (hA : 0 < A) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hr : r ∈ Set.uIcc q₀ q₁) (N : ℕ) :
    ∫ y, |gaussianProductScore A r N y *
        gaussianProductDensity A r N y| ∂volume ≤
      Real.sqrt N / (Real.sqrt 2 * min q₀ q₁) := by
  have hmin : min q₀ q₁ ≤ r := by
    rw [Set.mem_uIcc] at hr
    rcases hr with hr | hr
    · exact (min_le_left q₀ q₁).trans hr.1
    · exact (min_le_right q₀ q₁).trans hr.1
  have hr_pos : 0 < r := (lt_min hq₀ hq₁).trans_le hmin
  refine (integral_abs_gaussianProductScore_mul_density_le
    hA hr_pos N).trans ?_
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg N)
    (mul_pos (Real.sqrt_pos.2 (by norm_num)) (lt_min hq₀ hq₁))
    (mul_le_mul_of_nonneg_left hmin (Real.sqrt_nonneg 2))

/-- The parameter derivative is jointly integrable on a bounded positive
parameter strip and the full observation space.
@isnad1 id=integrab.3h4v.s7.2a45c59ef432 from=translated src=- shape=5120a993 vocab=70e2010e
-/
lemma integrable_gaussianProductScore_mul_density_prod
    {A q₀ q₁ : ℝ} (hA : 0 < A) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (N : ℕ) :
    Integrable
      (fun p : ℝ × (Fin N → ℝ) =>
        gaussianProductScore A p.1 N p.2 *
          gaussianProductDensity A p.1 N p.2)
      ((volume.restrict (Set.uIoc q₀ q₁)).prod volume) := by
  let F : ℝ × (Fin N → ℝ) → ℝ :=
    fun p => gaussianProductScore A p.1 N p.2 *
      gaussianProductDensity A p.1 N p.2
  have hF : Measurable F := by
    simpa only [F] using measurable_gaussianProductScore_mul_density A N
  rw [integrable_prod_iff hF.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    have hrIcc : r ∈ Set.uIcc q₀ q₁ := Set.uIoc_subset_uIcc hr
    have hrpos : 0 < r :=
      (lt_min hq₀ hq₁).trans_le hrIcc.1
    simpa only [F] using
      integrable_gaussianProductScore_mul_density hA hrpos N
  · have houter :
        AEStronglyMeasurable
          (fun r => ∫ y, ‖F (r, y)‖ ∂volume)
          (volume.restrict (Set.uIoc q₀ q₁)) :=
      hF.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    apply
      (integrableOn_const
        (C := Real.sqrt N / (Real.sqrt 2 * min q₀ q₁))
        (by simp [Set.uIoc, Real.volume_Ioc])).mono' houter
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    have hrIcc : r ∈ Set.uIcc q₀ q₁ := Set.uIoc_subset_uIcc hr
    have hbound :=
      integral_abs_gaussianProductScore_mul_density_le_uIcc
        hA hq₀ hq₁ hrIcc N
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [F, Real.norm_eq_abs] using hbound

/-- The finite product observation densities are Lipschitz in `L¹`, with the
paper's score-tensorization constant.
@isnad1 id=le.3h4v.s7.787e6547f390 from=translated src=- shape=50d48c51 vocab=32ea1f5e
-/
lemma integral_abs_gaussianProductDensity_sub_le
    {A q₀ q₁ : ℝ} (hA : 0 < A) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (N : ℕ) :
    ∫ y, |gaussianProductDensity A q₁ N y -
        gaussianProductDensity A q₀ N y| ∂volume ≤
      Real.sqrt N / (Real.sqrt 2 * min q₀ q₁) * |q₁ - q₀| := by
  let G : ℝ → (Fin N → ℝ) → ℝ :=
    fun r y => |gaussianProductScore A r N y *
      gaussianProductDensity A r N y|
  have hprod :=
    integrable_gaussianProductScore_mul_density_prod hA hq₀ hq₁ N
  have hG :
      Integrable (Function.uncurry G)
        ((volume.restrict (Set.uIoc q₀ q₁)).prod volume) := by
    apply hprod.norm.congr
    filter_upwards with p
    rfl
  have hright :
      Integrable (fun y => ∫ r in Set.uIoc q₀ q₁, G r y ∂volume)
        volume := by
    simpa only [Function.uncurry] using hG.integral_prod_right
  have hdiff :
      Integrable
        (fun y => |gaussianProductDensity A q₁ N y -
          gaussianProductDensity A q₀ N y|) volume := by
    apply hright.mono'
      ((measurable_gaussianProductDensity A q₁ N).sub
        (measurable_gaussianProductDensity A q₀ N)).abs.aestronglyMeasurable
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_gaussianProductDensity_sub_le_integral_abs
      hA hq₀ hq₁ N y
  calc
    ∫ y, |gaussianProductDensity A q₁ N y -
        gaussianProductDensity A q₀ N y| ∂volume
        ≤ ∫ y, ∫ r in Set.uIoc q₀ q₁, G r y ∂volume ∂volume := by
      apply integral_mono hdiff hright
      intro y
      exact abs_gaussianProductDensity_sub_le_integral_abs
        hA hq₀ hq₁ N y
    _ = ∫ r in Set.uIoc q₀ q₁, ∫ y, G r y ∂volume ∂volume := by
      simpa only [Function.uncurry] using
        (integral_integral_swap hG).symm
    _ ≤ ∫ _r in Set.uIoc q₀ q₁,
          Real.sqrt N / (Real.sqrt 2 * min q₀ q₁) ∂volume := by
      apply integral_mono_ae hG.integral_prod_left
        (integrableOn_const (by simp [Set.uIoc, Real.volume_Ioc]))
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
      exact integral_abs_gaussianProductScore_mul_density_le_uIcc
        hA hq₀ hq₁ (Set.uIoc_subset_uIcc hr) N
    _ = Real.sqrt N / (Real.sqrt 2 * min q₀ q₁) * |q₁ - q₀| := by
      simp [Set.uIoc, max_sub_min_eq_abs, mul_comm]

/-- The finite product observation laws satisfy the sharp half-`L¹`
total-variation bound.
@isnad1 id=le.3h4v.s7.6ef995b748ef from=translated src=- shape=d2c23326 vocab=6c7e4596
-/
lemma tvDist_gaussianProductObservationMeasure_le
    {A q₀ q₁ : ℝ} (hA : 0 < A) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (N : ℕ) :
    tvDist (gaussianProductObservationMeasure A q₁ N)
        (gaussianProductObservationMeasure A q₀ N) ≤
      Real.sqrt N / (2 * Real.sqrt 2 * min q₀ q₁) * |q₁ - q₀| := by
  let f : (Fin N → ℝ) → ℝ :=
    fun y => gaussianProductDensity A q₁ N y -
      gaussianProductDensity A q₀ N y
  have hf : Integrable f volume := by
    exact (integrable_gaussianProductDensity hA hq₁ N).sub
      (integrable_gaussianProductDensity hA hq₀ N)
  have hmass (q : ℝ) (hq : 0 < q) :
      ∫ y, gaussianProductDensity A q N y ∂volume = 1 := by
    calc
      ∫ y, gaussianProductDensity A q N y ∂volume =
          ∫ y in Set.univ, gaussianProductDensity A q N y ∂volume := by
        simp
      _ = (gaussianProductObservationMeasure A q N Set.univ).toReal :=
        (gaussianProductObservationMeasure_apply_toReal
          hA hq N MeasurableSet.univ).symm
      _ = 1 := by
        rw [← map_gaussianProductObservationMap_eq hA hq N,
          Measure.map_apply
            (measurable_gaussianProductObservationMap A q N)
            MeasurableSet.univ]
        simp
  have htotal : ∫ y, f y ∂volume = 0 := by
    rw [integral_sub
      (integrable_gaussianProductDensity hA hq₁ N)
      (integrable_gaussianProductDensity hA hq₀ N),
      hmass q₁ hq₁, hmass q₀ hq₀, sub_self]
  unfold tvDist
  apply ciSup_le
  intro s
  rw [gaussianProductObservationMeasure_apply_toReal hA hq₁ N s.prop,
    gaussianProductObservationMeasure_apply_toReal hA hq₀ N s.prop,
    ← integral_sub
      (integrable_gaussianProductDensity hA hq₁ N).integrableOn
      (integrable_gaussianProductDensity hA hq₀ N).integrableOn]
  change |∫ y in s.1, f y ∂volume| ≤ _
  have hcomp :
      ∫ y in s.1ᶜ, f y ∂volume = -(∫ y in s.1, f y ∂volume) := by
    have hsplit := integral_add_compl s.prop hf
    linarith
  have hsbound :
      |∫ y in s.1, f y ∂volume| ≤
        ∫ y in s.1, |f y| ∂volume := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (μ := volume.restrict s.1) f)
  have hcbound :
      |∫ y in s.1ᶜ, f y ∂volume| ≤
        ∫ y in s.1ᶜ, |f y| ∂volume := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (μ := volume.restrict s.1ᶜ) f)
  have hcbound' :
      |∫ y in s.1, f y ∂volume| ≤
        ∫ y in s.1ᶜ, |f y| ∂volume := by
    rw [hcomp, abs_neg] at hcbound
    exact hcbound
  have habssplit :
      (∫ y in s.1, |f y| ∂volume) +
          ∫ y in s.1ᶜ, |f y| ∂volume =
        ∫ y, |f y| ∂volume :=
    integral_add_compl s.prop hf.abs
  have hhalf :
      2 * |∫ y in s.1, f y ∂volume| ≤
        ∫ y, |f y| ∂volume := by
    linarith
  have hl1 :=
    integral_abs_gaussianProductDensity_sub_le hA hq₀ hq₁ N
  change
    ∫ y, |f y| ∂volume ≤
      Real.sqrt N / (Real.sqrt 2 * min q₀ q₁) * |q₁ - q₀| at hl1
  calc
    |∫ y in s.1, f y ∂volume|
        ≤ (1 / 2 : ℝ) * ∫ y, |f y| ∂volume := by
      linarith
    _ ≤ (1 / 2 : ℝ) *
        (Real.sqrt N / (Real.sqrt 2 * min q₀ q₁) * |q₁ - q₀|) :=
      mul_le_mul_of_nonneg_left hl1 (by norm_num)
    _ = Real.sqrt N / (2 * Real.sqrt 2 * min q₀ q₁) *
        |q₁ - q₀| := by ring

/-- Paper-facing one-step score smoothing for the scalar squared-radius
kernel.
@isnad1 id=le.3h4v.s7.146d72e5cad8 from=translated src=- shape=25204ce3 vocab=33712a8a
-/
lemma tvDist_Kchain_apply_le_of_pos
    {A q₀ q₁ : ℝ} (hA : 0 < A) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (N : ℕ) :
    tvDist (Kchain A N q₁) (Kchain A N q₀) ≤
      Real.sqrt N / (2 * Real.sqrt 2 * min q₀ q₁) * |q₁ - q₀| := by
  let μ₁ := gaussianProductObservationMeasure A q₁ N
  let μ₀ := gaussianProductObservationMeasure A q₀ N
  haveI : IsProbabilityMeasure μ₁ := by
    dsimp only [μ₁]
    constructor
    rw [← map_gaussianProductObservationMap_eq hA hq₁ N,
      Measure.map_apply
        (measurable_gaussianProductObservationMap A q₁ N)
        MeasurableSet.univ]
    simp
  haveI : IsProbabilityMeasure μ₀ := by
    dsimp only [μ₀]
    constructor
    rw [← map_gaussianProductObservationMap_eq hA hq₀ N,
      Measure.map_apply
        (measurable_gaussianProductObservationMap A q₀ N)
        MeasurableSet.univ]
    simp
  calc
    tvDist (Kchain A N q₁) (Kchain A N q₀) =
        tvDist (Measure.map (gaussianProductAverage N) μ₁)
          (Measure.map (gaussianProductAverage N) μ₀) := by
      rw [map_gaussianProductAverage_observationMeasure_eq_Kchain
          hA hq₁ N,
        map_gaussianProductAverage_observationMeasure_eq_Kchain
          hA hq₀ N]
    _ ≤ tvDist μ₁ μ₀ :=
      tvDist_map_le μ₁ μ₀ (gaussianProductAverage N)
        (measurable_gaussianProductAverage N)
    _ ≤ Real.sqrt N / (2 * Real.sqrt 2 * min q₀ q₁) * |q₁ - q₀| :=
      tvDist_gaussianProductObservationMeasure_le hA hq₀ hq₁ N

end AbsorptionCutoff
