import Tengoku.SingularityCompleteLean.Singularity.ExponentialLattice
import Tengoku.Seed.Analysis.SpecialFunctions.ImproperIntegrals

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exponential decay of logarithmic Poisson profiles

These are elementary upper-half-plane kernel estimates. They do not identify
random-walk hitting densities with Poisson densities. A separate geometric
comparison is needed to apply the estimates to those hitting measures.
-/

noncomputable section
open MeasureTheory Set

namespace Singularity

/-- The upper-half-plane Poisson density at boundary coordinate u.-/
def halfPlanePoisson (x y u : ℝ) : ℝ :=
  y / (Real.pi * ((u - x) ^ 2 + y ^ 2))

/-- A finite constant controlling both tails after logarithmic change of variable.-/
def poissonEnvelopeConstant (x y : ℝ) : ℝ :=
  (2 * y ^ 2 + 2 * x ^ 2 + 1) / (Real.pi * y)

/--
@isnad1 id=lt.1h2v.s4.22ebfcc1d332 from=translated src=- shape=61bdc3e7 vocab=e48ec109
-/
theorem poissonEnvelopeConstant_pos (x : ℝ) {y : ℝ} (hy : 0 < y) :
    0 < poissonEnvelopeConstant x y := by
  unfold poissonEnvelopeConstant
  positivity

/--
@isnad1 id=le.1h3v.s4.1c7974ffa724 from=translated src=- shape=e0c7d5e6 vocab=8ddcb37c
-/
theorem halfPlanePoisson_nonneg (x : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    0 ≤ halfPlanePoisson x y u := by
  unfold halfPlanePoisson
  positivity

/-- A uniform rational bound for the Poisson kernel, with no sign restriction on u.
@isnad1 id=le.1h3v.s6.ddd3cd920de8 from=translated src=- shape=c6cf3eab vocab=066ab7c2
-/
theorem halfPlanePoisson_le (x : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    halfPlanePoisson x y u ≤ poissonEnvelopeConstant x y / (1 + u ^ 2) := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
  have hquad : 1 + u ^ 2 ≤ 2 * (u - x) ^ 2 + 2 * x ^ 2 + 1 := by
    nlinarith [sq_nonneg (u - 2 * x)]
  have hden : y ^ 2 * (1 + u ^ 2) ≤
      (2 * y ^ 2 + 2 * x ^ 2 + 1) * ((u - x) ^ 2 + y ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hquad (le_of_lt hy2)
    have hnon := mul_nonneg (show 0 ≤ 2 * x ^ 2 + 1 by positivity) (sq_nonneg (u - x))
    nlinarith [sq_nonneg (y ^ 2)]
  unfold halfPlanePoisson poissonEnvelopeConstant
  rw [div_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    y * (Real.pi * y * (1 + u ^ 2)) = Real.pi * (y ^ 2 * (1 + u ^ 2)) := by ring
    _ ≤ Real.pi * ((2 * y ^ 2 + 2 * x ^ 2 + 1) * ((u - x) ^ 2 + y ^ 2)) :=
      mul_le_mul_of_nonneg_left hden Real.pi_pos.le
    _ = (2 * y ^ 2 + 2 * x ^ 2 + 1) * (Real.pi * ((u - x) ^ 2 + y ^ 2)) := by ring

/-- The symmetric elementary envelope in logarithmic coordinates.
@isnad1 id=le.0h1v.s5.1125688c8182 from=translated src=- shape=aa40d5a2 vocab=12ec161a
-/
theorem exp_ratio_le_exp_neg_abs (t : ℝ) :
    Real.exp t / (1 + (Real.exp t) ^ 2) ≤ Real.exp (-|t|) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, div_le_iff₀ (by positivity)]
    have hp : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    have hpp : Real.exp (-t) * (Real.exp t) ^ 2 = Real.exp t := by
      rw [pow_two, ← mul_assoc, hp, one_mul]
    nlinarith [Real.exp_pos (-t)]
  · rw [abs_of_neg (lt_of_not_ge ht), neg_neg, div_le_iff₀ (by positivity)]
    nlinarith [Real.exp_pos t, mul_nonneg (Real.exp_pos t).le (sq_nonneg (Real.exp t))]

/-- Positive-side logarithmic density, including the Jacobian exp(t).-/
def logPoissonProfile (x y t : ℝ) : ℝ := Real.exp t * halfPlanePoisson x y (Real.exp t)

/--
@isnad1 id=le.1h3v.s4.6c77cb041483 from=translated src=- shape=e0c7d5e6 vocab=12da1eee
-/
theorem logPoissonProfile_nonneg (x : ℝ) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    0 ≤ logPoissonProfile x y t :=
  mul_nonneg (Real.exp_pos t).le (halfPlanePoisson_nonneg x hy _)

/-- Both logarithmic tails decay exponentially, with an explicit finite constant.
@isnad1 id=le.1h3v.s5.bafb2573aa5d from=translated src=- shape=8e509188 vocab=14b8d489
-/
theorem logPoissonProfile_decay (x : ℝ) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    logPoissonProfile x y t ≤ poissonEnvelopeConstant x y * Real.exp (-|t|) := by
  calc
    logPoissonProfile x y t ≤ Real.exp t *
        (poissonEnvelopeConstant x y / (1 + (Real.exp t) ^ 2)) :=
      mul_le_mul_of_nonneg_left (halfPlanePoisson_le x hy _) (Real.exp_pos t).le
    _ = poissonEnvelopeConstant x y * (Real.exp t / (1 + (Real.exp t) ^ 2)) := by ring
    _ ≤ poissonEnvelopeConstant x y * Real.exp (-|t|) :=
      mul_le_mul_of_nonneg_left (exp_ratio_le_exp_neg_abs t) (poissonEnvelopeConstant_pos x hy).le

/-- The negative-side profile is the positive-side profile with reflected center.
@isnad1 id=eq.0h3v.s5.a97108ba64b6 from=translated src=- shape=8a62c7f6 vocab=d4fc3b88
-/
theorem negative_logPoissonProfile (x y t : ℝ) :
    Real.exp t * halfPlanePoisson x y (-Real.exp t) = logPoissonProfile (-x) y t := by
  unfold logPoissonProfile halfPlanePoisson
  congr 2
  ring

/-- The exponential envelope is integrable on the whole logarithmic line.
@isnad1 id=integrab.0h0v.s5.10edc6429c6b from=translated src=- shape=0b72565c vocab=80595ee4
-/
theorem integrable_exp_neg_abs : Integrable (fun t : ℝ => Real.exp (-|t|)) := by
  have hl : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) (Iic 0) :=
    (integrableOn_exp_Iic 0).congr_fun (fun t ht => by simp [abs_of_nonpos (show t ≤ 0 from ht)]) measurableSet_Iic
  have hr : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).congr_fun (fun t ht => by rw [abs_of_pos ht]) measurableSet_Ioi
  have h := integrableOn_union.mpr ⟨hl, hr⟩
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

/-- Logarithmic Poisson profiles are integrable by the proved envelope.
@isnad1 id=integrab.1h2v.s5.95f3d170edb1 from=translated src=- shape=09749f8b vocab=02d623dd
-/
theorem logPoissonProfile_integrable (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (logPoissonProfile x y) := by
  have hc : Continuous (logPoissonProfile x y) := by
    unfold logPoissonProfile halfPlanePoisson
    fun_prop (disch := intro t; positivity)
  apply (integrable_exp_neg_abs.const_mul (poissonEnvelopeConstant x y)).mono'
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (logPoissonProfile_nonneg x hy t)]
    exact logPoissonProfile_decay x hy t)

/-- A bounded multiple of a Poisson profile inherits the explicit decay bound.
@isnad1 id=le.3h5v.s6.e7de8ec8ed8d from=translated src=- shape=363fa7da vocab=14b8d489
-/
theorem poisson_dominated_decay (x : ℝ) {y B : ℝ} (hy : 0 < y) (hB : 0 ≤ B)
    (k : ℝ → ℝ) (hk : ∀ t, k t ≤ B * logPoissonProfile x y t) (t : ℝ) :
    k t ≤ (B * poissonEnvelopeConstant x y) * Real.exp (-|t|) := by
  exact (hk t).trans ((mul_le_mul_of_nonneg_left (logPoissonProfile_decay x hy t) hB).trans_eq
    (mul_assoc _ _ _).symm)

/-- Measurable nonnegative densities dominated by a Poisson profile are integrable.
@isnad1 id=integrab.4h4v.s6.7031ade24f6b from=translated src=- shape=75d82efa vocab=21e306b6
-/
theorem poisson_dominated_integrable (x : ℝ) {y B : ℝ} (hy : 0 < y)
    (k : ℝ → ℝ) (hkm : AEStronglyMeasurable k) (hk0 : ∀ t, 0 ≤ k t)
    (hk : ∀ t, k t ≤ B * logPoissonProfile x y t) : Integrable k := by
  apply ((logPoissonProfile_integrable x hy).const_mul B).mono' hkm
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hk0 t)]
    exact hk t)

end Singularity
