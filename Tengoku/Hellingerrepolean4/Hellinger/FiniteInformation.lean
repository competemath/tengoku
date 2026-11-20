import Tengoku.Hellingerrepolean4.Hellinger.EntropyTransfer
import Tengoku.Seed.InformationTheory.KullbackLeibler.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.SumMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The genuine finite probability and KL-divergence model underlying the
posterior information expression. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set

namespace Hellinger.FiniteInformation

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

def weightedMeasure (p : α → ℝ) : Measure α :=
  ∑ a, ENNReal.ofReal (p a) • Measure.dirac a

/--
@isnad1 id=isfinite.0h2v.s4.daf97aca894c from=translated src=- shape=a1945fe4 vocab=a59f22ae
-/
instance weightedMeasure_isFinite (p : α → ℝ) : IsFiniteMeasure (weightedMeasure p) := by
  constructor
  simp only [weightedMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun a _ => ENNReal.ofReal_lt_top)

/--
@isnad1 id=eq.0h3v.s5.ac6190dd545a from=translated src=- shape=f3143b58 vocab=d360b0e5
-/
@[simp] theorem weightedMeasure_singleton (p : α → ℝ) (a : α) :
    weightedMeasure p {a} = ENNReal.ofReal (p a) := by
  classical
  simp [weightedMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply', Pi.single_apply]

/--
@isnad1 id=eq.1h3v.s5.32a40a6e06b9 from=translated src=- shape=8796280e vocab=5a9e90c8
-/
theorem weightedMeasure_real_singleton (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (a : α) :
    (weightedMeasure p).real {a} = p a := by
  rw [measureReal_def, weightedMeasure_singleton, ENNReal.toReal_ofReal (hp a)]

omit [MeasurableSingletonClass α] in
/--
@isnad1 id=eq.1h2v.s5.39e2797034d7 from=translated src=- shape=265424d5 vocab=a228da5e
-/
theorem weightedMeasure_univ (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    weightedMeasure p univ = ENNReal.ofReal (∑ a, p a) := by
  simp [weightedMeasure, Measure.finsetSum_apply, ← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a)]

/--
@isnad1 id=eq.1h3v.s6.dc8faf359391 from=translated src=- shape=4ad203bc vocab=0826c59b
-/
theorem weightedMeasure_integral (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (f : α → ℝ) :
    ∫ a, f a ∂weightedMeasure p = ∑ a, p a * f a := by
  rw [integral_fintype Integrable.of_finite]
  simp only [weightedMeasure_real_singleton p hp, smul_eq_mul]

/--
@isnad1 id=eq.3h3v.s6.1a583ced988a from=translated src=- shape=9cc761fa vocab=e9c50d06
-/
theorem weightedMeasure_eq_withDensity (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 ≤ q a) (hs : ∀ a, q a = 0 → p a = 0) :
    weightedMeasure p = (weightedMeasure q).withDensity (fun a => ENNReal.ofReal (p a / q a)) := by
  apply Measure.ext_of_singleton
  intro a
  rw [weightedMeasure_singleton, withDensity_apply _ (measurableSet_singleton a),
    lintegral_singleton, weightedMeasure_singleton]
  by_cases hqa : q a = 0
  · simp [hqa, hs a hqa]
  · rw [← ENNReal.ofReal_mul (div_nonneg (hp a) (hq a)), div_mul_cancel₀ _ hqa]

/--
@isnad1 id=absolute.3h3v.s6.42b874b40ca7 from=translated src=- shape=1fa971b7 vocab=953d181a
-/
theorem weightedMeasure_absolutelyContinuous (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 ≤ q a) (hs : ∀ a, q a = 0 → p a = 0) :
    weightedMeasure p ≪ weightedMeasure q := by
  rw [weightedMeasure_eq_withDensity p q hp hq hs]
  exact withDensity_absolutelyContinuous _ _

/--
@isnad1 id=eventual.3h3v.s6.a161c77fb60d from=translated src=- shape=6fbc62ca vocab=8965e073
-/
theorem weightedMeasure_llr (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 ≤ q a) (hs : ∀ a, q a = 0 → p a = 0) :
    llr (weightedMeasure p) (weightedMeasure q) =ᵐ[weightedMeasure p]
      fun a => Real.log (p a / q a) := by
  have hac := weightedMeasure_absolutelyContinuous p q hp hq hs
  have hd : (weightedMeasure p).rnDeriv (weightedMeasure q) =ᵐ[weightedMeasure q]
      fun a => ENNReal.ofReal (p a / q a) := by
    rw [weightedMeasure_eq_withDensity p q hp hq hs]
    exact Measure.rnDeriv_withDensity _ (measurable_of_countable _)
  filter_upwards [hac hd] with a ha
  simp only [llr, ha, ENNReal.toReal_ofReal (div_nonneg (hp a) (hq a))]

/--
@isnad1 id=ne.3h3v.s6.c6fa38c373a9 from=translated src=- shape=3b15e441 vocab=59aa5055
-/
theorem klDiv_weightedMeasure_ne_top (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 ≤ q a) (hs : ∀ a, q a = 0 → p a = 0) :
    InformationTheory.klDiv (weightedMeasure p) (weightedMeasure q) ≠ ∞ :=
  InformationTheory.klDiv_ne_top (weightedMeasure_absolutelyContinuous p q hp hq hs)
    Integrable.of_finite

/-- The finite KL sum is derived from mathlib's measure-theoretic KL
divergence, including absolute continuity and finiteness at zero masses.
@isnad1 id=eq.4h3v.s7.690a935ee568 from=translated src=- shape=86d1f084 vocab=1328983c
-/
theorem klDiv_weightedMeasure (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 ≤ q a) (hs : ∀ a, q a = 0 → p a = 0)
    (hm : (∑ a, p a) = ∑ a, q a) :
    (InformationTheory.klDiv (weightedMeasure p) (weightedMeasure q)).toReal =
      ∑ a, p a * Real.log (p a / q a) := by
  rw [InformationTheory.toReal_klDiv_of_measure_eq
    (weightedMeasure_absolutelyContinuous p q hp hq hs)
    (by rw [weightedMeasure_univ p hp, weightedMeasure_univ q hq, hm])]
  rw [integral_congr_ae (weightedMeasure_llr p q hp hq hs), weightedMeasure_integral p hp]

def signProbability (t : ℝ) (b : Bool) : ℝ :=
  if b then (1 - t) / 2 else (1 + t) / 2

/--
@isnad1 id=le.1h2v.s5.863cebab1aa5 from=translated src=- shape=3bdbe2db vocab=61414482
-/
theorem signProbability_nonneg {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (b : Bool) :
    0 ≤ signProbability t b := by
  cases b <;> simp only [signProbability, Bool.false_eq_true, ite_false, ite_true] <;> linarith [ht.1, ht.2]

/--
@isnad1 id=eq.0h1v.s4.53fb60c1d07d from=translated src=- shape=521cf472 vocab=cfff6d78
-/
theorem signProbability_sum (t : ℝ) : ∑ b : Bool, signProbability t b = 1 := by
  simp [signProbability]
  ring

open Hellinger.Fourier

/--
@isnad1 id=eq.0h3v.s5.7c788382c566 from=translated src=- shape=4060ae70 vocab=db066e21
-/
theorem mean_signProbability {Ω : Type*} [Fintype Ω] [Nonempty Ω] (u : Ω → ℝ) (b : Bool) :
    mean (fun y => signProbability (u y) b) = signProbability (mean u) b := by
  cases b
  · change mean (fun y => (1 + u y) / 2) = (1 + mean u) / 2
    simp only [div_eq_mul_inv]
    rw [mean_mul_const, mean_add, mean_const]
  · change mean (fun y => (1 - u y) / 2) = (1 - mean u) / 2
    simp only [div_eq_mul_inv]
    rw [mean_mul_const, mean_sub, mean_const]

/--
@isnad1 id=eq.2h4v.s6.db1dbb776e90 from=translated src=- shape=0cfe73ae vocab=bb73d923
-/
theorem signProbability_zero_of_mean_zero
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (u : Ω → ℝ)
    (hu : ∀ y, u y ∈ Icc (-1 : ℝ) 1) (b : Bool)
    (hm : signProbability (mean u) b = 0) (y : Ω) : signProbability (u y) b = 0 := by
  have hmean : mean (fun y => signProbability (u y) b) = 0 := by rw [mean_signProbability, hm]
  have hs : (∑ y, signProbability (u y) b) = 0 := by
    unfold mean at hmean
    exact (mul_eq_zero.mp hmean).resolve_left (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => signProbability_nonneg (hu y) b)).mp hs
    y (Finset.mem_univ y)

def posteriorMass {Ω : Type*} [Fintype Ω] (u : Ω → ℝ) (p : Bool × Ω) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * signProbability (u p.2) p.1

def productMass {Ω : Type*} [Fintype Ω] (u : Ω → ℝ) (p : Bool × Ω) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * signProbability (mean u) p.1

/--
@isnad1 id=le.1h3v.s5.90edb816f002 from=translated src=- shape=ad289fff vocab=ae3fbd57
-/
theorem posteriorMass_nonneg {Ω : Type*} [Fintype Ω]
    (u : Ω → ℝ) (hu : ∀ y, u y ∈ Icc (-1 : ℝ) 1) (p : Bool × Ω) :
    0 ≤ posteriorMass u p := mul_nonneg (by positivity) (signProbability_nonneg (hu p.2) p.1)

/--
@isnad1 id=le.1h3v.s5.e59050beeaa3 from=translated src=- shape=ff8b882d vocab=ad8eacf9
-/
theorem productMass_nonneg {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : Ω → ℝ) (hu : ∀ y, u y ∈ Icc (-1 : ℝ) 1) (p : Bool × Ω) :
    0 ≤ productMass u p :=
  mul_nonneg (by positivity) (signProbability_nonneg (EntropyTransfer.mean_mem_Icc hu) p.1)

/--
@isnad1 id=eq.2h3v.s6.d5a05a9a54eb from=translated src=- shape=3e29a052 vocab=97cd2530
-/
theorem posteriorMass_support {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : Ω → ℝ) (hu : ∀ y, u y ∈ Icc (-1 : ℝ) 1) (p : Bool × Ω)
    (hp : productMass u p = 0) : posteriorMass u p = 0 := by
  have hcard : (Fintype.card Ω : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hm := (mul_eq_zero.mp hp).resolve_left hcard
  simp only [posteriorMass, signProbability_zero_of_mean_zero u hu p.1 hm p.2, mul_zero]

/--
@isnad1 id=eq.0h2v.s5.0fced65d23ef from=translated src=- shape=f5186507 vocab=79c3cd78
-/
theorem posteriorMass_sum {Ω : Type*} [Fintype Ω] [Nonempty Ω] (u : Ω → ℝ) :
    ∑ p, posteriorMass u p = 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [posteriorMass, ← Finset.mul_sum, signProbability_sum, mul_one]
  simp [Fintype.card_ne_zero]

/--
@isnad1 id=eq.0h2v.s5.d374095b9edd from=translated src=- shape=f5186507 vocab=25f15023
-/
theorem productMass_sum {Ω : Type*} [Fintype Ω] [Nonempty Ω] (u : Ω → ℝ) :
    ∑ p, productMass u p = 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [productMass, ← Finset.mul_sum, signProbability_sum, mul_one]
  simp [Fintype.card_ne_zero]

/--
@isnad1 id=eq.0h1v.s5.af55987152fa from=translated src=- shape=05caa3fb vocab=a8d08ad1
-/
theorem signProbability_entropy (t : ℝ) :
    (∑ b : Bool, signProbability t b * Real.log (signProbability t b)) =
      -Real.binEntropy ((1 - t) / 2) := by
  have hrel : 1 - (1 - t) / 2 = (1 + t) / 2 := by ring
  rw [Real.binEntropy, Real.log_inv, Real.log_inv, hrel]
  simp [signProbability]
  ring

/--
@isnad1 id=eq.1h2v.s6.5e056de3138c from=translated src=- shape=cc54452d vocab=fbc39f5a
-/
theorem mul_log_div_of_support (p q : ℝ) (h : q = 0 → p = 0) :
    p * Real.log (p / q) = p * Real.log p - p * Real.log q := by
  by_cases hp : p = 0
  · simp [hp]
  · have hq : q ≠ 0 := mt h hp
    rw [Real.log_div hp hq]
    ring

/--
@isnad1 id=eq.1h2v.s7.b1f6eb78a101 from=translated src=- shape=533be892 vocab=48510c2f
-/
theorem posteriorMass_KL_sum {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : Ω → ℝ) (hu : ∀ y, u y ∈ Icc (-1 : ℝ) 1) :
    (∑ p, posteriorMass u p * Real.log (posteriorMass u p / productMass u p)) =
      Real.binEntropy ((1 - mean u) / 2) - mean (fun y => Real.binEntropy ((1 - u y) / 2)) := by
  have hcard : (Fintype.card Ω : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hterm (b : Bool) (y : Ω) :
      posteriorMass u (b, y) * Real.log (posteriorMass u (b, y) / productMass u (b, y)) =
        (Fintype.card Ω : ℝ)⁻¹ *
          (signProbability (u y) b * Real.log (signProbability (u y) b) -
            signProbability (u y) b * Real.log (signProbability (mean u) b)) := by
    dsimp only [posteriorMass, productMass]
    rw [mul_div_mul_left _ _ hcard, mul_assoc,
      mul_log_div_of_support _ _ (fun h => signProbability_zero_of_mean_zero u hu b h y)]
  simp_rw [Fintype.sum_prod_type, hterm]
  simp_rw [← Finset.mul_sum]
  simp_rw [Finset.sum_sub_distrib]
  rw [mul_sub]
  have hfirst : (Fintype.card Ω : ℝ)⁻¹ *
      ∑ b : Bool, ∑ y, signProbability (u y) b * Real.log (signProbability (u y) b) =
        -mean (fun y => Real.binEntropy ((1 - u y) / 2)) := by
    rw [Finset.sum_comm]
    simp only [signProbability_entropy, mean, Finset.sum_neg_distrib, mul_neg]
  have hsecond : (Fintype.card Ω : ℝ)⁻¹ *
      ∑ b : Bool, ∑ y, signProbability (u y) b * Real.log (signProbability (mean u) b) =
        -Real.binEntropy ((1 - mean u) / 2) := by
    rw [Finset.mul_sum]
    simp_rw [← Finset.sum_mul, ← mul_assoc]
    change (∑ b : Bool, mean (fun y => signProbability (u y) b) *
      Real.log (signProbability (mean u) b)) = _
    simp only [mean_signProbability, signProbability_entropy]
  rw [hfirst, hsecond]
  ring

/--
@isnad1 id=eq.1h4v.s6.eb69ab576e19 from=translated src=- shape=c802e3ce vocab=88042b41
-/
theorem weightedMeasure_map {β : Type*} [Fintype β] [DecidableEq β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (F : α → β) :
    (weightedMeasure p).map F = weightedMeasure (fun b => ∑ a, if F a = b then p a else 0) := by
  classical
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_countable F) (measurableSet_singleton b),
    weightedMeasure_singleton]
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => ite_nonneg (hp a) le_rfl)]
  simp [weightedMeasure, Measure.finsetSum_apply, Measure.smul_apply, Set.indicator_apply]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

/--
@isnad1 id=eq.1h3v.s6.c8394e042c82 from=translated src=- shape=655d1755 vocab=9bf624dd
-/
theorem weightedMeasure_map_fst {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    (weightedMeasure p).map Prod.fst = weightedMeasure (fun a => ∑ b, p (a, b)) := by
  classical
  rw [weightedMeasure_map p hp Prod.fst]
  congr 1
  funext a
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

/--
@isnad1 id=eq.1h3v.s6.70d7e2a7f90e from=translated src=- shape=46270cff vocab=02cbda05
-/
theorem weightedMeasure_map_snd {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    (weightedMeasure p).map Prod.snd = weightedMeasure (fun b => ∑ a, p (a, b)) := by
  classical
  rw [weightedMeasure_map p hp Prod.snd]
  congr 1
  funext b
  simp [Fintype.sum_prod_type]

/--
@isnad1 id=eq.1h4v.s6.f3d7a95e8d64 from=translated src=- shape=64bda130 vocab=19f176ca
-/
theorem weightedMeasure_prod {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (p : α → ℝ) (q : β → ℝ) (hp : ∀ a, 0 ≤ p a) :
    (weightedMeasure p).prod (weightedMeasure q) = weightedMeasure (fun z => p z.1 * q z.2) := by
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, weightedMeasure_singleton, weightedMeasure_singleton,
    Set.singleton_prod_singleton, weightedMeasure_singleton, ENNReal.ofReal_mul (hp a)]

section PosteriorModel

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

def posteriorJoint (u : Ω → ℝ) : Measure (Bool × Ω) := weightedMeasure (posteriorMass u)

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/--
@isnad1 id=eq.0h3v.s5.81db648b5ef4 from=translated src=- shape=a4f42a23 vocab=c3626f7e
-/
theorem posteriorMass_first_marginal (u : Ω → ℝ) (b : Bool) :
    (∑ y, posteriorMass u (b, y)) = signProbability (mean u) b := by
  simpa only [posteriorMass, ← Finset.mul_sum, mean] using mean_signProbability u b

omit [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/--
@isnad1 id=eq.0h3v.s5.b9821c1ea850 from=translated src=- shape=976e0b83 vocab=5adf887d
-/
theorem posteriorMass_second_marginal (u : Ω → ℝ) (y : Ω) :
    (∑ b : Bool, posteriorMass u (b, y)) = (Fintype.card Ω : ℝ)⁻¹ := by
  simp only [posteriorMass, ← Finset.mul_sum, signProbability_sum, mul_one]

omit [MeasurableSingletonClass Ω] in
/--
@isnad1 id=isprobab.1h2v.s5.55d5f57be8ae from=translated src=- shape=bc30d175 vocab=5c19e8dc
-/
theorem posteriorJoint_probability (u : Ω → ℝ) (hu : ∀ y, u y ∈ Icc (-1 : ℝ) 1) :
    IsProbabilityMeasure (posteriorJoint u) := by
  constructor
  rw [posteriorJoint, weightedMeasure_univ _ (posteriorMass_nonneg u hu), posteriorMass_sum]
  simp

/--
@isnad1 id=eq.1h2v.s6.9a269c0c9d57 from=translated src=- shape=be4998fa vocab=ca4219fb
-/
theorem posteriorJoint_map_fst (u : Ω → ℝ) (hu : ∀ y, u y ∈ Icc (-1 : ℝ) 1) :
    (posteriorJoint u).map Prod.fst = weightedMeasure (signProbability (mean u)) := by
  rw [posteriorJoint, weightedMeasure_map_fst _ (posteriorMass_nonneg u hu)]
  simp only [posteriorMass_first_marginal]

omit [Nonempty Ω] in
/--
@isnad1 id=eq.1h2v.s6.9d0ace379310 from=translated src=- shape=02306739 vocab=09819fa1
-/
theorem posteriorJoint_map_snd (u : Ω → ℝ) (hu : ∀ y, u y ∈ Icc (-1 : ℝ) 1) :
    (posteriorJoint u).map Prod.snd = weightedMeasure (fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹) := by
  rw [posteriorJoint, weightedMeasure_map_snd _ (posteriorMass_nonneg u hu)]
  simp only [posteriorMass_second_marginal]

/--
@isnad1 id=eq.1h2v.s6.bf6d6b4e9390 from=translated src=- shape=7a901176 vocab=8dd6775b
-/
theorem posteriorJoint_product_marginals (u : Ω → ℝ) (hu : ∀ y, u y ∈ Icc (-1 : ℝ) 1) :
    ((posteriorJoint u).map Prod.fst).prod ((posteriorJoint u).map Prod.snd) =
      weightedMeasure (productMass u) := by
  rw [posteriorJoint_map_fst u hu, posteriorJoint_map_snd u hu,
    weightedMeasure_prod _ _ (signProbability_nonneg (EntropyTransfer.mean_mem_Icc hu))]
  congr 1
  funext p
  exact mul_comm _ _

/-- Mutual information in bits, defined by the KL divergence of the actual
joint measure against the product of its own two marginals.-/
def mutualInformationBits (μ : Measure (Bool × Ω)) : ℝ :=
  (InformationTheory.klDiv μ ((μ.map Prod.fst).prod (μ.map Prod.snd))).toReal / Real.log 2

/--
@isnad1 id=ne.1h2v.s6.c246cf7202be from=translated src=- shape=ddc9cbaa vocab=859fc703
-/
theorem posteriorJoint_KL_ne_top (u : Ω → ℝ) (hu : ∀ y, u y ∈ Icc (-1 : ℝ) 1) :
    InformationTheory.klDiv (posteriorJoint u)
      (((posteriorJoint u).map Prod.fst).prod ((posteriorJoint u).map Prod.snd)) ≠ ∞ := by
  rw [posteriorJoint_product_marginals u hu]
  exact klDiv_weightedMeasure_ne_top _ _ (posteriorMass_nonneg u hu) (productMass_nonneg u hu)
    (posteriorMass_support u hu)

/--
@isnad1 id=eq.1h2v.s7.1e00cea7da7f from=translated src=- shape=cbbd943e vocab=71e8db7d
-/
theorem posteriorJoint_mutualInformation (u : Ω → ℝ) (hu : ∀ y, u y ∈ Icc (-1 : ℝ) 1) :
    mutualInformationBits (posteriorJoint u) =
      PaperSpecs.binaryEntropyBits ((1 - mean u) / 2) -
        mean (fun y => PaperSpecs.binaryEntropyBits ((1 - u y) / 2)) := by
  rw [mutualInformationBits, posteriorJoint_product_marginals u hu]
  change (InformationTheory.klDiv (weightedMeasure (posteriorMass u))
    (weightedMeasure (productMass u))).toReal / Real.log 2 = _
  rw [klDiv_weightedMeasure _ _ (posteriorMass_nonneg u hu) (productMass_nonneg u hu)
    (posteriorMass_support u hu) (by rw [posteriorMass_sum, productMass_sum]),
    posteriorMass_KL_sum u hu, sub_div]
  unfold PaperSpecs.binaryEntropyBits
  congr 1
  simp only [div_eq_mul_inv, mean_mul_const]

end PosteriorModel

section ChannelModel

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The Boolean encoding of the sign output, with `true` representing `-1`.-/
def outputBit (f : Ω → ℝ) (x : Ω) : Bool := by
  classical
  exact decide (f x = -1)

omit [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/--
@isnad1 id=eq.1h4v.s6.232cddb3aaa4 from=translated src=- shape=fa70b07a vocab=d147143b
-/
theorem signProbability_boolean (f : Ω → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1)
    (x : Ω) (b : Bool) :
    signProbability (f x) b = if outputBit f x = b then 1 else 0 := by
  rcases hf x with h | h <;> cases b <;> norm_num [signProbability, outputBit, h]

omit [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/--
@isnad1 id=eq.0h5v.s5.b4c7803a1a9e from=translated src=- shape=20a43b33 vocab=e42c969b
-/
theorem apply_signProbability (K : UniformChannel Ω) (f : Ω → ℝ) (y : Ω) (b : Bool) :
    (∑ x, K.weight y x * signProbability (f x) b) = signProbability (K.apply f y) b := by
  cases b
  · simp only [signProbability, Bool.false_eq_true, ite_false, ← mul_div_assoc, mul_add,
      mul_one, ← Finset.sum_div, Finset.sum_add_distrib, K.row_sum, UniformChannel.apply]
  · simp only [signProbability, ite_true, ← mul_div_assoc, mul_sub,
      mul_one, ← Finset.sum_div, Finset.sum_sub_distrib, K.row_sum, UniformChannel.apply]

/-- A uniformly distributed input transmitted through the doubly stochastic
channel. The weight convention is `K.weight observed input`.-/
def channelMass (K : UniformChannel Ω) (z : Ω × Ω) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * K.weight z.2 z.1

def channelJoint (K : UniformChannel Ω) : Measure (Ω × Ω) := weightedMeasure (channelMass K)

omit [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/--
@isnad1 id=le.0h3v.s4.df4ea9c61dc7 from=translated src=- shape=67011975 vocab=e829026d
-/
theorem channelMass_nonneg (K : UniformChannel Ω) (z : Ω × Ω) : 0 ≤ channelMass K z :=
  mul_nonneg (by positivity) (K.nonneg _ _)

omit [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/--
@isnad1 id=eq.0h3v.s5.2ae8262966b2 from=translated src=- shape=235f4559 vocab=2039e498
-/
theorem channelMass_first_marginal (K : UniformChannel Ω) (x : Ω) :
    (∑ y, channelMass K (x, y)) = (Fintype.card Ω : ℝ)⁻¹ := by
  simp [channelMass, ← Finset.mul_sum, K.column_sum]

omit [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/--
@isnad1 id=eq.0h3v.s5.e5172566c56d from=translated src=- shape=5e2d321d vocab=2039e498
-/
theorem channelMass_second_marginal (K : UniformChannel Ω) (y : Ω) :
    (∑ x, channelMass K (x, y)) = (Fintype.card Ω : ℝ)⁻¹ := by
  simp [channelMass, ← Finset.mul_sum, K.row_sum]

omit [MeasurableSingletonClass Ω] in
/--
@isnad1 id=isprobab.0h2v.s4.ee4cdd5a61cb from=translated src=- shape=71996558 vocab=2b1653f3
-/
theorem channelJoint_probability (K : UniformChannel Ω) : IsProbabilityMeasure (channelJoint K) := by
  constructor
  rw [channelJoint, weightedMeasure_univ _ (channelMass_nonneg K), Fintype.sum_prod_type]
  simp only [channelMass_first_marginal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [Fintype.card_ne_zero]

/-- The actual joint distribution of the Boolean output of the input and the
observed channel output.-/
def outputJoint (K : UniformChannel Ω) (f : Ω → ℝ) : Measure (Bool × Ω) :=
  (channelJoint K).map (fun z => (outputBit f z.1, z.2))

omit [Nonempty Ω] in
/--
@isnad1 id=eq.1h3v.s6.c17cd70e6cb8 from=translated src=- shape=818ddcb0 vocab=193bb87d
-/
theorem outputJoint_eq_posteriorJoint (K : UniformChannel Ω) (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) :
    outputJoint K f = posteriorJoint (K.apply f) := by
  classical
  rw [outputJoint, channelJoint, weightedMeasure_map _ (channelMass_nonneg K)]
  unfold posteriorJoint
  congr 1
  funext p
  rcases p with ⟨b, y⟩
  rw [Fintype.sum_prod_type]
  have ht (x : Ω) :
      (∑ z : Ω, if (outputBit f x, z) = (b, y) then channelMass K (x, z) else 0) =
        if outputBit f x = b then channelMass K (x, y) else 0 := by
    by_cases h : outputBit f x = b <;> simp [h]
  simp_rw [ht]
  have hs (x : Ω) : (if outputBit f x = b then channelMass K (x, y) else 0) =
      (Fintype.card Ω : ℝ)⁻¹ * (K.weight y x * signProbability (f x) b) := by
    rw [signProbability_boolean f hf]
    split_ifs <;> simp [channelMass]
  simp_rw [hs]
  rw [← Finset.mul_sum, apply_signProbability]
  rfl

/--
@isnad1 id=isprobab.1h3v.s6.76ec2e160ca5 from=translated src=- shape=abecc59d vocab=554700b7
-/
theorem outputJoint_probability (K : UniformChannel Ω) (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) : IsProbabilityMeasure (outputJoint K f) := by
  rw [outputJoint_eq_posteriorJoint K f hf]
  apply posteriorJoint_probability
  apply K.apply_mem_Icc
  intro x
  rcases hf x with h | h <;> rw [h] <;> norm_num

/--
@isnad1 id=ne.1h3v.s6.3151ef368982 from=translated src=- shape=8209a968 vocab=ff55eca3
-/
theorem outputJoint_KL_ne_top (K : UniformChannel Ω) (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) :
    InformationTheory.klDiv (outputJoint K f)
      (((outputJoint K f).map Prod.fst).prod ((outputJoint K f).map Prod.snd)) ≠ ∞ := by
  rw [outputJoint_eq_posteriorJoint K f hf]
  apply posteriorJoint_KL_ne_top
  apply K.apply_mem_Icc
  intro x
  rcases hf x with h | h <;> rw [h] <;> norm_num

/--
@isnad1 id=eq.1h3v.s7.2ce037bf20a6 from=translated src=- shape=d316f1e8 vocab=884097d4
-/
theorem outputJoint_mutualInformation (K : UniformChannel Ω) (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) :
    mutualInformationBits (outputJoint K f) =
      PaperSpecs.binaryEntropyBits ((1 - mean f) / 2) -
        mean (fun y => PaperSpecs.binaryEntropyBits ((1 - K.apply f y) / 2)) := by
  rw [outputJoint_eq_posteriorJoint K f hf,
    posteriorJoint_mutualInformation _ (K.apply_mem_Icc f (fun x => by
      rcases hf x with h | h <;> rw [h] <;> norm_num)), K.mean_apply]

end ChannelModel

/-- Mutual information in bits for a Boolean function of a uniform cube
input and the output of the genuine product binary symmetric channel.-/
def bscMutualInformation {n : ℕ} (f : PaperSpecs.Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) : ℝ :=
  mutualInformationBits (outputJoint (cubeBSC n ρ hρ) f)

/-- The uniform-input joint mass is exactly the product-BSC law, with crossover
probability `(1 - ρ) / 2` in every coordinate.
@isnad1 id=eq.1h4v.s7.fe69b207d1e3 from=translated src=- shape=ff28494c vocab=1c99b540
-/
theorem cubeBSC_joint_mass (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (x y : PaperSpecs.Cube n) :
    channelMass (cubeBSC n ρ hρ) (x, y) =
      (2 ^ n : ℝ)⁻¹ * ∏ i, if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2 := by
  simp only [channelMass, cubeBSC, UniformChannel.product, bsc, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

/-- Full model equivalence: the posterior entropy expression is the KL
mutual information of the actual pushed-forward BSC joint measure.
@isnad1 id=eq.2h3v.s5.3452c9d1cf6a from=translated src=- shape=d542c1f2 vocab=c89044ab
-/
theorem bscMutualInformation_eq_posteriorInformation {n : ℕ} (f : PaperSpecs.Cube n → ℝ)
    (hf : PaperSpecs.IsBoolean f) (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    bscMutualInformation f ρ hρ = PaperSpecs.posteriorInformation f ρ hρ :=
  outputJoint_mutualInformation (cubeBSC n ρ hρ) f hf

/--
@isnad1 id=ne.2h3v.s8.980ad7c2c659 from=translated src=- shape=0318e6f2 vocab=8b3568b9
-/
theorem bscMutualInformation_KL_ne_top {n : ℕ} (f : PaperSpecs.Cube n → ℝ)
    (hf : PaperSpecs.IsBoolean f) (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    InformationTheory.klDiv (outputJoint (cubeBSC n ρ hρ) f)
      (((outputJoint (cubeBSC n ρ hρ) f).map Prod.fst).prod
        ((outputJoint (cubeBSC n ρ hρ) f).map Prod.snd)) ≠ ∞ :=
  outputJoint_KL_ne_top (cubeBSC n ρ hρ) f hf

/--
@isnad1 id=le.3h3v.s6.b6ce2f4f31b5 from=translated src=- shape=751380ee vocab=f12bdd30
-/
theorem bscMutualInformation_le_of_hellinger {n : ℕ} (f : PaperSpecs.Cube n → ℝ)
    (hf : PaperSpecs.IsBoolean f) (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (hH : PaperSpecs.HellingerBound f ρ hρ) :
    bscMutualInformation f ρ hρ ≤ 1 - PaperSpecs.binaryEntropyBits ((1 - ρ) / 2) := by
  rw [bscMutualInformation_eq_posteriorInformation f hf]
  exact EntropyTransfer.hellinger_implies_ck f hf ρ hρ hH

end Hellinger.FiniteInformation
