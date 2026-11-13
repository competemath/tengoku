import Tengoku.Seed.Probability.Distributions.Uniform
import Tengoku.Seed.Probability.ProbabilityMassFunction.Integrals

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite uniform sequence law is a product law

Equality is proved on all singleton masses. Supports the iid side of the
without-replacement comparison (Hoeffding 1963, Theorem 4), atlas `srht-ose`.
-/

noncomputable section
open MeasureTheory
open ProbabilityTheory
open scoped Classical ENNReal
namespace NLAlib

/-- The finite uniform function law equals the product of the coordinate
uniform laws, including the empty coordinate family. Source: Hoeffding 1963, Theorem 4.
@isnad1 id=eq.0h2v.s6.90e387adb266 from=translated src=- shape=e5e7e20c vocab=b8944c0d
-/
theorem uniform_function_toMeasure_eq_pi
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (PMF.uniformOfFintype (ι → α)).toMeasure =
      Measure.pi (fun _ : ι => (PMF.uniformOfFintype α).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply,
    Fintype.card_fun, Finset.prod_const, Finset.card_univ, Nat.cast_pow, ENNReal.inv_pow]

/-- Coordinate compositions are independent under the
uniform finite sequence law. Source: product uniform law, `srht-ose`.
@isnad1 id=iindepfu.0h4v.s6.9d0b7b07a84e from=translated src=- shape=c6cb9fb1 vocab=8d5763b4
-/
theorem iIndepFun_uniform_sequence_comp
    {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] (f : α → β) :
    iIndepFun (fun a (I : ι → α) => f (I a))
      (PMF.uniformOfFintype (ι → α)).toMeasure := by
  rw [uniform_function_toMeasure_eq_pi (ι := ι) (α := α)]
  exact iIndepFun_pi (μ := fun _ : ι => (PMF.uniformOfFintype α).toMeasure)
    (X := fun _ : ι => f) (fun _ => Measurable.of_discrete.aemeasurable)

/-- Each coordinate of the finite uniform sequence has the exact
uniform expectation. Source: finite product integration, `srht-ose`.
@isnad1 id=eq.0h5v.s7.3cf8da61f86f from=translated src=- shape=2c569a94 vocab=5ebc5808
-/
theorem integral_uniform_sequence_comp_eval
    {ι α E : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : α → E) (a : ι) :
    (∫ I : ι → α, f (I a) ∂(PMF.uniformOfFintype (ι → α)).toMeasure) =
      (1 / (Fintype.card α : ℝ)) • ∑ j, f j := by
  rw [uniform_function_toMeasure_eq_pi (ι := ι) (α := α)]
  have hev := (measurePreserving_eval (fun _ : ι =>
    (PMF.uniformOfFintype α).toMeasure) a).map_eq
  have hmap := integral_map
    (μ := Measure.pi (fun _ : ι => (PMF.uniformOfFintype α).toMeasure))
    (φ := fun I : ι → α => I a) (f := f)
    (measurable_pi_apply a).aemeasurable StronglyMeasurable.of_discrete.aestronglyMeasurable
  rw [← hmap, hev, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← Finset.smul_sum, one_div]

end NLAlib
