import Tengoku.Nlalib.NLAlib.Probability.Exchangeable.ThirdCopy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Marginals and exact difference moments of the same-index resampling triple

All three sums have the original independent sum's law. Each of the three
ordered differences has exactly the uniform average of the individual
independent-copy difference laws, including nonidentical summands.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

private theorem hasLaw_triple_selected_sum
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] (a : Fin 3) :
    HasLaw (fun p : ι × ((ι × Fin 3) → E) => ∑ j, p.2 (j, if j = p.1 then a else 0))
      ((Measure.pi ν).map (fun x : ι → E => ∑ j, x j)) (resamplingTripleMeasure ν) := by
  have hg : Measurable (fun p : ι × ((ι × Fin 3) → E) =>
      ∑ j, p.2 (j, if j = p.1 then a else 0)) := by
    apply measurable_from_prod_countable_right
    intro i
    change Measurable (fun x : (ι × Fin 3) → E => ∑ j, x (j, if j = i then a else 0))
    fun_prop
  apply hasLaw_prod_of_sections hg
  intro i
  have hsel := hasLaw_pi_select (fun k : ι × Fin 3 => ν k.1)
    (fun j => (j, if j = i then a else 0)) (by intro j k h; exact congrArg Prod.fst h)
  have hs : HasLaw (fun x : ι → E => ∑ j, x j)
      ((Measure.pi ν).map (fun x : ι → E => ∑ j, x j)) (Measure.pi ν) :=
    ⟨by fun_prop, rfl⟩
  exact hs.comp hsel

/-- The original sum in the triple has the actual independent sum's law.
@isnad1 id=haslaw.0h3v.s7.0376879be7dd from=translated src=- shape=5485cc83 vocab=f55481ae
-/
theorem hasLaw_resamplingTripleOriginal
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw resamplingTripleOriginal ((Measure.pi ν).map (fun x : ι → E => ∑ j, x j))
      (resamplingTripleMeasure ν) := by
  change HasLaw (fun p : ι × ((ι × Fin 3) → E) => ∑ j, p.2 (j, 0)) _ _
  simpa only [ite_self] using hasLaw_triple_selected_sum ν 0

/-- The first replacement has exactly the original independent sum's law.
@isnad1 id=haslaw.0h3v.s7.b6cbc4cb4bb2 from=translated src=- shape=5485cc83 vocab=95744dcb
-/
theorem hasLaw_resamplingTripleFirst
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw resamplingTripleFirst ((Measure.pi ν).map (fun x : ι → E => ∑ j, x j))
      (resamplingTripleMeasure ν) := hasLaw_triple_selected_sum ν 1

/-- The second replacement and original sum have exactly the same law.
@isnad1 id=identdis.0h3v.s7.3d95a0976261 from=translated src=- shape=2726b001 vocab=2215b05c
-/
theorem identDistrib_resamplingTripleSecond_original
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    IdentDistrib resamplingTripleSecond resamplingTripleOriginal
      (resamplingTripleMeasure ν) (resamplingTripleMeasure ν) :=
  ⟨(hasLaw_resamplingTripleSecond ν).aemeasurable, (hasLaw_resamplingTripleOriginal ν).aemeasurable,
    (hasLaw_resamplingTripleSecond ν).map_eq.trans (hasLaw_resamplingTripleOriginal ν).map_eq.symm⟩

/-- The difference between original and second replacement uses the selected
original and its second independent copy.
@isnad1 id=eq.0h3v.s7.e28f9f59aa9a from=translated src=- shape=e7444e0f vocab=a8917cab
-/
theorem resamplingTriple_difference_second (p : ι × ((ι × Fin 3) → E)) :
    resamplingTripleOriginal p - resamplingTripleSecond p = p.2 (p.1, 0) - p.2 (p.1, 2) := by
  unfold resamplingTripleOriginal resamplingTripleSecond
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single p.1]
  · simp
  · intro j hj hji; simp [hji]
  · simp

/-- The difference between first and second replacements uses exactly the two
independent copies at the shared selected index.
@isnad1 id=eq.0h3v.s7.e803e7e5a83d from=translated src=- shape=e7444e0f vocab=441430c8
-/
theorem resamplingTriple_first_sub_second (p : ι × ((ι × Fin 3) → E)) :
    resamplingTripleFirst p - resamplingTripleSecond p = p.2 (p.1, 1) - p.2 (p.1, 2) := by
  calc
    _ = (resamplingTripleOriginal p - resamplingTripleSecond p) -
        (resamplingTripleOriginal p - resamplingTripleFirst p) := by abel
    _ = _ := by rw [resamplingTriple_difference_second, resamplingTriple_difference]; abel

/-- Any two distinct copy slots of one coordinate have the actual independent
product law of that individual summand.
@isnad1 id=haslaw.1h6v.s8.d5c4beb4d72c from=translated src=- shape=98a4d5d6 vocab=a64c6378
-/
theorem hasLaw_resamplingTriple_coordinate_pair
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (i : ι) (a b : Fin 3) (hab : a ≠ b) :
    HasLaw (fun x : (ι × Fin 3) → E => (x (i, a), x (i, b))) ((ν i).prod (ν i))
      (Measure.pi fun k : ι × Fin 3 => ν k.1) := by
  have hi : iIndepFun (fun k (x : (ι × Fin 3) → E) => x k)
      (Measure.pi fun k : ι × Fin 3 => ν k.1) := iIndepFun_pi (fun _ => aemeasurable_id)
  exact (hi.indepFun (by intro h; exact hab (congrArg Prod.snd h))).hasLaw_prod
    (measurePreserving_eval (fun k : ι × Fin 3 => ν k.1) (i, a)).hasLaw
    (measurePreserving_eval (fun k : ι × Fin 3 => ν k.1) (i, b)).hasLaw

/-- Every integrable measurable test of a selected independent-copy difference
is integrable on the actual three-copy resampling space.
@isnad1 id=integrab.3h6v.s8.61b4ce4b4e4e from=translated src=- shape=a03d873c vocab=562605a9
-/
theorem integrable_resamplingTriple_selected_difference
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (a b : Fin 3) (hab : a ≠ b) (G : E → ℝ) (hG : Measurable G)
    (hGi : ∀ i, Integrable (fun p : E × E => G (p.1 - p.2)) ((ν i).prod (ν i))) :
    Integrable (fun p : ι × ((ι × Fin 3) → E) => G (p.2 (p.1, a) - p.2 (p.1, b)))
      (resamplingTripleMeasure ν) := by
  have hm : Measurable (fun p : ι × ((ι × Fin 3) → E) => G (p.2 (p.1, a) - p.2 (p.1, b))) := by
    apply measurable_from_prod_countable_right
    intro i
    change Measurable (fun x : (ι × Fin 3) → E => G (x (i, a) - x (i, b)))
    exact hG.comp ((measurable_pi_apply _).sub (measurable_pi_apply _))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ fun i => ?_, Integrable.of_finite⟩
  have hp := (hasLaw_resamplingTriple_coordinate_pair ν i a b hab).measurePreserving (by fun_prop)
  simpa only [Function.comp_def] using hp.integrable_comp_of_integrable (hGi i)

/-- The exact uniform average of every integrable measurable test of any two
distinct copies' difference. Taking a third-moment trace test gives precisely
M3/card(iota), with no identical-distribution assumption.
@isnad1 id=eq.3h6v.s8.f42e8ce69fe0 from=translated src=- shape=915f1035 vocab=c783f83e
-/
theorem integral_resamplingTriple_selected_difference
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (a b : Fin 3) (hab : a ≠ b) (G : E → ℝ) (hG : Measurable G)
    (hGi : ∀ i, Integrable (fun p : E × E => G (p.1 - p.2)) ((ν i).prod (ν i))) :
    (∫ p : ι × ((ι × Fin 3) → E), G (p.2 (p.1, a) - p.2 (p.1, b))
      ∂resamplingTripleMeasure ν) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ p : E × E, G (p.1 - p.2) ∂(ν i).prod (ν i) := by
  have hi := integrable_resamplingTriple_selected_difference ν a b hab G hG hGi
  change (∫ p : ι × ((ι × Fin 3) → E), G (p.2 (p.1, a) - p.2 (p.1, b))
    ∂(PMF.uniformOfFintype ι).toMeasure.prod (Measure.pi fun k : ι × Fin 3 => ν k.1)) = _
  rw [integral_prod _ hi]
  have he (i : ι) :
      (∫ x : (ι × Fin 3) → E, G (x (i, a) - x (i, b)) ∂Measure.pi (fun k : ι × Fin 3 => ν k.1)) =
        ∫ p : E × E, G (p.1 - p.2) ∂(ν i).prod (ν i) := by
    simpa only [Function.comp_def] using
      (hasLaw_resamplingTriple_coordinate_pair ν i a b hab).integral_comp (hGi i).aestronglyMeasurable
  simp_rw [he]
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, Finset.mul_sum]

/-- The exact average moment formula for D = X-X'.
@isnad1 id=eq.2h4v.s8.933e2c260034 from=translated src=- shape=37c7cb33 vocab=77dc68db
-/
theorem integral_resamplingTriple_original_sub_first
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (G : E → ℝ) (hG : Measurable G)
    (hGi : ∀ i, Integrable (fun p : E × E => G (p.1 - p.2)) ((ν i).prod (ν i))) :
    (∫ p, G (resamplingTripleOriginal p - resamplingTripleFirst p) ∂resamplingTripleMeasure ν) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ p : E × E, G (p.1 - p.2) ∂(ν i).prod (ν i) := by
  simpa only [resamplingTriple_difference] using
    integral_resamplingTriple_selected_difference ν 0 1 (by decide) G hG hGi

/-- The exact average moment formula for E = X'-X''.
@isnad1 id=eq.2h4v.s8.9ccd96029d9d from=translated src=- shape=37c7cb33 vocab=8b9c2fa2
-/
theorem integral_resamplingTriple_first_sub_second
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (G : E → ℝ) (hG : Measurable G)
    (hGi : ∀ i, Integrable (fun p : E × E => G (p.1 - p.2)) ((ν i).prod (ν i))) :
    (∫ p, G (resamplingTripleFirst p - resamplingTripleSecond p) ∂resamplingTripleMeasure ν) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ p : E × E, G (p.1 - p.2) ∂(ν i).prod (ν i) := by
  simpa only [resamplingTriple_first_sub_second] using
    integral_resamplingTriple_selected_difference ν 1 2 (by decide) G hG hGi

/-- The exact average moment formula for F = X-X''.
@isnad1 id=eq.2h4v.s8.fbabe732e991 from=translated src=- shape=37c7cb33 vocab=4dcfd834
-/
theorem integral_resamplingTriple_original_sub_second
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (G : E → ℝ) (hG : Measurable G)
    (hGi : ∀ i, Integrable (fun p : E × E => G (p.1 - p.2)) ((ν i).prod (ν i))) :
    (∫ p, G (resamplingTripleOriginal p - resamplingTripleSecond p) ∂resamplingTripleMeasure ν) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ p : E × E, G (p.1 - p.2) ∂(ν i).prod (ν i) := by
  simpa only [resamplingTriple_difference_second] using
    integral_resamplingTriple_selected_difference ν 0 2 (by decide) G hG hGi

end NLAlib
