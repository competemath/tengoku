import Tengoku.Nlalib.NLAlib.Probability.Exchangeable.ThirdCopyMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The common actual marginal law of all three resampling differences

The common law is the uniform mixture of the individual independent-copy
difference laws. Summand laws may vary with their coordinate index.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Uniform mixture of the individual summands' independent-copy difference
laws; it is shared by all three differences of the resampling triple.-/
def resamplingDifferenceLaw (ν : ι → Measure E) : Measure E :=
  (PMF.uniformOfFintype ι).toMeasure.bind
    (fun i => ((ν i).prod (ν i)).map (fun p : E × E => p.1 - p.2))

/-- Every two distinct copy slots yield precisely the same actual mixed
difference law, with no moments or identical-distribution assumptions.
@isnad1 id=haslaw.1h5v.s8.c3b1d72fcba2 from=translated src=- shape=3b7aa1c2 vocab=b34508c0
-/
theorem hasLaw_resamplingTriple_selected_difference
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (a b : Fin 3) (hab : a ≠ b) :
    HasLaw (fun p : ι × ((ι × Fin 3) → E) => p.2 (p.1, a) - p.2 (p.1, b))
      (resamplingDifferenceLaw ν) (resamplingTripleMeasure ν) := by
  have hm : Measurable (fun p : ι × ((ι × Fin 3) → E) => p.2 (p.1, a) - p.2 (p.1, b)) := by
    apply measurable_from_prod_countable_right
    intro i
    change Measurable (fun x : (ι × Fin 3) → E => x (i, a) - x (i, b))
    fun_prop
  apply hasLaw_prod_of_section_laws hm
  intro i
  have hd : HasLaw (fun p : E × E => p.1 - p.2)
      (((ν i).prod (ν i)).map (fun p : E × E => p.1 - p.2)) ((ν i).prod (ν i)) :=
    ⟨by fun_prop, rfl⟩
  exact hd.comp (hasLaw_resamplingTriple_coordinate_pair ν i a b hab)

/-- D=X-X' has the uniform mixture of independent-copy difference laws.
@isnad1 id=haslaw.0h3v.s8.3bd10172deba from=translated src=- shape=f69835df vocab=9082ab6a
-/
theorem hasLaw_resamplingTriple_original_sub_first
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw (resamplingTripleOriginal - resamplingTripleFirst)
      (resamplingDifferenceLaw ν) (resamplingTripleMeasure ν) := by
  have he : (resamplingTripleOriginal - resamplingTripleFirst : (ι × ((ι × Fin 3) → E)) → E) =
      (fun p => p.2 (p.1, 0) - p.2 (p.1, 1)) := by funext p; exact resamplingTriple_difference p
  rw [he]
  exact hasLaw_resamplingTriple_selected_difference ν 0 1 (by decide)

/-- E=X'-X'' has the same actual marginal difference law as D.
@isnad1 id=haslaw.0h3v.s8.8220d5abb550 from=translated src=- shape=f69835df vocab=f003975d
-/
theorem hasLaw_resamplingTriple_first_sub_second
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw (resamplingTripleFirst - resamplingTripleSecond)
      (resamplingDifferenceLaw ν) (resamplingTripleMeasure ν) := by
  have he : (resamplingTripleFirst - resamplingTripleSecond : (ι × ((ι × Fin 3) → E)) → E) =
      (fun p => p.2 (p.1, 1) - p.2 (p.1, 2)) := by funext p; exact resamplingTriple_first_sub_second p
  rw [he]
  exact hasLaw_resamplingTriple_selected_difference ν 1 2 (by decide)

/-- F=X-X'' has the same actual marginal difference law as D and E.
@isnad1 id=haslaw.0h3v.s8.c762624956d4 from=translated src=- shape=f69835df vocab=c2a1f24a
-/
theorem hasLaw_resamplingTriple_original_sub_second
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw (resamplingTripleOriginal - resamplingTripleSecond)
      (resamplingDifferenceLaw ν) (resamplingTripleMeasure ν) := by
  have he : (resamplingTripleOriginal - resamplingTripleSecond : (ι × ((ι × Fin 3) → E)) → E) =
      (fun p => p.2 (p.1, 0) - p.2 (p.1, 2)) := by funext p; exact resamplingTriple_difference_second p
  rw [he]
  exact hasLaw_resamplingTriple_selected_difference ν 0 2 (by decide)

end NLAlib
