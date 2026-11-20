import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Permuton

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Individual four-pattern densities

The analytic development uses one event for the union of the eight dihedral
patterns.  Here we split that event into the individual strict four-pattern
events appearing in the paper.  Rank chambers use strict inequalities, so a
sample with a tie in either coordinate lies in no pattern event.
-/

namespace QuartetDistance.PermutonPatterns

open MeasureTheory Set
open scoped BigOperators

abbrev Four := Permuton.Four
abbrev Perm4 := Permuton.Perm4

/-- The event that four planar samples have strict relative pattern `σ`.
The two rank permutations list sample names in increasing coordinate order;
their relative permutation is therefore the standardized pattern.-/
def patternPointEvent (σ : Perm4) : Set (Four → ℝ × ℝ) :=
  ⋃ qx : Perm4, ⋃ qy : Perm4,
    ⋃ (_ : Circular.relativePermutation qx qy = σ),
      Permuton.firstCoordinates ⁻¹' Permuton.rankChamber qx ∩
        Permuton.secondCoordinates ⁻¹' Permuton.rankChamber qy

/--
@isnad1 id=measurab.0h1v.s4.ab86275a875e from=translated src=- shape=661fc97e vocab=634abebb
-/
theorem measurableSet_patternPointEvent (σ : Perm4) :
    MeasurableSet (patternPointEvent σ) := by
  unfold patternPointEvent
  apply MeasurableSet.iUnion
  intro qx
  apply MeasurableSet.iUnion
  intro qy
  apply MeasurableSet.iUnion
  intro h
  exact
    ((Permuton.measurableSet_rankChamber qx).preimage
      Permuton.measurable_firstCoordinates).inter
    ((Permuton.measurableSet_rankChamber qy).preimage
      Permuton.measurable_secondCoordinates)

/-- Membership in a strict pattern event forces both coordinate vectors to
be injective.  Thus tied samples are excluded rather than assigned an
arbitrary pattern.
@isnad1 id=and.1h2v.s5.40a20cd423f0 from=translated src=- shape=e0991c99 vocab=2e0f1931
-/
theorem injective_coordinates_of_mem_patternPointEvent
    {σ : Perm4} {z : Four → ℝ × ℝ} (hz : z ∈ patternPointEvent σ) :
    Function.Injective (Permuton.firstCoordinates z) ∧
      Function.Injective (Permuton.secondCoordinates z) := by
  simp only [patternPointEvent, mem_iUnion, mem_inter_iff, mem_preimage] at hz
  obtain ⟨qx, qy, hpattern, hx, hy⟩ := hz
  have hsx : StrictMono (Permuton.firstCoordinates z ∘ qx) :=
    (Permuton.mem_rankChamber_iff _ _).mp hx
  have hsy : StrictMono (Permuton.secondCoordinates z ∘ qy) :=
    (Permuton.mem_rankChamber_iff _ _).mp hy
  constructor
  · intro i j hij
    have hcomp :
        (Permuton.firstCoordinates z ∘ qx) (qx.symm i) =
          (Permuton.firstCoordinates z ∘ qx) (qx.symm j) := by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij
    exact qx.symm.injective (hsx.injective hcomp)
  · intro i j hij
    have hcomp :
        (Permuton.secondCoordinates z ∘ qy) (qy.symm i) =
          (Permuton.secondCoordinates z ∘ qy) (qy.symm j) := by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij
    exact qy.symm.injective (hsy.injective hcomp)

/--
@isnad1 id=not.1h2v.s5.28032f592a3a from=translated src=- shape=07307d5c vocab=f91a364a
-/
theorem not_mem_patternPointEvent_of_not_injective_first
    (σ : Perm4) (z : Four → ℝ × ℝ)
    (hz : ¬ Function.Injective (Permuton.firstCoordinates z)) :
    z ∉ patternPointEvent σ := by
  intro hmem
  exact hz (injective_coordinates_of_mem_patternPointEvent hmem).1

/--
@isnad1 id=not.1h2v.s5.428817994300 from=translated src=- shape=07307d5c vocab=9660fcff
-/
theorem not_mem_patternPointEvent_of_not_injective_second
    (σ : Perm4) (z : Four → ℝ × ℝ)
    (hz : ¬ Function.Injective (Permuton.secondCoordinates z)) :
    z ∉ patternPointEvent σ := by
  intro hmem
  exact hz (injective_coordinates_of_mem_patternPointEvent hmem).2

/-- On a tie-free sample, event membership is exactly equality with the usual
standardized four-point pattern.
@isnad1 id=iff.2h2v.s6.26d9f8355b40 from=translated src=- shape=eb1870e3 vocab=909a36e1
-/
theorem mem_patternPointEvent_iff (σ : Perm4) (z : Four → ℝ × ℝ)
    (hx : Function.Injective (Permuton.firstCoordinates z))
    (hy : Function.Injective (Permuton.secondCoordinates z)) :
    z ∈ patternPointEvent σ ↔
      Circular.relativePermutation
          (Tuple.sort (Permuton.firstCoordinates z))
          (Tuple.sort (Permuton.secondCoordinates z)) = σ := by
  have hxsort : Permuton.firstCoordinates z ∈
      Permuton.rankChamber (Tuple.sort (Permuton.firstCoordinates z)) := by
    rw [Permuton.mem_rankChamber_iff]
    exact
      (Tuple.monotone_sort (Permuton.firstCoordinates z)).strictMono_of_injective
        (hx.comp (Tuple.sort (Permuton.firstCoordinates z)).injective)
  have hysort : Permuton.secondCoordinates z ∈
      Permuton.rankChamber (Tuple.sort (Permuton.secondCoordinates z)) := by
    rw [Permuton.mem_rankChamber_iff]
    exact
      (Tuple.monotone_sort (Permuton.secondCoordinates z)).strictMono_of_injective
        (hy.comp (Tuple.sort (Permuton.secondCoordinates z)).injective)
  constructor
  · intro hz
    simp only [patternPointEvent, mem_iUnion, mem_inter_iff, mem_preimage] at hz
    obtain ⟨qx, qy, hpattern, hxq, hyq⟩ := hz
    have heqx : qx = Tuple.sort (Permuton.firstCoordinates z) := by
      by_contra hne
      exact
        (Set.disjoint_left.1 (Permuton.rankChamber_pairwise_disjoint hne)
          hxq hxsort)
    have heqy : qy = Tuple.sort (Permuton.secondCoordinates z) := by
      by_contra hne
      exact
        (Set.disjoint_left.1 (Permuton.rankChamber_pairwise_disjoint hne)
          hyq hysort)
    simpa [heqx, heqy] using hpattern
  · intro hpattern
    simp only [patternPointEvent, mem_iUnion, mem_inter_iff, mem_preimage]
    exact ⟨Tuple.sort (Permuton.firstCoordinates z),
      Tuple.sort (Permuton.secondCoordinates z), hpattern, hxsort, hysort⟩

/-- Distinct strict patterns are disjoint events.
@isnad1 id=disjoint.1h2v.s6.ae4eb7c123e0 from=translated src=- shape=f0da93a8 vocab=c4a681f3
-/
theorem patternPointEvent_disjoint {σ τ : Perm4} (hστ : σ ≠ τ) :
    Disjoint (patternPointEvent σ) (patternPointEvent τ) := by
  apply Set.disjoint_left.2
  intro z hzσ hzτ
  simp only [patternPointEvent, mem_iUnion, mem_inter_iff, mem_preimage] at hzσ hzτ
  obtain ⟨qx, qy, hσ, hx, hy⟩ := hzσ
  obtain ⟨rx, ry, hτ, hrx, hry⟩ := hzτ
  have heqx : qx = rx := by
    by_contra hne
    exact Set.disjoint_left.1 (Permuton.rankChamber_pairwise_disjoint hne) hx hrx
  have heqy : qy = ry := by
    by_contra hne
    exact Set.disjoint_left.1 (Permuton.rankChamber_pairwise_disjoint hne) hy hry
  apply hστ
  calc
    σ = Circular.relativePermutation qx qy := hσ.symm
    _ = Circular.relativePermutation rx ry := by rw [heqx, heqy]
    _ = τ := hτ

/-- All twenty-four pattern events are pairwise disjoint; in particular this
holds for the eight events indexed by `Circular.dihedral4`.
@isnad1 id=pairwise.0h0v.s6.7db7a6e3ea57 from=translated src=- shape=c65b5bb9 vocab=25314852
-/
theorem patternPointEvent_pairwise_disjoint :
    Pairwise (fun σ τ : Perm4 => Disjoint (patternPointEvent σ) (patternPointEvent τ)) := by
  intro σ τ hστ
  exact patternPointEvent_disjoint hστ

/--
@isnad1 id=pairwise.0h0v.s6.dea64395b529 from=translated src=- shape=0ad2b0a6 vocab=37e5eee6
-/
theorem dihedralPatternEvents_pairwise_disjoint :
    Set.Pairwise (↑Circular.dihedral4)
      (fun σ τ => Disjoint (patternPointEvent σ) (patternPointEvent τ)) := by
  intro σ hσ τ hτ hστ
  exact patternPointEvent_disjoint hστ

/-- The event used in `Permuton.dihedralDensity` is exactly the finite union
of the eight individual pattern events.
@isnad1 id=eq.0h0v.s5.8e1543bcd754 from=translated src=- shape=98ae3b5a vocab=01a55717
-/
theorem dihedralPointEvent_eq_biUnion_patternPointEvent :
    Permuton.dihedralPointEvent =
      ⋃ σ ∈ Circular.dihedral4, patternPointEvent σ := by
  ext z
  simp only [Permuton.dihedralPointEvent, patternPointEvent, mem_iUnion,
    mem_inter_iff, mem_preimage, Circular.isDihedral4_iff_mem]
  constructor
  · rintro ⟨qx, qy, hd, hx, hy⟩
    exact ⟨Circular.relativePermutation qx qy, hd, qx, qy, rfl, hx, hy⟩
  · rintro ⟨σ, hσ, qx, qy, hpattern, hx, hy⟩
    exact ⟨qx, qy, hpattern.symm ▸ hσ, hx, hy⟩

/-- The individual four-pattern density `d(σ, μ)` from the paper.-/
noncomputable def d (σ : Perm4) (μ : Permuton.BorelPermuton) : ℝ :=
  (Measure.pi (fun _ : Four => μ.measure) (patternPointEvent σ)).toReal

/-- The sum of the eight individual densities is the dihedral-event density
used by the analytic development.
@isnad1 id=eq.0h1v.s4.9050e2ff8a56 from=translated src=- shape=09e22ce3 vocab=89930ca6
-/
theorem sum_d_dihedral4_eq_dihedralDensity (μ : Permuton.BorelPermuton) :
    (∑ σ ∈ Circular.dihedral4, d σ μ) = Permuton.dihedralDensity μ := by
  let ν : Measure (Four → ℝ × ℝ) := Measure.pi fun _ : Four => μ.measure
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have hmeasure :
      ν.real (⋃ σ ∈ Circular.dihedral4, patternPointEvent σ) =
        ∑ σ ∈ Circular.dihedral4, ν.real (patternPointEvent σ) := by
    exact measureReal_biUnion_finset dihedralPatternEvents_pairwise_disjoint
      (fun σ hσ => measurableSet_patternPointEvent σ)
  change (∑ σ ∈ Circular.dihedral4, ν.real (patternPointEvent σ)) =
    ν.real Permuton.dihedralPointEvent
  calc
    (∑ σ ∈ Circular.dihedral4, ν.real (patternPointEvent σ)) =
        ν.real (⋃ σ ∈ Circular.dihedral4, patternPointEvent σ) := hmeasure.symm
    _ = ν.real Permuton.dihedralPointEvent := by
      rw [← dihedralPointEvent_eq_biUnion_patternPointEvent]

/-- The cited theorem in the literal notation of the paper.-/
def PublishedPermutonPatternSumInequality : Prop :=
  ∀ μ : Permuton.BorelPermuton,
    (1 : ℝ) / 3 ≤ ∑ σ ∈ Circular.dihedral4, d σ μ

/-- The literal sum formulation is exactly equivalent to the event-level
external hypothesis used elsewhere in the formalization.
@isnad1 id=iff.0h0v.s1.94d64c5e8fbe from=translated src=- shape=25b03439 vocab=d1cb8fa9
-/
theorem publishedPermutonPatternSumInequality_iff :
    PublishedPermutonPatternSumInequality ↔
      Permuton.PublishedPermutonInequality := by
  constructor
  · intro h μ
    rw [← sum_d_dihedral4_eq_dihedralDensity]
    exact h μ
  · intro h μ
    rw [sum_d_dihedral4_eq_dihedralDensity]
    exact h μ

end QuartetDistance.PermutonPatterns
