import Tengoku.Seed.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension
import Tengoku.Seed.Topology.DiscreteSubset
import Tengoku.Seed.Topology.Compactness.Lindelof
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Countable measurable injective partitions from local injectivity, and
local injectivity at nonsingular C¹ points. No semialgebraic hypothesis is used. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory

/-- A measurable subset of a second-countable space has a countable measurable
injective partition whenever the map is locally injective along that subset.
@isnad1 id=ex.2h4v.s7.d7b98e352112 from=translated src=- shape=55695cf2 vocab=dfc096d0
-/
theorem exists_measurable_injective_partition
    {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (S : Set X) (hS : MeasurableSet S) (f : X → Y)
    (hloc : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U) :
    ∃ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (⋃ n, A n) = S ∧ ∀ n, Set.InjOn f (A n) := by
  classical
  by_cases hne : S.Nonempty
  · choose U hU hxU hi using (fun x : S => hloc x.val x.property)
    obtain ⟨T, hT, hcov⟩ := TopologicalSpace.isOpen_iUnion_countable U hU
    have hTne : T.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      have hh : x ∈ ⋃ y : S, U y := mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
      rw [← hcov] at hh
      obtain ⟨y, hy⟩ := mem_iUnion.mp hh
      obtain ⟨hyT, _⟩ := mem_iUnion.mp hy
      exact ⟨y, hyT⟩
    obtain ⟨e, he⟩ := hT.exists_eq_range hTne
    let u (n : ℕ) := U (e n)
    have hSu : S ⊆ ⋃ n, u n := by
      intro x hx
      have hh : x ∈ ⋃ y : S, U y := mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
      rw [← hcov] at hh
      obtain ⟨y, hy⟩ := mem_iUnion.mp hh
      obtain ⟨hyT, hxy⟩ := mem_iUnion.mp hy
      rw [he] at hyT
      obtain ⟨n, rfl⟩ := hyT
      exact mem_iUnion.mpr ⟨n, hxy⟩
    refine ⟨fun n => S ∩ disjointed u n, ?_, ?_, ?_, ?_⟩
    · intro n
      exact hS.inter (MeasurableSet.disjointed (fun n => (hU (e n)).measurableSet) n)
    · exact pairwise_disjoint_mono (disjoint_disjointed u) (fun n => inter_subset_right)
    · rw [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left.mpr hSu]
    · intro n
      exact (hi (e n)).mono (inter_subset_right.trans (disjointed_subset u n))
  · have hzero : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst S
    refine ⟨fun _ => ∅, ?_, ?_, ?_, ?_⟩ <;> simp [Set.InjOn, Pairwise]

/--
@isnad1 id=countabl.1h5v.s6.805715688ade from=translated src=- shape=29b5eb9d vocab=a52624e9
-/
theorem countable_fiber_of_local_injectivity
    {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (S : Set X) (f : X → Y)
    (hloc : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U) (y : Y) :
    ({x | x ∈ S ∧ f x = y}).Countable := by
  have hd : IsDiscrete {x | x ∈ S ∧ f x = y} := by
    apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    intro x hx
    obtain ⟨U, hU, hxU, hinj⟩ := hloc x hx.1
    refine ⟨U, hU, ?_⟩
    ext z
    constructor
    · intro hz
      exact hinj hz.1 hxU (hz.2.2.trans hx.2.symm)
    · rintro rfl
      exact ⟨hxU, hx⟩
  exact (isLindelof_iff_lindelofSpace.mpr inferInstance).countable_of_isDiscrete hd

/--
@isnad1 id=ex.3h4v.s7.0cbb7a9dc30f from=translated src=- shape=32fbab7b vocab=96b1cd1f
-/
theorem exists_open_injective_of_contDiffAt_det_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} {D : E →L[ℝ] E} {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hD : HasFDerivAt f D x) (hdet : D.det ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U := by
  let e := D.toContinuousLinearEquivOfDetNeZero hdet
  have hDe : HasFDerivAt f (e : E →L[ℝ] E) x := hD
  let H := hf.toOpenPartialHomeomorph f hDe (by norm_num)
  exact ⟨H.source, H.open_source, hf.mem_toOpenPartialHomeomorph_source hDe (by norm_num),
    H.injOn⟩

end
end DuistermaatVanDerKallen
