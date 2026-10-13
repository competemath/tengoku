/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Second moments of local event counts

Under a product of probability measures, two events that depend on disjoint finite
sets of coordinates have independent indicators, so their covariance vanishes; any
two unit indicators have covariance at most one. Summing over pairs bounds the
variance of the event count, and Chebyshev's inequality bounds its deviation.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]

omit [Fintype ι] in
/-- The indicator of a measurable set depending only on the coordinates in `S` is a
measurable function of those coordinates.
@isnad1 id=ex.2h5v.s8.63eb4cb8fd2c from=translated src=- shape=a6f22443 vocab=35e83637
-/
theorem exists_indicator_eq_comp {S : Finset ι} {A : Set (Π i, Ω i)} (hA : MeasurableSet A)
    (hdep : ∀ ω ω' : Π i, Ω i, (∀ i ∈ S, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A))
    (ω₀ : Π i, Ω i) :
    ∃ g : (Π i : S, Ω i) → ℝ, Measurable g ∧
      A.indicator (fun _ => (1 : ℝ)) = g ∘ fun ω (i : S) => ω i := by
  refine ⟨fun y => A.indicator (fun _ => (1 : ℝ)) (Function.updateFinset ω₀ S y),
    (measurable_const.indicator hA).comp measurable_updateFinset, ?_⟩
  funext ω
  have hmem : Function.updateFinset ω₀ S (fun i : S => ω i) ∈ A ↔ ω ∈ A :=
    hdep _ _ fun i hi => by simp [Function.updateFinset, hi]
  exact Set.indicator_eq_indicator (f := fun _ => (1 : ℝ)) (g := fun _ => (1 : ℝ))
    hmem.symm rfl

/-- Events depending on disjoint coordinate sets have independent indicators under a
product of probability measures.
@isnad1 id=indepfun.5h7v.s8.d4d9364019b4 from=translated src=- shape=bddd1313 vocab=71d6ac25
-/
theorem indepFun_indicator_of_disjoint {S T : Finset ι} {A B : Set (Π i, Ω i)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hdepA : ∀ ω ω' : Π i, Ω i, (∀ i ∈ S, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A))
    (hdepB : ∀ ω ω' : Π i, Ω i, (∀ i ∈ T, ω i = ω' i) → (ω ∈ B ↔ ω' ∈ B))
    (hST : Disjoint S T) :
    IndepFun (A.indicator fun _ => (1 : ℝ)) (B.indicator fun _ => (1 : ℝ)) (Measure.pi μ) := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure (Measure.pi μ)
  obtain ⟨g, hg, hgA⟩ := exists_indicator_eq_comp hA hdepA ω₀
  obtain ⟨h, hh, hhB⟩ := exists_indicator_eq_comp hB hdepB ω₀
  have hind : iIndepFun (fun i (ω : Π i, Ω i) => ω i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun i => (id : Ω i → Ω i)) fun _ => aemeasurable_id
  rw [hgA, hhB]
  exact (hind.indepFun_finset S T hST fun i => measurable_pi_apply i).comp hg hh

end Algebraic.Cutwidth.Gaussian.Internal
