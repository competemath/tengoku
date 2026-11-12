import Tengoku.AbelFormalization.AbelFormalization.WeightedDeformationGenerators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Homogeneous components of the full weighted initial ideal

The least-weight generators make the full initial ideal homogeneous. Two
independent weight projections commute, including over coefficient rings
with zero divisors. These facts allow successive weight refinements without
treating arbitrary members of a homogeneous ideal as homogeneous elements.
-/

noncomputable section

namespace AbelFormalization

section Components

variable {R ι M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]

/-- Two weight projections are commuting filters on the coefficient support.
@isnad1 id=eq.0h9v.s9.c8ec58fc3edb from=translated src=- shape=d1a9c6bf vocab=a567b01f
-/
theorem weightedHomogeneousComponents_commute (ω : ι → M) (ν : ι → N)
    (α : M) (β : N) (f : MvPolynomial ι R) :
    MvPolynomial.weightedHomogeneousComponent ω α
        (MvPolynomial.weightedHomogeneousComponent ν β f) =
      MvPolynomial.weightedHomogeneousComponent ν β
        (MvPolynomial.weightedHomogeneousComponent ω α f) := by
  classical
  ext d
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs <;> rfl

/-- Projecting for one grading preserves homogeneity for another grading.
@isnad1 id=isweight.1h9v.s7.bf71bddd6dcb from=translated src=- shape=46fef16f vocab=8e4695d3
-/
theorem weightedHomogeneousComponent_preserves_homogeneity
    (ω : ι → M) (ν : ι → N) (α : M) {β : N} {f : MvPolynomial ι R}
    (hf : f.IsWeightedHomogeneous ν β) :
    (MvPolynomial.weightedHomogeneousComponent ω α f).IsWeightedHomogeneous ν β := by
  classical
  intro d hd
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hd
  split_ifs at hd with hweight
  · exact hf hd
  · exact (hd rfl).elim

/-- A finite sum indexed by the weights actually occurring in the support.
@isnad1 id=eq.0h5v.s8.f5db6681b7f6 from=translated src=- shape=1a6994b0 vocab=0c0eee0c
-/
theorem sum_weightedHomogeneousComponent_support [DecidableEq M] (ω : ι → M)
    (f : MvPolynomial ι R) :
    (∑ α ∈ f.support.image (Finsupp.weight ω),
      MvPolynomial.weightedHomogeneousComponent ω α f) = f := by
  classical
  ext d
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (Finsupp.weight ω d)]
  · simp
  · intro α hα hne
    simp [Ne.symm hne]
  · intro hd
    simp only [ite_true]
    by_contra hcoeff
    exact hd (Finset.mem_image.mpr ⟨d, MvPolynomial.mem_support_iff.mpr hcoeff, rfl⟩)

end Components

section InitialIdeal

variable {R ι : Type*} [CommRing R]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The full initial ideal is homogeneous for the weight used to form it.
@isnad1 id=ishomoge.0h4v.s7.a092a9470304 from=translated src=- shape=61683f1d vocab=6605fa44
-/
theorem weightedInitialIdeal_isHomogeneous (ω : ι → ℤ)
    (I : Ideal (MvPolynomial ι R)) :
    (weightedInitialIdeal ω I).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R ω) := by
  classical
  apply Ideal.homogeneous_span
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨minimumSupportWeight ω f,
    MvPolynomial.weightedHomogeneousComponent_mem ω f (minimumSupportWeight ω f)⟩

/-- Every weight component of every member belongs to the full initial ideal.
@isnad1 id=mem.1h6v.s9.0f6cc53af647 from=translated src=- shape=45096a23 vocab=e9d03784
-/
theorem weightedInitialIdeal_component_mem (ω : ι → ℤ)
    (I : Ideal (MvPolynomial ι R)) {g : MvPolynomial ι R}
    (hg : g ∈ weightedInitialIdeal ω I) (α : ℤ) :
    MvPolynomial.weightedHomogeneousComponent ω α g ∈ weightedInitialIdeal ω I :=
  MvPolynomial.weightedHomogeneousComponent_mem_of_mem R ω
    (weightedInitialIdeal_isHomogeneous ω I) hg α

/-- A nonzero homogeneous polynomial has exactly its homogeneous weight
as its minimum support weight.
@isnad1 id=eq.2h5v.s6.a601ef9d5dad from=translated src=- shape=85f0198c vocab=148b5850
-/
theorem minimumSupportWeight_of_homogeneous (ω : ι → ℤ)
    {α : ℤ} {f : MvPolynomial ι R} (hf : f.IsWeightedHomogeneous ω α)
    (hne : f ≠ 0) : minimumSupportWeight ω f = α := by
  obtain ⟨d, hd, hmin⟩ := exists_support_weight_eq_minimum ω hne
  exact hmin.symm.trans (hf (MvPolynomial.mem_support_iff.mp hd))

/-- Initial formation fixes ideals already homogeneous for that weight.
@isnad1 id=eq.1h4v.s7.a6c19e62db1e from=translated src=- shape=f34c9ddd vocab=6605fa44
-/
theorem weightedInitialIdeal_eq_of_homogeneous (ω : ι → ℤ)
    (I : Ideal (MvPolynomial ι R))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule R ω)) :
    weightedInitialIdeal ω I = I := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem R ω hI hf _
  · intro f hf
    rw [← sum_weightedHomogeneousComponent_support ω f]
    apply Ideal.sum_mem
    intro α hα
    let g := MvPolynomial.weightedHomogeneousComponent ω α f
    have hg : g ∈ I :=
      MvPolynomial.weightedHomogeneousComponent_mem_of_mem R ω hI hf α
    by_cases hzero : g = 0
    · change g ∈ weightedInitialIdeal ω I
      rw [hzero]
      exact (weightedInitialIdeal ω I).zero_mem
    · have hhom : g.IsWeightedHomogeneous ω α :=
        MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous α f
      have hmin := minimumSupportWeight_of_homogeneous ω hhom hzero
      have heq : MvPolynomial.weightedHomogeneousComponent ω
          (minimumSupportWeight ω g) g = g := by
        rw [hmin]
        exact hhom.weightedHomogeneousComponent_same
      have hmem : MvPolynomial.weightedHomogeneousComponent ω
          (minimumSupportWeight ω g) g ∈ weightedInitialIdeal ω I :=
        Ideal.subset_span ⟨g, hg, rfl⟩
      change g ∈ weightedInitialIdeal ω I
      rwa [heq] at hmem

end InitialIdeal

end AbelFormalization
