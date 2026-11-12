import Tengoku.AbelFormalization.AbelFormalization.LexicographicInitialIdealComponents

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Secondary homogeneity of lexicographic initial ideals

Lexicographic initial formation filters coefficients by the chosen vector
weight.  That filter commutes with every second weighted grading.  Hence an
ideal homogeneous for a second grading has a lexicographic initial ideal
homogeneous for the same grading.  A prescribed lexicographic component can
also be lifted by a polynomial homogeneous for that second grading.

No relation between the two variable-weight functions is needed.
-/

noncomputable section

namespace AbelFormalization

variable {R ι M : Type*} [CommRing R] [AddCommMonoid M] {h : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- Taking a component for an arbitrary second grading commutes with taking
the least lexicographic form.  The nonzero hypothesis identifies that
component with the least lexicographic form of the corresponding component
of the original polynomial.
@isnad1 id=eq.1h8v.s9.bd12e0c9bc03 from=translated src=- shape=c29e17b7 vocab=2fc37b2a
-/
theorem lexicographicInitialForm_of_weightedComponent
    (secondaryWeight : ι → M) (multiWeight : ι → Fin h → ℤ)
    (degree : M) (f : MvPolynomial ι R)
    (hne : MvPolynomial.weightedHomogeneousComponent secondaryWeight degree
      (lexicographicInitialForm multiWeight f) ≠ 0) :
    lexicographicInitialForm multiWeight
        (MvPolynomial.weightedHomogeneousComponent secondaryWeight degree f) =
      MvPolynomial.weightedHomogeneousComponent secondaryWeight degree
        (lexicographicInitialForm multiWeight f) := by
  classical
  let p := MvPolynomial.weightedHomogeneousComponent secondaryWeight degree f
  let beta := lexicographicMinimumWeight multiWeight f
  have hcomm :
      MvPolynomial.weightedHomogeneousComponent
          (fun i => toLex (multiWeight i)) beta p =
        MvPolynomial.weightedHomogeneousComponent secondaryWeight degree
          (lexicographicInitialForm multiWeight f) := by
    exact weightedHomogeneousComponents_commute
      (fun i => toLex (multiWeight i)) secondaryWeight beta degree f
  have hbound : ∀ d ∈ p.support,
      beta ≤ Finsupp.weight (fun i => toLex (multiWeight i)) d := by
    intro d hd
    have hsupport : p.support ⊆ f.support := by
      change
        (MvPolynomial.weightedHomogeneousComponent secondaryWeight degree f).support ⊆
          f.support
      rw [MvPolynomial.support_weightedHomogeneousComponent]
      exact Finset.filter_subset _ _
    exact lexicographicMinimumWeight_le multiWeight f (hsupport hd)
  have hmin : lexicographicMinimumWeight multiWeight p = beta :=
    lexicographicMinimumWeight_eq_of_component_ne_zero
      multiWeight p beta hbound (by rwa [hcomm])
  change MvPolynomial.weightedHomogeneousComponent
    (fun i => toLex (multiWeight i))
      (lexicographicMinimumWeight multiWeight p) p = _
  rw [hmin]
  exact hcomm

/-- Lexicographic initial formation preserves homogeneity for any independent
secondary weighted grading.  In particular, `secondaryWeight` may be the
positive ordinary-degree function while `multiWeight` is the signed vector
weight used for the initial ideal.
@isnad1 id=ishomoge.1h7v.s8.b56dd5335fbc from=translated src=- shape=72804371 vocab=72b0c61d
-/
theorem lexicographicInitialIdeal_isHomogeneous_of_isHomogeneous
    [DecidableEq M]
    (secondaryWeight : ι → M) (multiWeight : ι → Fin h → ℤ)
    (I : Ideal (MvPolynomial ι R))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R secondaryWeight)) :
    (lexicographicInitialIdeal multiWeight I).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R secondaryWeight) := by
  classical
  rw [Ideal.IsHomogeneous.iff_eq]
  apply le_antisymm
  · exact Ideal.toIdeal_homogeneousCore_le _ _
  · apply Ideal.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    rw [← sum_weightedHomogeneousComponent_support secondaryWeight
      (lexicographicInitialForm multiWeight f)]
    apply Ideal.sum_mem
    intro degree hdegree
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    · exact ⟨degree,
        MvPolynomial.weightedHomogeneousComponent_mem secondaryWeight
          (lexicographicInitialForm multiWeight f) degree⟩
    · by_cases hzero :
          MvPolynomial.weightedHomogeneousComponent secondaryWeight degree
            (lexicographicInitialForm multiWeight f) = 0
      · rw [hzero]
        exact (lexicographicInitialIdeal multiWeight I).zero_mem
      · rw [← lexicographicInitialForm_of_weightedComponent
          secondaryWeight multiWeight degree f hzero]
        exact lexicographicInitialForm_mem_initialIdeal multiWeight I
          (MvPolynomial.weightedHomogeneousComponent_mem_of_mem R
            secondaryWeight hI hf degree)

/-- Ordinary-degree specialization of preservation of secondary
homogeneity.
@isnad1 id=ishomoge.1h6v.s8.67717794c232 from=translated src=- shape=30fbc06e vocab=39dd15db
-/
theorem lexicographicInitialIdeal_isOrdinaryHomogeneous
    (ordinaryDegree : ι → ℕ) (multiWeight : ι → Fin h → ℤ)
    (I : Ideal (MvPolynomial ι R))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R ordinaryDegree)) :
    (lexicographicInitialIdeal multiWeight I).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R ordinaryDegree) :=
  lexicographicInitialIdeal_isHomogeneous_of_isHomogeneous
    ordinaryDegree multiWeight I hI

end AbelFormalization
