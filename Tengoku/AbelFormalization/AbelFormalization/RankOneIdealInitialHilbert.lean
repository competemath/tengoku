import Tengoku.AbelFormalization.AbelFormalization.RankOneLexicographicWindowCompatibility

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Ordinary Hilbert lengths of rank-one lexicographic initial ideals

The ordinary-degree slice is embedded in the finite ordered product of
lexicographic weight pieces.  Fixed-degree rank-one compatibility identifies
the embedded slice of the lexicographic initial ideal with the finite-weight
initial submodule of the original embedded slice.  The exact-sequence theorem
`finiteWeightInitial_length` then proves equality of their module lengths.

Artinian or Noetherian hypotheses are not needed for this equality.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- If an injective realization identifies one submodule with the
finite-weight initial of another, the original two submodules have equal
length.
@isnad1 id=eq.2h7v.s9.ea12dc7f5363 from=translated src=- shape=40c480c9 vocab=a2024b03
-/
theorem submodule_length_eq_of_map_eq_finiteWeightInitial
    {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {m : ℕ} {M : Fin m → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (embedding : V →ₗ[R] (∀ i, M i))
    (embedding_injective : Function.Injective embedding)
    (source target : Submodule R V)
    (hcompat : target.map embedding =
      finiteWeightInitial (source.map embedding)) :
    Module.length R target = Module.length R source := by
  calc
    Module.length R target = Module.length R (target.map embedding) :=
      (Submodule.equivMapOfInjective embedding embedding_injective
        target).length_eq
    _ = Module.length R (finiteWeightInitial (source.map embedding)) := by
      rw [hcompat]
    _ = Module.length R (source.map embedding) :=
      finiteWeightInitial_length (source.map embedding)
    _ = Module.length R source :=
      (Submodule.equivMapOfInjective embedding embedding_injective
        source).length_eq.symm

/-- A negative ordinary degree has no rank-one monomials when the module
shift is zero.
@isnad1 id=eq.1h4v.s8.11faca82cea3 from=translated src=- shape=5c05d17a vocab=7f4def92
-/
theorem rankOne_ordinaryPolynomialModulePiece_eq_bot_of_neg
    (ordinaryDegree : Fin n → ℕ) {degree : ℤ} (hdegree : degree < 0) :
    artinianPolynomialModulePiece (B := B)
        ordinaryDegree (fun _ : Fin 1 => 0) degree = ⊥ := by
  apply le_antisymm
  · intro P hP
    rw [Submodule.mem_bot]
    funext k
    apply MvPolynomial.ext
    intro d
    by_contra hcoeff
    have hterm :=
      (mem_artinianPolynomialModuleSupported _ _).mp hP k d hcoeff
    have hweight : (Finsupp.weight ordinaryDegree d : ℤ) = degree := by
      simpa [artinianPolynomialDegreeTerms,
        artinianPolynomialTermDegree] using hterm
    have hnonneg : 0 ≤ degree := by
      rw [← hweight]
      exact Int.natCast_nonneg _
    exact (not_lt_of_ge hnonneg) hdegree
  · exact bot_le

/-- Consequently every submodule cut out inside a negative rank-one degree
piece is zero.
@isnad1 id=eq.1h5v.s11.a0af9fc38965 from=translated src=- shape=0343f1a9 vocab=18a2fcd4
-/
theorem rankOne_artinianPolynomialSubmoduleDegree_eq_bot_of_neg
    (ordinaryDegree : Fin n → ℕ)
    (I : Ideal (MvPolynomial (Fin n) B))
    {degree : ℤ} (hdegree : degree < 0) :
    artinianPolynomialSubmoduleDegree
        (rankOnePolynomialIdealSubmodule I)
        ordinaryDegree (fun _ : Fin 1 => 0) degree = ⊥ := by
  apply bot_unique
  intro P hP
  rw [Submodule.mem_bot]
  apply Subtype.ext
  have hPbot : (P : artinianFreePolynomialModule B n 1) ∈
      (⊥ : Submodule B (artinianFreePolynomialModule B n 1)) := by
    rw [← rankOne_ordinaryPolynomialModulePiece_eq_bot_of_neg
      ordinaryDegree hdegree]
    exact P.property
  rw [Submodule.mem_bot] at hPbot
  exact hPbot

end AbelFormalization
