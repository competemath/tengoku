import Tengoku.AbelFormalization.AbelFormalization.OrdinaryHomogenization
import Tengoku.AbelFormalization.AbelFormalization.OrdinaryHomogeneousDehomogenizationHeight
import Tengoku.Seed.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Flat ordinary homogenization

This scratch module puts the outer homogenizing variable used by
`ordinaryHomogenize` into the same `MvPolynomial` variable type as the
original variables.  The distinguished homogenizing variable is the unique
element of `Fin 1` on the left of `Fin 1 ⊕ ι`.

The construction is transported through an explicit algebra equivalence,
so the existing height theorem for full ordinary homogenization applies
without any new commutative-algebra argument.  The remaining proofs record
that the transported generators are homogeneous and that evaluation at the
distinguished variable equal to one recovers the original ideal exactly.
-/

noncomputable section

namespace AbelFormalization

variable {R ι : Type*}

/-- `none` is the new homogenizing variable and `some i` is the old variable
`i`.  This is stated explicitly instead of hiding the variable convention in
an arbitrary cardinality equivalence.-/
def optionEquivFinOneSum (ι : Type*) : Option ι ≃ Fin 1 ⊕ ι where
  toFun
    | none => Sum.inl 0
    | some i => Sum.inr i
  invFun
    | Sum.inl _ => none
    | Sum.inr i => some i
  left_inv := by
    intro i
    cases i <;> rfl
  right_inv := by
    intro i
    rcases i with j | j
    · change Sum.inl (0 : Fin 1) = Sum.inl j
      exact congrArg Sum.inl (Subsingleton.elim _ _)
    · rfl

/--
@isnad1 id=eq.0h1v.s6.8994be8e4af3 from=translated src=- shape=85a28be7 vocab=01f15218
-/
@[simp]
theorem optionEquivFinOneSum_none :
    optionEquivFinOneSum ι none = Sum.inl 0 :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.a65dffe3f16d from=translated src=- shape=56bda619 vocab=0de1da7c
-/
@[simp]
theorem optionEquivFinOneSum_some (i : ι) :
    optionEquivFinOneSum ι (some i) = Sum.inr i :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.07a09429fcb4 from=translated src=- shape=55b83378 vocab=655963a1
-/
@[simp]
theorem optionEquivFinOneSum_symm_inl (j : Fin 1) :
    (optionEquivFinOneSum ι).symm (Sum.inl j) = none :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.e6e3927f916c from=translated src=- shape=521ba5d1 vocab=1f06677a
-/
@[simp]
theorem optionEquivFinOneSum_symm_inr (i : ι) :
    (optionEquivFinOneSum ι).symm (Sum.inr i) = some i :=
  rfl

section Semiring

variable [CommSemiring R]

/-- Regroup a flat polynomial in the variables `Fin 1 ⊕ ι` as a
univariate polynomial in the distinguished variable, with coefficients in
the old multivariate polynomial ring.-/
def flatPolynomialEquiv (R : Type*) [CommSemiring R] (ι : Type*) :
    MvPolynomial (Fin 1 ⊕ ι) R ≃ₐ[R]
      Polynomial (MvPolynomial ι R) :=
  (MvPolynomial.renameEquiv R (optionEquivFinOneSum ι).symm).trans
    (MvPolynomial.optionEquivLeft R ι)

/--
@isnad1 id=eq.0h3v.s9.26abbf639957 from=translated src=- shape=d6bd927d vocab=f5d4ce3a
-/
@[simp]
theorem flatPolynomialEquiv_C (r : R) :
    flatPolynomialEquiv R ι (MvPolynomial.C r) =
      Polynomial.C (MvPolynomial.C r) := by
  simp [flatPolynomialEquiv]

/--
@isnad1 id=eq.0h3v.s8.3dbc0b6de148 from=translated src=- shape=f61013c5 vocab=5d0f61ce
-/
@[simp]
theorem flatPolynomialEquiv_X_left (j : Fin 1) :
    flatPolynomialEquiv R ι (MvPolynomial.X (Sum.inl j)) =
      Polynomial.X := by
  simp [flatPolynomialEquiv]

/--
@isnad1 id=eq.0h3v.s9.0ea5875473f0 from=translated src=- shape=f4e703ed vocab=8289de65
-/
@[simp]
theorem flatPolynomialEquiv_X_right (i : ι) :
    flatPolynomialEquiv R ι (MvPolynomial.X (Sum.inr i)) =
      Polynomial.C (MvPolynomial.X i) := by
  simp [flatPolynomialEquiv]

/-- The Option-indexed form of ordinary homogenization, before renaming
`none` and `some i` to the two summands of `Fin 1 ⊕ ι`.-/
def optionOrdinaryHomogenize (f : MvPolynomial ι R) :
    MvPolynomial (Option ι) R :=
  (MvPolynomial.optionEquivLeft R ι).symm (ordinaryHomogenize f)

/-- Ordinary homogenization as one flat multivariate polynomial.-/
def flatOrdinaryHomogenize (f : MvPolynomial ι R) :
    MvPolynomial (Fin 1 ⊕ ι) R :=
  (flatPolynomialEquiv R ι).symm (ordinaryHomogenize f)

/--
@isnad1 id=eq.0h3v.s8.73eefc3fd219 from=translated src=- shape=fc47e3be vocab=36648062
-/
theorem flatOrdinaryHomogenize_eq_rename (f : MvPolynomial ι R) :
    flatOrdinaryHomogenize f =
      MvPolynomial.rename (optionEquivFinOneSum ι)
        (optionOrdinaryHomogenize f) := by
  rfl

private theorem optionEquivLeft_symm_monomial
    (d : ι →₀ ℕ) (k : ℕ) (r : R) :
    (MvPolynomial.optionEquivLeft R ι).symm
        (Polynomial.monomial k (MvPolynomial.monomial d r)) =
      MvPolynomial.monomial (d.optionElim k) r := by
  apply (MvPolynomial.optionEquivLeft R ι).injective
  rw [AlgEquiv.apply_symm_apply]
  simpa using
    (MvPolynomial.optionEquivLeft_monomial
      (R := R) (S₁ := ι) (d.optionElim k) r).symm

private theorem degree_optionElim (d : ι →₀ ℕ) (k : ℕ) :
    (d.optionElim k).degree = k + d.degree := by
  classical
  have hsplit :
      d.optionElim k =
        Finsupp.single none k + d.embDomain Function.Embedding.some := by
    ext i
    rcases i with _ | i <;> simp
  rw [hsplit, map_add, Finsupp.degree_single,
    Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]

/-- The Option-indexed homogenization is homogeneous of the original total
degree.  This includes the zero polynomial, for which mathlib's total degree
is zero.
@isnad1 id=ishomoge.0h3v.s4.acb90d34dd3e from=translated src=- shape=161690f2 vocab=cb3aa2d6
-/
theorem optionOrdinaryHomogenize_isHomogeneous
    (f : MvPolynomial ι R) :
    (optionOrdinaryHomogenize f).IsHomogeneous f.totalDegree := by
  classical
  rw [optionOrdinaryHomogenize, ordinaryHomogenize, map_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  rw [optionEquivLeft_symm_monomial]
  apply MvPolynomial.isHomogeneous_monomial
  rw [degree_optionElim]
  change f.totalDegree - d.degree + d.degree = f.totalDegree
  apply Nat.sub_add_cancel
  exact MvPolynomial.le_totalDegree hd

/-- Every flat ordinary homogenization is homogeneous of its original total
degree for the ordinary grading in which all variables, including `H`, have
degree one.
@isnad1 id=ishomoge.0h3v.s5.f656d69e6f66 from=translated src=- shape=725fb8ed vocab=e058785f
-/
theorem flatOrdinaryHomogenize_isHomogeneous
    (f : MvPolynomial ι R) :
    (flatOrdinaryHomogenize f).IsHomogeneous f.totalDegree := by
  rw [flatOrdinaryHomogenize_eq_rename]
  exact (optionOrdinaryHomogenize_isHomogeneous f).rename_isHomogeneous

/-- Full flat ordinary homogenization is the transport of the existing full
ordinary homogenization ideal across the polynomial regrouping equivalence.-/
def flatFullOrdinaryHomogenization (I : Ideal (MvPolynomial ι R)) :
    Ideal (MvPolynomial (Fin 1 ⊕ ι) R) :=
  (fullOrdinaryHomogenization I).map
    (flatPolynomialEquiv R ι).symm.toRingHom

/-- Generator presentation of the transported full ideal.
@isnad1 id=eq.0h3v.s7.207d876bd5e3 from=translated src=- shape=c0d79864 vocab=ad02734a
-/
theorem flatFullOrdinaryHomogenization_eq_span
    (I : Ideal (MvPolynomial ι R)) :
    flatFullOrdinaryHomogenization I =
      Ideal.span
        (flatOrdinaryHomogenize '' (I : Set (MvPolynomial ι R))) := by
  rw [flatFullOrdinaryHomogenization, fullOrdinaryHomogenization,
    Ideal.map_span, Set.image_image]
  rfl

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The flat full ideal is homogeneous for ordinary total degree.
@isnad1 id=ishomoge.0h3v.s7.0c75afbecb6a from=translated src=- shape=a9fa8169 vocab=a97430d5
-/
theorem flatFullOrdinaryHomogenization_isHomogeneous
    (I : Ideal (MvPolynomial ι R)) :
    (flatFullOrdinaryHomogenization I).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ : Fin 1 ⊕ ι => (1 : ℕ))) := by
  rw [flatFullOrdinaryHomogenization_eq_span]
  refine Ideal.homogeneous_span
    (MvPolynomial.weightedHomogeneousSubmodule R
      (fun _ : Fin 1 ⊕ ι => (1 : ℕ))) _ ?_
  rintro _ ⟨f, _, rfl⟩
  refine ⟨f.totalDegree, ?_⟩
  exact flatOrdinaryHomogenize_isHomogeneous f

end Semiring

section Ring

variable [CommRing R]

/-- Under the flat regrouping equivalence, setting the left variable equal
to one is exactly evaluation of the outer polynomial variable at one.
@isnad1 id=eq.0h2v.s9.33f5734b3d69 from=translated src=- shape=8bbe58cc vocab=96b931c2
-/
theorem ordinaryDehomogenizationHom_eq_eval_comp_flatPolynomialEquiv :
    ordinaryDehomogenizationHom (B := R) (ι := ι) =
      (Polynomial.evalRingHom (1 : MvPolynomial ι R)).comp
        (flatPolynomialEquiv R ι).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · rintro (j | i)
    · simp
    · simp

/-- Dehomogenizing a transported ordinary homogenization recovers its input
exactly.
@isnad1 id=eq.0h3v.s7.032504d8fbe3 from=translated src=- shape=1d3e5fd8 vocab=b76d7cfa
-/
@[simp]
theorem ordinaryDehomogenizationHom_flatOrdinaryHomogenize
    (f : MvPolynomial ι R) :
    ordinaryDehomogenizationHom (B := R) (ι := ι)
        (flatOrdinaryHomogenize f) = f := by
  rw [ordinaryDehomogenizationHom_eq_eval_comp_flatPolynomialEquiv]
  simp [flatOrdinaryHomogenize]

/-- Dehomogenization at `H = 1` of the full flat homogenization is the
original ideal, as an equality of ideals rather than only a generator-wise
containment.
@isnad1 id=eq.0h3v.s8.e708b9b3a412 from=translated src=- shape=41e61012 vocab=a2ea805e
-/
theorem flatFullOrdinaryHomogenization_map_dehomogenization
    (I : Ideal (MvPolynomial ι R)) :
    (flatFullOrdinaryHomogenization I).map
        (ordinaryDehomogenizationHom (B := R) (ι := ι)) = I := by
  rw [flatFullOrdinaryHomogenization_eq_span, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    simpa using hf
  · intro f hf
    apply Ideal.subset_span
    refine ⟨flatOrdinaryHomogenize f, ⟨f, hf, rfl⟩, ?_⟩
    exact ordinaryDehomogenizationHom_flatOrdinaryHomogenize f

end Ring

end AbelFormalization
