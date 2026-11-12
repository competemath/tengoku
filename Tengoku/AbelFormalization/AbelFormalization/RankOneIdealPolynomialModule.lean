import Tengoku.AbelFormalization.AbelFormalization.PolynomialWindowDescent
import Tengoku.Seed.Algebra.Module.Submodule.Range
import Tengoku.Seed.Algebra.Module.Submodule.RestrictScalars

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Rank-one ideals as free polynomial submodules

The rank-one free polynomial module is literally

`Fin 1 → MvPolynomial (Fin n) B`.

This file records the concrete linear equivalence with the polynomial ring,
uses it to transport ideals to polynomial submodules, and relates that
transport to coefficient restriction and bounded polynomial windows.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

/-- Put a polynomial in the unique coordinate of the rank-one free
polynomial module.-/
def rankOnePolynomialModuleEquiv :
    MvPolynomial (Fin n) B ≃ₗ[MvPolynomial (Fin n) B]
      artinianFreePolynomialModule B n 1 where
  toFun := fun P _ => P
  invFun := fun P => P 0
  left_inv := fun _ => rfl
  right_inv := by
    intro P
    funext i
    exact congrArg P (Subsingleton.elim 0 i)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/--
@isnad1 id=eq.0h4v.s9.0c3426730eff from=translated src=- shape=c2ca2bfb vocab=53bbc133
-/
@[simp]
theorem rankOnePolynomialModuleEquiv_apply
    (P : MvPolynomial (Fin n) B) (i : Fin 1) :
    rankOnePolynomialModuleEquiv P i = P :=
  rfl

/--
@isnad1 id=eq.0h3v.s10.9e65f1b8f3fd from=translated src=- shape=95be6f8f vocab=8fe75f5f
-/
@[simp]
theorem rankOnePolynomialModuleEquiv_symm_apply
    (P : artinianFreePolynomialModule B n 1) :
    rankOnePolynomialModuleEquiv.symm P = P 0 :=
  rfl

/-- The same equivalence after restricting scalars from the polynomial ring
to its coefficient ring.-/
def rankOnePolynomialModuleCoeffEquiv :
    MvPolynomial (Fin n) B ≃ₗ[B]
      artinianFreePolynomialModule B n 1 :=
  rankOnePolynomialModuleEquiv.restrictScalars B

/--
@isnad1 id=eq.0h4v.s9.e89ba330982e from=translated src=- shape=650f80d8 vocab=5f84e9ad
-/
@[simp]
theorem rankOnePolynomialModuleCoeffEquiv_apply
    (P : MvPolynomial (Fin n) B) (i : Fin 1) :
    rankOnePolynomialModuleCoeffEquiv P i = P :=
  rfl

/--
@isnad1 id=eq.0h3v.s9.0f0ef869183a from=translated src=- shape=a419298d vocab=2190e3f3
-/
@[simp]
theorem rankOnePolynomialModuleCoeffEquiv_symm_apply
    (P : artinianFreePolynomialModule B n 1) :
    rankOnePolynomialModuleCoeffEquiv.symm P = P 0 :=
  rfl

/-- An ideal of the polynomial ring, regarded as a polynomial submodule of
the rank-one free polynomial module.-/
def rankOnePolynomialIdealSubmodule
    (I : Ideal (MvPolynomial (Fin n) B)) :
    Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n 1) :=
  Submodule.map rankOnePolynomialModuleEquiv.toLinearMap I

/-- Membership in the transported ideal is membership of the unique
coordinate in the original ideal.
@isnad1 id=iff.0h4v.s9.41189364b872 from=translated src=- shape=87ed9945 vocab=ee7f16d2
-/
@[simp]
theorem mem_rankOnePolynomialIdealSubmodule_iff
    (I : Ideal (MvPolynomial (Fin n) B))
    (P : artinianFreePolynomialModule B n 1) :
    P ∈ rankOnePolynomialIdealSubmodule I ↔ P 0 ∈ I := by
  rw [rankOnePolynomialIdealSubmodule, Submodule.mem_map_equiv]
  rfl

/-- The canonical rank-one vector of `P` belongs to the transported ideal
exactly when `P` belongs to the ideal.
@isnad1 id=iff.0h4v.s10.dbbfea330a85 from=translated src=- shape=ecdea37f vocab=908f7eb6
-/
@[simp]
theorem rankOnePolynomialModuleEquiv_mem_idealSubmodule_iff
    (I : Ideal (MvPolynomial (Fin n) B))
    (P : MvPolynomial (Fin n) B) :
    rankOnePolynomialModuleEquiv P ∈
        rankOnePolynomialIdealSubmodule I ↔
      P ∈ I := by
  rw [mem_rankOnePolynomialIdealSubmodule_iff,
    rankOnePolynomialModuleEquiv_apply]

/-- Mapping the transported submodule back through the inverse equivalence
recovers the ideal.
@isnad1 id=eq.0h3v.s9.aacb52c1b2b2 from=translated src=- shape=73e3bc7f vocab=c9bd363d
-/
@[simp]
theorem map_rankOnePolynomialIdealSubmodule_symm
    (I : Ideal (MvPolynomial (Fin n) B)) :
    (rankOnePolynomialIdealSubmodule I).map
        rankOnePolynomialModuleEquiv.symm.toLinearMap = I := by
  ext P
  simp

/-- Transport to the rank-one polynomial module reflects inclusion.
@isnad1 id=iff.0h4v.s9.406e45c402ac from=translated src=- shape=6a74a93e vocab=f307b60e
-/
theorem rankOnePolynomialIdealSubmodule_le_iff
    (I J : Ideal (MvPolynomial (Fin n) B)) :
    rankOnePolynomialIdealSubmodule I ≤
        rankOnePolynomialIdealSubmodule J ↔
      I ≤ J := by
  constructor
  · intro h P hP
    have hmap : rankOnePolynomialModuleEquiv P ∈
        rankOnePolynomialIdealSubmodule I := by
      simpa using hP
    have := h hmap
    simpa using this
  · intro h P hP
    rw [mem_rankOnePolynomialIdealSubmodule_iff] at hP ⊢
    exact h hP

/-- Transport from ideals to rank-one polynomial submodules is injective.
@isnad1 id=injectiv.0h2v.s7.930a3935127d from=translated src=- shape=6a19b44f vocab=41cc20de
-/
theorem rankOnePolynomialIdealSubmodule_injective :
    Function.Injective
      (rankOnePolynomialIdealSubmodule (B := B) (n := n)) := by
  intro I J hIJ
  apply le_antisymm
  · exact (rankOnePolynomialIdealSubmodule_le_iff I J).mp hIJ.le
  · exact (rankOnePolynomialIdealSubmodule_le_iff J I).mp hIJ.ge

/--
@isnad1 id=eq.0h2v.s9.2ba6c9b5692b from=translated src=- shape=d4744780 vocab=d18d1359
-/
@[simp]
theorem rankOnePolynomialIdealSubmodule_bot :
    rankOnePolynomialIdealSubmodule
        (⊥ : Ideal (MvPolynomial (Fin n) B)) = ⊥ := by
  ext P
  rw [mem_rankOnePolynomialIdealSubmodule_iff]
  constructor
  · intro hP
    rw [Submodule.mem_bot] at hP ⊢
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact hP
  · intro hP
    rw [Submodule.mem_bot] at hP ⊢
    simpa only [hP, Pi.zero_apply]

/--
@isnad1 id=eq.0h2v.s9.0024e3258d3f from=translated src=- shape=d4744780 vocab=a8f7b9a9
-/
@[simp]
theorem rankOnePolynomialIdealSubmodule_top :
    rankOnePolynomialIdealSubmodule
        (⊤ : Ideal (MvPolynomial (Fin n) B)) = ⊤ := by
  ext P
  simp

/-- Restricting the transported polynomial submodule to coefficient scalars
is the same as first restricting the ideal and then applying the
coefficient-linear rank-one equivalence.
@isnad1 id=eq.0h3v.s9.65a4fdaea872 from=translated src=- shape=68dd127e vocab=019163e9
-/
theorem rankOnePolynomialIdealSubmodule_restrictScalars
    (I : Ideal (MvPolynomial (Fin n) B)) :
    (rankOnePolynomialIdealSubmodule I).restrictScalars B =
      (I.restrictScalars B).map
        rankOnePolynomialModuleCoeffEquiv.toLinearMap := by
  change
    (Submodule.map rankOnePolynomialModuleEquiv.toLinearMap I).restrictScalars B = _
  rw [Submodule.restrictScalars_map]
  rfl

/-! ## Bounded-window compatibility -/

variable (G : PolynomialGradedLexData n 1 h)

/-- The coefficient-linear submodule of polynomials whose canonical
rank-one vector belongs to the bounded window.-/
def PolynomialGradedLexData.rankOnePolynomialWindowPreimage
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    Submodule B (MvPolynomial (Fin n) B) :=
  (G.windowModule B hpositive D).comap
    rankOnePolynomialModuleCoeffEquiv.toLinearMap

/--
@isnad1 id=iff.1h6v.s10.12273262df29 from=translated src=- shape=dce23059 vocab=91c0b5be
-/
@[simp]
theorem PolynomialGradedLexData.mem_rankOnePolynomialWindowPreimage_iff
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (P : MvPolynomial (Fin n) B) :
    P ∈ G.rankOnePolynomialWindowPreimage hpositive D ↔
      rankOnePolynomialModuleCoeffEquiv P ∈
        G.windowModule B hpositive D :=
  Iff.rfl

/-- Concrete coefficient-support description of the pulled-back rank-one
window.
@isnad1 id=iff.1h6v.s8.36a133c83afe from=translated src=- shape=1ddc0717 vocab=7cdb7c9f
-/
theorem PolynomialGradedLexData.mem_rankOnePolynomialWindowPreimage_iff_coeff
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (P : MvPolynomial (Fin n) B) :
    P ∈ G.rankOnePolynomialWindowPreimage hpositive D ↔
      ∀ d : Fin n →₀ ℕ, P.coeff d ≠ 0 →
        ((0 : Fin 1), d) ∈ G.windowTermSet hpositive D := by
  rw [G.mem_rankOnePolynomialWindowPreimage_iff]
  change rankOnePolynomialModuleCoeffEquiv P ∈
      artinianPolynomialModuleSupported (G.windowTermSet hpositive D) ↔ _
  rw [mem_artinianPolynomialModuleSupported]
  constructor
  · intro hP d hd
    exact hP 0 d (by simpa using hd)
  · intro hP i d hd
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact hP d (by simpa using hd)

/-- Membership in the bounded part of a transported ideal is detected in
the unique rank-one coordinate.
@isnad1 id=iff.1h7v.s11.2a3a038d8ac5 from=translated src=- shape=99a5a600 vocab=cc734e9c
-/
@[simp]
theorem PolynomialGradedLexData.mem_polynomialWindowPart_rankOneIdeal_iff
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (P : G.windowModule B hpositive D) :
    P ∈ G.polynomialWindowPart hpositive D
        (rankOnePolynomialIdealSubmodule I) ↔
      ((P : artinianFreePolynomialModule B n 1) 0) ∈ I := by
  change (P : artinianFreePolynomialModule B n 1) ∈
      rankOnePolynomialIdealSubmodule I ↔ _
  exact mem_rankOnePolynomialIdealSubmodule_iff I P

/-- The image in the ambient rank-one module of the bounded part is the
intersection of the bounded window with the coefficient restriction of the
transported ideal.
@isnad1 id=eq.1h6v.s10.a42088e4bca3 from=translated src=- shape=9622a6ef vocab=8e262c3d
-/
theorem PolynomialGradedLexData.map_polynomialWindowPart_rankOneIdeal
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B)) :
    (G.polynomialWindowPart hpositive D
        (rankOnePolynomialIdealSubmodule I)).map
        (G.windowModule B hpositive D).subtype =
      G.windowModule B hpositive D ⊓
        (rankOnePolynomialIdealSubmodule I).restrictScalars B := by
  simpa only [PolynomialGradedLexData.polynomialWindowPart] using
    (Submodule.map_comap_subtype
      (p := G.windowModule B hpositive D)
      (p' := (rankOnePolynomialIdealSubmodule I).restrictScalars B))

/-- Under the coefficient-linear rank-one equivalence, intersecting an
ideal with the pulled-back bounded window becomes the intersection of the
transported ideal with the actual bounded window.
@isnad1 id=eq.1h6v.s10.b196d38a5f33 from=translated src=- shape=8dd8f5b8 vocab=c49e3a31
-/
theorem PolynomialGradedLexData.map_rankOneIdeal_inf_windowPreimage
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B)) :
    ((I.restrictScalars B) ⊓
        G.rankOnePolynomialWindowPreimage hpositive D).map
        rankOnePolynomialModuleCoeffEquiv.toLinearMap =
      (rankOnePolynomialIdealSubmodule I).restrictScalars B ⊓
        G.windowModule B hpositive D := by
  rw [Submodule.map_inf _ rankOnePolynomialModuleCoeffEquiv.injective,
    ← rankOnePolynomialIdealSubmodule_restrictScalars I]
  change _ ⊓
      ((G.windowModule B hpositive D).comap
        rankOnePolynomialModuleCoeffEquiv.toLinearMap).map
          rankOnePolynomialModuleCoeffEquiv.toLinearMap = _
  rw [Submodule.map_comap_eq_of_surjective
    rankOnePolynomialModuleCoeffEquiv.surjective]

/-- Membership in the polynomial-window carrier of a transported ideal is
the conjunction of ideal membership in the unique coordinate and bounded
window membership.
@isnad1 id=iff.1h7v.s9.8a29d1abc25a from=translated src=- shape=bcda1dee vocab=0250fce5
-/
@[simp]
theorem PolynomialGradedLexData.mem_polynomialWindowCarrier_rankOneIdeal_iff
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (P : artinianFreePolynomialModule B n 1) :
    P ∈ G.polynomialWindowCarrier hpositive D
        (rankOnePolynomialIdealSubmodule I) ↔
      P 0 ∈ I ∧ P ∈ G.windowModule B hpositive D := by
  simp only [PolynomialGradedLexData.polynomialWindowCarrier,
    Set.mem_ofPred_eq, mem_rankOnePolynomialIdealSubmodule_iff]

/-- Membership in the transported bounded part after ordered-weight
decomposition can still be read by returning to its unique polynomial
coordinate.
@isnad1 id=iff.1h7v.s14.ba743d44fab4 from=translated src=- shape=0f4d94c3 vocab=32fdb2d5
-/
@[simp]
theorem PolynomialGradedLexData.mem_polynomialWindowOrderedWeightPart_rankOneIdeal_iff
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (x : (i : Fin (G.weightCount hpositive D)) →
      G.orderedWeightPiece B hpositive D i) :
    x ∈ G.polynomialWindowOrderedWeightPart hpositive D
        (rankOnePolynomialIdealSubmodule I) ↔
      ((((G.windowOrderedWeightLinearEquiv (B := B) hpositive D).symm x :
          G.windowModule B hpositive D) :
        artinianFreePolynomialModule B n 1) 0) ∈ I := by
  rw [PolynomialGradedLexData.polynomialWindowOrderedWeightPart,
    Submodule.mem_map_equiv]
  exact G.mem_polynomialWindowPart_rankOneIdeal_iff hpositive D I _

end AbelFormalization
