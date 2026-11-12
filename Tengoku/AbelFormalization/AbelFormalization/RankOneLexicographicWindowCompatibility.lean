import Tengoku.AbelFormalization.AbelFormalization.RankOneIdealHomogeneity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Rank-one lexicographic initial ideals in a bounded polynomial window

For an ordinary homogeneous ideal, taking the full lexicographic initial
ideal and then restricting to a bounded ordinary-degree window agrees with
the literal finite-coordinate initial submodule of that window.  The proof
uses all elements of the ideal.  A lift of a prescribed lexicographic
component is truncated by ordinary degree; ordinary homogeneity keeps that
truncation in the ideal.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Ordinary-degree truncation -/

/-- A natural ordinary-degree component is the corresponding component for
the integral casts of the variable degrees.-/
theorem weightedHomogeneousComponent_nat_eq_intCast
    (ordinaryDegree : Fin n → ℕ) (degree : ℕ)
    (f : MvPolynomial (Fin n) B) :
    MvPolynomial.weightedHomogeneousComponent ordinaryDegree degree f =
      MvPolynomial.weightedHomogeneousComponent
        (fun i => (ordinaryDegree i : ℤ)) (degree : ℤ) f := by
  classical
  ext d
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent,
    finsupp_weight_natCast, Int.ofNat_inj]

section CanonicalRankOneGrading

variable (ordinaryDegree : Fin n → ℕ)
variable (multiDegree : Fin n → Fin h → ℤ)

local notation "G₁" =>
  rankOnePolynomialGradedLexData ordinaryDegree multiDegree

/-! ## Rank-one coordinates and prefix vanishing -/

/-- The unique coordinate of a rank-one module weight component is the
corresponding polynomial weight component.-/
theorem rankOnePolynomial_weightFiberComponent_zero_module
    (weight : PolynomialLexWeight h)
    (P : artinianFreePolynomialModule B n 1) :
    (artinianPolynomialModuleFiberComponent (G₁).termWeight weight P 0) =
      MvPolynomial.weightedHomogeneousComponent
        (fun i => toLex (multiDegree i)) weight (P 0) := by
  classical
  ext d
  rw [artinianPolynomialModuleFiberComponent_coeff,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  simp only [rankOnePolynomialGradedLexData_termWeight]

/-- A grouped rank-one weight piece is homogeneous of that polynomial
weight.-/
theorem rankOne_windowWeightPiece_isWeightedHomogeneous
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (weight : PolynomialLexWeight h)
    (v : (G₁).windowWeightPiece B hpositive D weight) :
    ((v : artinianFreePolynomialModule B n 1) 0).IsWeightedHomogeneous
      (fun i => toLex (multiDegree i)) weight := by
  intro d hd
  have ht := (mem_artinianPolynomialModuleSupported _ _).mp v.property
    0 d hd
  simpa only [rankOnePolynomialGradedLexData_termWeight] using ht.2

/-- The polynomial in a grouped rank-one weight piece belongs to the
pulled-back ordinary-degree window.-/
theorem rankOne_windowWeightPiece_mem_window
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (weight : PolynomialLexWeight h)
    (v : (G₁).windowWeightPiece B hpositive D weight) :
    ((v : artinianFreePolynomialModule B n 1) 0) ∈
      (G₁).rankOnePolynomialWindowPreimage hpositive D := by
  rw [(G₁).mem_rankOnePolynomialWindowPreimage_iff_coeff]
  intro d hd
  exact ((mem_artinianPolynomialModuleSupported _ _).mp v.property
    0 d hd).1

/-! ## Coordinate initial pieces -/

/-! ## The full bounded-window identity -/

/-! ## One fixed ordinary-degree slice -/

/-- Include one ordinary-degree piece in a containing window and then pass
to ordered weight coordinates.-/
def PolynomialGradedLexData.ordinaryDegreeOrderedWeightEmbedding
    (G : PolynomialGradedLexData n 1 h)
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D degree : ℤ)
    (hdegree : degree ≤ D) :
    artinianPolynomialModulePiece (B := B)
        G.ordinaryDegree G.ordinaryShift degree →ₗ[B]
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :=
  (G.windowOrderedWeightLinearEquiv hpositive D).toLinearMap.comp
    (Submodule.inclusion
      (G.ordinaryPiece_le_windowModule hpositive D degree hdegree))

/-- The fixed-degree embedding loses no information.-/
theorem PolynomialGradedLexData.ordinaryDegreeOrderedWeightEmbedding_injective
    (G : PolynomialGradedLexData n 1 h)
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D degree : ℤ)
    (hdegree : degree ≤ D) :
    Function.Injective
      (G.ordinaryDegreeOrderedWeightEmbedding (B := B)
        hpositive D degree hdegree) := by
  exact (G.windowOrderedWeightLinearEquiv
    (B := B) hpositive D).injective.comp
      (Submodule.inclusion_injective
        (G.ordinaryPiece_le_windowModule hpositive D degree hdegree))

@[simp]
theorem PolynomialGradedLexData.windowEquiv_symm_ordinaryDegreeEmbedding
    (G : PolynomialGradedLexData n 1 h)
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D degree : ℤ)
    (hdegree : degree ≤ D)
    (P : artinianPolynomialModulePiece (B := B)
      G.ordinaryDegree G.ordinaryShift degree) :
    (G.windowOrderedWeightLinearEquiv hpositive D).symm
        (G.ordinaryDegreeOrderedWeightEmbedding hpositive D degree hdegree P) =
      Submodule.inclusion
        (G.ordinaryPiece_le_windowModule hpositive D degree hdegree) P := by
  exact (G.windowOrderedWeightLinearEquiv
    (B := B) hpositive D).symm_apply_apply _

/-- The ordered image of the part of a rank-one ideal in one ordinary
degree.  Its ambient module is the same finite product as the whole bounded
window, so finite-weight initial formation applies literally.-/
def PolynomialGradedLexData.rankOnePolynomialDegreeOrderedWeightPart
    (G : PolynomialGradedLexData n 1 h)
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D degree : ℤ)
    (hdegree : degree ≤ D)
    (I : Ideal (MvPolynomial (Fin n) B)) :
    Submodule B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :=
  (artinianPolynomialSubmoduleDegree
      (rankOnePolynomialIdealSubmodule I)
      G.ordinaryDegree G.ordinaryShift degree).map
    (G.ordinaryDegreeOrderedWeightEmbedding
      hpositive D degree hdegree)

/-- For the canonical rank-one grading, membership in a module ordinary
piece is exactly polynomial weighted homogeneity in the unique coordinate.-/
theorem rankOne_mem_ordinaryPiece_iff_isWeightedHomogeneous
    (degree : ℕ) (P : artinianFreePolynomialModule B n 1) :
    P ∈ artinianPolynomialModulePiece (B := B)
        ordinaryDegree (G₁).ordinaryShift (degree : ℤ) ↔
      (P 0).IsWeightedHomogeneous
        (fun i => (ordinaryDegree i : ℤ)) (degree : ℤ) := by
  classical
  constructor
  · intro hP d hd
    have hterm := (mem_artinianPolynomialModuleSupported _ _).mp hP
      0 d hd
    change artinianPolynomialTermDegree ordinaryDegree (fun _ : Fin 1 => 0)
      ((0 : Fin 1), d) = (degree : ℤ) at hterm
    change Finsupp.weight (fun i => (ordinaryDegree i : ℤ)) d =
      (degree : ℤ)
    rw [finsupp_weight_natCast]
    simpa only [artinianPolynomialTermDegree, add_zero] using hterm
  · intro hP
    apply (mem_artinianPolynomialModuleSupported _ _).mpr
    intro k d hd
    have hk : k = 0 := Subsingleton.elim k 0
    subst k
    have hdegree := hP hd
    change artinianPolynomialTermDegree ordinaryDegree (fun _ : Fin 1 => 0)
      ((0 : Fin 1), d) = (degree : ℤ)
    simp only [artinianPolynomialTermDegree, add_zero]
    rw [← finsupp_weight_natCast]
    exact hdegree

/-- A concrete membership test for the ordered image of one degree slice.-/
theorem mem_rankOnePolynomialDegreeOrderedWeightPart_iff
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (degree : ℕ) (hdegree : (degree : ℤ) ≤ D)
    (I : Ideal (MvPolynomial (Fin n) B))
    (x : (i : Fin ((G₁).weightCount hpositive D)) →
      (G₁).orderedWeightPiece B hpositive D i) :
    x ∈ (G₁).rankOnePolynomialDegreeOrderedWeightPart
        hpositive D (degree : ℤ) hdegree I ↔
      (((((G₁).windowOrderedWeightLinearEquiv
          (B := B) hpositive D).symm x :
            (G₁).windowModule B hpositive D) :
          artinianFreePolynomialModule B n 1) 0) ∈ I ∧
      (((((G₁).windowOrderedWeightLinearEquiv
          (B := B) hpositive D).symm x :
            (G₁).windowModule B hpositive D) :
          artinianFreePolynomialModule B n 1) 0).IsWeightedHomogeneous
            (fun i => (ordinaryDegree i : ℤ)) (degree : ℤ) := by
  classical
  let E := (G₁).windowOrderedWeightLinearEquiv (B := B) hpositive D
  constructor
  · rintro ⟨P, hP, rfl⟩
    have hback := (G₁).windowEquiv_symm_ordinaryDegreeEmbedding
      (B := B) hpositive D (degree : ℤ) hdegree P
    have hPI :
        (((P : artinianPolynomialModulePiece (B := B)
            ordinaryDegree (G₁).ordinaryShift (degree : ℤ)) :
          artinianFreePolynomialModule B n 1) 0) ∈ I := by
      change ((P : artinianPolynomialModulePiece (B := B)
        ordinaryDegree (G₁).ordinaryShift (degree : ℤ)) :
          artinianFreePolynomialModule B n 1) ∈
        rankOnePolynomialIdealSubmodule I at hP
      exact (mem_rankOnePolynomialIdealSubmodule_iff I _).mp hP
    constructor
    · rw [hback]
      exact hPI
    · rw [hback]
      exact (rankOne_mem_ordinaryPiece_iff_isWeightedHomogeneous
        ordinaryDegree multiDegree degree
          (P : artinianFreePolynomialModule B n 1)).mp P.property
  · rintro ⟨hxI, hxhom⟩
    let P : artinianPolynomialModulePiece (B := B)
        ordinaryDegree (G₁).ordinaryShift (degree : ℤ) :=
      ⟨((E.symm x : (G₁).windowModule B hpositive D) :
          artinianFreePolynomialModule B n 1),
        (rankOne_mem_ordinaryPiece_iff_isWeightedHomogeneous
          ordinaryDegree multiDegree degree _).mpr hxhom⟩
    refine ⟨P, ?_, ?_⟩
    · change ((P : artinianPolynomialModulePiece (B := B)
        ordinaryDegree (G₁).ordinaryShift (degree : ℤ)) :
          artinianFreePolynomialModule B n 1) ∈
        rankOnePolynomialIdealSubmodule I
      apply (mem_rankOnePolynomialIdealSubmodule_iff I _).mpr
      exact hxI
    · change E (Submodule.inclusion
          ((G₁).ordinaryPiece_le_windowModule
            hpositive D (degree : ℤ) hdegree) P) = x
      exact E.apply_symm_apply x

end CanonicalRankOneGrading

end AbelFormalization
