import Tengoku.AbelFormalization.AbelFormalization.LexicographicInitialIdealSecondaryHomogeneity
import Tengoku.AbelFormalization.AbelFormalization.RankOneIdealGrading

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Homogeneity of rank-one ideal submodules

The ordinary grading stored by `PolynomialGradedLexData` uses natural
variable degrees and integral shifted module degrees.  For a rank-one ideal
with zero shift its coefficient projection is exactly the polynomial
weighted-homogeneous projection for the integral casts of those degrees.
The analogous statement for the lexicographic grading was recorded in
`RankOneIdealGrading`.  These identities transport ideal homogeneity to the
two polynomial-submodule homogeneity predicates used by bounded descent.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- Natural-weight sums cast to integers coordinatewise.
@isnad1 id=eq.0h3v.s8.9aaafccb87d6 from=translated src=- shape=c7980f24 vocab=1a50c3f9
-/
theorem finsupp_weight_natCast
    (weight : Fin n → ℕ) (d : Fin n →₀ ℕ) :
    Finsupp.weight (fun i => (weight i : ℤ)) d =
      (Finsupp.weight weight d : ℤ) := by
  classical
  induction d using Finsupp.induction with
  | zero => simp
  | single_add i a d hi ha ih =>
      simp [map_add, Finsupp.weight_single, ih, Nat.cast_add, Nat.cast_mul]

/-- The unique coordinate of the rank-one ordinary projection is the
ordinary weighted-homogeneous projection of the polynomial.
@isnad1 id=eq.0h5v.s10.efa571309db8 from=translated src=- shape=5a1c11a5 vocab=cd90c771
-/
theorem rankOnePolynomial_ordinaryComponent_zero
    (ordinaryDegree : Fin n → ℕ) (degree : ℤ)
    (P : MvPolynomial (Fin n) B) :
    (artinianPolynomialModuleComponent ordinaryDegree (fun _ => 0) degree
        (rankOnePolynomialModuleCoeffEquiv P) 0) =
      MvPolynomial.weightedHomogeneousComponent
        (fun i => (ordinaryDegree i : ℤ)) degree P := by
  classical
  ext d
  rw [artinianPolynomialModuleComponent_coeff,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  simp only [rankOnePolynomialModuleCoeffEquiv_apply,
    artinianPolynomialTermDegree, add_zero, finsupp_weight_natCast]

/-- At a nonnegative integral degree, the same component is the polynomial
component indexed by the corresponding natural number.
@isnad1 id=eq.0h5v.s10.b4411c2e0e2d from=translated src=- shape=dfe8c106 vocab=cd90c771
-/
theorem rankOnePolynomial_ordinaryComponent_zero_nat
    (ordinaryDegree : Fin n → ℕ) (degree : ℕ)
    (P : MvPolynomial (Fin n) B) :
    (artinianPolynomialModuleComponent ordinaryDegree (fun _ => 0)
        (degree : ℤ) (rankOnePolynomialModuleCoeffEquiv P) 0) =
      MvPolynomial.weightedHomogeneousComponent ordinaryDegree degree P := by
  classical
  ext d
  rw [artinianPolynomialModuleComponent_coeff,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  simp only [rankOnePolynomialModuleCoeffEquiv_apply,
    artinianPolynomialTermDegree, add_zero]
  by_cases hd : Finsupp.weight ordinaryDegree d = degree
  · simp [hd]
  · have hd' : (Finsupp.weight ordinaryDegree d : ℤ) ≠ (degree : ℤ) := by
      exact fun h => hd (Int.ofNat_inj.mp h)
    simp [hd, hd']

/-- A rank-one ordinary component in a negative degree vanishes.
@isnad1 id=eq.1h5v.s10.3b45f8800ec9 from=translated src=- shape=7adc3eba vocab=d5c1b9ab
-/
theorem rankOnePolynomial_ordinaryComponent_eq_zero_of_neg
    (ordinaryDegree : Fin n → ℕ) {degree : ℤ} (hdegree : degree < 0)
    (P : MvPolynomial (Fin n) B) :
    artinianPolynomialModuleComponent ordinaryDegree (fun _ => 0) degree
        (rankOnePolynomialModuleCoeffEquiv P) = 0 := by
  classical
  funext k
  have hk : k = 0 := Subsingleton.elim k 0
  subst k
  apply MvPolynomial.ext
  intro d
  rw [artinianPolynomialModuleComponent_coeff]
  have hne : (Finsupp.weight ordinaryDegree d : ℤ) ≠ degree := by
    intro heq
    have hnonneg : (0 : ℤ) ≤ (Finsupp.weight ordinaryDegree d : ℤ) :=
      Int.natCast_nonneg _
    omega
  simp [artinianPolynomialTermDegree, hne]

/-- Ordinary ideal homogeneity becomes the shifted ordinary homogeneity of
the transported rank-one polynomial submodule.
@isnad1 id=isartini.1h4v.s7.d80415268584 from=translated src=- shape=060fe629 vocab=16e3b009
-/
theorem rankOnePolynomialIdealSubmodule_ordinaryHomogeneous
    (ordinaryDegree : Fin n → ℕ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ)))) :
    IsArtinianPolynomialSubmoduleHomogeneous ordinaryDegree (fun _ => 0)
      (rankOnePolynomialIdealSubmodule I) := by
  intro P hP degree
  rw [mem_rankOnePolynomialIdealSubmodule_iff] at hP ⊢
  change
    (artinianPolynomialModuleComponent ordinaryDegree (fun _ => 0) degree P) 0 ∈ I
  have hcomponent :
      (artinianPolynomialModuleComponent ordinaryDegree (fun _ => 0) degree P) 0 =
        MvPolynomial.weightedHomogeneousComponent
          (fun i => (ordinaryDegree i : ℤ)) degree (P 0) := by
    have hPeq : rankOnePolynomialModuleCoeffEquiv (P 0) = P := by
      funext i
      exact congrArg P (Subsingleton.elim 0 i)
    rw [← hPeq]
    exact rankOnePolynomial_ordinaryComponent_zero ordinaryDegree degree (P 0)
  rw [hcomponent]
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem B
    (fun i => (ordinaryDegree i : ℤ)) hI hP degree

/-- Natural-valued ordinary homogeneity, as used by mathlib's standard
weighted polynomial grading, also gives the shifted module homogeneity used
by the bounded-generator API.
@isnad1 id=isartini.1h4v.s7.83016fe1fe50 from=translated src=- shape=8e8dab4e vocab=07b5ff62
-/
theorem rankOnePolynomialIdealSubmodule_ordinaryHomogeneous_of_nat
    (ordinaryDegree : Fin n → ℕ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B ordinaryDegree)) :
    IsArtinianPolynomialSubmoduleHomogeneous ordinaryDegree (fun _ => 0)
      (rankOnePolynomialIdealSubmodule I) := by
  intro P hP degree
  rw [mem_rankOnePolynomialIdealSubmodule_iff] at hP ⊢
  by_cases hdegree : degree < 0
  · have hPeq : rankOnePolynomialModuleCoeffEquiv (P 0) = P := by
      funext i
      exact congrArg P (Subsingleton.elim 0 i)
    have hzero := rankOnePolynomial_ordinaryComponent_eq_zero_of_neg
      ordinaryDegree hdegree (P 0)
    rw [← hPeq, hzero]
    exact I.zero_mem
  · have hnonneg : 0 ≤ degree := le_of_not_gt hdegree
    have hcast : (degree.toNat : ℤ) = degree := Int.toNat_of_nonneg hnonneg
    have hPeq : rankOnePolynomialModuleCoeffEquiv (P 0) = P := by
      funext i
      exact congrArg P (Subsingleton.elim 0 i)
    rw [← hPeq, ← hcast,
      rankOnePolynomial_ordinaryComponent_zero_nat]
    exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem B
      ordinaryDegree hI hP degree.toNat

/-- Lexicographic ideal homogeneity becomes grouped weight homogeneity of
the transported rank-one polynomial submodule.
@isnad1 id=ispolyno.1h6v.s8.949744e440ee from=translated src=- shape=781c5e3d vocab=f7651d12
-/
theorem rankOnePolynomialIdealSubmodule_weightHomogeneous
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => toLex (multiDegree i)))) :
    PolynomialGradedLexData.IsPolynomialModuleWeightHomogeneous
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree)
        (rankOnePolynomialIdealSubmodule I) := by
  intro P hP weight
  rw [mem_rankOnePolynomialIdealSubmodule_iff] at hP ⊢
  have hcomponent :
      (artinianPolynomialModuleFiberComponent
        (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).termWeight
        weight P) 0 =
        MvPolynomial.weightedHomogeneousComponent
          (fun i => toLex (multiDegree i)) weight (P 0) := by
    have hPeq : rankOnePolynomialModuleCoeffEquiv (P 0) = P := by
      funext i
      exact congrArg P (Subsingleton.elim 0 i)
    rw [← hPeq]
    exact rankOnePolynomial_weightFiberComponent_zero
      ordinaryDegree multiDegree weight (P 0)
  rw [hcomponent]
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem B
    (fun i => toLex (multiDegree i)) hI hP weight

/-- Every lexicographic initial ideal gives a weight-homogeneous rank-one
polynomial submodule.
@isnad1 id=ispolyno.0h6v.s6.5620a64f1ed1 from=translated src=- shape=78638b14 vocab=644b5e44
-/
theorem rankOnePolynomialIdealSubmodule_lexicographicInitial_weightHomogeneous
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (I : Ideal (MvPolynomial (Fin n) B)) :
    PolynomialGradedLexData.IsPolynomialModuleWeightHomogeneous
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree)
        (rankOnePolynomialIdealSubmodule
          (lexicographicInitialIdeal multiDegree I)) :=
  rankOnePolynomialIdealSubmodule_weightHomogeneous
    ordinaryDegree multiDegree (lexicographicInitialIdeal multiDegree I)
    (lexicographicInitialIdeal_isHomogeneous multiDegree I)

/-- Lexicographic initial formation preserves the ordinary homogeneity
needed by the bounded-generator theorem.
@isnad1 id=isartini.1h6v.s8.e4e9337fd91a from=translated src=- shape=9f3443d5 vocab=27144caf
-/
theorem rankOnePolynomialIdealSubmodule_lexicographicInitial_ordinaryHomogeneous
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ)))) :
    IsArtinianPolynomialSubmoduleHomogeneous ordinaryDegree (fun _ => 0)
      (rankOnePolynomialIdealSubmodule
        (lexicographicInitialIdeal multiDegree I)) :=
  rankOnePolynomialIdealSubmodule_ordinaryHomogeneous ordinaryDegree _
    (lexicographicInitialIdeal_isHomogeneous_of_isHomogeneous
      (fun i => (ordinaryDegree i : ℤ)) multiDegree I hI)

end AbelFormalization
