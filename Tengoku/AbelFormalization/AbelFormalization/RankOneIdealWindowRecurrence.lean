import Tengoku.AbelFormalization.AbelFormalization.PolynomialWindowIteration
import Tengoku.AbelFormalization.AbelFormalization.RankOneLexicographicWindowCompatibility

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Rank-one ideal iteration and its bounded-window recurrence

This file packages the manuscript's ideal sequence

`I₀ = in(Q)`, `I_(j+1) = in(J(I_j))`

and identifies the bounded ordered-weight part of every successor with the
finite-weight descent step.  The only interface required from the polynomial
automorphism is its action on the chosen bounded window and preservation of
the independent ordinary grading.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## The ideal and rank-one-submodule sequences -/

/-- Iterate full lexicographic initial formation after applying a polynomial
ring automorphism.  The initial object is itself a full initial ideal, so
every term of the sequence is homogeneous for the lexicographic grading.-/
def lexicographicInitialIdealIteration
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) :
    ℕ → Ideal (MvPolynomial (Fin n) B)
  | 0 => lexicographicInitialIdeal multiDegree Q
  | j + 1 =>
      lexicographicInitialIdeal multiDegree
        ((lexicographicInitialIdealIteration multiDegree J Q j).map
          J.toRingHom)

/--
@isnad1 id=eq.0h6v.s7.2f7951b7f62b from=translated src=- shape=84429255 vocab=3a047e36
-/
@[simp]
theorem lexicographicInitialIdealIteration_zero
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) :
    lexicographicInitialIdealIteration multiDegree J Q 0 =
      lexicographicInitialIdeal multiDegree Q :=
  rfl

/--
@isnad1 id=eq.0h7v.s8.ee2781abdc3f from=translated src=- shape=20787ecd vocab=d2710446
-/
@[simp]
theorem lexicographicInitialIdealIteration_succ
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ) :
    lexicographicInitialIdealIteration multiDegree J Q (j + 1) =
      lexicographicInitialIdeal multiDegree
        ((lexicographicInitialIdealIteration multiDegree J Q j).map
          J.toRingHom) :=
  rfl

/-- The actual rank-one polynomial submodule corresponding to `I_j`.-/
def rankOneLexicographicInitialSubmoduleIteration
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ) :
    Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n 1) :=
  rankOnePolynomialIdealSubmodule
    (lexicographicInitialIdealIteration multiDegree J Q j)

/-- The rank-one submodule obtained by applying `J` to `I_j`.  This is the
sequence called `JN` by the abstract polynomial-window stabilization API.-/
def rankOneMappedLexicographicInitialSubmoduleIteration
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ) :
    Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n 1) :=
  rankOnePolynomialIdealSubmodule
    ((lexicographicInitialIdealIteration multiDegree J Q j).map J.toRingHom)

/-! ## Homogeneity of the iteration -/

/-- Every rank-one term of the ideal iteration is homogeneous for the
ordered lexicographic weight projections.
@isnad1 id=ispolyno.0h8v.s7.cf2543bb27eb from=translated src=- shape=f1cb457d vocab=407dead3
-/
theorem rankOneLexicographicInitialSubmoduleIteration_weightHomogeneous
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ) :
    PolynomialGradedLexData.IsPolynomialModuleWeightHomogeneous
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree)
      (rankOneLexicographicInitialSubmoduleIteration multiDegree J Q j) := by
  cases j with
  | zero =>
      exact
        rankOnePolynomialIdealSubmodule_lexicographicInitial_weightHomogeneous
          ordinaryDegree multiDegree Q
  | succ j =>
      exact
        rankOnePolynomialIdealSubmodule_lexicographicInitial_weightHomogeneous
          ordinaryDegree multiDegree
          ((lexicographicInitialIdealIteration multiDegree J Q j).map
            J.toRingHom)

/-- If `Q` is ordinary homogeneous and `J` preserves ordinary homogeneous
ideals, then every `I_j` remains ordinary homogeneous.
@isnad1 id=ishomoge.2h8v.s10.bcf2a7f80cb1 from=translated src=- shape=a52df68b vocab=d0838600
-/
theorem lexicographicInitialIdealIteration_ordinaryHomogeneous
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (hJordinary : ∀ I : Ideal (MvPolynomial (Fin n) B),
      I.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) →
        (I.map J.toRingHom).IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ)))) :
    ∀ j, (lexicographicInitialIdealIteration multiDegree J Q j).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))) := by
  intro j
  induction j with
  | zero =>
      exact lexicographicInitialIdeal_isHomogeneous_of_isHomogeneous
        (fun i => (ordinaryDegree i : ℤ)) multiDegree Q hQ
  | succ j ih =>
      exact lexicographicInitialIdeal_isHomogeneous_of_isHomogeneous
        (fun i => (ordinaryDegree i : ℤ)) multiDegree
        ((lexicographicInitialIdealIteration multiDegree J Q j).map
          J.toRingHom)
        (hJordinary _ ih)

/-- The intermediate mapped ideal `J(I_j)` is ordinary homogeneous.
@isnad1 id=ishomoge.2h8v.s10.5d058fead1f3 from=translated src=- shape=5369a44e vocab=d0838600
-/
theorem lexicographicInitialIdealIteration_map_ordinaryHomogeneous
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (hJordinary : ∀ I : Ideal (MvPolynomial (Fin n) B),
      I.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) →
        (I.map J.toRingHom).IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))))
    (j : ℕ) :
    ((lexicographicInitialIdealIteration multiDegree J Q j).map
        J.toRingHom).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))) :=
  hJordinary _
    (lexicographicInitialIdealIteration_ordinaryHomogeneous
      ordinaryDegree multiDegree J Q hQ hJordinary j)

/-! ## Exact bounded-window recurrence -/

/-! ## Direct interface to polynomial-window stabilization -/

end AbelFormalization
