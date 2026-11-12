import Tengoku.AbelFormalization.AbelFormalization.ProjectedZeroFamily

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial sign sets as projected zero sets

This file formalizes the elementary existential encodings used for the
semialgebraic closure property of the manuscript's projected-zero family.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/--
@isnad1 id=eq.0h3v.s8.e10fa0c2294d from=translated src=- shape=b53213d2 vocab=3ad2f4be
-/
@[simp]
theorem realEuclideanDropLastLinearMap_append_one
    {n : ℕ} (x : RealEuclidean n) (z : RealEuclidean 1) :
    realEuclideanDropLastLinearMap n (realEuclideanAppend x z) = x := by
  funext i
  change realEuclideanAppend x z (Fin.castAdd 1 i) = x i
  exact realEuclideanAppend_castAdd x z i

/--
@isnad1 id=eq.0h3v.s5.dca70e14eab1 from=translated src=- shape=c1a6d3be vocab=95c9b9ab
-/
@[simp]
theorem realEuclideanAppend_last_one
    {n : ℕ} (x : RealEuclidean n) (z : RealEuclidean 1) :
    realEuclideanAppend x z (Fin.last n) = z 0 := by
  have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by ext; simp
  rw [hlast]
  exact realEuclideanAppend_natAdd x z (0 : Fin 1)

/-- The equation `P(x) u² - 1 = 0` existentially represents `P(x) > 0`.-/
def polynomialPositiveWitnessEquation {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) : RealEuclideanFunction (n + 1) :=
  fun v ↦
    MvPolynomial.eval (realEuclideanDropLastLinearMap n v) P *
      v (Fin.last n) ^ 2 - 1

/--
@isnad1 id=eq.0h4v.s7.c4c0659bb704 from=translated src=- shape=24b011e0 vocab=a6b43052
-/
@[simp]
theorem polynomialPositiveWitnessEquation_append
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : RealEuclidean n) (z : RealEuclidean 1) :
    polynomialPositiveWitnessEquation P (realEuclideanAppend x z) =
      MvPolynomial.eval x P * (z 0) ^ 2 - 1 := by
  simp [polynomialPositiveWitnessEquation]

/--
@isnad1 id=mem.1h3v.s6.02af0b3a1b4a from=translated src=- shape=4f80f973 vocab=52e59400
-/
theorem IsGeometricFunctionFamily.polynomialPositiveWitnessEquation_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    polynomialPositiveWitnessEquation P ∈ G (n + 1) := by
  let L := realEuclideanDropLastLinearMap n
  let p : RealEuclideanFunction (n + 1) :=
    fun v ↦ MvPolynomial.eval (L v) P
  let u : RealEuclideanFunction (n + 1) := fun v ↦ v (Fin.last n)
  have hp : p ∈ G (n + 1) := by
    exact hG.affine_comp (hG.polynomial P) L.toAffineMap
  have hu : u ∈ G (n + 1) := by
    simpa [u] using hG.polynomial (MvPolynomial.X (Fin.last n))
  have hmem := hG.sub_mem (hG.mul hp (hG.sq_mem hu)) hG.one_mem
  change (fun v ↦ p v * u v ^ 2 - 1) ∈ G (n + 1)
  rw [show (fun v ↦ p v * u v ^ 2 - 1) =
      p * (fun v ↦ u v ^ 2) - 1 by
    funext v
    rfl]
  exact hmem

/--
@isnad1 id=isprojec.1h3v.s6.832b7616ecfe from=translated src=- shape=d3f33f22 vocab=f82a8748
-/
theorem isProjectedZeroSet_polynomial_zero
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    IsProjectedZeroSet G {x | MvPolynomial.eval x P = 0} :=
  isProjectedZeroSet_zeroSet (hG.polynomial P)

/--
@isnad1 id=isprojec.1h3v.s6.5255de7cd84e from=translated src=- shape=0d49a96c vocab=51dafa23
-/
theorem isProjectedZeroSet_polynomial_pos
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    IsProjectedZeroSet G {x | 0 < MvPolynomial.eval x P} := by
  refine ⟨1, polynomialPositiveWitnessEquation P,
    hG.polynomialPositiveWitnessEquation_mem P, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hp
    let u : ℝ := (Real.sqrt (MvPolynomial.eval x P))⁻¹
    refine ⟨fun _ ↦ u, ?_⟩
    rw [polynomialPositiveWitnessEquation_append]
    rw [← Real.sq_sqrt hp.le]
    dsimp only [u]
    field_simp
    norm_num
  · rintro ⟨z, hz⟩
    rw [polynomialPositiveWitnessEquation_append, sub_eq_zero] at hz
    have hu : z 0 ≠ 0 := by
      intro hu
      simp [hu] at hz
    have hu2 : 0 < (z 0) ^ 2 := sq_pos_of_ne_zero hu
    have hprod : 0 < MvPolynomial.eval x P * (z 0) ^ 2 := by
      rw [hz]
      norm_num
    rcases mul_pos_iff.mp hprod with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hu2.le hneg.2).elim

/--
@isnad1 id=isprojec.1h3v.s6.d69bfb5f07d7 from=translated src=- shape=d3f33f22 vocab=51dafa23
-/
theorem isProjectedZeroSet_polynomial_neg
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    IsProjectedZeroSet G {x | MvPolynomial.eval x P < 0} := by
  have h := isProjectedZeroSet_polynomial_pos hG (-P)
  simpa using h

/-- Finite unions and intersections of polynomial zero/positive/negative sign
conditions. This is the disjunctive-normal-form presentation of real
semialgebraic sets used in the manuscript's elementary encoding.-/
inductive PolynomialSignConstructible (n : ℕ) :
    Set (RealEuclidean n) → Prop
  | zero (P : MvPolynomial (Fin n) ℝ) :
      PolynomialSignConstructible n {x | MvPolynomial.eval x P = 0}
  | pos (P : MvPolynomial (Fin n) ℝ) :
      PolynomialSignConstructible n {x | 0 < MvPolynomial.eval x P}
  | neg (P : MvPolynomial (Fin n) ℝ) :
      PolynomialSignConstructible n {x | MvPolynomial.eval x P < 0}
  | inter {s t} : PolynomialSignConstructible n s →
      PolynomialSignConstructible n t →
        PolynomialSignConstructible n (s ∩ t)
  | union {s t} : PolynomialSignConstructible n s →
      PolynomialSignConstructible n t →
        PolynomialSignConstructible n (s ∪ t)

/--
@isnad1 id=polynomi.0h1v.s3.be2b42fe7a90 from=translated src=- shape=1725868c vocab=9c57e95f
-/
theorem polynomialSignConstructible_empty (n : ℕ) :
    PolynomialSignConstructible n (∅ : Set (RealEuclidean n)) := by
  have h := PolynomialSignConstructible.zero
    (n := n) (1 : MvPolynomial (Fin n) ℝ)
  simpa using h

/--
@isnad1 id=polynomi.0h1v.s2.9a2f7628e49c from=translated src=- shape=6a6a934a vocab=7dbc7e45
-/
theorem polynomialSignConstructible_univ (n : ℕ) :
    PolynomialSignConstructible n (Set.univ : Set (RealEuclidean n)) := by
  have h := PolynomialSignConstructible.zero
    (n := n) (0 : MvPolynomial (Fin n) ℝ)
  simpa using h

/-- Polynomial sign normal forms are closed under complement by trichotomy of
real polynomial values and De Morgan's laws.
@isnad1 id=polynomi.1h2v.s4.138d5bbae39e from=translated src=- shape=d9d161f7 vocab=209c9eae
-/
theorem PolynomialSignConstructible.compl
    {n : ℕ} {s : Set (RealEuclidean n)}
    (hs : PolynomialSignConstructible n s) :
    PolynomialSignConstructible n sᶜ := by
  induction hs with
  | zero P =>
      rw [show {x | MvPolynomial.eval x P = 0}ᶜ =
          {x | 0 < MvPolynomial.eval x P} ∪
            {x | MvPolynomial.eval x P < 0} by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · intro hne
          rcases lt_or_gt_of_ne hne with hneg | hpos
          · exact Or.inr hneg
          · exact Or.inl hpos
        · rintro (hpos | hneg)
          · exact ne_of_gt hpos
          · exact ne_of_lt hneg]
      exact .union (.pos P) (.neg P)
  | pos P =>
      rw [show {x | 0 < MvPolynomial.eval x P}ᶜ =
          {x | MvPolynomial.eval x P = 0} ∪
            {x | MvPolynomial.eval x P < 0} by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · intro hnpos
          rcases eq_or_lt_of_le (not_lt.mp hnpos) with hzero | hneg
          · exact Or.inl hzero
          · exact Or.inr hneg
        · rintro (hzero | hneg)
          · simp [hzero]
          · exact not_lt_of_ge hneg.le]
      exact .union (.zero P) (.neg P)
  | neg P =>
      rw [show {x | MvPolynomial.eval x P < 0}ᶜ =
          {x | MvPolynomial.eval x P = 0} ∪
            {x | 0 < MvPolynomial.eval x P} by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · intro hnneg
          rcases eq_or_lt_of_le (not_lt.mp hnneg) with hzero | hpos
          · exact Or.inl hzero.symm
          · exact Or.inr hpos
        · rintro (hzero | hpos)
          · simp [hzero]
          · exact not_lt_of_ge hpos.le]
      exact .union (.zero P) (.pos P)
  | inter hs ht ihs iht =>
      rw [compl_inter]
      exact .union ihs iht
  | union hs ht ihs iht =>
      rw [compl_union]
      exact .inter ihs iht

end AbelFormalization
