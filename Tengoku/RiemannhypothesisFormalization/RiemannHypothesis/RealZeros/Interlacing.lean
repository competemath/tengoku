/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Analysis.Calculus.LocalExtr.Polynomial
import Tengoku.Seed.Analysis.Calculus.Deriv.Star
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Analysis.Complex.Polynomial.GaussLucas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strict interlacing data for real polynomials

Pinned Mathlib proves Rolle-style cardinality estimates for the roots of a
real polynomial and its derivative, but it does not expose a reusable
interlacing predicate or the classical real-rooted derivative interlacing
theorem.  This file supplies an exact finite-dimensional representation.

`StrictlyInterlaces a b` means

`a₀ < b₀ < a₁ < ... < bₙ₋₁ < aₙ`.

`OrientedStrictInterlacingPolynomialData A B` additionally records complete
linear factorizations of `A` and `B` and a positive product of leading
constants.  The orientation is essential in Hermite--Biehler statements:
interlacing alone is invariant under `B ↦ -B`, while the half-plane norm
inequality is not.
-/

namespace OverflowResidueRH

/-- Two finite ordered root arrays strictly interlace, with the first array
having one more element than the second.-/
def StrictlyInterlaces {n : ℕ}
    (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) : Prop :=
  StrictMono a ∧ StrictMono b ∧
    ∀ i : Fin n, a i.castSucc < b i ∧ b i < a i.succ

namespace StrictlyInterlaces

theorem left_lt {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (h : StrictlyInterlaces a b) (i : Fin n) :
    a i.castSucc < b i :=
  (h.2.2 i).1

theorem right_lt {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (h : StrictlyInterlaces a b) (i : Fin n) :
    b i < a i.succ :=
  (h.2.2 i).2

theorem outer_lt {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (h : StrictlyInterlaces a b) (i : Fin n) :
    a i.castSucc < a i.succ :=
  (h.left_lt i).trans (h.right_lt i)

theorem a_injective {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (h : StrictlyInterlaces a b) : Function.Injective a :=
  h.1.injective

theorem b_injective {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (h : StrictlyInterlaces a b) : Function.Injective b :=
  h.2.1.injective

end StrictlyInterlaces

/-! ## Unconditional Rolle and Gauss--Lucas consequences -/

/-- Rolle's theorem in the exact polynomial form needed for finite
interlacing: between two distinct real roots of `p` lies a root of `p'`.-/
theorem polynomial_derivative_root_between
    (p : Polynomial ℝ) {x y : ℝ}
    (hxy : x < y) (hx : p.eval x = 0) (hy : p.eval y = 0) :
    ∃ c : ℝ, x < c ∧ c < y ∧ p.derivative.eval c = 0 := by
  obtain ⟨c, hc, hder⟩ :=
    exists_deriv_eq_zero hxy p.continuousOn (hx.trans hy.symm)
  refine ⟨c, hc.1, hc.2, ?_⟩
  rwa [p.deriv] at hder

/-- A direct Gauss--Lucas specialization: if every root of a nonconstant
complex polynomial is real, then every root of its derivative is real.
This conclusion allows repeated roots; it is not a simplicity theorem.-/
theorem polynomial_derivative_roots_real
    {P : Polynomial ℂ} (hdegree : 0 < P.degree)
    (hreal : ∀ z : ℂ, P.eval z = 0 → z.im = 0) :
    ∀ z : ℂ, P.derivative.eval z = 0 → z.im = 0 := by
  have hconv : Convex ℝ {z : ℂ | z.im = 0} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    simp [hx, hy]
  have hrootSubset : P.rootSet ℂ ⊆ {z : ℂ | z.im = 0} := by
    intro z hz
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hz
    exact hreal z hz.2
  have hhull : convexHull ℝ (P.rootSet ℂ) ⊆ {z : ℂ | z.im = 0} :=
    convexHull_min hrootSubset hconv
  intro z hz
  apply hhull
  apply Polynomial.rootSet_derivative_subset_convexHull_rootSet hdegree
  rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
  exact ⟨Polynomial.derivative_ne_zero.mpr
    ((Polynomial.natDegree_pos_iff_degree_pos.mpr hdegree).ne'), hz⟩

/-- Complete, oriented factorization data for a pair of real polynomials
whose simple roots strictly interlace.-/
structure OrientedStrictInterlacingPolynomialData
    (A B : Polynomial ℝ) where
  n : ℕ
  a : Fin (n + 1) → ℝ
  b : Fin n → ℝ
  leadingA : ℝ
  leadingB : ℝ
  leadingA_ne : leadingA ≠ 0
  leadingB_ne : leadingB ≠ 0
  factorA :
    A = Polynomial.C leadingA *
      ∏ i : Fin (n + 1), (Polynomial.X - Polynomial.C (a i))
  factorB :
    B = Polynomial.C leadingB *
      ∏ i : Fin n, (Polynomial.X - Polynomial.C (b i))
  interlaces : StrictlyInterlaces a b
  orientation : 0 < leadingA * leadingB

namespace OrientedStrictInterlacingPolynomialData

theorem A_ne_zero {A B : Polynomial ℝ}
    (D : OrientedStrictInterlacingPolynomialData A B) : A ≠ 0 := by
  rw [D.factorA]
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr D.leadingA_ne)
    (Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _)

theorem B_ne_zero {A B : Polynomial ℝ}
    (D : OrientedStrictInterlacingPolynomialData A B) : B ≠ 0 := by
  rw [D.factorB]
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr D.leadingB_ne)
    (Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _)

theorem a_isRoot {A B : Polynomial ℝ}
    (D : OrientedStrictInterlacingPolynomialData A B) (i : Fin (D.n + 1)) :
    A.eval (D.a i) = 0 := by
  calc
    A.eval (D.a i) =
        (Polynomial.C D.leadingA *
          ∏ j : Fin (D.n + 1),
            (Polynomial.X - Polynomial.C (D.a j))).eval (D.a i) :=
      congrArg (fun p : Polynomial ℝ => p.eval (D.a i)) D.factorA
    _ = 0 := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
      apply mul_eq_zero.mpr
      right
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem b_isRoot {A B : Polynomial ℝ}
    (D : OrientedStrictInterlacingPolynomialData A B) (i : Fin D.n) :
    B.eval (D.b i) = 0 := by
  calc
    B.eval (D.b i) =
        (Polynomial.C D.leadingB *
          ∏ j : Fin D.n,
            (Polynomial.X - Polynomial.C (D.b j))).eval (D.b i) :=
      congrArg (fun p : Polynomial ℝ => p.eval (D.b i)) D.factorB
    _ = 0 := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
      apply mul_eq_zero.mpr
      right
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- The displayed array exhausts all real roots of `A`.-/
theorem A_eval_eq_zero_iff {A B : Polynomial ℝ}
    (D : OrientedStrictInterlacingPolynomialData A B) (x : ℝ) :
    A.eval x = 0 ↔ ∃ i : Fin (D.n + 1), D.a i = x := by
  classical
  have heval : A.eval x =
      D.leadingA * ∏ i : Fin (D.n + 1), (x - D.a i) := by
    calc
      A.eval x =
          (Polynomial.C D.leadingA *
            ∏ i : Fin (D.n + 1),
              (Polynomial.X - Polynomial.C (D.a i))).eval x :=
        congrArg (Polynomial.eval x) D.factorA
      _ = D.leadingA * ∏ i : Fin (D.n + 1), (x - D.a i) := by
        simp [Polynomial.eval_mul, Polynomial.eval_prod]
  rw [heval, mul_eq_zero]
  simp only [D.leadingA_ne, false_or, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (sub_eq_zero.mp hi).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, sub_eq_zero.mpr hi.symm⟩

/-- The displayed array exhausts all real roots of `B`.-/
theorem B_eval_eq_zero_iff {A B : Polynomial ℝ}
    (D : OrientedStrictInterlacingPolynomialData A B) (x : ℝ) :
    B.eval x = 0 ↔ ∃ i : Fin D.n, D.b i = x := by
  classical
  have heval : B.eval x =
      D.leadingB * ∏ i : Fin D.n, (x - D.b i) := by
    calc
      B.eval x =
          (Polynomial.C D.leadingB *
            ∏ i : Fin D.n,
              (Polynomial.X - Polynomial.C (D.b i))).eval x :=
        congrArg (Polynomial.eval x) D.factorB
      _ = D.leadingB * ∏ i : Fin D.n, (x - D.b i) := by
        simp [Polynomial.eval_mul, Polynomial.eval_prod]
  rw [heval, mul_eq_zero]
  simp only [D.leadingB_ne, false_or, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (sub_eq_zero.mp hi).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, sub_eq_zero.mpr hi.symm⟩

/-- No root in the `A` array equals a root in the `B` array.-/
theorem a_ne_b {A B : Polynomial ℝ}
    (D : OrientedStrictInterlacingPolynomialData A B)
    (i : Fin (D.n + 1)) (j : Fin D.n) : D.a i ≠ D.b j := by
  by_cases hij : i.val ≤ j.val
  · have hfin : i ≤ j.castSucc := hij
    have hle : D.a i ≤ D.a j.castSucc := D.interlaces.1.monotone hfin
    exact ne_of_lt (hle.trans_lt (D.interlaces.left_lt j))
  · have hji : j.val + 1 ≤ i.val := by omega
    have hfin : j.succ ≤ i := hji
    have hle : D.a j.succ ≤ D.a i := D.interlaces.1.monotone hfin
    exact ne_of_gt ((D.interlaces.right_lt j).trans_le hle)

/-- Strict interlacing factorization data itself proves that `A` and `B`
have no common real root.-/
theorem no_common_real_root {A B : Polynomial ℝ}
    (D : OrientedStrictInterlacingPolynomialData A B) (x : ℝ) :
    ¬ (A.eval x = 0 ∧ B.eval x = 0) := by
  rintro ⟨hA, hB⟩
  obtain ⟨i, hi⟩ := (D.A_eval_eq_zero_iff x).mp hA
  obtain ⟨j, hj⟩ := (D.B_eval_eq_zero_iff x).mp hB
  exact D.a_ne_b i j (hi.trans hj.symm)

/-- Each adjacent pair of roots in the complete `A` factorization contains
a real root of `A'`.  This is an actual finite Rolle-interlacing theorem,
not an interface field.-/
theorem derivative_root_between_a {A B : Polynomial ℝ}
    (D : OrientedStrictInterlacingPolynomialData A B) (i : Fin D.n) :
    ∃ c : ℝ,
      D.a i.castSucc < c ∧ c < D.a i.succ ∧ A.derivative.eval c = 0 :=
  polynomial_derivative_root_between A (D.interlaces.outer_lt i)
    (D.a_isRoot i.castSucc) (D.a_isRoot i.succ)

end OrientedStrictInterlacingPolynomialData

/-- The polynomial and its derivative have the canonical oriented strict
interlacing factorization.  This is the exact finite statement needed by the
derivative-companion Hermite--Biehler specialization.-/
def DerivativeStrictInterlacing (p : Polynomial ℝ) : Prop :=
  Nonempty (OrientedStrictInterlacingPolynomialData p p.derivative)

/-! ## Function-level interlacing

There are two deliberately distinct notions below.

* `EntirePairwiseGapInterlacingData` records only the local statement that
  consecutive zeros of either function contain exactly one zero of the other.
  For zero-free functions, or functions with too few zeros to form a gap,
  these clauses can be vacuous.
* `EntireBiInfiniteStrictInterlacingData` records a genuine exhaustive
  bi-infinite alternation.  Its two integer-indexed arrays enumerate *all*
  complex zeros, and the inequalities alternate at every integer index.

Keeping the weaker predicate separately named prevents a local gap condition
from being mistaken for the full hypothesis in an entire-function
Hermite--Biehler theorem.
-/

/-- A real number, embedded in `ℂ`, is a zero of `F`.-/
def IsRealZero (F : ℂ → ℂ) (x : ℝ) : Prop :=
  F (x : ℂ) = 0

/-- Two real zeros are consecutive: the open interval between them contains
no further real zero of the same function.-/
def ConsecutiveRealZeros (F : ℂ → ℂ) (x y : ℝ) : Prop :=
  IsRealZero F x ∧ IsRealZero F y ∧ x < y ∧
    ∀ t : ℝ, x < t → t < y → ¬ IsRealZero F t

/-- There is exactly one real zero of `F` in the open interval `(x,y)`.-/
def HasUniqueRealZeroBetween (F : ℂ → ℂ) (x y : ℝ) : Prop :=
  ∃ z : ℝ, x < z ∧ z < y ∧ IsRealZero F z ∧
    ∀ w : ℝ, x < w → w < y → IsRealZero F w → w = z

/-- Local pairwise-gap interlacing data.  It records entire and Schwarz
regularity, real and simple zeros, absence of common zeros, and the two
consecutive-gap conditions.  It does **not** assert that either zero set is
nonempty or exhausted by a chosen indexing, so it is intentionally not called
full strict interlacing.-/
structure EntirePairwiseGapInterlacingData (A B : ℂ → ℂ) : Prop where
  A_differentiable : Differentiable ℂ A
  B_differentiable : Differentiable ℂ B
  A_schwarz : ∀ z : ℂ, A (star z) = star (A z)
  B_schwarz : ∀ z : ℂ, B (star z) = star (B z)
  A_roots_real : ∀ z : ℂ, A z = 0 → z.im = 0
  B_roots_real : ∀ z : ℂ, B z = 0 → z.im = 0
  A_simple : ∀ x : ℝ, IsRealZero A x → deriv A (x : ℂ) ≠ 0
  B_simple : ∀ x : ℝ, IsRealZero B x → deriv B (x : ℂ) ≠ 0
  no_common : ∀ x : ℝ, ¬ (IsRealZero A x ∧ IsRealZero B x)
  B_between_A :
    ∀ x y : ℝ, ConsecutiveRealZeros A x y →
      HasUniqueRealZeroBetween B x y
  A_between_B :
    ∀ x y : ℝ, ConsecutiveRealZeros B x y →
      HasUniqueRealZeroBetween A x y

/-- Oriented local pairwise-gap data.  For `E=A+iB`, the displayed Wronskian
orientation distinguishes `B` from `-B`, but it does not repair the possible
vacuity of the local gap clauses.-/
structure OrientedEntirePairwiseGapInterlacingData
    (A B : ℂ → ℂ) : Prop extends EntirePairwiseGapInterlacingData A B where
  wronskian_orientation :
    ∀ x : ℝ,
      0 < (B (x : ℂ) * deriv A (x : ℂ) -
        A (x : ℂ) * deriv B (x : ℂ)).re

/-- Exhaustive bi-infinite strict interlacing of the zero sets of two entire
Schwarz-symmetric functions.  The arrays `a` and `b` enumerate every complex
zero, alternate as `a n < b n < a (n+1)`, and contain only simple zeros.-/
structure EntireBiInfiniteStrictInterlacingData
    (A B : ℂ → ℂ) where
  A_differentiable : Differentiable ℂ A
  B_differentiable : Differentiable ℂ B
  A_schwarz : ∀ z : ℂ, A (star z) = star (A z)
  B_schwarz : ∀ z : ℂ, B (star z) = star (B z)
  a : ℤ → ℝ
  b : ℤ → ℝ
  a_strictMono : StrictMono a
  b_strictMono : StrictMono b
  alternating : ∀ n : ℤ, a n < b n ∧ b n < a (n + 1)
  A_zero_iff : ∀ z : ℂ, A z = 0 ↔ ∃ n : ℤ, z = (a n : ℂ)
  B_zero_iff : ∀ z : ℂ, B z = 0 ↔ ∃ n : ℤ, z = (b n : ℂ)
  A_simple : ∀ n : ℤ, deriv A (a n : ℂ) ≠ 0
  B_simple : ∀ n : ℤ, deriv B (b n : ℂ) ≠ 0

namespace EntireBiInfiniteStrictInterlacingData

/-- Every zero of the first function is real.-/
theorem A_roots_real {A B : ℂ → ℂ}
    (D : EntireBiInfiniteStrictInterlacingData A B)
    {z : ℂ} (hz : A z = 0) : z.im = 0 := by
  obtain ⟨n, rfl⟩ := (D.A_zero_iff z).mp hz
  simp

/-- Every zero of the second function is real.-/
theorem B_roots_real {A B : ℂ → ℂ}
    (D : EntireBiInfiniteStrictInterlacingData A B)
    {z : ℂ} (hz : B z = 0) : z.im = 0 := by
  obtain ⟨n, rfl⟩ := (D.B_zero_iff z).mp hz
  simp

/-- Exhaustive alternating enumerations have no common zero.-/
theorem no_common {A B : ℂ → ℂ}
    (D : EntireBiInfiniteStrictInterlacingData A B) (z : ℂ) :
    ¬ (A z = 0 ∧ B z = 0) := by
  rintro ⟨hA, hB⟩
  obtain ⟨m, hm⟩ := (D.A_zero_iff z).mp hA
  obtain ⟨n, hn⟩ := (D.B_zero_iff z).mp hB
  have hab : D.a m = D.b n := by
    exact_mod_cast hm.symm.trans hn
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have haa : D.a m < D.a n := D.a_strictMono hmn
    have hnb : D.a n < D.b n := (D.alternating n).1
    exact (ne_of_lt (haa.trans hnb)) hab
  · subst n
    exact (ne_of_lt (D.alternating m).1) hab
  · have hindex : n + 1 ≤ m := by omega
    have haa : D.a (n + 1) ≤ D.a m := D.a_strictMono.monotone hindex
    have hlt : D.b n < D.a m := (D.alternating n).2.trans_le haa
    exact (ne_of_gt hlt) hab

end EntireBiInfiniteStrictInterlacingData

/-- The exhaustive bi-infinite strict-interlacing data with the Wronskian
orientation appropriate to `E=A+iB`.-/
structure OrientedEntireBiInfiniteStrictInterlacingData
    (A B : ℂ → ℂ) extends EntireBiInfiniteStrictInterlacingData A B where
  wronskian_orientation :
    ∀ x : ℝ,
      0 < (B (x : ℂ) * deriv A (x : ℂ) -
        A (x : ℂ) * deriv B (x : ℂ)).re

end OverflowResidueRH
