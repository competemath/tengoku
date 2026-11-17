/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.PBW.G2SquareDivisibility

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Uniform polynomial cancellation for the G₂ D,e scalar recurrence

A division-free Hermite family and two commuting raising recurrences construct
`scalarPolynomial` over ℤ[X]. Its four-correction Gaussian recurrence is proved
for all three indices. Cancellation of X - 1 occurs before specialization.
-/

noncomputable section
namespace LieLean.QuantumGroup.G2Integral
namespace DECancellation
variable {R : Type*} [CommRing R]

/-- A division-free polynomial family.-/
def hermite (x z : R) : ℕ → R
  | 0 => 1
  | 1 => 1 + x * z
  | n + 2 => (1 + x ^ (n + 2) * z) * hermite x z (n + 1) +
      x ^ (n + 2) * (1 - x ^ (n + 1)) * z ^ 2 * hermite x z n

/--
@isnad1 id=eq.0h3v.s5.6b3078526f15 from=translated src=- shape=9c02e61a vocab=5a1ecdcb
-/
@[simp] lemma hermite_zero (x z : R) : hermite x z 0 = 1 := rfl
/--
@isnad1 id=eq.0h3v.s6.5ec495dba072 from=translated src=- shape=56d94e71 vocab=f48180d0
-/
@[simp] lemma hermite_one (x z : R) : hermite x z 1 = 1 + x * z := rfl
/--
@isnad1 id=eq.0h4v.s8.f68c4c731e45 from=translated src=- shape=e6fab6ab vocab=e0211075
-/
lemma hermite_step (x z : R) (n : ℕ) :
    hermite x z (n + 2) = (1 + x ^ (n + 2) * z) * hermite x z (n + 1) +
      x ^ (n + 2) * (1 - x ^ (n + 1)) * z ^ 2 * hermite x z n := rfl

/--
@isnad1 id=and.0h4v.s9.133f8a4073d1 from=translated src=- shape=22a9c9d5 vocab=e0211075
-/
lemma hermite_identities (x z : R) (n : ℕ) :
    (hermite x (x * z) (n + 1) = x ^ (n + 1) * hermite x z (n + 1) +
      (1 - x ^ (n + 1)) * hermite x (x * z) n) ∧
    (hermite x z (n + 1) =
      (1 + x * z + x ^ 2 * z ^ 2) * hermite x (x * z) n -
        x ^ (n + 2) * z ^ 2 * hermite x z n) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    obtain ⟨hs, hn⟩ := ih
    constructor
    · simp only [show n + 1 + 1 = n + 2 by omega, hermite_step, hs]
      simp only [pow_add, pow_one] at hn ⊢
      linear_combination -(x ^ (n + 2) * (1 - x ^ (n + 1))) * hn
    · rw [show n + 1 + 1 = n + 2 by omega, hermite_step, hs]
      simp only [pow_add, pow_one] at hn ⊢
      linear_combination (1 - x * x ^ n) * hn

/--
@isnad1 id=eq.0h4v.s7.df98b7c9ea5f from=translated src=- shape=0ef7de7b vocab=e0211075
-/
lemma hermite_shift (x z : R) (n : ℕ) :
    hermite x (x * z) (n + 1) = x ^ (n + 1) * hermite x z (n + 1) +
      (1 - x ^ (n + 1)) * hermite x (x * z) n :=
  (hermite_identities x z n).1

/--
@isnad1 id=eq.0h4v.s8.1daaaab281bb from=translated src=- shape=e881d6e5 vocab=e0211075
-/
lemma hermite_newton (x z : R) (n : ℕ) :
    hermite x z (n + 1) =
      (1 + x * z + x ^ 2 * z ^ 2) * hermite x (x * z) n -
        x ^ (n + 2) * z ^ 2 * hermite x z n :=
  (hermite_identities x z n).2

/-- Product of the elementary triple factors.-/
def triple (x : R) : ℕ → R
  | 0 => 1
  | n + 1 => triple x n * (1 + x ^ (n + 1) + x ^ (2 * (n + 1)))

/-- Division-free candidate in three indices.-/
def scalarPoly (x : R) : ℕ → ℕ → ℕ → R
  | 0, b, c => triple x c * hermite x (x ^ c) b
  | a + 1, b, c => scalarPoly x a (b + 1) c +
      x ^ (2 * a + b + c + 2) * scalarPoly x a b c

/--
@isnad1 id=eq.0h5v.s7.32da8ce9ea36 from=translated src=- shape=e706f915 vocab=25c11d79
-/
lemma scalarPoly_a (x : R) (a b c : ℕ) :
    scalarPoly x (a + 1) b c = scalarPoly x a (b + 1) c +
      x ^ (2 * a + b + c + 2) * scalarPoly x a b c := rfl

/--
@isnad1 id=eq.0h5v.s7.310446c57315 from=translated src=- shape=284fbee4 vocab=25c11d79
-/
lemma scalarPoly_c (x : R) (a b c : ℕ) :
    scalarPoly x a b (c + 1) = scalarPoly x a (b + 1) c +
      x ^ (a + b + 2 * c + 2) * scalarPoly x a b c := by
  induction a generalizing b with
  | zero =>
    simp only [scalarPoly, triple, Nat.zero_add]
    rw [hermite_newton]
    simp only [pow_add, pow_mul, pow_one]
    ring
  | succ a ih =>
    rw [scalarPoly_a, scalarPoly_a, scalarPoly_a, ih (b + 1), ih b]
    simp only [pow_add, pow_mul, pow_one]
    ring

/--
@isnad1 id=eq.0h5v.s4.750d3c9375f9 from=translated src=- shape=d9e941a4 vocab=5a156f05
-/
lemma scalarPoly_symm (x : R) (a b c : ℕ) :
    scalarPoly x a b c = scalarPoly x c b a := by
  induction a generalizing b c with
  | zero =>
    induction c generalizing b with
    | zero => rfl
    | succ c ih =>
      rw [scalarPoly_c, scalarPoly_a, ih (b + 1), ih b]
      simp only [Nat.zero_add, Nat.add_zero]
      rw [show b + 2 * c + 2 = 2 * c + b + 2 by omega]
  | succ a ih =>
    rw [scalarPoly_a, scalarPoly_c, ih (b + 1) c, ih b c]
    rw [show 2 * a + b + c + 2 = c + b + 2 * a + 2 by omega]

/-- The denominator-cleared ordinary-Gaussian recurrence residual.-/
def residual (x : R) (a b c : ℕ) : R :=
  (1 - x ^ (2 * a + b + c)) * scalarPoly x a b c -
    (1 - x ^ (3 * a)) * scalarPoly x (a - 1) (b + 1) c -
    x ^ (3 * a) * (1 - x ^ (b - 1)) * (1 - x ^ b) *
      scalarPoly x a (b - 2) (c + 1) -
    x ^ (3 * a + b - 1) * (1 + x) * (1 - x ^ b) * scalarPoly x a (b - 1) c -
    x ^ (3 * a + 2 * b) * (1 - x ^ (3 * c)) * scalarPoly x a b (c - 1)

/--
@isnad1 id=eq.0h5v.s7.105a01bc4857 from=translated src=- shape=284fbee4 vocab=1af8d4e1
-/
lemma residual_c (x : R) (a b c : ℕ) :
    residual x a b (c + 1) = residual x a (b + 1) c +
      x ^ (a + b + 2 * c + 2) * residual x a b c := by
  rcases a with _ | a <;> rcases b with _ | _ | b <;> rcases c with _ | c
  all_goals simp only [residual, Nat.mul_add,
    Nat.mul_one, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd,
    Nat.add_sub_cancel, Nat.zero_sub, Nat.sub_self,
    pow_zero, sub_self, zero_mul, mul_zero, sub_zero]
  all_goals try simp (disch := omega) only [Nat.add_sub_assoc, Nat.reduceSub]
  all_goals simp only [scalarPoly_c, scalarPoly_a]
  all_goals simp only [pow_add, pow_mul, pow_one, pow_zero]
  all_goals ring

/--
@isnad1 id=eq.0h4v.s9.8628cd0609ef from=translated src=- shape=091c7363 vocab=e0211075
-/
lemma hermite_boundary (x z : R) (b : ℕ) :
    (1 - (x * z) ^ 2 * x ^ b) * hermite x (x * z) b -
      (1 - x * z) * hermite x z (b + 1) -
      (x * z) ^ 3 * (1 - x ^ (2 * b)) * hermite x (x * z) (b - 1) -
      (x * z) ^ 4 * x ^ b * (1 - x ^ (b - 1)) * (1 - x ^ b) *
        hermite x (x * z) (b - 2) = 0 := by
  rcases b with _ | _ | b
  · simp; ring
  · norm_num only [hermite]; ring
  · have hn := hermite_newton x z (b + 2)
    have hs := hermite_shift x z (b + 1)
    have hb := hermite_step x (x * z) b
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_sub_cancel,
      show b + 2 - 1 = b + 1 by omega] at hn hs hb ⊢
    simp only [pow_add, pow_mul, pow_one] at hn hs hb ⊢
    linear_combination -(1 - x * z) * hn +
      (x * z) ^ 2 * (1 - x ^ (b + 2)) * hb -
      (x * z) ^ 2 * (1 - x * z) * hs

/--
@isnad1 id=eq.0h4v.s6.ffb0eadd168b from=translated src=- shape=c98abb3d vocab=46eacab9
-/
lemma scalarPoly_last_zero (x : R) (a b : ℕ) :
    scalarPoly x a b 0 = triple x a * hermite x (x ^ a) b := by
  rw [scalarPoly_symm]
  rfl

/--
@isnad1 id=eq.0h4v.s5.9a9f2eac4df3 from=translated src=- shape=bff5c5aa vocab=457a1f40
-/
lemma residual_zero_right (x : R) (a b : ℕ) : residual x a b 0 = 0 := by
  rcases a with _ | a
  · rcases b with _ | _ | b
    · simp [residual]
    · simp [residual, scalarPoly, triple, hermite]; ring
    · simp only [residual, scalarPoly_c, scalarPoly_last_zero]
      simp only [Nat.zero_add, Nat.add_zero,
        Nat.add_assoc, Nat.reduceAdd, Nat.add_sub_cancel, Nat.zero_sub,
        show b + 2 - 1 = b + 1 by omega, triple, pow_zero, sub_self,
        zero_mul, mul_zero, one_mul, sub_zero]
      have hb := hermite_step x 1 b
      simp only [pow_add, pow_one, one_pow, mul_one] at hb ⊢
      linear_combination (1 - x ^ (b + 2)) * hb
  · have he := hermite_boundary x (x ^ a) b
    rw [show x * x ^ a = x ^ (a + 1) by ring] at he
    rcases b with _ | _ | b
    all_goals simp only [residual, scalarPoly_c, scalarPoly_last_zero]
    all_goals simp only [Nat.zero_add, Nat.add_zero,
      Nat.mul_add, Nat.add_assoc, Nat.reduceAdd, Nat.add_sub_cancel, Nat.zero_sub,
      Nat.sub_self, pow_zero, sub_self, zero_mul, mul_zero, sub_zero] at he ⊢
    all_goals try simp (disch := omega) only [Nat.add_sub_assoc, Nat.reduceSub] at he ⊢
    all_goals simp only [triple, pow_add, pow_mul, pow_one] at he ⊢
    all_goals linear_combination triple x a * (1 + x ^ (a + 1) + x ^ (2 * (a + 1))) * he

/--
@isnad1 id=eq.0h5v.s5.27c3cd99561e from=translated src=- shape=62241139 vocab=457a1f40
-/
lemma residual_eq_zero (x : R) (a b c : ℕ) : residual x a b c = 0 := by
  induction c generalizing b with
  | zero => exact residual_zero_right x a b
  | succ c ih => rw [residual_c, ih, ih, mul_zero, add_zero]

open Polynomial Finset SquareCancellation

/-- An integral polynomial, before any specialization of the parameter.-/
def scalarPolynomial (a b c : ℕ) : ℤ[X] := scalarPoly X a b c

/--
@isnad1 id=eq.0h0v.s5.5c0c5a0abb73 from=translated src=- shape=3152ee67 vocab=4270865d
-/
lemma scalarPolynomial_zero : scalarPolynomial 0 0 0 = 1 := by
  simp [scalarPolynomial, scalarPoly, triple]

/-- Polynomial cancellation of the complete quantum-integer divisor.
@isnad1 id=eq.0h3v.s9.93de53182a75 from=translated src=- shape=d9c2a6d1 vocab=148e9143
-/
theorem scalarPolynomial_recurrence (a b c : ℕ) :
    gaussian (2 * a + b + c) * scalarPolynomial a b c =
      gaussian (3 * a) * scalarPolynomial (a - 1) (b + 1) c +
      (1 - X) * X ^ (3 * a) * gaussian (b - 1) * gaussian b *
        scalarPolynomial a (b - 2) (c + 1) +
      X ^ (3 * a + b - 1) * (1 + X) * gaussian b * scalarPolynomial a (b - 1) c +
      X ^ (3 * a + 2 * b) * gaussian (3 * c) * scalarPolynomial a b (c - 1) := by
  have hg (n : ℕ) : 1 - (X : ℤ[X]) ^ n = -(gaussian n * (X - 1)) := by
    rw [show gaussian n * ((X : ℤ[X]) - 1) = X ^ n - 1 from geom_sum_mul X n]
    ring
  have hz : (X : ℤ[X]) - 1 ≠ 0 := by simpa using (X_sub_C_ne_zero (1 : ℤ))
  apply mul_right_cancel₀ hz
  have hr := residual_eq_zero (X : ℤ[X]) a b c
  simp only [residual, hg] at hr
  simp only [scalarPolynomial]
  linear_combination -hr

end DECancellation
end LieLean.QuantumGroup.G2Integral
