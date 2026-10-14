/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Tengoku

/-!
# Frobenius pairing, entrywise positive part, and the Schur product

This file records the real Frobenius inner product `⟨B, C⟩ = tr(Bᵀ C)`, the
entrywise positive part of a matrix, the rank-one Laplacian
`vecMulVec (e i - e j) (e i - e j)`, and the Schur product theorem for real
positive semidefinite matrices.
-/

@[expose] public section

namespace BollobasNikiforov

open Matrix
open scoped Matrix

variable {m n : Type*}

/-! ### N06 — Frobenius pairing -/

/-- The real Frobenius pairing `⟨B, C⟩ = tr(Bᵀ C)`. -/
def inner [Fintype n] (B C : Matrix n n ℝ) : ℝ :=
  (Bᵀ * C).trace

section Inner

variable [Fintype n]

/-- The Frobenius pairing is symmetric.
@isnad1 id=eq.0h3v.s4.86a124d5e396 from=translated src=- shape=162d12c2 vocab=c0cafa75
-/
lemma inner_comm (B C : Matrix n n ℝ) : inner B C = inner C B := by
  simpa [inner, transpose_mul] using (trace_transpose (Bᵀ * C)).symm

/-- The Frobenius pairing is additive in the first argument.
@isnad1 id=eq.0h4v.s6.f215fc1e0a92 from=translated src=- shape=332d62b8 vocab=5e58f55d
-/
lemma inner_add_left (B₁ B₂ C : Matrix n n ℝ) :
    inner (B₁ + B₂) C = inner B₁ C + inner B₂ C := by
  simp [inner, transpose_add, add_mul, trace_add]

/-- The Frobenius pairing is additive in the second argument.
@isnad1 id=eq.0h4v.s6.7eecc4c8922f from=translated src=- shape=821afdcc vocab=5e58f55d
-/
lemma inner_add_right (B C₁ C₂ : Matrix n n ℝ) :
    inner B (C₁ + C₂) = inner B C₁ + inner B C₂ := by
  simp [inner, mul_add, trace_add]

/-- The Frobenius pairing is homogeneous in the first argument.
@isnad1 id=eq.0h4v.s5.29e1c1033497 from=translated src=- shape=83cdabac vocab=6495bbd8
-/
lemma inner_smul_left (r : ℝ) (B C : Matrix n n ℝ) :
    inner (r • B) C = r * inner B C := by
  simp [inner, transpose_smul, smul_mul, trace_smul, smul_eq_mul]

/-- The Frobenius pairing is homogeneous in the second argument.
@isnad1 id=eq.0h4v.s5.9630a6f80b7c from=translated src=- shape=2876f6a1 vocab=6495bbd8
-/
lemma inner_smul_right (r : ℝ) (B C : Matrix n n ℝ) :
    inner B (r • C) = r * inner B C := by
  simp [inner, Matrix.mul_smul, trace_smul, smul_eq_mul]

/-- Expanding the Frobenius pairing as an entrywise sum. This identity does not
require symmetry of either argument; in particular it yields the
Frobenius–Hadamard formula for a symmetric first factor.
@isnad1 id=eq.0h3v.s5.d710dec8f5c3 from=translated src=- shape=76dfa22e vocab=cd64d526
-/
lemma inner_eq_sum (B C : Matrix n n ℝ) :
    inner B C = ∑ i, ∑ j, B i j * C i j := by
  simp only [inner, trace, diag, mul_apply, transpose_apply]
  rw [Finset.sum_comm]

/-- The squared Frobenius norm is the sum of squares of entries.
@isnad1 id=eq.0h2v.s5.be5ff6d4988c from=translated src=- shape=7cedb8d1 vocab=24eff09c
-/
lemma inner_self (B : Matrix n n ℝ) :
    inner B B = ∑ i, ∑ j, B i j ^ 2 := by
  simp [inner_eq_sum, pow_two]

end Inner

/-! ### N08 — Entrywise positive part -/

/-- The entrywise positive part `(posPart X) i j = max (X i j) 0`. -/
def posPart (X : Matrix m n ℝ) : Matrix m n ℝ :=
  of fun i j => max (X i j) 0

/--
@isnad1 id=eq.0h5v.s5.f388d1b3f6ea from=translated src=- shape=adf66eec vocab=55444c33
-/
@[simp]
lemma posPart_apply (X : Matrix m n ℝ) (i : m) (j : n) :
    posPart X i j = max (X i j) 0 :=
  rfl

/--
@isnad1 id=le.0h5v.s4.d86eb633af80 from=translated src=- shape=ae387377 vocab=501da21e
-/
lemma posPart_nonneg (X : Matrix m n ℝ) (i : m) (j : n) :
    0 ≤ posPart X i j :=
  le_max_right _ _

/--
@isnad1 id=eq.1h5v.s5.dd94f5f98192 from=translated src=- shape=d5228fa5 vocab=501da21e
-/
lemma posPart_eq_of_nonneg (X : Matrix m n ℝ) {i : m} {j : n}
    (h : 0 ≤ X i j) : posPart X i j = X i j :=
  max_eq_left h

/-! ### N09 — Rank-one Laplacian entries -/

/-- The standard basis vector `e k` in `n → ℝ`. -/
def e [DecidableEq n] (k : n) : n → ℝ :=
  Pi.single k 1

/-- The vector `e i - e j` in coordinates.
@isnad1 id=eq.1h4v.s6.ed74aac7f2bc from=translated src=- shape=15d72893 vocab=b15be7c3
-/
lemma sub_single_apply [DecidableEq n] {i j : n} (hij : i ≠ j) (a : n) :
    (e i - e j) a = if a = i then (1 : ℝ) else if a = j then -1 else 0 := by
  simp only [e, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> simp_all

/-- Entries of the rank-one Laplacian `vecMulVec (e i - e j) (e i - e j)`.
@isnad1 id=eq.1h5v.s7.e252e205dd1d from=translated src=- shape=53820d56 vocab=d9d0734d
-/
lemma vecMulVec_sub_single_apply [DecidableEq n] {i j : n} (hij : i ≠ j)
    (a b : n) :
    vecMulVec (e i - e j) (e i - e j) a b =
      if a = i ∧ b = i then 1
      else if a = j ∧ b = j then 1
      else if a = i ∧ b = j then -1
      else if a = j ∧ b = i then -1
      else 0 := by
  simp only [vecMulVec_apply, sub_single_apply hij]
  split_ifs <;> simp_all

/-! ### N10 — Inner product against a rank-one Laplacian -/

/--
@isnad1 id=eq.2h4v.s7.766f20456dc5 from=translated src=- shape=ea8430a3 vocab=b347ac3d
-/
lemma inner_vecMulVec_sub_single [Fintype n] [DecidableEq n]
    {C : Matrix n n ℝ} (hC : C.IsSymm) {i j : n} (hij : i ≠ j) :
    inner C (vecMulVec (e i - e j) (e i - e j)) =
      C i i + C j j - 2 * C i j := by
  rw [inner_eq_sum]
  set x := e i - e j
  simp_rw [vecMulVec_apply]
  have hx0 {a : n} (hai : a ≠ i) (haj : a ≠ j) : x a = 0 := by
    simp [x, sub_single_apply hij, hai, haj]
  have hxi : x i = 1 := by simp [x, sub_single_apply hij]
  have hxj : x j = -1 := by
    simp only [x]
    rw [sub_single_apply hij, ite_eq_right hij.symm, ite_eq_left rfl]
  have hpair : ({i, j} : Finset n) ⊆ Finset.univ := Finset.subset_univ _
  have not_mem {a : n} (ha : a ∉ ({i, j} : Finset n)) : a ≠ i ∧ a ≠ j :=
    not_or.mp (by simpa [Finset.mem_insert, Finset.mem_singleton] using ha)
  have hvan_b (a : n) : ∀ b ∈ Finset.univ, b ∉ ({i, j} : Finset n) →
      C a b * (x a * x b) = 0 := by
    intro b _ hb
    obtain ⟨hbi, hbj⟩ := not_mem hb
    simp [hx0 hbi hbj]
  have hinter (a : n) :
      ∑ b, C a b * (x a * x b) = ∑ b ∈ ({i, j} : Finset n), C a b * (x a * x b) :=
    (Finset.sum_subset hpair (hvan_b a)).symm
  have hvan_a : ∀ a ∈ Finset.univ, a ∉ ({i, j} : Finset n) →
      (∑ b ∈ ({i, j} : Finset n), C a b * (x a * x b)) = 0 := by
    intro a _ ha
    obtain ⟨hai, haj⟩ := not_mem ha
    simp [hx0 hai haj]
  simp_rw [hinter]
  rw [← Finset.sum_subset hpair hvan_a, Finset.sum_pair hij]
  simp_rw [Finset.sum_pair hij, hxi, hxj]
  rw [hC.apply i j]
  ring

/-! ### N14 — Schur product of PSD matrices -/

/--
@isnad1 id=eq.0h5v.s6.380af9720fc5 from=translated src=- shape=22ea6c07 vocab=ce8b1a21
-/
lemma mul_diagonal_mul_transpose_apply [Fintype n] [DecidableEq n]
    (U : Matrix n n ℝ) (d : n → ℝ) (a b : n) :
    (U * diagonal d * Uᵀ) a b = ∑ k, d k * U a k * U b k := by
  calc (U * diagonal d * Uᵀ) a b
      = ∑ k, (U * diagonal d) a k * Uᵀ k b := by rw [mul_apply]
    _ = ∑ k, (U a k * d k) * U b k := by simp [mul_diagonal, transpose_apply]
    _ = ∑ k, d k * U a k * U b k :=
        Finset.sum_congr rfl fun _ _ => by ring

/--
@isnad1 id=eq.0h3v.s7.8888cf1e5986 from=translated src=- shape=c3314c2d vocab=a6485558
-/
lemma mul_diagonal_mul_transpose_eq_sum_smul_vecMulVec
    [Fintype n] [DecidableEq n] (U : Matrix n n ℝ) (d : n → ℝ) :
    U * diagonal d * Uᵀ =
      ∑ k, d k • vecMulVec (U.col k) (U.col k) := by
  ext a b
  rw [mul_diagonal_mul_transpose_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [smul_eq_mul, vecMulVec_apply, col_apply, mul_assoc]

/-- The unitary diagonalization of a real Hermitian matrix expands as a sum of
real rank-one terms.
@isnad1 id=eq.1h2v.s8.0eee181ffb56 from=translated src=- shape=c13f19de vocab=226ae2b2
-/
lemma isHermitian_eq_sum_smul_vecMulVec [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A = ∑ k, hA.eigenvalues k •
      vecMulVec ((hA.eigenvectorUnitary : Matrix n n ℝ).col k)
        ((hA.eigenvectorUnitary : Matrix n n ℝ).col k) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp]
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  exact mul_diagonal_mul_transpose_eq_sum_smul_vecMulVec _ _

/-- Hadamard product against a real rank-one matrix is a diagonal congruence.
@isnad1 id=eq.0h3v.s6.bdf7bb49079b from=translated src=- shape=938a284e vocab=f78b552b
-/
lemma hadamard_vecMulVec_eq_diagonal_mul [Fintype n] [DecidableEq n]
    (v : n → ℝ) (Y : Matrix n n ℝ) :
    vecMulVec v v ⊙ Y = diagonal v * Y * diagonal v := by
  ext i j
  simp [hadamard_apply, vecMulVec_apply, diagonal_mul, mul_diagonal]
  ring

/--
@isnad1 id=eq.0h6v.s6.4736f5b58d09 from=translated src=- shape=d21b1f21 vocab=345c908c
-/
lemma hadamard_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix m n ℝ)
    (Y : Matrix m n ℝ) : (∑ i ∈ s, f i) ⊙ Y = ∑ i ∈ s, f i ⊙ Y := by
  ext i j
  simp [hadamard_apply, Matrix.sum_apply, Finset.sum_mul]

/-- A real diagonal congruence preserves positive semidefiniteness.
@isnad1 id=possemid.1h3v.s6.42642d2b3217 from=translated src=- shape=f0de1bae vocab=979bb35a
-/
lemma posSemidef_diagonal_mul_mul_diagonal [Fintype n] [DecidableEq n]
    {Y : Matrix n n ℝ} (hY : Y.PosSemidef) (v : n → ℝ) :
    (diagonal v * Y * diagonal v).PosSemidef := by
  have h := hY.mul_mul_conjTranspose_same (diagonal v)
  rwa [conjTranspose_eq_transpose_of_trivial, diagonal_transpose] at h

/-- **Schur product theorem** (real PSD version): the Hadamard product of
positive semidefinite matrices is positive semidefinite.
@isnad1 id=possemid.2h3v.s5.801a51946a4e from=translated src=- shape=722f89e8 vocab=eb2fa268
-/
theorem posSemidef_hadamard [Finite n]
    {X Y : Matrix n n ℝ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (X ⊙ Y).PosSemidef := by
  cases nonempty_fintype n
  classical
  rw [isHermitian_eq_sum_smul_vecMulVec hX.isHermitian, hadamard_sum]
  simp_rw [smul_hadamard, hadamard_vecMulVec_eq_diagonal_mul]
  exact posSemidef_sum _ fun k _ =>
    (posSemidef_diagonal_mul_mul_diagonal hY _).smul (hX.eigenvalues_nonneg k)

/-- The entrywise square of a real PSD matrix is PSD.
@isnad1 id=possemid.1h2v.s4.2437a6ee6f3f from=translated src=- shape=19a416bd vocab=eb2fa268
-/
theorem posSemidef_hadamard_self [Finite n]
    {X : Matrix n n ℝ} (hX : X.PosSemidef) : (X ⊙ X).PosSemidef :=
  posSemidef_hadamard hX hX

end BollobasNikiforov
