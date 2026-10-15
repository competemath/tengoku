/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.Monlib4.Preq.Ites

/-!
 # Conjugate of a matrix

This file defines the conjugate of a matrix, `matrix.conj` with the notation `ᴴᵀ`
(i.e., `xᴴᵀ i j = star (x i j)`), and shows basic properties about it.
-/

@[expose] public section

namespace Matrix

open scoped Matrix

variable {α n₁ n₂ : Type _}

/--
conjugate of matrix defined as $\bar{x} := {(x^*)}^\top$, i.e., $\bar{x}_{ij}=\overline{x_{ij}}$ -/
def conj [Star α] (x : Matrix n₁ n₂ α) : Matrix n₁ n₂ α :=
  xᴴᵀ

/-- Postfix notation `ᴴᵀ` for `Matrix.conj`. -/
scoped postfix:1024 "ᴴᵀ" => Matrix.conj

/--
@isnad1 id=eq.0h6v.s5.175fbd2ba8cd from=translated src=- shape=4ab569f2 vocab=83fefda2
-/
theorem conj_apply [Star α] (x : Matrix n₁ n₂ α) (i : n₁) (j : n₂) : xᴴᵀ i j = star (x i j) :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.5631008f8193 from=translated src=- shape=81e5d907 vocab=c89cafb2
-/
theorem conj_conj [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᵀᴴᵀ = x :=
  (conjTranspose_conjTranspose (xᵀᵀ)).trans (transpose_transpose _)

/--
@isnad1 id=eq.0h5v.s6.5353b90736a9 from=translated src=- shape=efb7b60a vocab=c3afc53f
-/
theorem conj_add [AddMonoid α] [StarAddMonoid α] (x y : Matrix n₁ n₂ α) : (x + y)ᴴᵀ = xᴴᵀ + yᴴᵀ :=
  by simp_rw [conj, ← transpose_add, ← conjTranspose_add]

/--
@isnad1 id=eq.0h6v.s6.6ab3dfc53c04 from=translated src=- shape=805555cd vocab=ee1f4a0e
-/
theorem conj_smul {R : Type _} [Star R] [Star α] [SMul R α] [StarModule R α] (c : R)
    (x : Matrix n₁ n₂ α) : (c • x)ᴴᵀ = star c • xᴴᵀ := by
  simp_rw [conj, ← transpose_smul, ← conjTranspose_smul]

/--
@isnad1 id=eq.0h4v.s5.3fa73110df56 from=translated src=- shape=513ef1f1 vocab=ae8fab97
-/
theorem conj_conjTranspose [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᵀᴴ = xᵀ :=
  conjTranspose_conjTranspose (xᵀ)

/--
@isnad1 id=eq.0h4v.s5.d9efc096aaa9 from=translated src=- shape=51c7fb99 vocab=ae8fab97
-/
theorem conjTranspose_conj [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᴴᵀ = xᵀ :=
  conj_conjTranspose _

/--
@isnad1 id=eq.0h4v.s5.f59bd8a819c4 from=translated src=- shape=513ef1f1 vocab=db6170c3
-/
theorem transpose_conj_eq_conjTranspose [Star α] (x : Matrix n₁ n₂ α) : xᴴᵀᵀ = xᴴ :=
  rfl

namespace IsHermitian

/--
@isnad1 id=eq.1h3v.s5.61323bb7cf63 from=translated src=- shape=ee823f11 vocab=ad56273d
-/
theorem conj {α n : Type _} [Star α] {x : Matrix n n α} (hx : x.IsHermitian) :
    xᴴᵀ = xᵀ := by simp_rw [Matrix.conj, hx.eq]

end IsHermitian

/--
@isnad1 id=eq.0h6v.s7.d30d65ec7c47 from=translated src=- shape=bcac401f vocab=ebc189bb
-/
theorem conj_mul {α m n p : Type _} [Fintype n] [CommSemiring α] [StarRing α] (x : Matrix m n α)
    (y : Matrix n p α) : (x * y)ᴴᵀ = xᴴᵀ * yᴴᵀ := by
  ext
  simp_rw [conj_apply, mul_apply, star_sum, StarMul.star_mul, conj_apply, mul_comm]

/--
@isnad1 id=eq.0h2v.s6.802c082b14b4 from=translated src=- shape=c1b4d2fd vocab=0c83c12c
-/
theorem conj_one {α n : Type _} [DecidableEq n] [Semiring α] [StarRing α] :
    (1 : Matrix n n α)ᴴᵀ = 1 := by
  ext
  simp_rw [conj_apply, one_apply, star_ite, star_one, star_zero]

/--
@isnad1 id=eq.0h3v.s6.d80eaabefffd from=translated src=- shape=938e9a06 vocab=2cc69f25
-/
theorem conj_zero {α n₁ n₂ : Type _} [AddMonoid α] [StarAddMonoid α] :
  (0 : Matrix n₁ n₂ α)ᴴᵀ = 0 := by
  ext
  simp_rw [conj_apply, zero_apply, star_zero]

end Matrix
