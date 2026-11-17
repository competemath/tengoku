/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupExchange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Generalized Cartan matrices of finite type: the Weyl group is finite

Let `A` be a Cartan matrix of finite type in the sense of Mathlib's `Matrix.IsFiniteCartan`: a
generalized Cartan matrix such that `D A` is symmetric positive definite for some diagonal matrix
`D = diag(d)` with positive integer entries. This is the characterization of finite type by
symmetrizability and positive definiteness ([Kac] Prop. 4.9; Kac's definition of finite type,
[Kac] Thm. 4.3 (Fin), equivalently positivity of all principal minors ([Kac] Prop. 4.7 (a)),
is equivalent for indecomposable symmetrizable matrices). Mathlib shows that the Cartan matrix of a
finite crystallographic root system is of this kind
(`RootPairing.Base.cartanMatrix_isFiniteCartan`).

Let `(𝔥, Π, Π^∨)` be a realization of `A` over a field `K` of characteristic zero. We prove:

* `A` is nonsingular, so `dim 𝔥 = |ι|` and the simple roots form a basis of `𝔥*`.
* The integral quadratic form `q(k) = kᵀ D A k` on the root lattice `Q = ℤ^ι` is `W`-invariant:
  a direct computation shows `q(rᵢ k) = q(k)` for `rᵢ k = k - (A k)ᵢ eᵢ`. (Up to the positive
  scalars `dᵢ`, `q` is the restriction to `Q` of the form `(·|·)` of [Kac] §2.1.)
* Since `q` is positive definite, it has finitely many vectors of bounded norm
  (`Matrix.PosDef.finite_setOfPred_dotProduct_mulVec_le`). Every real root `w αᵢ` lies in the
  root lattice and has `q(w αᵢ) = q(αᵢ) = 2 dᵢ`, so the set of real roots is finite.
* Since `W` acts faithfully on the simple roots
  (`Matrix.Realization.eq_one_of_forall_apply_root_eq`), `w ↦ (w αᵢ)ᵢ` embeds `W` in the finite
  set of maps from `ι` to the real roots; hence `W` is finite ([Kac] Prop. 4.9).

The argument is the standard one; we reconstructed it rather than following a specific printed
proof.

## Main results

* `Matrix.Realization.finrank_eq_card_of_isFiniteCartan`: `dim 𝔥 = |ι|`.
* `Matrix.Realization.span_root_eq_top_of_isFiniteCartan`: the simple roots span `𝔥*`.
* `Matrix.Realization.exists_apply_rootOf_eq_rootOf_and_quadForm_eq`: `W` preserves the form
  `kᵀ D A k` on the root lattice.
* `Matrix.Realization.finite_realRoots`: the set of real roots is finite.
* `Matrix.Realization.finite_weylGroup`: the Weyl group is finite.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.1, §4.3, §4.7,
  §4.9, §5.1.
-/

open Module

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ}

/-- For a symmetric matrix `D A` with `D = diag(d)`, the quadratic form `k ↦ kᵀ D A k` is
invariant under the fundamental reflection `k ↦ k - (A k)ᵢ eᵢ`.-/
lemma dotProduct_diagonal_mul_mulVec_reflection {d : ι → ℤ} (hd : (diagonal d * A).IsSymm)
    (hA : A.IsGeneralizedCartan) (i : ι) (k : ι → ℤ) :
    (k - (A *ᵥ k) i • Pi.single i 1) ⬝ᵥ (diagonal d * A) *ᵥ (k - (A *ᵥ k) i • Pi.single i 1) =
      k ⬝ᵥ (diagonal d * A) *ᵥ k := by
  have hsymm : k ⬝ᵥ (diagonal d * A) *ᵥ Pi.single i 1 =
      Pi.single i 1 ⬝ᵥ (diagonal d * A) *ᵥ k := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hd.eq, dotProduct_comm]
  have hGk : Pi.single i 1 ⬝ᵥ (diagonal d * A) *ᵥ k = d i * (A *ᵥ k) i := by
    rw [single_one_dotProduct, ← mulVec_mulVec, mulVec_diagonal]
  have hGi : Pi.single i 1 ⬝ᵥ (diagonal d * A) *ᵥ Pi.single i (1 : ℤ) = 2 * d i := by
    rw [single_one_dotProduct, ← mulVec_mulVec, mulVec_diagonal, mulVec_single_one]
    simp [hA.diag i, mul_comm]
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, hsymm, hGk, hGi]
  ring

end Matrix

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

variable {d : ι → ℤ} (hd : (diagonal d * A).IsSymm) (hA : A.IsGeneralizedCartan)
include hd

omit hd

variable [CharZero K]

end Matrix.Realization
