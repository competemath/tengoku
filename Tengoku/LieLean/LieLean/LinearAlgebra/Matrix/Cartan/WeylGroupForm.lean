/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.LinearAlgebra.Matrix.Cartan.WeylGroup
import Tengoku.LieLean.LieLean.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Weyl group preserves the form on `𝔥*`

For a symmetrization `S` of a generalized Cartan matrix `A`, the Weyl group preserves the
symmetric bilinear form `(·|·)` on `𝔥*` ([Kac] Prop. 3.9). For positive integers `dᵢ` with
`diag(d) A` symmetric (e.g. those of a finite-type Cartan matrix, `Matrix.IsFiniteCartan`), the
symmetrization `εᵢ = 1 / dᵢ` has `(∑ kᵢ αᵢ | x) = ∑ kᵢ dᵢ ⟨x, αᵢ^∨⟩`; on the root lattice its
values are those of the integral quadratic form `kᵀ diag(d) A k`.

## Main definitions

* `Matrix.Symmetrization.ofDiagonal`: the symmetrization `εᵢ = 1 / dᵢ` of a matrix with
  `diag(d) A` symmetric.

## Main results

* `Matrix.Realization.dualBilinForm_weylGroup`: `(w μ | w μ') = (μ | μ')` for `w ∈ W`.
* `Matrix.Realization.dualBilinForm_ofDiagonal_rootOf`: `(∑ kᵢ αᵢ | x) = ∑ kᵢ dᵢ ⟨x, αᵢ^∨⟩`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Prop. 3.9.
-/

noncomputable section

open Module

namespace Matrix.Symmetrization

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ}

/-- The symmetrization `εᵢ = 1 / dᵢ` attached to positive integers `dᵢ` with `diag(d) A`
symmetric; its symmetric matrix is `diag(d) A`.-/
def ofDiagonal (d : ι → ℤ) (hd : ∀ i, 0 < d i) (hsymm : (diagonal d * A).IsSymm) :
    A.Symmetrization where
  ε i := 1 / d i
  ε_pos i := by have := hd i; positivity
  ε_mul_comm i j := by
    have h := congrFun (congrFun hsymm i) j
    simp only [transpose_apply, diagonal_mul] at h
    have hi : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
    have hj : (d j : ℚ) ≠ 0 := by exact_mod_cast (hd j).ne'
    have h' : (d j * A j i : ℚ) = d i * A i j := by exact_mod_cast h
    field_simp
    linarith

end Matrix.Symmetrization

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  [FiniteDimensional K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsGeneralizedCartan) (S : A.Symmetrization)

/-! ### `W`-invariance of the form on `𝔥*` -/

variable [DecidableEq ι]

end Matrix.Realization
