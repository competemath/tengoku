/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Subgroups of `GL₂(𝔽_ℓ)` containing a transvection and stabilizing no line

The group theory behind [GenEll], Lemma 3.1(iii) (Serre, *Abelian ℓ-adic representations*,
IV-3.2, Lemma 2): a subgroup `G ≤ GL₂(𝔽_ℓ)` (`ℓ` prime) that contains a transvection `T ≠ 1`
(`(T − 1)² = 0`) and stabilizes no line contains `SL₂(𝔽_ℓ)`
(`Iut.SL2.toGL_mem_of_transvection`).

The proof: `N = T − 1` has `N² = 0`, `N ≠ 0`, so `N` has a nonzero vector `v` with `Nv = 0`.
Some `g ∈ G` has `w = gv ∉ 𝔽_ℓ·v`, and in the basis `(v, w)` the elements `T` and `gTg⁻¹`
become the elementary matrices `E₁₂(b)`, `E₂₁(c)` with `b, c ≠ 0`. Their powers give all
`E₁₂(x)`, `E₂₁(y)` (`𝔽_ℓ` is a prime field), and the elementary matrices generate `SL₂`
(`Matrix.SpecialLinearGroup.SL2.transvection_induction`).

An element of order `ℓ` of `GL₂(𝔽_ℓ)` is such a transvection (`Iut.SL2.transvection_of_orderOf`):
`(M − 1)^ℓ = M^ℓ − 1 = 0`, and a nilpotent `2 × 2` matrix squares to zero.
-/

namespace Iut.SL2

open Matrix Polynomial
open scoped MatrixGroups

/-! ### Nilpotent `2 × 2` matrices -/

/-! ### The generation lemma -/

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The matrix with columns `v`, `w`. -/
def colMat (v w : Fin 2 → ZMod ℓ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := !![v 0, w 0; v 1, w 1]

end Iut.SL2
