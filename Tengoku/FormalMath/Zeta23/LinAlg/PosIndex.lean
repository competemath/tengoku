/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were produced first, as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper —
like all Lean code in this repository, written by Claude, under the direction of the paper's authors — and are
incorporated here unchanged; they have no upstream outside this project (see README § Provenance and attribution).
-/
import Tengoku

/-!
# Positive index of a Hermitian matrix

For a Hermitian matrix `A` over `𝕜 = ℝ` or `ℂ`, the *positive index*
`n₊(A)` is the number of strictly positive eigenvalues. By Sylvester's law
of inertia this equals the maximal dimension of a subspace on which the
Hermitian form `x ↦ xᴴ A x` is positive definite.

This file defines `posIndex` via the eigenvalue count, together with the
real-valued trace `rtrace` and squared Frobenius norm `frobSq` needed for
the rank–trace inequality (paper §3, `lem:ranktrace`).
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index `n₊(A)` of a Hermitian matrix: the number of strictly
positive eigenvalues. Equivalently (Sylvester's law of inertia), the maximal
dimension of a subspace on which the form `x ↦ xᴴAx` is positive definite. -/
def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  #{i | 0 < hA.eigenvalues i}

/-- The negative index `n₋(A)`: the number of strictly negative eigenvalues. -/
def negIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  #{i | hA.eigenvalues i < 0}

/-- The thresholded positive index `n₊^θ(A)`: the number of eigenvalues
strictly above `θ`. `posIndexAbove hA 0 = posIndex hA`. -/
def posIndexAbove {A : Matrix n n 𝕜} (hA : A.IsHermitian) (θ : ℝ) : ℕ :=
  #{i | θ < hA.eigenvalues i}

/--
@isnad1 id=le.1h3v.s6.8cc5bd5e1fe1 from=translated src=- shape=e0bc0072 vocab=830f7524
-/
lemma posIndex_le_card {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    posIndex hA ≤ Fintype.card n :=
  (card_filter_le _ _).trans_eq card_univ

/-- For a PSD Hermitian matrix the positive index is the rank (every nonzero
eigenvalue is positive).
@isnad1 id=eq.1h3v.s6.177c4908b85d from=translated src=- shape=b4b7df51 vocab=5e5bf64f
-/
lemma posIndex_eq_rank_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    posIndex hA.isHermitian = A.rank := by
  rw [hA.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  unfold posIndex
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq]
  exact ⟨fun h => h.ne', fun h => (hA.eigenvalues_nonneg i).lt_of_ne' h⟩

/-- Real part of the trace. For a Hermitian matrix this is the full trace,
since the trace of a Hermitian matrix is real. -/
def rtrace (A : Matrix n n 𝕜) : ℝ := RCLike.re A.trace

/-- Squared Frobenius norm, `‖A‖_F² = Re tr(AᴴA) = ∑ᵢⱼ |Aᵢⱼ|²`. -/
def frobSq (A : Matrix n n 𝕜) : ℝ := RCLike.re (Aᴴ * A).trace

/--
@isnad1 id=eq.1h3v.s6.0a7fccaf8c08 from=translated src=- shape=3c943499 vocab=7e058011
-/
lemma rtrace_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    rtrace A = ∑ i, hA.eigenvalues i := by
  unfold rtrace
  rw [hA.trace_eq_sum_eigenvalues]
  simp

section Reindex

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)

/-- The canonical equivalence `Fin (card n) ≃ n` under which
`eigenvalues (e k) = eigenvalues₀ k`. -/
def eigEquiv : Fin (Fintype.card n) ≃ n :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

/--
@isnad1 id=eq.1h4v.s7.4d31dcefb787 from=translated src=- shape=270e0e64 vocab=3e41c95d
-/
lemma eigenvalues_eigEquiv (k : Fin (Fintype.card n)) :
    hA.eigenvalues (eigEquiv (n := n) k) = hA.eigenvalues₀ k := by
  simp [Matrix.IsHermitian.eigenvalues, eigEquiv]

/-- Any sum over `n` of a function of the eigenvalues equals the corresponding
sum over `Fin (card n)` of the function applied to `eigenvalues₀`.
@isnad1 id=eq.1h5v.s7.3a1d9f62cfc1 from=translated src=- shape=1e99875a vocab=0ed0c889
-/
lemma sum_eigenvalues_reindex {α : Type*} [AddCommMonoid α] (g : ℝ → α) :
    ∑ i, g (hA.eigenvalues i) = ∑ k, g (hA.eigenvalues₀ k) := by
  rw [← (eigEquiv (n := n)).sum_comp]
  simp only [eigenvalues_eigEquiv]

/--
@isnad1 id=eq.1h4v.s7.022043693c09 from=translated src=- shape=f8d35cc6 vocab=eb96dca1
-/
lemma card_eigenvalues_reindex (p : ℝ → Prop) [DecidablePred p] :
    #{i | p (hA.eigenvalues i)} = #{k | p (hA.eigenvalues₀ k)} := by
  apply Finset.card_nbij' (eigEquiv (n := n)).symm (eigEquiv (n := n))
  · intro i hi
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hi ⊢
    rwa [← eigenvalues_eigEquiv hA, Equiv.apply_symm_apply]
  · intro k hk
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hk ⊢
    rwa [eigenvalues_eigEquiv hA]
  · exact fun i _ => Equiv.apply_symm_apply _ i
  · exact fun k _ => Equiv.symm_apply_apply _ k

end Reindex

open Unitary in
/-- For a Hermitian matrix, `‖A‖_F² = ∑ᵢ λᵢ²` (sum of squared eigenvalues).
@isnad1 id=eq.1h3v.s6.9e06549a8f92 from=translated src=- shape=328737d3 vocab=89a51b0c
-/
lemma frobSq_hermitian_eq_sum_sq_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    frobSq A = ∑ i, (hA.eigenvalues i) ^ 2 := by
  -- A = U D Uᴴ ⟹ AᴴA = A² = U D² Uᴴ ⟹ tr(AᴴA) = ∑ λᵢ²
  unfold frobSq
  rw [hA.eq]
  conv_lhs => rw [hA.spectral_theorem, ← map_mul, conjStarAlgAut_apply,
    trace_mul_cycle, coe_star_mul_self, one_mul,
    diagonal_mul_diagonal, trace_diagonal]
  simp [sq]

end RHLinalg
