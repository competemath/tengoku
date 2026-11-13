import Tengoku.Seed.Analysis.InnerProductSpace.SingularValues
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Singular value decomposition

Every matrix `A : Matrix m n 𝕜` over `𝕜 = ℝ` or `ℂ` (any `RCLike` field), with `m`, `n` arbitrary
finite types, factors as `A = U Σ Vᴴ` with `U`, `V` unitary and `Σ = rectDiag (singularValues A)` rectangular
diagonal with nonnegative, non-increasing real diagonal (Horn–Johnson 2013, Thm 2.6.3;
HMT 2011, §2.1). Over `ℝ`, `Vᴴ` is definitionally `Vᵀ` and `U`, `V` are orthogonal.

## Conventions

* `NLAlib.singularValues A : ℕ → ℝ` is Mathlib's `LinearMap.singularValues` of the Euclidean
 linear map of `A`, defined for `A : Matrix m n 𝕜` with `𝕜` `RCLike` and `m`, `n` arbitrary
 finite types: **zero-indexed** (`σ 0` is the largest), nonnegative, antitone, and
 `σ k ≠ 0 ↔ k < A.rank`; in particular `σ k = 0` for `k ≥ min m n`. Indexing by `ℕ` (rather
 than `Fin (min m n)`) means the singular values of matrices of different shapes are compared
 without casts, a rank-`k` split is `k < ·` vs `k ≤ ·`, and the truncated SVD is
 `rectDiag (fun i => if i < k then σ i else 0)`.
* The singular values are a *function of `A`*, not an existential witness: `exists_isSVD` only
 chooses the singular vectors `U`, `V`.
* `NLAlib.rectDiag σ : Matrix (Fin p) (Fin q) 𝕜` has entry `(σ i : 𝕜)` at `(i, i)` and `0`
 elsewhere (`rectDiag_apply_ofReal`); over `ℝ` the entry is `σ i` (`rectDiag_apply`). It is
 *positional*: its rows and columns are the sorted singular directions, like Mathlib's
 `Matrix.IsHermitian.eigenvalues₀ : Fin (card n) → ℝ`.
* Index shapes of `IsSVD A U V` for `A : Matrix m n 𝕜`: `U : Matrix m (Fin p) 𝕜`,
 `V : Matrix n (Fin q) 𝕜`, unitary (`UᴴU = 1`, `UUᴴ = 1`, so `p = card m`, `IsSVD.card_left`),
 the `k`-th column being the `k`-th singular vector. `exists_isSVD A` fills `p = card m`
 automatically; for `A : Matrix (Fin a) (Fin b) 𝕜` it gives `U : Matrix (Fin a) (Fin a) 𝕜`
 (`Fintype.card_fin`), so `Fin` statements need no casts. (`Fintype.equivFin (Fin a)` is an
 unspecified permutation, so a `rectDiag : Matrix m n 𝕜` built from `equivFin` would not be the
 positional diagonal at `Fin`; see `docs/rclike/F1b-alpha.md`.)
* Real matrices. Lemmas are stated once, with `ᴴ` (no `ᵀ` twins, `docs/STANDARDS.md` §2): at `ℝ`
 a term of the general statement elaborates against the `ᵀ` form, and a `rw` on a `ᵀ` goal uses
 `show Uᵀ * U = 1 from h.conjTranspose_mul_left` or
 `simp only [Matrix.conjTranspose_eq_transpose_of_trivial]`. The one real entry lemma kept is
 `rectDiag_apply` (cast-free entries of a real `rectDiag`).

## Main results

* `NLAlib.exists_isSVD`: `∃ U V, IsSVD A U V` (atlas `svd`).
* `NLAlib.IsSVD.conjTranspose_mul_self`, `NLAlib.IsSVD.mul_conjTranspose_self`:
 `AᴴA = V Σ² Vᴴ`, `AAᴴ = U Σ² Uᴴ`.
* `NLAlib.IsSVD.apply`: the entrywise outer-product expansion
 `A i j = ∑_{k < min m n} σ_k U_{ik} conj(V_{jk})`.
* `NLAlib.frobSq_eq_sum_sq_singularValues` (in `SingularValueSpectrum`):
 `‖A‖_F² = ∑_{k < min m n} σ_k²`.
* `NLAlib.singularValues_ne_zero_iff`, `NLAlib.rank_eq_card_singularValues_ne_zero`: rank.
* `NLAlib.sq_singularValues_eq_eigenvalues₀`: `σ_k²` is the `k`-th largest eigenvalue of `AᴴA`.
* `NLAlib.IsSVD.eq_head_add_tail`: block split `A = U Σ_{<k} Vᴴ + U Σ_{≥k} Vᴴ`.
* `NLAlib.singularValues_eq_of_eq_mul_rectDiag_mul`: uniqueness of the singular values (used for
 `singularValues_transpose` and the isometry invariances in `SingularValueInvariance.lean`).

The orthonormal completion of `{A vⱼ / σⱼ : σⱼ ≠ 0}` (atlas `orthonormal-completion`) is
Mathlib's `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`.

Atlas: `svd`.
-/

noncomputable section

open scoped Matrix
open Module Polynomial

namespace NLAlib

/-! ### Singular values -/

section General

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The singular values `σ₀ ≥ σ₁ ≥ ⋯ ≥ 0` of a matrix over `ℝ` or `ℂ` (any `RCLike` field) with
arbitrary finite row and column types, zero-indexed, padded with zeros:
`σ k = √(λ_k(AᴴA))` for `k < card n` and `σ k = 0` for `k ≥ card n`. Defined as Mathlib's
`LinearMap.singularValues` of `Matrix.toEuclideanLin A` (Horn–Johnson 2013, §2.6;
HMT 2011, §2.1). Deviation: zero-indexed, indexed by `ℕ`.
atlas: svd-def-/
def singularValues (A : Matrix m n 𝕜) : ℕ → ℝ :=
  fun k => (Matrix.toEuclideanLin A).singularValues k

/-- Bridge to Mathlib's `LinearMap.singularValues` (definitional). Atlas `svd`.
@isnad1 id=eq.0h5v.s12.8f9b1018184b from=translated src=- shape=f48dabb2 vocab=855c29ed
-/
theorem singularValues_eq_linearMap (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k = (Matrix.toEuclideanLin A).singularValues k := rfl

/-- Singular values are nonnegative. Atlas `svd`.
@isnad1 id=le.0h5v.s5.be40cef5cff5 from=translated src=- shape=04e0c756 vocab=f4e92ce5
-/
theorem singularValues_nonneg (A : Matrix m n 𝕜) (k : ℕ) :
    0 ≤ singularValues A k :=
  LinearMap.singularValues_nonneg _ _

/-- Singular values are listed in non-increasing order. Atlas `svd`.
@isnad1 id=antitone.0h4v.s5.978930220afc from=translated src=- shape=6b234148 vocab=37010eba
-/
theorem singularValues_antitone (A : Matrix m n 𝕜) :
    Antitone (singularValues A) :=
  fun _ _ h => LinearMap.singularValues_antitone _ h

end General

section RectDiag

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-! ### Rectangular diagonal matrices -/

/-- The `m × n` rectangular diagonal matrix over `𝕜` (`ℝ` or `ℂ`) with real diagonal
`σ 0, σ 1, …, σ (min m n - 1)`, cast to `𝕜`. Over `ℝ` the entries are `σ i` (definitionally).
Atlas `svd`.
atlas: svd-def-/
def rectDiag (σ : ℕ → ℝ) : Matrix (Fin m) (Fin n) 𝕜 :=
  Matrix.of fun i j => if (i : ℕ) = j then (σ i : 𝕜) else 0

/-- Entries of `rectDiag` over `𝕜`: `(σ i : 𝕜)` on the diagonal, `0` elsewhere. Atlas `svd`.
@isnad1 id=eq.0h6v.s6.2621c71ca05f from=translated src=- shape=42eba4c7 vocab=031b533c
-/
theorem rectDiag_apply_ofReal (σ : ℕ → ℝ) (i : Fin m) (j : Fin n) :
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜) i j = if (i : ℕ) = j then (σ i : 𝕜) else 0 := rfl

/-- Entries of a real `rectDiag` (no cast): the real form of `rectDiag_apply_ofReal`.
Atlas `svd`.
@isnad1 id=eq.0h5v.s5.9634bffbd7c0 from=translated src=- shape=33b3ca97 vocab=13cf0ca0
-/
theorem rectDiag_apply (σ : ℕ → ℝ) (i : Fin m) (j : Fin n) :
    (rectDiag σ : Matrix (Fin m) (Fin n) ℝ) i j = if (i : ℕ) = j then σ i else 0 := rfl

/-- The transpose of a rectangular diagonal matrix is rectangular diagonal. Atlas `svd`.
@isnad1 id=eq.0h4v.s5.755d0d3be991 from=translated src=- shape=785003f3 vocab=e7e97a40
-/
theorem transpose_rectDiag (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜)ᵀ = rectDiag σ := by
  ext i j
  simp only [Matrix.transpose_apply, rectDiag_apply_ofReal]
  split_ifs with h₁ h₂ h₂
  · rw [h₁]
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · rfl

/-- The conjugate transpose of a rectangular diagonal matrix (real diagonal) is rectangular
diagonal. Atlas `svd`.
@isnad1 id=eq.0h4v.s6.f11de2073faf from=translated src=- shape=785003f3 vocab=3e22cb70
-/
theorem conjTranspose_rectDiag (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜)ᴴ = rectDiag σ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, rectDiag_apply_ofReal]
  split_ifs with h₁ h₂ h₂
  · rw [h₁, RCLike.star_def, RCLike.conj_ofReal]
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · exact star_zero _

/-- `Σᴴ Σ` is diagonal with entries `σ_j²` for `j < m` and `0` beyond. Atlas `svd`.
@isnad1 id=eq.0h4v.s7.c35815d371e6 from=translated src=- shape=255e9989 vocab=13f36d20
-/
theorem conjTranspose_rectDiag_mul_rectDiag (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜)ᴴ * rectDiag σ =
      Matrix.diagonal fun j : Fin n => if (j : ℕ) < m then ((σ j ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [conjTranspose_rectDiag]
  ext j l
  simp only [Matrix.mul_apply, rectDiag_apply_ofReal, Matrix.diagonal_apply]
  by_cases hjm : (j : ℕ) < m
  · rw [Finset.sum_eq_single ⟨j, hjm⟩]
    · by_cases hjl : j = l
      · subst hjl; simp [hjm, sq]
      · have : (j : ℕ) ≠ l := fun h => hjl (Fin.ext h)
        simp [hjl, this]
    · intro i _ hi
      rw [ite_eq_right (fun h => hi (Fin.ext h.symm)), zero_mul]
    · simp
  · rw [Finset.sum_eq_zero]
    · split_ifs <;> simp_all
    · intro i _
      rw [ite_eq_right (fun (h : (j : ℕ) = i) => hjm (h ▸ i.isLt)), zero_mul]

/-- `Σ Σᴴ` is diagonal with entries `σ_i²` for `i < n` and `0` beyond. Atlas `svd`.
@isnad1 id=eq.0h4v.s7.80570e3e9a10 from=translated src=- shape=4ac002e8 vocab=13f36d20
-/
theorem rectDiag_mul_conjTranspose_rectDiag (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜) * (rectDiag σ)ᴴ =
      Matrix.diagonal fun i : Fin m => if (i : ℕ) < n then ((σ i ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [← conjTranspose_rectDiag (𝕜 := 𝕜) (m := n) (n := m) σ, Matrix.conjTranspose_conjTranspose,
    conjTranspose_rectDiag_mul_rectDiag]

/-- `rectDiag` is additive. Atlas `svd`.
@isnad1 id=eq.0h5v.s6.e084007c7b65 from=translated src=- shape=395cafca vocab=4706b581
-/
theorem rectDiag_add (σ τ : ℕ → ℝ) :
    (rectDiag (σ + τ) : Matrix (Fin m) (Fin n) 𝕜) = rectDiag σ + rectDiag τ := by
  ext i j
  simp only [rectDiag_apply_ofReal, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

end RectDiag

/-! ### Unitary matrices from orthonormal bases -/

section Unitary

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- The matrix whose columns are an orthonormal basis of `𝕜ᵐ`, indexed by any finite `ι`, has
orthonormal columns: `CᴴC = I`. Atlas `svd` (helper; belongs in a `Basic.lean`).
@isnad1 id=eq.0h4v.s9.ce67f6206329 from=translated src=- shape=bb92624f vocab=90eb638a
-/
theorem conjTranspose_mul_self_of_orthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 m)) :
    (Matrix.of fun i j => c j i : Matrix m ι 𝕜)ᴴ * (Matrix.of fun i j => c j i) = 1 := by
  ext i j
  rw [Matrix.one_apply, ← c.inner_eq_ite, EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.mul_apply, dotProduct, mul_comm]

/-- Orthonormal columns plus a square count make a unitary matrix: if `U : Matrix m (Fin p) 𝕜`
has `UᴴU = I` and `p = card m`, then `UUᴴ = I`. Atlas `svd`.
@isnad1 id=eq.2h4v.s8.ba42975def1e from=translated src=- shape=36c475ea vocab=9d12d4b9
-/
theorem mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one {p : ℕ} {U : Matrix m (Fin p) 𝕜}
    (hp : Fintype.card m = p) (hU : Uᴴ * U = 1) : U * Uᴴ = 1 := by
  let e : Fin p ≃ m := (finCongr hp.symm).trans (Fintype.equivFin m).symm
  have h1 : (Uᴴ.submatrix e.symm (Equiv.refl m)) * U.submatrix (Equiv.refl m) e.symm = 1 := by
    rw [Matrix.submatrix_mul_equiv, hU, Matrix.submatrix_one_equiv]
  have h2 := mul_eq_one_comm.1 h1
  rw [Matrix.submatrix_mul_equiv, Equiv.coe_refl, Matrix.submatrix_id_id] at h2
  exact h2

/-- A unitary `U : Matrix m (Fin p) 𝕜` (`UᴴU = I` and `UUᴴ = I`) has `p = card m` columns
(compare traces). Atlas `svd`.
@isnad1 id=eq.2h4v.s8.07b924af18a9 from=translated src=- shape=78951c22 vocab=9d12d4b9
-/
theorem card_eq_of_conjTranspose_mul_eq_one {p : ℕ} {U : Matrix m (Fin p) 𝕜}
    (h₁ : Uᴴ * U = 1) (h₂ : U * Uᴴ = 1) : Fintype.card m = p := by
  have h := congrArg Matrix.trace h₁
  rw [Matrix.trace_mul_comm, h₂, Matrix.trace_one, Matrix.trace_one, Fintype.card_fin] at h
  exact_mod_cast h

end Unitary

/-! ### The decomposition -/

section Decomposition

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- `IsSVD A U V` for `A : Matrix m n 𝕜`: `U : Matrix m (Fin p) 𝕜` and `V : Matrix n (Fin q) 𝕜`
are unitary (orthogonal over `ℝ`; so `p = card m`, `q = card n`) and `A = U Σ Vᴴ` with
`Σ = rectDiag (singularValues A)` (Horn–Johnson 2013, Thm 2.6.3; HMT 2011, §2.1). The `k`-th
columns of `U` and `V` are the left/right singular vectors for `σ_k`. At `m = Fin a`, `n = Fin b`
the factors are square, `U : Matrix (Fin a) (Fin a) 𝕜`. Over `ℝ`, `Uᴴ` is definitionally `Uᵀ`,
so the fields elaborate against the `ᵀ` forms. Atlas `svd`.
atlas: svd-def-/
structure IsSVD {p q : ℕ} (A : Matrix m n 𝕜) (U : Matrix m (Fin p) 𝕜)
    (V : Matrix n (Fin q) 𝕜) : Prop where
  /-- `U` has orthonormal columns: `UᴴU = I`.-/
  conjTranspose_mul_left : Uᴴ * U = 1
  /-- `V` has orthonormal columns: `VᴴV = I`.-/
  conjTranspose_mul_right : Vᴴ * V = 1
  /-- The factorization `A = U Σ Vᴴ`.-/
  eq : A = U * (rectDiag (singularValues A) : Matrix (Fin p) (Fin q) 𝕜) * Vᴴ
  /-- `U` is unitary: `UUᴴ = I`.-/
  mul_conjTranspose_left : U * Uᴴ = 1
  /-- `V` is unitary: `VVᴴ = I`.-/
  mul_conjTranspose_right : V * Vᴴ = 1

namespace IsSVD

variable {p q : ℕ} {A : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}

/-- The left factor of an SVD is square: `p = card m`. Atlas `svd`.
@isnad1 id=eq.1h8v.s5.64ca324fd858 from=translated src=- shape=0f108d46 vocab=ef41f9f4
-/
theorem card_left (h : IsSVD A U V) : Fintype.card m = p :=
  card_eq_of_conjTranspose_mul_eq_one h.conjTranspose_mul_left h.mul_conjTranspose_left

/-- The right factor of an SVD is square: `q = card n`. Atlas `svd`.
@isnad1 id=eq.1h8v.s5.0aa299d5c23f from=translated src=- shape=bfd7b165 vocab=ef41f9f4
-/
theorem card_right (h : IsSVD A U V) : Fintype.card n = q :=
  card_eq_of_conjTranspose_mul_eq_one h.conjTranspose_mul_right h.mul_conjTranspose_right

/-- `A V = U Σ`, i.e. `A vₖ = σₖ uₖ`. Atlas `svd`.
@isnad1 id=eq.1h8v.s7.e49ebc94a174 from=translated src=- shape=0284f12c vocab=c0adadd1
-/
theorem mul_right (h : IsSVD A U V) : A * V = U * rectDiag (singularValues A) := by
  conv_lhs => rw [h.eq]
  rw [Matrix.mul_assoc, h.conjTranspose_mul_right, Matrix.mul_one]

/-- `Uᴴ A = Σ Vᴴ`, i.e. `Aᴴ uₖ = σₖ vₖ`. Atlas `svd`.
@isnad1 id=eq.1h8v.s8.d2f88956be49 from=translated src=- shape=3729cb4a vocab=94398ede
-/
theorem conjTranspose_mul (h : IsSVD A U V) : Uᴴ * A = rectDiag (singularValues A) * Vᴴ := by
  conv_lhs => rw [h.eq]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.conjTranspose_mul_left, Matrix.one_mul]

/-- `Uᴴ A V = Σ`. Atlas `svd`.
@isnad1 id=eq.1h8v.s7.17437dc2ac0d from=translated src=- shape=fc741ab3 vocab=94398ede
-/
theorem conjTranspose_mul_mul (h : IsSVD A U V) : Uᴴ * A * V = rectDiag (singularValues A) := by
  rw [Matrix.mul_assoc, h.mul_right, ← Matrix.mul_assoc, h.conjTranspose_mul_left,
    Matrix.one_mul]

/-- `Aᴴ = V Σᴴ Uᴴ`: an SVD of the conjugate transpose. Atlas `svd`.
@isnad1 id=eq.1h8v.s8.3b36a4872559 from=translated src=- shape=ec47e93e vocab=94398ede
-/
theorem conjTranspose_eq (h : IsSVD A U V) :
    Aᴴ = V * (rectDiag (singularValues A) : Matrix (Fin q) (Fin p) 𝕜) * Uᴴ := by
  conv_lhs => rw [h.eq]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    conjTranspose_rectDiag, Matrix.mul_assoc]

/-- Block SVD split at index `k` (HMT 2011, §2.1, `A = U₁Σ₁V₁ᴴ + U₂Σ₂V₂ᴴ`): the head
`U Σ_{<k} Vᴴ` (the truncated SVD) plus the tail `U Σ_{≥k} Vᴴ`. Atlas `svd`.
atlas: svd-/
theorem eq_head_add_tail (h : IsSVD A U V) (k : ℕ) :
    A = U * (rectDiag (fun i => if i < k then singularValues A i else 0) :
        Matrix (Fin p) (Fin q) 𝕜) * Vᴴ +
      U * (rectDiag (fun i => if i < k then 0 else singularValues A i) :
        Matrix (Fin p) (Fin q) 𝕜) * Vᴴ := by
  rw [← Matrix.add_mul, ← Matrix.mul_add, ← rectDiag_add]
  convert h.eq using 4
  funext i
  simp only [Pi.add_apply]; split_ifs <;> simp

end IsSVD

end Decomposition

end NLAlib
