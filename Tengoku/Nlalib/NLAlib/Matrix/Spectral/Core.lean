import Tengoku.Seed.Analysis.Matrix.Spectrum
import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Seed.LinearAlgebra.Matrix.DotProduct
import Tengoku.Nlalib.NLAlib.Matrix.Basic.Pseudoinverse
import Tengoku.Nlalib.NLAlib.Matrix.Norms.SpectralNormBounds
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SVD

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Extreme eigenvalues and singular values

The extreme spectral quantities of a matrix over `𝕜` (`ℝ` or `ℂ`), their variational
characterisations, and the bounds on the inverse Gram matrix that the probabilistic arguments
about the smallest singular value start from.

* `NLAlib.lambdaMax A`, `NLAlib.lambdaMin A`: `sSup` / `sInf` of the real spectrum of a square
 matrix. For a Hermitian `A` they are Mathlib's sorted eigenvalues at the first and last index
 (`lambdaMax_eq_eigenvalues₀_zero`, `lambdaMin_eq_eigenvalues₀_last`); for a non-Hermitian `A`
 the real spectrum may be empty and the values are junk (`sSup ∅ = 0`).
* The smallest eigenvalue of a Hermitian `M` is `hM.eigenvalues₀ ⟨card n - 1, _⟩`, with the
 Rayleigh characterisation `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf`
 (`λ_min(M) = inf { Re(x* M x) : ‖x‖₂ = 1 }`).
* The smallest singular value of `A : Matrix m n 𝕜` is `singularValues A (card n - 1)` (for a
 wide matrix this is `0`; for the smallest singular value of a wide matrix use `Aᴴ`), with the
 variational form `singularValues_last_eq_iInf` (`σ_min(A) = inf { ‖Ax‖₂ : ‖x‖₂ = 1 }`) and
 the consequences `singularValues_last_le_norm_mulVec`, `le_singularValues_last`,
 `singularValues_last_mul_norm_le`.

## Contents

* Coordinates and nets: `⟨v, A u⟩ = ∑ᵢⱼ vᵢ Aᵢⱼ uⱼ`, and the net bound
 `(1 - 2ε)‖A‖₂ ≤ max_{(u,v) ∈ I} ⟨v, A u⟩` for an `ε`-net `I` of pairs of unit vectors
 (`one_sub_two_mul_mul_specNorm_le_iSup`), used by the Gaussian comparison proofs of
 `NLAlib.RandomMatrix.Gaussian.Spectral`.
* Small `σ_min` and column distances (atlas `smin-small-ball`): if `σ_min(A) ≤ s` then some column
 of `A` is within `√n · s` of the span of the others
 (`exists_iInf_norm_mulVec_le_of_singularValues_last_le`).
* The inverse Gram matrix (atlas `pseudoinverse`): for `A Aᵀ` invertible,
 `‖(A Aᵀ)⁻¹‖₂ = 1/σ_min(Aᵀ)²` and `‖A†‖₂² = ‖(A Aᵀ)⁻¹‖₂` with `A† = pinvR A`.

The Frobenius Lipschitz bound `|σ_k(A) − σ_k(B)| ≤ ‖A − B‖_F` (atlas `norm-lipschitz`) is
`abs_singularValues_sub_le_frobNorm` in `NLAlib.Matrix.Spectral.Weyl`. The entrywise extension
`realMatrixComplexification` is in `NLAlib.Matrix.Spectral.Complexification`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Extreme eigenvalues -/

/-- The largest real spectral value `sSup (spectrum ℝ A)`; the largest eigenvalue of a Hermitian
matrix (`lambdaMax_eq_eigenvalues₀_zero`). For a non-Hermitian `A` the real spectrum may be
empty and the value is Mathlib's `sSup ∅ = 0`. Tropp 2015, §2.1.
atlas: matrix-calculus-def-/
def lambdaMax [DecidableEq n] (A : Matrix n n 𝕜) : ℝ := sSup (spectrum ℝ A)

/-- The smallest real spectral value `sInf (spectrum ℝ A)`; the smallest eigenvalue of a
Hermitian matrix (`lambdaMin_eq_eigenvalues₀_last`). For a non-Hermitian `A` the real spectrum
may be empty and the value is Mathlib's `sInf ∅ = 0`. Tropp 2015, §2.1.
atlas: matrix-calculus-def-/
def lambdaMin [DecidableEq n] (A : Matrix n n 𝕜) : ℝ := sInf (spectrum ℝ A)

/-- The sorted eigenvalues `eigenvalues₀` and the `n`-indexed `eigenvalues` have the same
range.
@isnad1 id=eq.1h3v.s6.0bb318eae2c8 from=translated src=- shape=8187bf00 vocab=35836537
-/
theorem _root_.Matrix.IsHermitian.range_eigenvalues₀ [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : Set.range hA.eigenvalues₀ = Set.range hA.eigenvalues := by
  have h : hA.eigenvalues = hA.eigenvalues₀ ∘ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm :=
    rfl
  rw [h, (Equiv.surjective _).range_comp]

/-- For a Hermitian `A` on a nonempty index type, `lambdaMax A` is the first (largest) of
Mathlib's decreasingly sorted eigenvalues. Horn–Johnson 2013, Thm 4.2.2.
@isnad1 id=eq.1h3v.s6.57c370b90116 from=translated src=- shape=c469c9d4 vocab=4b2dd724
-/
theorem lambdaMax_eq_eigenvalues₀_zero [DecidableEq n] [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : lambdaMax A = hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩ := by
  rw [lambdaMax, hA.spectrum_real_eq_range_eigenvalues, ← hA.range_eigenvalues₀]
  refine IsGreatest.csSup_eq ⟨⟨_, rfl⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact hA.eigenvalues₀_antitone (Nat.zero_le (i : ℕ))

/-- For a Hermitian `A` on a nonempty index type, `lambdaMin A` is the last (smallest) of
Mathlib's decreasingly sorted eigenvalues. Horn–Johnson 2013, Thm 4.2.2.
@isnad1 id=eq.1h3v.s6.328ff547e017 from=translated src=- shape=084d396c vocab=0bfe80ae
-/
theorem lambdaMin_eq_eigenvalues₀_last [DecidableEq n] [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    lambdaMin A = hA.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_one_lt_of_lt Fintype.card_pos⟩ := by
  rw [lambdaMin, hA.spectrum_real_eq_range_eigenvalues, ← hA.range_eigenvalues₀]
  refine IsLeast.csInf_eq ⟨⟨_, rfl⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact hA.eigenvalues₀_antitone (Nat.le_sub_one_of_lt i.isLt)

/-- Sorted eigenvalues depend only on the matrix: equal matrices have equal `eigenvalues₀`
(whatever Hermitian proofs are supplied).
@isnad1 id=eq.3h5v.s7.bc3c2e0ac898 from=translated src=- shape=6e97db69 vocab=a7a31ecd
-/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_congr [DecidableEq n] {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) (i : Fin (Fintype.card n)) :
    hA.eigenvalues₀ i = hB.eigenvalues₀ i := by
  subst h; rfl

/-! ### The unit sphere -/

/-- The Euclidean unit sphere of `n → 𝕜` is nonempty as soon as the index type is.
@isnad1 id=nonempty.0h2v.s6.5605bcf3861e from=translated src=- shape=99c403ae vocab=2db39694
-/
theorem nonempty_unitSphere [Nonempty n] :
    Nonempty {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} := by
  classical
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨⟨Pi.single i 1, ?_⟩⟩
  rw [show (WithLp.toLp 2 (Pi.single i (1 : 𝕜)) : EuclideanSpace 𝕜 n) = EuclideanSpace.single i 1
    from rfl, PiLp.norm_single, norm_one]

/-- The Euclidean unit sphere of `n → 𝕜` is empty when the index type is.
@isnad1 id=isempty.0h2v.s6.e4d109456205 from=translated src=- shape=99c403ae vocab=6b08b86a
-/
theorem isEmpty_unitSphere [IsEmpty n] :
    IsEmpty {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} := ⟨fun x => by
  have h := x.2
  rw [Subsingleton.elim x.1 0, WithLp.toLp_zero, norm_zero] at h
  exact zero_ne_one h⟩

/-! ### Rayleigh characterisation of the smallest eigenvalue -/

/-- **Rayleigh characterisation of the smallest eigenvalue.** For a Hermitian `M` on a nonempty
index type, the last (smallest) of Mathlib's decreasingly sorted eigenvalues is
`λ_min(M) = inf { Re(x* M x) : ‖x‖₂ = 1 }`. Horn–Johnson 2013, Theorem 4.2.2.
@isnad1 id=eq.2h3v.s9.213d131134aa from=translated src=- shape=1bf137e8 vocab=3928f507
-/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_last_eq_iInf [DecidableEq n] {M : Matrix n n 𝕜}
    (hM : M.IsHermitian) (hn : 0 < Fintype.card n) :
    hM.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_one_lt_of_lt hn⟩ =
      ⨅ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (star x.1 ⬝ᵥ (M *ᵥ x.1)) := by
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  set k : Fin (Fintype.card n) := ⟨Fintype.card n - 1, Nat.sub_one_lt_of_lt hn⟩
  have hmin : ∀ i, hM.eigenvalues₀ k ≤ hM.eigenvalues i := fun i =>
    hM.eigenvalues₀_antitone (Nat.le_sub_one_of_lt (e.symm i).isLt)
  -- eigen-coordinates `y = Uᴴ x`: `Re(x* M x) = ∑ᵢ λᵢ ‖yᵢ‖²` and `∑ᵢ ‖yᵢ‖² = ‖x‖²`
  set U : Matrix n n 𝕜 := (hM.eigenvectorUnitary : Matrix n n 𝕜)
  have hUU : U * Uᴴ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hD : Uᴴ * M * U = Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) := by
    have h := hM.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, U, Matrix.star_eq_conjTranspose] using h
  have hUy : ∀ x : n → 𝕜, U *ᵥ (Uᴴ *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hquad : ∀ x : n → 𝕜, RCLike.re (star x ⬝ᵥ (M *ᵥ x)) =
      ∑ i, hM.eigenvalues i * ‖(Uᴴ *ᵥ x) i‖ ^ 2 := by
    intro x
    have h1 : star x ⬝ᵥ (M *ᵥ x) =
        ∑ i, (hM.eigenvalues i : 𝕜) * (star ((Uᴴ *ᵥ x) i) * (Uᴴ *ᵥ x) i) := by
      calc star x ⬝ᵥ (M *ᵥ x) = star (U *ᵥ (Uᴴ *ᵥ x)) ⬝ᵥ (M *ᵥ (U *ᵥ (Uᴴ *ᵥ x))) := by
            rw [hUy]
        _ = star (Uᴴ *ᵥ x) ⬝ᵥ ((Uᴴ * M * U) *ᵥ (Uᴴ *ᵥ x)) := by
            rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
              Matrix.mulVec_mulVec]
        _ = _ := by
            rw [hD]
            simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, Pi.star_apply]
            exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
      RCLike.ofReal_re]
  have hnorm : ∀ x : n → 𝕜, ∑ i, ‖(Uᴴ *ᵥ x) i‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
    intro x
    rw [← EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (Uᴴ *ᵥ x)), norm_toLp_sq_eq_re_star_dotProduct,
      norm_toLp_sq_eq_re_star_dotProduct, star_mulVec_dotProduct_mulVec_self,
      Matrix.conjTranspose_conjTranspose, hUU, Matrix.one_mulVec]
  have hlow : ∀ x : n → 𝕜, hM.eigenvalues₀ k * ‖WithLp.toLp 2 x‖ ^ 2 ≤
      RCLike.re (star x ⬝ᵥ (M *ᵥ x)) := by
    intro x
    rw [hquad, ← hnorm, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg _)
  -- the eigenvector of `λ_min` attains the bound
  set v : n → 𝕜 := ⇑(hM.eigenvectorBasis (e k))
  have hv : ‖WithLp.toLp 2 v‖ = 1 := by
    rw [show (WithLp.toLp 2 v : EuclideanSpace 𝕜 n) = hM.eigenvectorBasis (e k) from rfl]
    exact hM.eigenvectorBasis.orthonormal.1 (e k)
  have hbdd : BddBelow (Set.range fun x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} =>
      RCLike.re (star x.1 ⬝ᵥ (M *ᵥ x.1))) :=
    ⟨hM.eigenvalues₀ k, by rintro _ ⟨x, rfl⟩; simpa [x.2] using hlow x.1⟩
  apply le_antisymm
  · have : Nonempty {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} := ⟨⟨v, hv⟩⟩
    exact le_ciInf fun x => by simpa [x.2] using hlow x.1
  · refine (ciInf_le hbdd ⟨v, hv⟩).trans_eq ?_
    show RCLike.re (star v ⬝ᵥ (M *ᵥ v)) = _
    rw [hM.mulVec_eigenvectorBasis, dotProduct_smul, RCLike.smul_re, ← norm_toLp_sq_eq_re_star_dotProduct,
      hv, one_pow, mul_one]
    simp [Matrix.IsHermitian.eigenvalues, e, k]

/-! ### Variational characterisation of the smallest singular value -/

/-! ### Coordinates and nets -/

open scoped RealInnerProductSpace in
/-- The bilinear form of a matrix in coordinates: `⟨v, A u⟩ = ∑ᵢⱼ vᵢ Aᵢⱼ uⱼ`.
@isnad1 id=eq.0h5v.s13.b7d83fae9ec9 from=translated src=- shape=ee829299 vocab=bc7fb702
-/
theorem inner_toEuclideanLin_eq_sum [DecidableEq n] (A : Matrix m n ℝ)
    (u : EuclideanSpace ℝ n) (v : EuclideanSpace ℝ m) :
    ⟪v, (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A u⟫
      = ∑ i, ∑ j, v i * A i j * u j := by
  simp [PiLp.inner_apply, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

open scoped Matrix.Norms.L2Operator RealInnerProductSpace in
/-- Net argument for the spectral norm: if every pair of unit vectors `(u, v)` is `ε`-close to a
pair in the finite set `I` (whose second components are unit vectors), then
`(1 - 2ε)‖A‖₂ ≤ max_{(u,v) ∈ I} ⟨v, A u⟩`. Vershynin 2012, Lemma 5.4 (in this form). Helper for
atlas `gordon`, `spectral-second-moment`.
@isnad1 id=le.3h5v.s9.1d212a16565a from=translated src=- shape=e3ee998e vocab=c884d262
-/
theorem one_sub_two_mul_mul_specNorm_le_iSup [DecidableEq n] (A : Matrix m n ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (I : Finset (EuclideanSpace ℝ n × EuclideanSpace ℝ m))
    (hI : ∀ t ∈ I, ‖t.2‖ = 1)
    (hcov : ∀ (u : EuclideanSpace ℝ n) (v : EuclideanSpace ℝ m), ‖u‖ = 1 → ‖v‖ = 1 →
      ∃ t ∈ I, ‖u - t.1‖ ≤ ε ∧ ‖v - t.2‖ ≤ ε) :
    (1 - 2 * ε) * specNorm A ≤ ⨆ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j := by
  set Φ := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A with hΦ
  have hM : specNorm A = ‖Φ‖ := rfl
  set S := ⨆ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j with hS
  have hbdd : BddAbove (Set.range fun t : I => ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j) :=
    (Set.finite_range _).bddAbove
  set M := ‖Φ‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  rw [hM]
  rcases hM0.lt_or_eq with hMpos | hMzero
  · -- main case
    have claim : ∀ r : ℝ, 0 ≤ r → r < M → r - 2 * ε * M ≤ S := by
      intro r hr0 hrM
      obtain ⟨x, hx1, hrx⟩ := Φ.exists_lt_apply_of_lt_opNorm hrM
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hrx
        linarith
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      set u : EuclideanSpace ℝ n := (‖x‖⁻¹ : ℝ) • x with hu
      have hu1 : ‖u‖ = 1 := norm_smul_inv_norm hx0
      have hΦu : ‖Φ x‖ ≤ ‖Φ u‖ := by
        rw [hu, map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
        rw [le_inv_mul_iff₀ hxpos]
        exact mul_le_of_le_one_left (norm_nonneg _) hx1.le
      set w := Φ u with hw
      have hrw : r < ‖w‖ := lt_of_lt_of_le hrx hΦu
      have hw0 : w ≠ 0 := by
        intro h; rw [h, norm_zero] at hrw; linarith
      set v : EuclideanSpace ℝ m := (‖w‖⁻¹ : ℝ) • w with hv
      have hv1 : ‖v‖ = 1 := norm_smul_inv_norm hw0
      have hvw : ⟪v, w⟫ = ‖w‖ := by
        rw [hv, real_inner_smul_left, real_inner_self_eq_norm_sq]
        have : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
        field_simp
      obtain ⟨t, ht, htu, htv⟩ := hcov u v hu1 hv1
      have ht2 : ‖t.2‖ = 1 := hI t ht
      have hwM : ‖w‖ ≤ M := by
        have := Φ.le_opNorm u; rw [hu1, mul_one] at this; exact this
      have hdecomp : Φ t.1 = w - Φ (u - t.1) := by
        rw [map_sub]; abel
      have hval : ∑ i, ∑ j, t.2 i * A i j * t.1 j = ⟪t.2, Φ t.1⟫ :=
        (inner_toEuclideanLin_eq_sum A t.1 t.2).symm
      have hval2 : ⟪t.2, Φ t.1⟫ = ⟪v, w⟫ - ⟪v - t.2, w⟫ - ⟪t.2, Φ (u - t.1)⟫ := by
        rw [hdecomp, inner_sub_right, inner_sub_left]; ring
      have hb1 : ⟪v - t.2, w⟫ ≤ ε * M := by
        refine (real_inner_le_norm _ _).trans ?_
        exact mul_le_mul htv hwM (norm_nonneg _) hε
      have hb2 : ⟪t.2, Φ (u - t.1)⟫ ≤ ε * M := by
        refine (real_inner_le_norm _ _).trans ?_
        rw [ht2, one_mul]
        refine (Φ.le_opNorm _).trans ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right htu hM0
      have hle : ∑ i, ∑ j, t.2 i * A i j * t.1 j ≤ S :=
        le_ciSup hbdd (⟨t, ht⟩ : I)
      rw [hval, hval2, hvw] at hle
      linarith
    by_contra hcon
    push Not at hcon
    set r := (S + 2 * ε * M + M) / 2
    have h1 := claim (max r 0) (le_max_right _ _) (max_lt (by
      simp only [r]; nlinarith) hMpos)
    have : r ≤ max r 0 := le_max_left _ _
    simp only [r] at this
    nlinarith
  · -- `A = 0`
    have hA : Φ = 0 := norm_eq_zero.1 hMzero.symm
    have hA' : ∀ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j = 0 := by
      intro t
      rw [← inner_toEuclideanLin_eq_sum, ← hΦ, hA]
      simp
    rw [← hMzero]
    simp only [mul_zero]
    rw [hS]
    simp only [hA', Real.iSup_const_zero, le_refl]

/-! ### Small `σ_min` and column distances -/

/-! ### The inverse Gram matrix and the pseudoinverse -/

section InverseGram

variable [DecidableEq m]

open scoped Matrix.Norms.L2Operator in
/-- **Spectral norm of the pseudoinverse.** For a real matrix `A` with `A Aᵀ` invertible,
`‖A†‖₂² = ‖(A Aᵀ)⁻¹‖₂` with `A† = pinvR A = Aᵀ (A Aᵀ)⁻¹` (`C*`-identity `‖A†‖² = ‖(A†)ᵀ A†‖`
and `(A†)ᵀ A† = (A Aᵀ)⁻¹`). (Without the hypothesis both sides are `0`.) HMT 2011, proof of
Prop A.3 / Prop 10.4; helper for `pinv-spectral-tail`.
atlas: pseudoinverse
@isnad1 id=eq.1h3v.s7.a9c6ee1db15b from=translated src=- shape=aede0870 vocab=4dc8fdad
-/
theorem specNorm_pinvR_sq [DecidableEq n] (A : Matrix m n ℝ) (hA : IsUnit (A * Aᵀ)) :
    specNorm (pinvR A) ^ 2 = specNorm (A * Aᵀ)⁻¹ := by
  unfold specNorm pinvR
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
  have hsym : (A * Aᵀ)ᵀ = A * Aᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have key : (Aᵀ * (A * Aᵀ)⁻¹)ᴴ * (Aᵀ * (A * Aᵀ)⁻¹) = (A * Aᵀ)⁻¹ := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, hsym, Matrix.mul_assoc,
      ← Matrix.mul_assoc A, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA),
      Matrix.mul_one]
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self, key]

end InverseGram

end NLAlib
