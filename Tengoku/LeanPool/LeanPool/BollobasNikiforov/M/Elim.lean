/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Tengoku.LeanPool.LeanPool.BollobasNikiforov.CP.Basic
public import Tengoku.LeanPool.LeanPool.BollobasNikiforov.M.Config
public import Tengoku.LeanPool.LeanPool.BollobasNikiforov.TN.Truncated
public import Tengoku

/-!
# Ordered elimination residuals

The residual of symmetric Gaussian elimination of a principal index list is a
ratio of minors (EL01). Eliminating `idxZ0` leaves the `z`-block and its
`y`-coupling unchanged (EL02). That `z`-block is a Gram matrix plus a
positive diagonal, hence PD, so later pivots stay positive (EL03). The
numerator minor expands in the `I`-diagonal as a sum of complementary Gram
minors (EL04); those principal cofactors have sign `+1` (EL05). Factoring
`s i > 0` and `ρ > 0` leaves the unscaled kernel `(1 + t_a t_b)²` or a last
row `(t_b - x)₊²` (EL06). An algebraic identity rewrites `(1 + s t)²` as a
truncated square (EL07). Row arguments `-1/t_a` are increasing and lie
below any `x ≥ 0` (EL08–EL09). Those leftover minors are nonnegative by
TN13 (EL10), so residual columns stay nonnegative (EL11). Scaled outer
products of those columns yield a completely positive `C₀` (EL12). The
remainder is the `T`-Schur complement of `E` and is PSD (EL13–EL14).
-/

@[expose] public section

open Matrix Function

namespace BollobasNikiforov

variable {ι : Type*} {r : ℕ}

noncomputable section

/-- The residual entry after eliminating the principal block indexed by `e`. -/
def schurComplementEntry (A : Matrix ι ι ℝ) (e : Fin r → ι) (α j : ι) : ℝ :=
  A α j - (fun i ↦ A α (e i)) ⬝ᵥ ((A.submatrix e e)⁻¹ *ᵥ fun i ↦ A (e i) j)

/--
@isnad1 id=eq.0h6v.s7.54f03e74434b from=translated src=- shape=7562d8b8 vocab=0040849a
-/
lemma submatrix_elim_eq_fromBlocks (A : Matrix ι ι ℝ) (e : Fin r → ι) (α j : ι) :
    A.submatrix (Sum.elim e fun _ : Fin 1 ↦ α) (Sum.elim e fun _ : Fin 1 ↦ j) =
      fromBlocks (A.submatrix e e) (A.submatrix e fun _ : Fin 1 ↦ j)
        (A.submatrix (fun _ : Fin 1 ↦ α) e)
        (A.submatrix (fun _ : Fin 1 ↦ α) fun _ : Fin 1 ↦ j) := by
  ext i k
  cases i <;> cases k <;> rfl

/--
@isnad1 id=eq.0h4v.s8.ebab36a13aff from=translated src=- shape=71654734 vocab=46edeb73
-/
lemma snoc_eq_elim_comp_finSumFinEquiv_symm (e : Fin r → ι) (x : ι) :
    Fin.snoc e x =
      Sum.elim e (fun _ : Fin 1 ↦ x) ∘ (finSumFinEquiv (m := r) (n := 1)).symm := by
  ext i
  induction i using Fin.lastCases with
  | last =>
    have hlast : (finSumFinEquiv (m := r) (n := 1)).symm (Fin.last r) = Sum.inr 0 := by
      refine (finSumFinEquiv (m := r) (n := 1)).symm_apply_eq.2 ?_
      apply Fin.ext
      simp [finSumFinEquiv_apply_right]
    simp [Fin.snoc_last, hlast]
  | cast k =>
    simp [Fin.snoc_castSucc, finSumFinEquiv_symm_apply_castSucc]

/--
@isnad1 id=eq.0h6v.s8.2b7b99309fdc from=translated src=- shape=bd0df401 vocab=ef90eca4
-/
lemma det_submatrix_snoc_eq_det_elim (A : Matrix ι ι ℝ) (e : Fin r → ι) (α j : ι) :
    (A.submatrix (Fin.snoc e α) (Fin.snoc e j)).det =
      (A.submatrix (Sum.elim e fun _ : Fin 1 ↦ α)
        (Sum.elim e fun _ : Fin 1 ↦ j)).det := by
  have hα := snoc_eq_elim_comp_finSumFinEquiv_symm e α
  have hj := snoc_eq_elim_comp_finSumFinEquiv_symm e j
  rw [hα, hj, ← submatrix_submatrix, det_submatrix_equiv_self]

/--
@isnad1 id=eq.0h4v.s7.2c1892ce0f0e from=translated src=- shape=c6d432a7 vocab=de4287fd
-/
lemma mul_fin_one_apply (C : Matrix (Fin 1) (Fin r) ℝ) (M : Matrix (Fin r) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin 1) ℝ) :
    (C * M * B) 0 0 = (fun i ↦ C 0 i) ⬝ᵥ (M *ᵥ fun i ↦ B i 0) := by
  calc
    (C * M * B) 0 0 = ∑ i, (∑ k, C 0 k * M k i) * B i 0 := by
      simp [Matrix.mul_apply]
    _ = ∑ i, ∑ k, C 0 k * M k i * B i 0 := by
      simp [Finset.sum_mul]
    _ = ∑ k, ∑ i, C 0 k * (M k i * B i 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
      ring
    _ = (fun k ↦ C 0 k) ⬝ᵥ (M *ᵥ fun i ↦ B i 0) := by
      simp [dotProduct, mulVec, Finset.mul_sum]

/-- EL01: the residual after eliminating the principal block `A[I]` is a ratio of
minors. Injectivity of `e` and `α, j ∉ range e` record the elimination setup.
@isnad1 id=eq.4h6v.s7.4793c427abe6 from=translated src=- shape=e5acfe7b vocab=7acdf6c0
-/
lemma schurComplementEntry_eq_minor_div_det (A : Matrix ι ι ℝ) (e : Fin r → ι)
    (_he : e.Injective) {α j : ι} (_hα : α ∉ Set.range e) (_hj : j ∉ Set.range e)
    (hdet : (A.submatrix e e).det ≠ 0) :
    schurComplementEntry A e α j =
      (A.submatrix (Fin.snoc e α) (Fin.snoc e j)).det / (A.submatrix e e).det := by
  let AII := A.submatrix e e
  let B : Matrix (Fin r) (Fin 1) ℝ := A.submatrix e fun _ ↦ j
  let C : Matrix (Fin 1) (Fin r) ℝ := A.submatrix (fun _ ↦ α) e
  let D : Matrix (Fin 1) (Fin 1) ℝ := A.submatrix (fun _ ↦ α) fun _ ↦ j
  have hunit : IsUnit AII := (Matrix.isUnit_iff_isUnit_det AII).2 (Ne.isUnit hdet)
  let : Invertible AII := hunit.invertible
  have hblocks : A.submatrix (Sum.elim e fun _ : Fin 1 ↦ α) (Sum.elim e fun _ : Fin 1 ↦ j) =
      fromBlocks AII B C D := submatrix_elim_eq_fromBlocks A e α j
  have hdetb : (fromBlocks AII B C D).det = AII.det * (D - C * ⅟AII * B).det :=
    det_fromBlocks₁₁ AII B C D
  have hsnoc : (A.submatrix (Fin.snoc e α) (Fin.snoc e j)).det = (fromBlocks AII B C D).det := by
    rw [det_submatrix_snoc_eq_det_elim, hblocks]
  have hentry : (D - C * ⅟AII * B).det = schurComplementEntry A e α j := by
    rw [det_fin_one, Matrix.sub_apply, invOf_eq_nonsing_inv, mul_fin_one_apply]
    simp [schurComplementEntry, AII, B, C, D, submatrix_apply]
  rw [eq_div_iff hdet, hsnoc, hdetb, hentry, mul_comm]

/-- Empty elimination: the residual is the original entry and the denominator is `1`.
@isnad1 id=and.0h5v.s6.0ae7524080c5 from=translated src=- shape=87efee7e vocab=ba961352
-/
lemma schurComplementEntry_elim0 (A : Matrix ι ι ℝ) (e : Fin 0 → ι) (α j : ι) :
    schurComplementEntry A e α j = A α j ∧ (A.submatrix e e).det = 1 := by
  refine ⟨?_, det_fin_zero⟩
  · simp [schurComplementEntry]

/-- A vanishing eliminated row leaves the residual equal to the original entry.
@isnad1 id=eq.1h6v.s5.bf4c1b8defcc from=translated src=- shape=74997ff3 vocab=e12b3260
-/
lemma schurComplementEntry_eq_of_row (A : Matrix ι ι ℝ) (e : Fin r → ι) {α j : ι}
    (h : ∀ i, A α (e i) = 0) :
    schurComplementEntry A e α j = A α j := by
  simp [schurComplementEntry, h]

/-- A vanishing eliminated column leaves the residual equal to the original entry.
@isnad1 id=eq.1h6v.s5.b7bde2cbe28a from=translated src=- shape=1f042b3a vocab=e12b3260
-/
lemma schurComplementEntry_eq_of_col (A : Matrix ι ι ℝ) (e : Fin r → ι) {α j : ι}
    (h : ∀ i, A (e i) j = 0) :
    schurComplementEntry A e α j = A α j := by
  have hz : (fun i ↦ A (e i) j) = 0 := funext h
  unfold schurComplementEntry
  rw [hz]
  simp [mulVec, dotProduct]

/-- Singleton Schur residual, before simplifying the `1 × 1` inverse.
@isnad1 id=eq.0h5v.s7.9a038d7d1291 from=translated src=- shape=4a218482 vocab=9315f59e
-/
lemma schurComplementEntry_one (A : Matrix ι ι ℝ) (q α j : ι) :
    schurComplementEntry A (fun _ : Fin 1 ↦ q) α j =
      A α j -
        A α q * ((A.submatrix (fun _ : Fin 1 ↦ q) (fun _ : Fin 1 ↦ q))⁻¹ 0 0) *
          A q j := by
  simp only [schurComplementEntry, dotProduct, mulVec, Fin.sum_univ_one]
  ring

/-- The inverse entry of a nonzero `1 × 1` matrix is the reciprocal.
@isnad1 id=eq.1h1v.s7.44394aa36a30 from=translated src=- shape=463b0d16 vocab=f62e5ae3
-/
lemma inv_fin_one_apply (A : Matrix (Fin 1) (Fin 1) ℝ) (hA : A 0 0 ≠ 0) :
    A⁻¹ 0 0 = (A 0 0)⁻¹ := by
  have hdet : A.det ≠ 0 := by
    rwa [det_fin_one]
  have hmul := mul_nonsing_inv A (Ne.isUnit hdet)
  have hentry : (A * A⁻¹) 0 0 = 1 := by
    rw [hmul]
    rfl
  rw [Matrix.mul_apply, Fin.sum_univ_one] at hentry
  exact eq_inv_of_mul_eq_one_right hentry

/-- Singleton Schur residual as the rank-one update `A α j - A α q * A q j / A q q`.
@isnad1 id=eq.1h5v.s6.289c44caa0cc from=translated src=- shape=9cb03774 vocab=25e83b26
-/
lemma schurComplementEntry_one_div (A : Matrix ι ι ℝ) (q α j : ι) (hq : A q q ≠ 0) :
    schurComplementEntry A (fun _ : Fin 1 ↦ q) α j =
      A α j - A α q * A q j / A q q := by
  have hinv :
      (A.submatrix (fun _ : Fin 1 ↦ q) (fun _ : Fin 1 ↦ q))⁻¹ 0 0 = (A q q)⁻¹ := by
    have h0 : (A.submatrix (fun _ : Fin 1 ↦ q) (fun _ : Fin 1 ↦ q)) 0 0 ≠ 0 := by
      simpa [submatrix_apply] using hq
    rw [inv_fin_one_apply _ h0, submatrix_apply]
  rw [schurComplementEntry_one, hinv, div_eq_mul_inv]
  ring

variable {k p : ℕ}

/-- The opposite `z`-`z₀` block entry vanishes by symmetry of `Xconfig`.
@isnad1 id=eq.0h7v.s6.a7bac06c8e9c from=translated src=- shape=3d18e7ce vocab=0fb64db6
-/
lemma MX_z_z0 (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) :
    M (Xconfig s t ρ x) (idxZ i) idxZ0 = 0 := by
  rw [M_apply_of_ne _ (Xconfig_isSymm s t ρ x) (idxZ0_ne_idxZ (p := p) i).symm]
  rw [posPart_apply, (Xconfig_isSymm s t ρ x).apply, Xconfig_z0_z,
    max_eq_right (neg_nonpos.mpr (Real.sqrt_nonneg _)), zero_pow (by decide)]

/-- EL02: eliminating `idxZ0` does not change a `z`-`z` entry. The eliminated
column on `{idxZ i}` is zero (`MX_z0_z`).
@isnad1 id=eq.0h8v.s7.95e2a29e8a3b from=translated src=- shape=c3b2ae33 vocab=612595eb
-/
lemma schurComplementEntry_elimZ0_z_z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (i h : Fin k) :
    schurComplementEntry (M (Xconfig s t ρ x)) (fun _ : Fin 1 ↦ idxZ0)
      (idxZ i) (idxZ h) =
      M (Xconfig s t ρ x) (idxZ i) (idxZ h) :=
  schurComplementEntry_eq_of_col _ _ fun _ ↦ MX_z0_z s t ρ x h

/-- EL02: eliminating `idxZ0` does not change a `z`-`y` coupling. The
eliminated row on `{idxZ i}` is zero (`MX_z_z0`), even if `M idxZ0 (idxY j)`
is nonzero.
@isnad1 id=eq.0h8v.s7.41bbb60fb076 from=translated src=- shape=7115aad2 vocab=444a7182
-/
lemma schurComplementEntry_elimZ0_z_y (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (i : Fin k) (j : Fin p) :
    schurComplementEntry (M (Xconfig s t ρ x)) (fun _ : Fin 1 ↦ idxZ0)
      (idxZ i) (idxY j) =
      M (Xconfig s t ρ x) (idxZ i) (idxY j) :=
  schurComplementEntry_eq_of_row _ _ fun _ ↦ MX_z_z0 s t ρ x i

/-- EL02: the opposite `y`-`z` coupling is likewise unchanged (`MX_z0_z`).
@isnad1 id=eq.0h8v.s7.d4309f57db46 from=translated src=- shape=07e6c2b7 vocab=444a7182
-/
lemma schurComplementEntry_elimZ0_y_z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (j : Fin p) (i : Fin k) :
    schurComplementEntry (M (Xconfig s t ρ x)) (fun _ : Fin 1 ↦ idxZ0)
      (idxY j) (idxZ i) =
      M (Xconfig s t ρ x) (idxY j) (idxZ i) :=
  schurComplementEntry_eq_of_col _ _ fun _ ↦ MX_z0_z s t ρ x i

/-- Squared inner products of configuration `z`-vectors.
@isnad1 id=eq.1h5v.s7.8f0eac1ef126 from=translated src=- shape=aa44f4ae vocab=d7dc030a
-/
lemma zVec_dot_sq (s t : Fin k → ℝ) (hs : ∀ i, 0 < s i) (i h : Fin k) :
    (zVec s t i ⬝ᵥ zVec s t h) ^ 2 = s i * s h * (1 + t i * t h) ^ 2 := by
  rw [zVec_dot_zVec, mul_pow, mul_pow, Real.sq_sqrt (hs i).le, Real.sq_sqrt (hs h).le]

/-- Feature map `i ↦ zᵢ ⊗ zᵢ` on `Fin 2 × Fin 2`. -/
def zKron (s t : Fin k → ℝ) : Matrix (Fin k) (Fin 2 × Fin 2) ℝ :=
  fun i p ↦ zVec s t i p.1 * zVec s t i p.2

/-- The squared-Gram matrix of the `z`-vectors is `zKron * zKronᵀ`.
@isnad1 id=eq.0h3v.s8.8f09188ba54c from=translated src=- shape=24064b85 vocab=3a693ca7
-/
lemma zKron_mul_transpose (s t : Fin k → ℝ) :
    (of fun i h : Fin k ↦ (zVec s t i ⬝ᵥ zVec s t h) ^ 2) =
      zKron s t * (zKron s t)ᵀ := by
  ext i h
  calc
    (of fun i h ↦ (zVec s t i ⬝ᵥ zVec s t h) ^ 2) i h =
        (zVec s t i ⬝ᵥ zVec s t h) ^ 2 :=
      rfl
    _ = (∑ a, zVec s t i a * zVec s t h a) *
          (∑ b, zVec s t i b * zVec s t h b) := by
      simp [dotProduct, pow_two]
    _ = ∑ a, ∑ b,
          (zVec s t i a * zVec s t h a) * (zVec s t i b * zVec s t h b) := by
      rw [Finset.sum_mul_sum]
    _ = ∑ a, ∑ b,
          zVec s t i a * zVec s t i b * zVec s t h a * zVec s t h b := by
      refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
      ring
    _ = ∑ p : Fin 2 × Fin 2, zKron s t i p * zKron s t h p := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
      simp [zKron]
      ring
    _ = (zKron s t * (zKron s t)ᵀ) i h := by
      simp [mul_apply, transpose_apply]

/-- The squared-Gram `z`-block is positive semidefinite.
@isnad1 id=possemid.0h3v.s7.01159b6f2078 from=translated src=- shape=39228012 vocab=7cbb6dfd
-/
lemma zGram_posSemidef (s t : Fin k → ℝ) :
    (of fun i h : Fin k ↦ (zVec s t i ⬝ᵥ zVec s t h) ^ 2).PosSemidef := by
  rw [zKron_mul_transpose]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (zKron s t)

/-- EL03: the principal `z`-block is a Gram matrix plus `diagonal (s i * d i)`.
@isnad1 id=eq.3h6v.s8.1dfc170aa1ab from=translated src=- shape=e7b44693 vocab=a4bcb52a
-/
lemma MX_zBlock_eq (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) :
    (M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)) =
      (of fun i h ↦ (zVec s t i ⬝ᵥ zVec s t h) ^ 2) +
        diagonal fun i ↦ s i * configD t ρ x i := by
  ext i h
  rw [submatrix_apply, Matrix.add_apply, of_apply, diagonal_apply,
    MX_z_z s t ρ x hs ht hρ, zVec_dot_sq s t hs]

/-- EL03: the principal `z`-block is positive definite.
@isnad1 id=posdef.3h6v.s7.1af5ba3ec81f from=translated src=- shape=d4d54008 vocab=5daa3271
-/
lemma MX_zBlock_posDef (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) :
    ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))).PosDef := by
  rw [MX_zBlock_eq s t ρ x hs ht hρ]
  refine PosDef.posSemidef_add (zGram_posSemidef s t) ?_
  exact PosDef.diagonal fun i ↦ mul_pos (hs i) (configD_pos t hρ x i)

/-- A diagonal Schur residual of a PD matrix is a ratio of positive principal
minors, hence positive.
@isnad1 id=lt.3h5v.s5.b7bcafbe4873 from=translated src=- shape=46a84526 vocab=4fd383da
-/
lemma schurComplementEntry_diag_pos_of_posDef {n : Type*}
    {A : Matrix n n ℝ} (hA : A.PosDef) {m : ℕ} (e : Fin m → n) (he : e.Injective)
    {α : n} (hα : α ∉ Set.range e) :
    0 < schurComplementEntry A e α α := by
  have hI : (A.submatrix e e).PosDef := hA.submatrix he
  have hdetI : (A.submatrix e e).det ≠ 0 := (PosDef.det_pos hI).ne'
  have heα : (Fin.snoc e α).Injective := Fin.snoc_injective_of_injective he hα
  have hIa : (A.submatrix (Fin.snoc e α) (Fin.snoc e α)).PosDef := hA.submatrix heα
  rw [schurComplementEntry_eq_minor_div_det A e he hα hα hdetI]
  exact div_pos (PosDef.det_pos hIa) (PosDef.det_pos hI)

/-- EL03: every Schur pivot inside the `z`-block is positive.
@isnad1 id=lt.5h9v.s7.9ecf7f9a5f3a from=translated src=- shape=0e13e7bc vocab=63bd3c33
-/
lemma MX_zBlock_schur_pivot_pos (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (e : Fin m → Fin k) (he : e.Injective) {i : Fin k}
    (hi : i ∉ Set.range e) :
    0 < schurComplementEntry
      ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))) e i i :=
  schurComplementEntry_diag_pos_of_posDef (MX_zBlock_posDef s t ρ x hs ht hρ) e he hi

/-- EL03: leading principal submatrices of the `z`-block are PD.
@isnad1 id=posdef.4h7v.s7.7d94a29139d5 from=translated src=- shape=f530a3f3 vocab=62da7c50
-/
lemma MX_zBlock_leading_posDef (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (hm : m ≤ k) :
    (((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))).submatrix
      (Fin.castLE hm) (Fin.castLE hm)).PosDef :=
  (MX_zBlock_posDef s t ρ x hs ht hρ).submatrix (Fin.castLE_injective hm)

/-- EL03: leading principal minors of the `z`-block are positive.
@isnad1 id=lt.4h7v.s7.53dabeb277f2 from=translated src=- shape=1ba92d8b vocab=eb4f81fb
-/
lemma MX_zBlock_leading_det_pos (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (hm : m ≤ k) :
    0 < (((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))).submatrix
      (Fin.castLE hm) (Fin.castLE hm)).det :=
  PosDef.det_pos (MX_zBlock_leading_posDef s t ρ x hs ht hρ hm)

/-- EL03: after removing `idxZ0`, each remaining `z`-diagonal pivot is positive.
@isnad1 id=lt.3h7v.s7.98c93c2a6524 from=translated src=- shape=a72d1060 vocab=2022cfdd
-/
lemma schurComplementEntry_elimZ0_z_diag_pos (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) (i : Fin k) :
    0 < schurComplementEntry (M (Xconfig s t ρ x)) (fun _ : Fin 1 ↦ idxZ0)
      (idxZ i) (idxZ i) := by
  rw [schurComplementEntry_elimZ0_z_z]
  simpa [submatrix_apply] using
    PosDef.diag_pos (MX_zBlock_posDef s t ρ x hs ht hρ) (i := i)

/-! ### EL04 — diagonal expansion of a numerator minor -/

open Finset

/-- Unscaled `z`-`z` kernel `K_{ab} = (1 + t_a t_b)²`. -/
def elimKernelZZ (t : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b ↦ (1 + t a * t b) ^ 2

/-- Unscaled `z`-`y` kernel `K_{a,y} = (t_a - x)₊²`. -/
def elimKernelZY (t : Fin k → ℝ) (x : ℝ) : Fin k → ℝ :=
  fun a ↦ (max (t a - x) 0) ^ 2

/-- Non-dependent concatenation of a `z`-index list with a later index. -/
def elimSnoc {m : ℕ} (e : Fin m → Fin k) (z : Fin k) : Fin m.succ → Fin k :=
  fun a ↦ if h : a = Fin.last m then z else e (a.castPred h)

/--
@isnad1 id=eq.0h4v.s4.ed1b1e35b2d0 from=translated src=- shape=f0b5472e vocab=b21259bf
-/
lemma elimSnoc_last {m : ℕ} (e : Fin m → Fin k) (z : Fin k) :
    elimSnoc e z (Fin.last m) = z := by
  simp [elimSnoc]

/--
@isnad1 id=eq.0h5v.s4.8d0e2a26355c from=translated src=- shape=10ec71c5 vocab=4ea80ccc
-/
lemma elimSnoc_castSucc {m : ℕ} (e : Fin m → Fin k) (z : Fin k) (i : Fin m) :
    elimSnoc e z i.castSucc = e i := by
  simp [elimSnoc, Fin.castSucc_ne_last]

/-- `idxZ` is injective.
@isnad1 id=iff.0h4v.s4.17950863afcd from=translated src=- shape=12f2d131 vocab=a6e467e1
-/
lemma idxZ_inj {i h : Fin k} : idxZ (p := p) i = idxZ h ↔ i = h := by
  constructor
  · intro hih
    exact Fin.ext (by simpa [idxZ_val] using congrArg Fin.val hih)
  · rintro rfl; rfl

/-- Equal index Finsets give equal principal minors.
@isnad1 id=eq.1h4v.s8.77fe7c0d2247 from=translated src=- shape=e0c54463 vocab=a27ec48a
-/
lemma det_submatrix_finset_eq {n : Type*} [DecidableEq n]
    (A : Matrix n n ℝ) {s t : Finset n} (h : s = t) :
    (A.submatrix (Subtype.val : {x // x ∈ s} → n) Subtype.val).det =
      (A.submatrix (Subtype.val : {x // x ∈ t} → n) Subtype.val).det :=
  h ▸ rfl

/-- EL04: `det(A + diagonal d)` expands over kept index sets `S`.
The product runs over the complementary (deleted) diagonal entries, and the
leftover minor is the principal submatrix of `A` on `S`.
@isnad1 id=eq.0h3v.s7.d60938b96f0c from=translated src=- shape=80c30a08 vocab=c34f0f63
-/
lemma det_add_diagonal_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (d : n → ℝ) :
    (A + diagonal d).det =
      ∑ S : Finset n,
        (∏ i ∈ Sᶜ, d i) *
          (A.submatrix (Subtype.val : {x // x ∈ S} → n)
            (Subtype.val : {x // x ∈ S} → n)).det := by
  let D := detRowAlternating (R := ℝ) (n := n)
  have hdet : (A + diagonal d).det = D (fun i ↦ A i + (diagonal d) i) := rfl
  have hadd : (fun i ↦ A i + (diagonal d) i) =
      (fun i ↦ A i) + fun i ↦ (diagonal d) i := rfl
  rw [hdet, hadd, D.map_add_univ]
  refine Fintype.sum_congr _ _ fun S ↦ ?_
  have hscale :
      S.piecewise (A : n → n → ℝ) (diagonal d) =
        fun i ↦ (if i ∈ S then (1 : ℝ) else d i) •
          S.piecewise (A : n → n → ℝ) (1 : Matrix n n ℝ) i := by
    ext i j
    by_cases hi : i ∈ S
    · simp [Finset.piecewise, hi]
    · simp [Finset.piecewise, hi, diagonal, Matrix.one_apply, smul_eq_mul, mul_ite]
  rw [hscale, D.map_smul_univ, smul_eq_mul]
  have hc : (∏ i : n, if i ∈ S then (1 : ℝ) else d i) = ∏ i ∈ Sᶜ, d i := by
    rw [prod_ite, filter_univ_mem]
    have hSc : univ.filter (fun i : n ↦ i ∉ S) = Sᶜ := by
      ext i
      simp
    rw [hSc, prod_const_one, one_mul]
  rw [hc]
  congr 1
  have hpw :
      S.piecewise (A : n → n → ℝ) (1 : Matrix n n ℝ) =
        of (S.piecewise A.row (1 : Matrix n n ℝ).row) := by
    ext i j
    rfl
  rw [hpw]
  exact det_piecewise_one_eq_submatrix_det A S

/-- If `d` is supported on `I`, the expansion runs over deleted sets `S ⊆ I`.
@isnad1 id=eq.1h4v.s8.704eb1dba9ed from=translated src=- shape=c7ef3ce1 vocab=9ade70d2
-/
lemma det_add_diagonal_eq_sum_subset {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (d : n → ℝ) (I : Finset n)
    (hd : ∀ i, i ∉ I → d i = 0) :
    (A + diagonal d).det =
      ∑ S ∈ I.powerset,
        (∏ i ∈ S, d i) *
          (A.submatrix (Subtype.val : {x // x ∈ Sᶜ} → n)
            (Subtype.val : {x // x ∈ Sᶜ} → n)).det := by
  rw [det_add_diagonal_eq_sum]
  let e : Finset n ≃ Finset n :=
    { toFun := fun S ↦ (Sᶜ : Finset n)
      invFun := fun S ↦ Sᶜ
      left_inv := compl_compl
      right_inv := compl_compl }
  rw [Fintype.sum_equiv e
    (fun S ↦ (∏ i ∈ Sᶜ, d i) *
      (A.submatrix (Subtype.val : {x // x ∈ S} → n) Subtype.val).det)
    (fun S ↦ (∏ i ∈ S, d i) *
      (A.submatrix (Subtype.val : {x // x ∈ Sᶜ} → n) Subtype.val).det)
    (fun S ↦ by
      change (∏ i ∈ Sᶜ, d i) *
          (A.submatrix (Subtype.val : {x // x ∈ S} → n) Subtype.val).det =
        (∏ i ∈ Sᶜ, d i) *
          (A.submatrix (Subtype.val : {x // x ∈ (Sᶜ)ᶜ} → n) Subtype.val).det
      exact congrArg _ (det_submatrix_finset_eq A (compl_compl S).symm))]
  have hpow : I.powerset = univ.filter (fun S : Finset n ↦ S ⊆ I) := by
    ext S
    simp [mem_powerset]
  rw [hpow, sum_filter]
  refine Fintype.sum_congr _ _ fun S ↦ ?_
  by_cases hS : S ⊆ I
  · simp [hS]
  · have hz : ∏ i ∈ S, d i = 0 := by
      obtain ⟨i, hiS, hiI⟩ := not_subset.mp hS
      exact prod_eq_zero hiS (hd i hiI)
    simp [hS, hz]

/-- The leading block `I` inside `Fin (m + 1)`, excluding the last index. -/
def elimI (m : ℕ) : Finset (Fin m.succ) :=
  univ.map Fin.castSuccEmb

/--
@isnad1 id=iff.0h2v.s5.efdbed6df6b8 from=translated src=- shape=5f174cfb vocab=495b4ab4
-/
lemma mem_elimI_iff {m : ℕ} {a : Fin m.succ} : a ∈ elimI m ↔ a ≠ Fin.last m := by
  constructor
  · intro h
    rcases mem_map.mp h with ⟨i, _, hi⟩
    exact hi ▸ Fin.castSucc_ne_last i
  · intro ha
    refine mem_map.mpr ⟨a.castPred ha, mem_univ _, Fin.castSucc_castPred a ha⟩

/--
@isnad1 id=not.0h1v.s5.919b64634ad3 from=translated src=- shape=7adc91de vocab=0f0902a4
-/
lemma not_mem_elimI_last {m : ℕ} : Fin.last m ∉ elimI m := by
  simp [mem_elimI_iff]

/-- Diagonal weights `s i * d i` on `I`, and `0` on the last index. -/
def elimIDiag (s d : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k) : Fin m.succ → ℝ :=
  fun a ↦ if h : a = Fin.last m then 0 else s (e (a.castPred h)) * d (e (a.castPred h))

/--
@isnad1 id=eq.0h5v.s5.1ca60bdb2606 from=translated src=- shape=bd8aeec3 vocab=44df2d87
-/
lemma elimIDiag_last (s d : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k) :
    elimIDiag s d e (Fin.last m) = 0 := by
  simp [elimIDiag]

/--
@isnad1 id=eq.0h6v.s5.1a7cc4c8dab4 from=translated src=- shape=882d08fb vocab=59f4472a
-/
lemma elimIDiag_castSucc (s d : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k) (i : Fin m) :
    elimIDiag s d e i.castSucc = s (e i) * d (e i) := by
  simp [elimIDiag, Fin.castSucc_ne_last]

/--
@isnad1 id=eq.1h6v.s6.0e21531716df from=translated src=- shape=40c220d0 vocab=5d253193
-/
lemma elimIDiag_eq_zero_of_not_mem (s d : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k)
    {a : Fin m.succ} (ha : a ∉ elimI m) : elimIDiag s d e a = 0 := by
  have : a = Fin.last m := by
    simpa [mem_elimI_iff] using ha
  simp [this, elimIDiag_last]

/-- Pure Gram block on `elimSnoc e αidx` vs `elimSnoc e jidx` (no `I`-diagonal extras). -/
def elimGramZZ (s t : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k) (αidx jidx : Fin k) :
    Matrix (Fin m.succ) (Fin m.succ) ℝ :=
  of fun a b ↦
    s (elimSnoc e αidx a) * s (elimSnoc e jidx b) *
      (1 + t (elimSnoc e αidx a) * t (elimSnoc e jidx b)) ^ 2

/-- Last-entry correction when `α = j` (the pivot diagonal is not expanded). -/
def elimLastDiag (s : Fin k → ℝ) (d : Fin k → ℝ) {m : ℕ} (αidx jidx : Fin k) :
    Fin m.succ → ℝ :=
  fun a ↦ if a = Fin.last m ∧ αidx = jidx then s αidx * d αidx else 0

/--
@isnad1 id=iff.3h7v.s6.fa591a5809f3 from=translated src=- shape=c3a44441 vocab=3537c512
-/
lemma elimSnoc_eq_iff {m : ℕ} {e : Fin m → Fin k}
    (he : e.Injective) {zα zj : Fin k} (hzα : zα ∉ Set.range e) (hzj : zj ∉ Set.range e)
    {a b : Fin m.succ} :
    elimSnoc e zα a = elimSnoc e zj b ↔ a = b ∧ (a = Fin.last m → zα = zj) := by
  constructor
  · intro h
    by_cases ha : a = Fin.last m
    · by_cases hb : b = Fin.last m
      · subst ha; subst hb
        simp only [elimSnoc_last] at h
        exact ⟨rfl, fun _ ↦ h⟩
      · subst ha
        have hb' : elimSnoc e zj b = e (b.castPred hb) := by simp [elimSnoc, hb]
        rw [elimSnoc_last, hb'] at h
        exact (hzα ⟨b.castPred hb, h.symm⟩).elim
    · by_cases hb : b = Fin.last m
      · subst hb
        have ha' : elimSnoc e zα a = e (a.castPred ha) := by simp [elimSnoc, ha]
        rw [ha', elimSnoc_last] at h
        exact (hzj ⟨a.castPred ha, h⟩).elim
      · have ha' : elimSnoc e zα a = e (a.castPred ha) := by simp [elimSnoc, ha]
        have hb' : elimSnoc e zj b = e (b.castPred hb) := by simp [elimSnoc, hb]
        rw [ha', hb'] at h
        have hab' : a.castPred ha = b.castPred hb := he h
        have hab : a = b := by
          rw [← Fin.castSucc_castPred a ha, ← Fin.castSucc_castPred b hb, hab']
        exact ⟨hab, fun hlast ↦ (ha hlast).elim⟩
  · rintro ⟨hab, hz⟩
    subst hab
    by_cases ha : a = Fin.last m
    · subst ha
      simp [elimSnoc, hz rfl]
    · simp [elimSnoc, ha]

/-- The `z`-`z` numerator minor is the Gram block plus the `I`-diagonal
(and the unexpanded last diagonal if `α = j`).
@isnad1 id=eq.6h10v.s8.8f815d64bde7 from=translated src=- shape=4037b388 vocab=69bd4062
-/
lemma MX_snoc_z_eq_gram_add_diag (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (e : Fin m → Fin k) (he : e.Injective) {αidx jidx : Fin k}
    (hα : αidx ∉ Set.range e) (hj : jidx ∉ Set.range e) :
    (M (Xconfig s t ρ x)).submatrix
        (idxZ (p := p) ∘ elimSnoc e αidx) (idxZ (p := p) ∘ elimSnoc e jidx) =
      elimGramZZ s t e αidx jidx +
        diagonal (elimIDiag s (configD t ρ x) e) +
          diagonal (elimLastDiag s (configD t ρ x) αidx jidx) := by
  ext a b
  simp only [submatrix_apply, Function.comp_apply, Matrix.add_apply, of_apply,
    diagonal_apply, elimGramZZ]
  rw [MX_z_z s t ρ x hs ht hρ]
  rcases eq_or_ne a b with rfl | hab
  · by_cases ha : a = Fin.last m
    · subst ha
      simp [elimSnoc_last, elimIDiag_last, elimLastDiag]
    · simp [elimSnoc, ha, elimIDiag, elimLastDiag]
  · have hne : elimSnoc e αidx a ≠ elimSnoc e jidx b := fun h ↦
      hab ((elimSnoc_eq_iff he hα hj).mp h).1
    simp [hab, hne]

/-- EL04: expand a `z`-`z` numerator in the diagonal summands on `I`.
@isnad1 id=eq.6h10v.s9.c9479833d4a7 from=translated src=- shape=be9507e8 vocab=b964a569
-/
lemma det_MX_snoc_z_eq_sum (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (e : Fin m → Fin k) (he : e.Injective) {αidx jidx : Fin k}
    (hα : αidx ∉ Set.range e) (hj : jidx ∉ Set.range e) :
    ((M (Xconfig s t ρ x)).submatrix
        (idxZ (p := p) ∘ elimSnoc e αidx) (idxZ (p := p) ∘ elimSnoc e jidx)).det =
      ∑ S ∈ (elimI m).powerset,
        (∏ i ∈ S, elimIDiag s (configD t ρ x) e i) *
          ((elimGramZZ s t e αidx jidx +
              diagonal (elimLastDiag s (configD t ρ x) αidx jidx)).submatrix
            (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ)
            (Subtype.val)).det := by
  rw [MX_snoc_z_eq_gram_add_diag s t ρ x hs ht hρ e he hα hj]
  have hrearr :
      elimGramZZ s t e αidx jidx +
          diagonal (elimIDiag s (configD t ρ x) e) +
            diagonal (elimLastDiag s (configD t ρ x) αidx jidx) =
        elimGramZZ s t e αidx jidx +
            diagonal (elimLastDiag s (configD t ρ x) αidx jidx) +
          diagonal (elimIDiag s (configD t ρ x) e) := by
    abel
  rw [hrearr, det_add_diagonal_eq_sum_subset _ _ (elimI m)]
  intro a ha
  exact elimIDiag_eq_zero_of_not_mem s (configD t ρ x) e ha

/-- Gram/coupling block for a last `y`-row against columns `snoc e j`. -/
def elimGramZY (s t : Fin k → ℝ) (ρval xval : ℝ) {m : ℕ} (e : Fin m → Fin k)
    (jidx : Fin k) : Matrix (Fin m.succ) (Fin m.succ) ℝ :=
  of fun a b ↦
    if a = Fin.last m then
      s (elimSnoc e jidx b) * ρval * (max (t (elimSnoc e jidx b) - xval) 0) ^ 2
    else
      s (elimSnoc e jidx a) * s (elimSnoc e jidx b) *
        (1 + t (elimSnoc e jidx a) * t (elimSnoc e jidx b)) ^ 2

/-- The opposite `y`-`z` block equals the `z`-`y` formula.
@isnad1 id=eq.2h8v.s7.78db834e1045 from=translated src=- shape=1beaa76f vocab=cb19bbb1
-/
lemma MX_y_z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j) (i : Fin k) (j : Fin p) :
    M (Xconfig s t ρ x) (idxY j) (idxZ i) =
      s i * ρ j * (max (t i - x j) 0) ^ 2 := by
  have hX := Xconfig_isSymm s t ρ x
  have hne : (idxY j : ConfigIdx k p) ≠ idxZ i := (idxZ_ne_idxY (p := p) i j).symm
  rw [← MX_z_y s t ρ x hs hρ i j]
  rw [M_apply_of_ne _ hX hne, M_apply_of_ne _ hX hne.symm, posPart_apply, posPart_apply, hX.apply]

/-- Row map for a last `y`-index after the `I`-block. -/
def elimRowY {m : ℕ} (e : Fin m → Fin k) (ℓ : Fin p) : Fin m.succ → ConfigIdx k p :=
  fun a ↦ if h : a = Fin.last m then idxY ℓ else idxZ (p := p) (e (a.castPred h))

/--
@isnad1 id=eq.0h5v.s4.c0d83a46be8f from=translated src=- shape=8765c849 vocab=e2d662bf
-/
lemma elimRowY_last {m : ℕ} (e : Fin m → Fin k) (ℓ : Fin p) :
    elimRowY e ℓ (Fin.last m) = idxY ℓ := by
  simp [elimRowY]

/--
@isnad1 id=eq.0h6v.s5.e73ab81f7a39 from=translated src=- shape=2a597802 vocab=121155a9
-/
lemma elimRowY_castSucc {m : ℕ} (e : Fin m → Fin k) (ℓ : Fin p) (i : Fin m) :
    elimRowY e ℓ i.castSucc = idxZ (p := p) (e i) := by
  simp [elimRowY, Fin.castSucc_ne_last]

/-- The `y`-row numerator minor is the Gram/coupling block plus the `I`-diagonal.
@isnad1 id=eq.5h10v.s8.89b55740f90e from=translated src=- shape=4a864e3a vocab=e9ae323c
-/
lemma MX_snoc_y_eq_gram_add_diag (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (e : Fin m → Fin k) (he : e.Injective) {jidx : Fin k} {ℓ : Fin p}
    (hj : jidx ∉ Set.range e) :
    (M (Xconfig s t ρ x)).submatrix (elimRowY e ℓ) (idxZ (p := p) ∘ elimSnoc e jidx) =
      elimGramZY s t (ρ ℓ) (x ℓ) e jidx +
        diagonal (elimIDiag s (configD t ρ x) e) := by
  ext a b
  simp only [submatrix_apply, Function.comp_apply, Matrix.add_apply, diagonal_apply,
    elimGramZY, of_apply]
  by_cases ha : a = Fin.last m
  · subst ha
    simp only [elimRowY_last, elimIDiag_last]
    rw [MX_y_z s t ρ x hs hρ]
    simp
  · have hae : elimRowY e ℓ a = idxZ (p := p) (e (a.castPred ha)) := by
      simp [elimRowY, ha]
    have hrow : elimSnoc e jidx a = e (a.castPred ha) := by
      simp [elimSnoc, ha]
    rw [hae, MX_z_z s t ρ x hs ht hρ]
    have hab_iff : e (a.castPred ha) = elimSnoc e jidx b ↔ a = b := by
      by_cases hb : b = Fin.last m
      · subst hb
        simp only [elimSnoc_last, Nat.succ_eq_add_one]
        constructor
        · intro h
          exact (hj ⟨a.castPred ha, h⟩).elim
        · intro h
          exact (ha h).elim
      · have hbe : elimSnoc e jidx b = e (b.castPred hb) := by simp [elimSnoc, hb]
        rw [hbe]
        constructor
        · intro h
          have : a.castPred ha = b.castPred hb := he h
          rw [← Fin.castSucc_castPred a ha, ← Fin.castSucc_castPred b hb, this]
        · intro hab
          subst hab
          rfl
    simp [ha, hrow, hab_iff, elimIDiag]

/-- EL04: expand a `y`-row numerator in the diagonal summands on `I`.
@isnad1 id=eq.5h10v.s9.fad635ca414a from=translated src=- shape=cba69348 vocab=300a086f
-/
lemma det_MX_snoc_y_eq_sum (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (e : Fin m → Fin k) (he : e.Injective) {jidx : Fin k} {ℓ : Fin p}
    (hj : jidx ∉ Set.range e) :
    ((M (Xconfig s t ρ x)).submatrix
        (elimRowY e ℓ) (idxZ (p := p) ∘ elimSnoc e jidx)).det =
      ∑ S ∈ (elimI m).powerset,
        (∏ i ∈ S, elimIDiag s (configD t ρ x) e i) *
          ((elimGramZY s t (ρ ℓ) (x ℓ) e jidx).submatrix
            (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ)
            (Subtype.val)).det := by
  rw [MX_snoc_y_eq_gram_add_diag s t ρ x hs ht hρ e he hj,
    det_add_diagonal_eq_sum_subset _ _ (elimI m)]
  intro a ha
  exact elimIDiag_eq_zero_of_not_mem s (configD t ρ x) e ha

/-! ### EL05 — principal cofactor signs are `+1` -/

/-- EL05: a principal cofactor sign is `(-1)^{p+p} = 1`.
@isnad1 id=eq.0h1v.s5.2377c46daba1 from=translated src=- shape=16b58f28 vocab=327e0726
-/
lemma principal_cofactor_sign (q : ℕ) : (-1 : ℝ) ^ (q + q) = 1 := by
  rw [← two_mul, pow_mul, neg_one_pow_two, one_pow]

/-- EL05: deleting the same row and column subset contributes sign `+1`.
The leftover is the complementary principal minor, with no extra sign.
@isnad1 id=eq.0h3v.s8.dfe3a5198b4e from=translated src=- shape=bb439e93 vocab=8959752f
-/
lemma det_piecewise_one_eq_compl_minor {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (S : Finset n) :
    (of (Sᶜ.piecewise A.row (1 : Matrix n n ℝ).row)).det =
      (A.submatrix (Subtype.val : {x // x ∈ Sᶜ} → n) Subtype.val).det :=
  det_piecewise_one_eq_submatrix_det A Sᶜ

/-! ### EL06 — factor positive `s` and `ρ` -/

/-- Homogeneity: row scales `u` and column scales `v` factor out of `det`.
@isnad1 id=eq.0h4v.s7.b44556ea07a0 from=translated src=- shape=c6428628 vocab=6e704c75
-/
lemma det_smul_row_col {n : Type*} [Fintype n] [DecidableEq n]
    (u v : n → ℝ) (A : Matrix n n ℝ) :
    (of fun i j ↦ u i * v j * A i j).det =
      (∏ i, u i) * (∏ j, v j) * A.det := by
  have hfun :
      (of fun i j ↦ u i * v j * A i j) =
        of fun i j ↦ u i * (v j * A i j) := by
    ext i j
    exact mul_assoc _ _ _
  have hcol : (of fun i j ↦ v j * A i j).det = (∏ j, v j) * A.det :=
    det_mul_row v A
  have hrow :
      (of fun i j ↦ u i * (v j * A i j)).det =
        (∏ i, u i) * (of fun i j ↦ v j * A i j).det :=
    det_mul_column u (of fun i j ↦ v j * A i j)
  rw [hfun, hrow, hcol]
  ring

/-- EL06: a `z`-`z` Gram block factors as `s`-row and `s`-column times the
unscaled kernel minor.
@isnad1 id=eq.0h7v.s7.71f99ce35c54 from=translated src=- shape=309f5d1d vocab=5cbe00c2
-/
lemma det_elimGramZZ_factor (s t : Fin k → ℝ) {m : ℕ} (e : Fin m → Fin k)
    (αidx jidx : Fin k) :
    (elimGramZZ s t e αidx jidx).det =
      (∏ a, s (elimSnoc e αidx a)) * (∏ b, s (elimSnoc e jidx b)) *
        ((elimKernelZZ t).submatrix (elimSnoc e αidx) (elimSnoc e jidx)).det := by
  simpa [elimGramZZ, elimKernelZZ, submatrix_apply] using
    det_smul_row_col (s ∘ elimSnoc e αidx) (s ∘ elimSnoc e jidx)
      ((elimKernelZZ t).submatrix (elimSnoc e αidx) (elimSnoc e jidx))

/-- EL06: the same factoring on a complementary leftover of the `z`-`z` Gram.
@isnad1 id=eq.0h8v.s10.cb7351520db6 from=translated src=- shape=374049bf vocab=1da64cab
-/
lemma det_elimGramZZ_submatrix_factor (s t : Fin k → ℝ) {m : ℕ}
    (e : Fin m → Fin k) (αidx jidx : Fin k) (S : Finset (Fin m.succ)) :
    ((elimGramZZ s t e αidx jidx).submatrix
        (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val).det =
      (∏ i : {x // x ∈ Sᶜ}, s (elimSnoc e αidx i.val)) *
        (∏ i : {x // x ∈ Sᶜ}, s (elimSnoc e jidx i.val)) *
          ((elimKernelZZ t).submatrix
            (elimSnoc e αidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ))
            (elimSnoc e jidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ))).det := by
  let u : {x // x ∈ Sᶜ} → ℝ := fun i ↦ s (elimSnoc e αidx i.val)
  let v : {x // x ∈ Sᶜ} → ℝ := fun i ↦ s (elimSnoc e jidx i.val)
  let K : Matrix {x // x ∈ Sᶜ} {x // x ∈ Sᶜ} ℝ :=
    (elimKernelZZ t).submatrix
      (elimSnoc e αidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ))
      (elimSnoc e jidx ∘ (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ))
  have hfun :
      (elimGramZZ s t e αidx jidx).submatrix
          (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val =
        of fun i j ↦ u i * v j * K i j := by
    ext i j
    simp [elimGramZZ, elimKernelZZ, submatrix_apply, u, v, K]
  rw [hfun]
  exact det_smul_row_col (n := {x // x ∈ Sᶜ}) u v K

/-- Unscaled leftover kernel with a last truncated-square row. -/
def elimKernelMinorZY (t : Fin k → ℝ) (xval : ℝ) {m : ℕ}
    (e : Fin m → Fin k) (jidx : Fin k) : Matrix (Fin m.succ) (Fin m.succ) ℝ :=
  of fun a b ↦
    if a = Fin.last m then
      elimKernelZY t xval (elimSnoc e jidx b)
    else
      elimKernelZZ t (elimSnoc e jidx a) (elimSnoc e jidx b)

/-- EL06: a `y`-row Gram/coupling block factors `ρ` from the last row and
`s` from every `z`-row/column.
@isnad1 id=eq.0h8v.s7.98d2e2fa6633 from=translated src=- shape=1b8f1175 vocab=42af85d0
-/
lemma det_elimGramZY_factor (s t : Fin k → ℝ) (ρval xval : ℝ) {m : ℕ}
    (e : Fin m → Fin k) (jidx : Fin k) :
    (elimGramZY s t ρval xval e jidx).det =
      (∏ a, if a = Fin.last m then ρval else s (elimSnoc e jidx a)) *
        (∏ b, s (elimSnoc e jidx b)) *
          (elimKernelMinorZY t xval e jidx).det := by
  have hfun :
      elimGramZY s t ρval xval e jidx =
        of fun a b ↦
          (if a = Fin.last m then ρval else s (elimSnoc e jidx a)) *
            s (elimSnoc e jidx b) *
              elimKernelMinorZY t xval e jidx a b := by
    ext a b
    simp only [elimGramZY, elimKernelMinorZY, elimKernelZZ, elimKernelZY, of_apply]
    split_ifs <;> ring
  rw [hfun]
  exact det_smul_row_col
    (fun a ↦ if a = Fin.last m then ρval else s (elimSnoc e jidx a))
    (fun b ↦ s (elimSnoc e jidx b))
    (elimKernelMinorZY t xval e jidx)

/-- EL07: `(1 + s t)² = s² (t - (-1/s))₊²` for `s, t > 0`.
@isnad1 id=eq.2h2v.s7.5ed8bd7b3595 from=translated src=- shape=7deb4d9d vocab=ee958e6c
-/
lemma one_add_mul_sq_eq_sq_mul_max_sub {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (1 + s * t) ^ 2 = s ^ 2 * (max (t - (-1 / s)) 0) ^ 2 := by
  have hpos : 0 < t + s⁻¹ := add_pos ht (inv_pos.mpr hs)
  have hmax : max (t - (-1 / s)) 0 = t + s⁻¹ := by
    have : t - (-1 / s) = t + s⁻¹ := by
      rw [neg_div, sub_neg_eq_add, one_div]
    rw [this, max_eq_left hpos.le]
  rw [hmax]
  have hfac : s * (t + s⁻¹) = 1 + s * t := by
    rw [mul_add, mul_inv_cancel₀ hs.ne', add_comm]
  rw [← hfac, mul_pow]

/-- Reciprocal is antitone on `(0, ∞)`, so `-1/t` is increasing in `t > 0`.
@isnad1 id=le.3h2v.s6.a4f703f01592 from=translated src=- shape=b62c97ee vocab=0580ac1c
-/
lemma neg_one_div_le_neg_one_div {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (h : s ≤ t) :
    -1 / s ≤ -1 / t := by
  rw [neg_div, neg_div, neg_le_neg_iff, one_div, one_div]
  exact (inv_le_inv₀ ht hs).mpr h

/--
@isnad1 id=lt.1h1v.s5.4bbdfb727ffc from=translated src=- shape=2b158482 vocab=fbdab067
-/
lemma neg_one_div_lt_zero {t : ℝ} (ht : 0 < t) : -1 / t < 0 :=
  div_neg_of_neg_of_pos neg_one_lt_zero ht

/-- EL08: if `t` is positive and monotone, then `i ↦ -1 / t i` is monotone and negative.
@isnad1 id=monotone.2h2v.s6.f527d12649d7 from=translated src=- shape=0c01c968 vocab=c9854e30
-/
lemma monotone_neg_one_div {k : ℕ} {t : Fin k → ℝ} (ht : ∀ i, 0 < t i) (hmono : Monotone t) :
    Monotone (fun i ↦ -1 / t i) :=
  fun _ _ hij ↦ neg_one_div_le_neg_one_div (ht _) (ht _) (hmono hij)

/--
@isnad1 id=lt.1h3v.s5.946126f06563 from=translated src=- shape=87505cf2 vocab=df69fe05
-/
lemma neg_one_div_apply_lt_zero {k : ℕ} {t : Fin k → ℝ} (ht : ∀ i, 0 < t i) (i : Fin k) :
    -1 / t i < 0 :=
  neg_one_div_lt_zero (ht i)

/-- EL09: a later positive `t α ≥ t j` keeps `-1/t` nondecreasing.
@isnad1 id=le.3h2v.s6.c84fa762d20b from=translated src=- shape=360283d1 vocab=0580ac1c
-/
lemma neg_one_div_le_neg_one_div_of_ge {tα tj : ℝ} (hα : 0 < tα) (hj : 0 < tj) (h : tj ≤ tα) :
    -1 / tj ≤ -1 / tα :=
  neg_one_div_le_neg_one_div hj hα h

/-- EL09: a last argument `x ≥ 0` follows every `-1 / t a`.
@isnad1 id=le.2h2v.s5.5c95a8e973c2 from=translated src=- shape=ce9d0933 vocab=0580ac1c
-/
lemma neg_one_div_le_of_nonneg {ta x : ℝ} (hta : 0 < ta) (hx : 0 ≤ x) :
    -1 / ta ≤ x :=
  (neg_one_div_lt_zero hta).le.trans hx

/-! ### EL10 — leftover kernel minors are nonnegative -/

/--
@isnad1 id=eq.0h4v.s5.660745b7b2ba from=translated src=- shape=495936f9 vocab=57f73cce
-/
lemma elimSnoc_eq_finSnoc {m : ℕ} (e : Fin m → Fin k) (z : Fin k) :
    elimSnoc e z = Fin.snoc e z := by
  ext a
  by_cases ha : a = Fin.last m
  · subst ha
    simp [elimSnoc, Fin.snoc]
  · have hlt : a.val < m :=
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ a.isLt) fun h ↦ ha (Fin.ext h)
    simp [elimSnoc, Fin.snoc, ha, hlt]

/--
@isnad1 id=eq.1h4v.s6.2e32cf3d4369 from=translated src=- shape=189b1830 vocab=2f723f49
-/
lemma elimKernelZZ_eq_truncated (t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (a b : Fin k) :
    elimKernelZZ t a b =
      t a ^ 2 * truncatedSquare (fun i ↦ -1 / t i) t a b := by
  simpa [elimKernelZZ, truncatedSquare] using
    one_add_mul_sq_eq_sq_mul_max_sub (ht a) (ht b)

/--
@isnad1 id=monotone.2h4v.s6.c2bec9f75bd4 from=translated src=- shape=59fd384b vocab=5de644fd
-/
lemma elimSnoc_monotone {m : ℕ} {e : Fin m → Fin k} (he : Monotone e)
    {z : Fin k} (hz : ∀ i, e i ≤ z) : Monotone (elimSnoc e z) := by
  intro a b hab
  by_cases hb : b = Fin.last m
  · subst hb
    by_cases ha : a = Fin.last m
    · subst ha
      simp [elimSnoc]
    · simp only [elimSnoc, Nat.succ_eq_add_one, ha, ↓reduceDIte]
      exact hz _
  · have ha : a ≠ Fin.last m := by
      intro ha
      exact hb (le_antisymm (Fin.le_last b) (ha ▸ hab))
    simp only [elimSnoc, Nat.succ_eq_add_one, ha, ↓reduceDIte, hb, ge_iff_le]
    refine he ?_
    rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred, Fin.castSucc_castPred]
    exact hab

/--
@isnad1 id=strictmo.2h4v.s6.cb016d591324 from=translated src=- shape=59fd384b vocab=c66f2cb4
-/
lemma elimSnoc_strictMono {m : ℕ} {e : Fin m → Fin k} (he : StrictMono e)
    {z : Fin k} (hz : ∀ i, e i < z) : StrictMono (elimSnoc e z) := by
  intro a b hab
  by_cases hb : b = Fin.last m
  · subst hb
    have ha : a ≠ Fin.last m := ne_of_lt hab
    simp only [elimSnoc, Nat.succ_eq_add_one, ha, ↓reduceDIte, gt_iff_lt]
    exact hz _
  · have ha : a ≠ Fin.last m := fun h ↦
      hb (le_antisymm (Fin.le_last b) (h ▸ hab.le))
    simp only [elimSnoc, Nat.succ_eq_add_one, ha, ↓reduceDIte, hb, gt_iff_lt]
    refine he ?_
    rw [← Fin.castSucc_lt_castSucc_iff, Fin.castSucc_castPred, Fin.castSucc_castPred]
    exact hab

/--
@isnad1 id=lt.2h4v.s5.9cbf5b4a77f5 from=translated src=- shape=831a58d3 vocab=df2f06dc
-/
lemma castLE_lt {m : ℕ} (hm : m ≤ k) {z : Fin k} (hz : m ≤ z.val) (i : Fin m) :
    Fin.castLE hm i < z := by
  exact Nat.lt_of_lt_of_le i.isLt hz

/--
@isnad1 id=eq.0h3v.s8.e5dbfdac0bcf from=translated src=- shape=05483134 vocab=905a9e17
-/
lemma det_submatrix_subtype_eq_orderEmb {n : Type*}
    [LinearOrder n] [DecidableEq n]
    (A : Matrix n n ℝ) (S : Finset n) :
    (A.submatrix (Subtype.val : {x // x ∈ S} → n) Subtype.val).det =
      (A.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)).det := by
  rw [← det_submatrix_equiv_self (S.orderIsoOfFin rfl).toEquiv]
  rfl

/-- Row argument of the elimination step: the vector on `Fin m.succ` whose last entry is `xval` and
whose other entries are `-1 / t` along the indices selected by `elimSnoc e jidx`. -/
def elimRowArg (t : Fin k → ℝ) (xval : ℝ) {m : ℕ}
    (e : Fin m → Fin k) (jidx : Fin k) : Fin m.succ → ℝ :=
  fun a ↦ if a = Fin.last m then xval else -1 / t (elimSnoc e jidx a)

/-- Column argument of the elimination step: `t` evaluated along `elimSnoc e jidx`. -/
def elimColArg (t : Fin k → ℝ) {m : ℕ}
    (e : Fin m → Fin k) (jidx : Fin k) : Fin m.succ → ℝ :=
  fun b ↦ t (elimSnoc e jidx b)

/--
@isnad1 id=monotone.5h6v.s6.33452ab5ccda from=translated src=- shape=b48b2d2d vocab=206c31ab
-/
lemma elimRowArg_monotone (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    (xval : ℝ) (hx : 0 ≤ xval) {m : ℕ} {e : Fin m → Fin k} (he : Monotone e)
    {jidx : Fin k} (hj : ∀ i, e i ≤ jidx) :
    Monotone (elimRowArg t xval e jidx) := by
  intro a b hab
  by_cases hb : b = Fin.last m
  · subst hb
    by_cases ha : a = Fin.last m
    · subst ha
      simp [elimRowArg]
    · simp only [elimRowArg, Nat.succ_eq_add_one, ha, ↓reduceIte]
      exact neg_one_div_le_of_nonneg (ht _) hx
  · have ha : a ≠ Fin.last m := fun h ↦
      hb (le_antisymm (Fin.le_last b) (h ▸ hab))
    simp only [elimRowArg, Nat.succ_eq_add_one, ha, ↓reduceIte, hb, ge_iff_le]
    exact neg_one_div_le_neg_one_div (ht _) (ht _)
      (hmono (elimSnoc_monotone he hj hab))

/--
@isnad1 id=monotone.3h5v.s6.bac4a5d60c94 from=translated src=- shape=7288dfa0 vocab=3f424184
-/
lemma elimColArg_monotone (t : Fin k → ℝ) (hmono : Monotone t)
    {m : ℕ} {e : Fin m → Fin k} (he : Monotone e)
    {jidx : Fin k} (hj : ∀ i, e i ≤ jidx) :
    Monotone (elimColArg t e jidx) :=
  hmono.comp (elimSnoc_monotone he hj)

/--
@isnad1 id=eq.1h8v.s7.b268d76235f5 from=translated src=- shape=29c93ae6 vocab=a23074e3
-/
lemma elimKernelMinorZY_eq_scaled (t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (xval : ℝ) {m : ℕ} (e : Fin m → Fin k) (jidx : Fin k) (a b : Fin m.succ) :
    elimKernelMinorZY t xval e jidx a b =
      (if a = Fin.last m then (1 : ℝ) else t (elimSnoc e jidx a) ^ 2) *
        truncatedSquare (elimRowArg t xval e jidx) (elimColArg t e jidx) a b := by
  by_cases ha : a = Fin.last m
  · subst ha
    simp [elimKernelMinorZY, elimKernelZY, elimRowArg, elimColArg, truncatedSquare]
  · simp only [elimKernelMinorZY, elimKernelZZ, elimRowArg, elimColArg, truncatedSquare,
      ha, ↓reduceIte, of_apply]
    simpa using one_add_mul_sq_eq_sq_mul_max_sub (ht _) (ht _)

/--
@isnad1 id=eq.0h9v.s10.afbea53ca026 from=translated src=- shape=6853fdb9 vocab=da41d208
-/
lemma det_elimGramZY_submatrix_factor (s t : Fin k → ℝ) (ρval xval : ℝ)
    {m : ℕ} (e : Fin m → Fin k) (jidx : Fin k) (S : Finset (Fin m.succ)) :
    ((elimGramZY s t ρval xval e jidx).submatrix
        (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val).det =
      (∏ i : {x // x ∈ Sᶜ},
          if i.val = Fin.last m then ρval else s (elimSnoc e jidx i.val)) *
        (∏ i : {x // x ∈ Sᶜ}, s (elimSnoc e jidx i.val)) *
          ((elimKernelMinorZY t xval e jidx).submatrix
            (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val).det := by
  let u : {x // x ∈ Sᶜ} → ℝ :=
    fun i ↦ if i.val = Fin.last m then ρval else s (elimSnoc e jidx i.val)
  let v : {x // x ∈ Sᶜ} → ℝ := fun i ↦ s (elimSnoc e jidx i.val)
  let K : Matrix {x // x ∈ Sᶜ} {x // x ∈ Sᶜ} ℝ :=
    (elimKernelMinorZY t xval e jidx).submatrix Subtype.val Subtype.val
  have hfun :
      (elimGramZY s t ρval xval e jidx).submatrix
          (Subtype.val : {x // x ∈ Sᶜ} → Fin m.succ) Subtype.val =
        of fun i j ↦ u i * v j * K i j := by
    ext i j
    simp only [submatrix_apply, elimGramZY, elimKernelMinorZY, elimKernelZZ, elimKernelZY,
      of_apply, u, v, K]
    split_ifs <;> ring
  rw [hfun]
  exact det_smul_row_col (n := {x // x ∈ Sᶜ}) u v K

/-! ### EL11 — residual columns are nonnegative -/

/--
@isnad1 id=le.2h6v.s6.57c9f9b2f009 from=translated src=- shape=083038c9 vocab=d80d2dbf
-/
lemma elimIDiag_nonneg (s : Fin k → ℝ) (d : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hd : ∀ i, 0 ≤ d i) {m : ℕ} (e : Fin m → Fin k)
    (a : Fin m.succ) : 0 ≤ elimIDiag s d e a := by
  by_cases ha : a = Fin.last m
  · subst ha
    simp [elimIDiag]
  · simp only [elimIDiag, Nat.succ_eq_add_one, ha, ↓reduceDIte]
    exact mul_nonneg (hs _).le (hd _)

/--
@isnad1 id=eq.0h5v.s6.153f78e90387 from=translated src=- shape=199907fb vocab=63e5c620
-/
lemma elimRowY_eq_snoc {m : ℕ} (e : Fin m → Fin k) (ℓ : Fin p) :
    elimRowY e ℓ = Fin.snoc (idxZ (p := p) ∘ e) (idxY ℓ) := by
  ext a
  by_cases ha : a = Fin.last m
  · subst ha
    simp [elimRowY, Fin.snoc]
  · have hlt : a.val < m :=
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ a.isLt) fun h ↦ ha (Fin.ext h)
    simp [elimRowY, Fin.snoc, ha, hlt]

/--
@isnad1 id=eq.0h5v.s6.b7b5255b6a19 from=translated src=- shape=6557b69f vocab=9c701091
-/
lemma idxZ_comp_snoc {m : ℕ} (e : Fin m → Fin k) (z : Fin k) :
    idxZ (p := p) ∘ Fin.snoc e z = idxZ (p := p) ∘ elimSnoc e z := by
  simp [elimSnoc_eq_finSnoc]

/-! ### Index sets `E` and `T` for elimination -/

/-- Case split on a configuration index.
@isnad1 id=var.0h7v.s5.c03d8d34ebb6 from=translated src=- shape=0ee21076 vocab=936eea2a
-/
lemma elim_configIdx_cases {P : ConfigIdx k p → Prop} (α : ConfigIdx k p)
    (h0 : P idxZ0) (hz : ∀ i, P (idxZ i)) (hy : ∀ j, P (idxY j)) : P α := by
  rw [← (configIdxEquiv k p).symm_apply_apply α]
  rcases configIdxEquiv k p α with o | j
  · rcases o with _ | i
    · simpa [idxZ0] using h0
    · simpa [idxZ] using hz i
  · simpa [idxY] using hy j

/--
@isnad1 id=iff.0h4v.s4.c42be8ccd7fa from=translated src=- shape=e4257580 vocab=323ef03b
-/
lemma idxY_inj {j ℓ : Fin p} : idxY (k := k) j = idxY ℓ ↔ j = ℓ := by
  constructor
  · intro h
    exact Fin.ext (by simpa [idxY_val] using congrArg Fin.val h)
  · rintro rfl; rfl

/--
@isnad1 id=ishermit.0h6v.s7.627f7e99e1a8 from=translated src=- shape=3e591031 vocab=fc74114e
-/
lemma MX_isHermitian (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (M (Xconfig s t ρ x)).IsHermitian :=
  (M_posSemidef (Xconfig_posSemidef s t ρ x)).isHermitian

/--
@isnad1 id=issymm.0h6v.s6.91f3897fd537 from=translated src=- shape=3e591031 vocab=e95fcf13
-/
lemma MX_isSymm (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (M (Xconfig s t ρ x)).IsSymm :=
  isHermitian_iff_isSymm.mp (MX_isHermitian s t ρ x)

/-- `E`-embedding: `none` is `z₀`, `some i` is `zᵢ`. -/
def elimEEmbed : Option (Fin k) → ConfigIdx k p
  | none => idxZ0
  | some i => idxZ i

/-- `T`-embedding: the `y`-indices. -/
def elimT : Fin p → ConfigIdx k p := idxY

/--
@isnad1 id=eq.0h2v.s4.96526b35c609 from=translated src=- shape=f652e2d9 vocab=ae6d2be5
-/
lemma elimEEmbed_none : elimEEmbed (p := p) (none : Option (Fin k)) = idxZ0 := rfl
/--
@isnad1 id=eq.0h3v.s4.0a3a87271d5d from=translated src=- shape=a5837f9b vocab=c30a6550
-/
lemma elimEEmbed_some (i : Fin k) : elimEEmbed (p := p) (some i) = idxZ i := rfl
/--
@isnad1 id=eq.0h3v.s4.a4dc2f462457 from=translated src=- shape=40f8ff86 vocab=5ea3fc49
-/
lemma elimT_apply (j : Fin p) : elimT (k := k) j = idxY j := rfl

/--
@isnad1 id=eq.0h2v.s6.af623cd7c2b8 from=translated src=- shape=f462a5d3 vocab=26cf19c3
-/
lemma configIdxEquiv_idxZ0 : configIdxEquiv k p (idxZ0 : ConfigIdx k p) = Sum.inl none :=
  Equiv.apply_symm_apply _ _

/--
@isnad1 id=eq.0h3v.s6.b7bb7f3f13a8 from=translated src=- shape=09f6eb18 vocab=de1b26f8
-/
lemma configIdxEquiv_idxZ (i : Fin k) :
    configIdxEquiv k p (idxZ (p := p) i) = Sum.inl (some i) :=
  Equiv.apply_symm_apply _ _

/--
@isnad1 id=eq.0h3v.s6.48f652e3cafa from=translated src=- shape=d91242ac vocab=b5ffeff5
-/
lemma configIdxEquiv_idxY (j : Fin p) :
    configIdxEquiv k p (idxY (k := k) j) = Sum.inr j :=
  Equiv.apply_symm_apply _ _

/--
@isnad1 id=ne.0h4v.s4.e4f37a3c4adb from=translated src=- shape=b91a917b vocab=966639c7
-/
lemma elimEEmbed_ne_elimT (a : Option (Fin k)) (j : Fin p) :
    elimEEmbed (p := p) a ≠ elimT (k := k) j := by
  cases a with
  | none => exact idxZ0_ne_idxY j
  | some i => exact idxZ_ne_idxY i j

/-- The `E`-block of `M (Xconfig s t ρ x)`: rows and columns indexed by the axis vector and the left
vectors through `elimEEmbed`. -/
def elimEE (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Option (Fin k)) (Option (Fin k)) ℝ :=
  (M (Xconfig s t ρ x)).submatrix elimEEmbed elimEEmbed

/-- The block of `M (Xconfig s t ρ x)` with `E`-rows (via `elimEEmbed`) and right-vector columns
(via `elimT`). -/
def elimET (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Option (Fin k)) (Fin p) ℝ :=
  (M (Xconfig s t ρ x)).submatrix elimEEmbed elimT

/-- The block of `M (Xconfig s t ρ x)` with right-vector rows (via `elimT`) and `E`-columns (via
`elimEEmbed`). -/
def elimTE (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Fin p) (Option (Fin k)) ℝ :=
  (M (Xconfig s t ρ x)).submatrix elimT elimEEmbed

/-- The right-vector block of `M (Xconfig s t ρ x)`: rows and columns indexed through `elimT`. -/
def elimTT (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  (M (Xconfig s t ρ x)).submatrix elimT elimT

/--
@isnad1 id=eq.0h6v.s6.78f22e62be5e from=translated src=- shape=cd03d292 vocab=a5ea1bd0
-/
lemma elimEE_none_none (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    elimEE s t ρ x none none = M (Xconfig s t ρ x) idxZ0 idxZ0 := rfl

/--
@isnad1 id=eq.0h7v.s5.2d84d0e7c43a from=translated src=- shape=f865fffb vocab=677ed612
-/
lemma elimEE_none_some (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) :
    elimEE s t ρ x none (some i) = 0 :=
  MX_z0_z s t ρ x i

/--
@isnad1 id=eq.0h7v.s5.d39329deca90 from=translated src=- shape=3a790b3e vocab=677ed612
-/
lemma elimEE_some_none (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i : Fin k) :
    elimEE s t ρ x (some i) none = 0 :=
  MX_z_z0 s t ρ x i

/--
@isnad1 id=eq.0h8v.s7.85ec506eb35c from=translated src=- shape=d4cf7c2f vocab=dd7d711e
-/
lemma elimEE_some_some (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (i h : Fin k) :
    elimEE s t ρ x (some i) (some h) =
      M (Xconfig s t ρ x) (idxZ i) (idxZ h) := rfl

/--
@isnad1 id=ishermit.0h6v.s6.8fd0903c230d from=translated src=- shape=327233da vocab=d1c679d4
-/
lemma elimEE_isHermitian (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (elimEE s t ρ x).IsHermitian :=
  (MX_isHermitian s t ρ x).submatrix elimEEmbed

/--
@isnad1 id=issymm.0h6v.s5.b65b1efaea31 from=translated src=- shape=327233da vocab=2011b6a9
-/
lemma elimEE_isSymm (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (elimEE s t ρ x).IsSymm :=
  isHermitian_iff_isSymm.mp (elimEE_isHermitian s t ρ x)

/--
@isnad1 id=eq.0h7v.s7.1b0f4df7bad1 from=translated src=- shape=46ed4a85 vocab=3f44abe7
-/
lemma elimEE_mulVec_none (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (v : Option (Fin k) → ℝ) :
    (elimEE s t ρ x *ᵥ v) none =
      M (Xconfig s t ρ x) idxZ0 idxZ0 * v none := by
  simp [mulVec, dotProduct, Fintype.sum_option, elimEE_none_none, elimEE_none_some]

/--
@isnad1 id=eq.0h8v.s7.b83de9dbbdc3 from=translated src=- shape=d810d03a vocab=c90c9588
-/
lemma elimEE_mulVec_some (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (v : Option (Fin k) → ℝ) (i : Fin k) :
    (elimEE s t ρ x *ᵥ v) (some i) =
      (((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))) *ᵥ
        fun h => v (some h)) i := by
  simp [mulVec, dotProduct, Fintype.sum_option, elimEE_some_none, elimEE_some_some,
    submatrix_apply]

/--
@isnad1 id=eq.0h7v.s8.32df5be0f609 from=translated src=- shape=af4df4a6 vocab=f847ae63
-/
lemma elimEE_quad (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (v : Option (Fin k) → ℝ) :
    v ⬝ᵥ (elimEE s t ρ x *ᵥ v) =
      M (Xconfig s t ρ x) idxZ0 idxZ0 * v none * v none +
        (fun i => v (some i)) ⬝ᵥ
          ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)) *ᵥ
            fun i => v (some i)) := by
  simp [dotProduct, Fintype.sum_option, elimEE_mulVec_none, elimEE_mulVec_some]
  ring

/-- EL13: the principal `E`-block is positive definite.
@isnad1 id=posdef.4h6v.s6.7521d8ba715f from=translated src=- shape=396c438f vocab=5ed426da
-/
lemma elimEE_posDef (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    (elimEE s t ρ x).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (elimEE_isHermitian s t ρ x) fun v hv => ?_
  have hstar : star v = v := funext fun _ => star_trivial _
  rw [hstar, elimEE_quad]
  have hZ := MX_zBlock_posDef s t ρ x hs ht hρ
  have h00 := MX_z0_z0_pos s t ρ x hs hx
  have hZnn :=
    (posSemidef_iff_dotProduct_mulVec.mp hZ.posSemidef).2 (fun i => v (some i))
  have hstarZ : star (fun i : Fin k => v (some i)) = fun i => v (some i) :=
    funext fun _ => star_trivial _
  rw [hstarZ] at hZnn
  rcases eq_or_ne (v none) 0 with hv0 | hvn
  · have hsome : (fun i : Fin k => v (some i)) ≠ 0 := by
      intro h
      apply hv
      funext a
      cases a with
      | none => exact hv0
      | some i => exact congrFun h i
    have hpos := hZ.dotProduct_mulVec_pos hsome
    simp [hv0] at hpos ⊢
    simpa [hstarZ] using hpos
  · nlinarith [sq_pos_of_ne_zero hvn, h00, hZnn]

/--
@isnad1 id=eq.0h6v.s6.aa2ee30507a9 from=translated src=- shape=f4527ce3 vocab=4e13c32c
-/
lemma elimTE_eq_conjTranspose (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    elimTE s t ρ x = (elimET s t ρ x)ᴴ := by
  ext i j
  simp only [elimTE, submatrix_apply, elimET, conjTranspose_apply, star_trivial]
  exact (MX_isSymm s t ρ x).apply _ _

/--
@isnad1 id=eq.0h6v.s7.6e2302450ca0 from=translated src=- shape=c68959d3 vocab=ddb52eab
-/
lemma M_submatrix_sumElim (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    (M (Xconfig s t ρ x)).submatrix
        (Sum.elim (elimEEmbed (p := p)) (elimT (k := k)))
        (Sum.elim (elimEEmbed (p := p)) (elimT (k := k))) =
      fromBlocks (elimEE s t ρ x) (elimET s t ρ x)
        (elimTE s t ρ x) (elimTT s t ρ x) := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Schur complement of the `E`-block in the `T`-block. -/
def elimSchurR (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  elimTT s t ρ x - elimTE s t ρ x * (elimEE s t ρ x)⁻¹ * elimET s t ρ x

/-- Extension by zero off the `T`-indices. -/
def extendByZeroT (R : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ :=
  fun α β =>
    match configIdxEquiv k p α, configIdxEquiv k p β with
    | Sum.inr j, Sum.inr ℓ => R j ℓ
    | _, _ => 0

/--
@isnad1 id=eq.0h5v.s5.eb1bb1ec0cb0 from=translated src=- shape=8acfb2b2 vocab=b6b33003
-/
lemma extendByZeroT_y_y (R : Matrix (Fin p) (Fin p) ℝ) (j ℓ : Fin p) :
    extendByZeroT (k := k) R (idxY j) (idxY ℓ) = R j ℓ := by
  simp [extendByZeroT, configIdxEquiv_idxY]

/--
@isnad1 id=eq.0h4v.s4.41d91c48827c from=translated src=- shape=1514a434 vocab=3381adaf
-/
lemma extendByZeroT_z0_left (R : Matrix (Fin p) (Fin p) ℝ) (β : ConfigIdx k p) :
    extendByZeroT (k := k) R idxZ0 β = 0 := by
  simp [extendByZeroT, configIdxEquiv_idxZ0]

/--
@isnad1 id=eq.0h5v.s5.9d9b94778af5 from=translated src=- shape=4b6af381 vocab=f411aadb
-/
lemma extendByZeroT_z_left (R : Matrix (Fin p) (Fin p) ℝ) (i : Fin k)
    (β : ConfigIdx k p) :
    extendByZeroT (k := k) R (idxZ i) β = 0 := by
  simp [extendByZeroT, configIdxEquiv_idxZ]

/--
@isnad1 id=eq.0h4v.s4.08c55e0f8225 from=translated src=- shape=88d65057 vocab=3381adaf
-/
lemma extendByZeroT_z0_right (R : Matrix (Fin p) (Fin p) ℝ) (α : ConfigIdx k p) :
    extendByZeroT (k := k) R α idxZ0 = 0 := by
  simp [extendByZeroT, configIdxEquiv_idxZ0]

/--
@isnad1 id=eq.0h5v.s5.a1d140a7eb94 from=translated src=- shape=e34104a0 vocab=f411aadb
-/
lemma extendByZeroT_z_right (R : Matrix (Fin p) (Fin p) ℝ) (α : ConfigIdx k p)
    (i : Fin k) :
    extendByZeroT (k := k) R α (idxZ i) = 0 := by
  simp [extendByZeroT, configIdxEquiv_idxZ]

/-- EL13: the `T`-Schur complement of `E` is positive semidefinite.
@isnad1 id=possemid.4h6v.s6.0489374b053c from=translated src=- shape=858139ef vocab=5cc6e049
-/
lemma elimSchurR_posSemidef (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    (elimSchurR s t ρ x).PosSemidef := by
  have hE := elimEE_posDef s t ρ x hs ht hρ hx
  have hblk := M_submatrix_sumElim s t ρ x
  have hPSD :=
    (M_posSemidef (Xconfig_posSemidef s t ρ x)).submatrix
      (Sum.elim (elimEEmbed (p := p)) (elimT (k := k)))
  rw [hblk, elimTE_eq_conjTranspose] at hPSD
  let := hE.isUnit.invertible
  simpa [elimSchurR, elimTE_eq_conjTranspose] using
    (PosDef.fromBlocks₁₁ (elimET s t ρ x) (elimTT s t ρ x) hE).1 hPSD

/-! ### Residual columns after ordered `z`-elimination -/

/--
@isnad1 id=isunit.1h2v.s5.7d6ed0e0167d from=translated src=- shape=c3d20317 vocab=73baedb9
-/
lemma isUnit_det_of_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (h : IsUnit A) : IsUnit A.det :=
  (isUnit_iff_isUnit_det A).mp h

/--
@isnad1 id=eq.1h2v.s6.a5ff6ff82205 from=translated src=- shape=b987fbd7 vocab=d1515de7
-/
lemma mul_inv_of_isUnit_real {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (h : IsUnit A) : A * A⁻¹ = 1 :=
  mul_nonsing_inv A (isUnit_det_of_isUnit h)

/--
@isnad1 id=eq.1h2v.s6.c5834a4b5e39 from=translated src=- shape=cd070a0c vocab=d1515de7
-/
lemma inv_mul_of_isUnit_real {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (h : IsUnit A) : A⁻¹ * A = 1 :=
  nonsing_inv_mul A (isUnit_det_of_isUnit h)

/--
@isnad1 id=eq.0h8v.s5.b6e6ae860622 from=translated src=- shape=8bd65555 vocab=cbb33725
-/
lemma schurComplementEntry_submatrix {n : Type*}
    (A : Matrix ι ι ℝ) (f : n → ι) (e : Fin r → n) (a b : n) :
    schurComplementEntry (A.submatrix f f) e a b =
      schurComplementEntry A (f ∘ e) (f a) (f b) := by
  have h : (A.submatrix f f).submatrix e e = A.submatrix (f ∘ e) (f ∘ e) := by
    ext i j
    simp
  simp only [schurComplementEntry, submatrix_apply]
  rw [h]
  rfl

/--
@isnad1 id=eq.1h6v.s6.cd650d35fbb1 from=translated src=- shape=bd180a5a vocab=c2ba1fe0
-/
lemma schurComplementEntry_eq_zero_of_mem {n : Type*}
    (A : Matrix n n ℝ) (e : Fin r → n) (hU : IsUnit (A.submatrix e e))
    (i : Fin r) (j : n) :
    schurComplementEntry A e (e i) j = 0 := by
  have hmul := mul_inv_of_isUnit_real hU
  unfold schurComplementEntry
  have hdot :
      (fun k => A (e i) (e k)) ⬝ᵥ ((A.submatrix e e)⁻¹ *ᵥ fun k => A (e k) j) =
        ((A.submatrix e e) *ᵥ ((A.submatrix e e)⁻¹ *ᵥ fun k => A (e k) j)) i := by
    simp [mulVec, dotProduct, submatrix_apply]
  rw [hdot, mulVec_mulVec, hmul, one_mulVec]
  simp

/--
@isnad1 id=eq.2h2v.s4.6026a77f35b3 from=translated src=- shape=a825bb08 vocab=90c2ca43
-/
lemma castLE_proof_irrel {n : ℕ} (h1 h2 : n ≤ k) :
    Fin.castLE h1 = Fin.castLE h2 :=
  funext fun _ => Fin.ext rfl

/-- Residual of column `idxZ j` after eliminating earlier `z`-indices. -/
def elimRes (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j : Fin k)
    (α : ConfigIdx k p) : ℝ :=
  schurComplementEntry (M (Xconfig s t ρ x))
    (idxZ (p := p) ∘ Fin.castLE (Nat.le_of_lt j.isLt)) α (idxZ j)

/-- Pivot at `z`-index `j` after eliminating earlier `z`-indices. -/
def elimPivot (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j : Fin k) : ℝ :=
  schurComplementEntry
    ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))
    (Fin.castLE (Nat.le_of_lt j.isLt)) j j

/--
@isnad1 id=lt.3h7v.s6.ec1e5665449f from=translated src=- shape=03e24259 vocab=6d2dc7e3
-/
lemma elimPivot_pos (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) (j : Fin k) :
    0 < elimPivot s t ρ x j :=
  MX_zBlock_schur_pivot_pos s t ρ x hs ht hρ
    (Fin.castLE (Nat.le_of_lt j.isLt)) (Fin.castLE_injective _)
    (by
      rintro ⟨i, hi⟩
      exact i.isLt.ne (by simpa [Fin.ext_iff] using hi))

/--
@isnad1 id=eq.0h8v.s7.84711544163a from=translated src=- shape=8e915199 vocab=541ec146
-/
lemma elimRes_idxZ (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j β : Fin k) :
    elimRes s t ρ x j (idxZ β) =
      schurComplementEntry
        ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))
        (Fin.castLE (Nat.le_of_lt j.isLt)) β j :=
  (schurComplementEntry_submatrix (M (Xconfig s t ρ x)) (idxZ (p := p))
    (Fin.castLE (Nat.le_of_lt j.isLt)) β j).symm

/--
@isnad1 id=eq.0h7v.s5.ef7c707f7fda from=translated src=- shape=61e13473 vocab=0c1fecf7
-/
lemma elimRes_eq_pivot (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j : Fin k) :
    elimRes s t ρ x j (idxZ j) = elimPivot s t ρ x j :=
  elimRes_idxZ s t ρ x j j

/-! ### EL12 — `C₀` is completely positive -/

/-- The `idxZ0` column of `M (Xconfig s t ρ x)` divided by the square root of its diagonal entry:
the first factor of `C₀`. -/
def elimVec0 (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) : ConfigIdx k p → ℝ :=
  fun α =>
    M (Xconfig s t ρ x) α idxZ0 /
      Real.sqrt (M (Xconfig s t ρ x) idxZ0 idxZ0)

/-- The `j`-th elimination residual `elimRes` divided by the square root of its pivot `elimPivot`:
the `j.succ`-th factor of `C₀`. -/
def elimVec (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j : Fin k) :
    ConfigIdx k p → ℝ :=
  fun α => elimRes s t ρ x j α / Real.sqrt (elimPivot s t ρ x j)

/-- The `k + 1` factors of `C₀`: `elimVec0` followed by the vectors `elimVec s t ρ x j`. -/
def elimC0Factor (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Fin (k + 1) → ConfigIdx k p → ℝ :=
  Fin.cons (elimVec0 s t ρ x) (elimVec s t ρ x)

/-- Sum of scaled residual outer products. -/
def elimC0 (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ :=
  ∑ a : Fin (k + 1), vecMulVec (elimC0Factor s t ρ x a) (elimC0Factor s t ρ x a)

/--
@isnad1 id=le.3h7v.s6.a366713f641f from=translated src=- shape=5ee8657e vocab=47a20873
-/
lemma elimVec0_nonneg (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j)
    (α : ConfigIdx k p) :
    0 ≤ elimVec0 s t ρ x α :=
  div_nonneg
    (by
      rw [(MX_isSymm s t ρ x).apply]
      exact MX_z0_nonneg s t ρ x hs hρ hx α)
    (Real.sqrt_nonneg _)

/-! ### Gram of the `E`-columns and the identity `M = C₀ + pad R` -/

/-- Row `α` of `M (Xconfig s t ρ x)` restricted to the `E`-columns. -/
def elimColE (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (α : ConfigIdx k p) :
    Option (Fin k) → ℝ :=
  fun a => M (Xconfig s t ρ x) α (elimEEmbed a)

/-- `P EE⁻¹ Pᵀ` on configuration indices. -/
def elimGramE (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ :=
  fun α β =>
    elimColE s t ρ x α ⬝ᵥ (elimEE s t ρ x)⁻¹ *ᵥ elimColE s t ρ x β

/-- The leading `m × m` principal block of `M (Xconfig s t ρ x)` on the left-vector indices `idxZ
(Fin.castLE hm i)`. -/
def elimZLead (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) {m : ℕ} (hm : m ≤ k) :
    Matrix (Fin m) (Fin m) ℝ :=
  ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p))).submatrix
    (Fin.castLE hm) (Fin.castLE hm)

/-- Row `α` of `M (Xconfig s t ρ x)` restricted to the first `m` left-vector columns. -/
def elimColZLead (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) {m : ℕ} (hm : m ≤ k)
    (α : ConfigIdx k p) : Fin m → ℝ :=
  fun i => M (Xconfig s t ρ x) α (idxZ (Fin.castLE hm i))

/-- The matrix `c_α ⬝ᵥ (elimZLead)⁻¹ *ᵥ c_β` built from the columns `elimColZLead`: the part of `M`
explained by the first `m` left vectors. -/
def elimGramZLead (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) {m : ℕ} (hm : m ≤ k) :
    Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ :=
  fun α β =>
    elimColZLead s t ρ x hm α ⬝ᵥ
      (elimZLead s t ρ x hm)⁻¹ *ᵥ elimColZLead s t ρ x hm β

/-- The block-diagonal matrix on `Option (Fin k)` with `(M idxZ0 idxZ0)⁻¹` in the `none` corner and
the inverse of the left-vector block of `M (Xconfig s t ρ x)` on the `some` indices. -/
def elimEEInv (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) :
    Matrix (Option (Fin k)) (Option (Fin k)) ℝ :=
  fun a b =>
    match a, b with
    | none, none => (M (Xconfig s t ρ x) idxZ0 idxZ0)⁻¹
    | none, some _ => 0
    | some _, none => 0
    | some i, some h =>
        ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))⁻¹ i h

/--
@isnad1 id=eq.4h6v.s7.085d4a7217e9 from=translated src=- shape=ad6ceeb9 vocab=265876c0
-/
lemma elimEE_mul_inv (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    elimEE s t ρ x * elimEEInv s t ρ x = 1 := by
  have h00 := (MX_z0_z0_pos s t ρ x hs hx).ne'
  have hZ := (MX_zBlock_posDef s t ρ x hs ht hρ).isUnit
  have hZmul :=
    mul_inv_of_isUnit_real hZ
  ext a b
  cases a with
  | none =>
    cases b with
    | none =>
      simp only [Matrix.mul_apply, elimEEInv, Fintype.sum_option, elimEE_none_none,
        elimEE_none_some, mul_zero, sum_const_zero, add_zero, one_apply_eq]
      exact mul_inv_cancel₀ h00
    | some h =>
      simp [Matrix.mul_apply, Fintype.sum_option, elimEE_none_none, elimEE_none_some,
        elimEEInv]
  | some i =>
    cases b with
    | none =>
      simp [Matrix.mul_apply, Fintype.sum_option, elimEE_some_none, elimEE_some_some,
        elimEEInv]
    | some h =>
      have h1 :
          ∑ i' : Fin k,
              elimEE s t ρ x (some i) (some i') *
                elimEEInv s t ρ x (some i') (some h) =
            (1 : Matrix (Fin k) (Fin k) ℝ) i h := by
        simpa [elimEE_some_some, elimEEInv, Matrix.mul_apply] using
          congrFun (congrFun hZmul i) h
      simpa [Matrix.mul_apply, Fintype.sum_option, elimEE_some_none, elimEEInv,
        Matrix.one_apply] using h1

/--
@isnad1 id=eq.4h6v.s7.865a30d561ef from=translated src=- shape=df9e470a vocab=0f5f51f0
-/
lemma elimEE_inv_eq (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    (elimEE s t ρ x)⁻¹ = elimEEInv s t ρ x :=
  inv_eq_right_inv (elimEE_mul_inv s t ρ x hs ht hρ hx)

/--
@isnad1 id=eq.0h7v.s8.765711c59a0f from=translated src=- shape=2f7121ed vocab=ca123a8a
-/
lemma elimEEInv_mulVec (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (v : Option (Fin k) → ℝ) :
    elimEEInv s t ρ x *ᵥ v =
      fun a =>
        match a with
        | none => (M (Xconfig s t ρ x) idxZ0 idxZ0)⁻¹ * v none
        | some i =>
            (((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))⁻¹ *ᵥ
              fun h => v (some h)) i := by
  funext a
  cases a with
  | none =>
    simp [mulVec, dotProduct, Fintype.sum_option, elimEEInv]
  | some i =>
    simp [mulVec, dotProduct, Fintype.sum_option, elimEEInv]

/--
@isnad1 id=eq.4h8v.s8.ecb7998129f7 from=translated src=- shape=c252c0bf vocab=1d0aa3dd
-/
lemma elimGramE_eq_z0_add_Z (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) (α β : ConfigIdx k p) :
    elimGramE s t ρ x α β =
      (M (Xconfig s t ρ x) α idxZ0) *
          ((M (Xconfig s t ρ x) idxZ0 idxZ0)⁻¹ *
            M (Xconfig s t ρ x) β idxZ0) +
        elimGramZLead s t ρ x le_rfl α β := by
  have hinv := elimEE_inv_eq s t ρ x hs ht hρ hx
  simp only [elimGramE, elimGramZLead, elimZLead]
  rw [hinv, elimEEInv_mulVec]
  simp [dotProduct, Fintype.sum_option]
  rfl

/--
@isnad1 id=ishermit.2h2v.s6.141eda71475f from=translated src=- shape=9e81ce0d vocab=3b68d5dc
-/
lemma IsHermitian.nonsing_inv_real {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (_hU : IsUnit A) :
    A⁻¹.IsHermitian := by
  rw [isHermitian_iff_isSymm] at hA ⊢
  change (A⁻¹)ᵀ = A⁻¹
  rw [transpose_nonsing_inv, hA]

/--
@isnad1 id=eq.2h4v.s7.7c4a6edc3482 from=translated src=- shape=cf41b860 vocab=88933829
-/
lemma dotProduct_nonsing_inv_comm {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (hU : IsUnit A) (x y : n → ℝ) :
    x ⬝ᵥ (A⁻¹ *ᵥ y) = y ⬝ᵥ (A⁻¹ *ᵥ x) := by
  have hS : (A⁻¹)ᵀ = A⁻¹ :=
    isHermitian_iff_isSymm.mp (IsHermitian.nonsing_inv_real hA hU)
  simpa [hS] using (dotProduct_transpose_mulVec (A := A⁻¹) x y)

/--
@isnad1 id=eq.0h4v.s7.a81ed73b5845 from=translated src=- shape=953b099a vocab=4823027f
-/
lemma mulVec_sum_castSucc {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (x : Fin (m + 1) → ℝ) (i : Fin m) :
    (Z *ᵥ x) i.castSucc =
      ((Z.submatrix Fin.castSucc Fin.castSucc) *ᵥ fun j => x j.castSucc) i +
        Z i.castSucc (Fin.last m) * x (Fin.last m) := by
  simp [mulVec, dotProduct, Fin.sum_univ_castSucc, submatrix_apply]

/--
@isnad1 id=eq.0h3v.s7.e6023b6eb1ec from=translated src=- shape=0159b8ca vocab=7da6343e
-/
lemma mulVec_sum_last {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (x : Fin (m + 1) → ℝ) :
    (Z *ᵥ x) (Fin.last m) =
      (fun i : Fin m => Z (Fin.last m) i.castSucc) ⬝ᵥ (fun j => x j.castSucc) +
        Z (Fin.last m) (Fin.last m) * x (Fin.last m) := by
  simp [mulVec, dotProduct, Fin.sum_univ_castSucc]

/--
@isnad1 id=eq.0h3v.s6.d5296330a53b from=translated src=- shape=9404ddab vocab=fe4a24d5
-/
lemma dotProduct_sum_castSucc {m : ℕ} (P x : Fin (m + 1) → ℝ) :
    P ⬝ᵥ x =
      (fun i : Fin m => P i.castSucc) ⬝ᵥ (fun j => x j.castSucc) +
        P (Fin.last m) * x (Fin.last m) := by
  simp [dotProduct, Fin.sum_univ_castSucc]

/--
@isnad1 id=eq.1h4v.s9.a67643745000 from=translated src=- shape=f9791f20 vocab=7d9ca593
-/
lemma gram_inv_castSucc_step {m : ℕ}
    (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hZ : Z.PosDef)
    (Pα Pβ : Fin (m + 1) → ℝ) :
    Pα ⬝ᵥ (Z⁻¹ *ᵥ Pβ) =
      (fun i : Fin m => Pα i.castSucc) ⬝ᵥ
          ((Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
            fun i : Fin m => Pβ i.castSucc) +
        (1 / schurComplementEntry Z Fin.castSucc (Fin.last m) (Fin.last m)) *
          (Pα (Fin.last m) -
            (fun i : Fin m => Pα i.castSucc) ⬝ᵥ
              ((Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
                fun i : Fin m => Z i.castSucc (Fin.last m))) *
          (Pβ (Fin.last m) -
            (fun i : Fin m => Pβ i.castSucc) ⬝ᵥ
              ((Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
                fun i : Fin m => Z i.castSucc (Fin.last m))) := by
  set A := Z.submatrix Fin.castSucc Fin.castSucc
  set b : Fin m → ℝ := fun i => Z i.castSucc (Fin.last m)
  set d := schurComplementEntry Z Fin.castSucc (Fin.last m) (Fin.last m)
  set resP := fun P : Fin (m + 1) → ℝ =>
    P (Fin.last m) - (fun i : Fin m => P i.castSucc) ⬝ᵥ (A⁻¹ *ᵥ b)
  have hA : A.PosDef := hZ.submatrix (Fin.castSucc_injective (n := m))
  have hlast : Fin.last m ∉ Set.range Fin.castSucc := by
    rintro ⟨i, hi⟩
    exact (Fin.castSucc_lt_last i).ne hi
  have hdpos :=
    schurComplementEntry_diag_pos_of_posDef hZ Fin.castSucc
      (Fin.castSucc_injective (n := m)) hlast
  have hd0 : d ≠ 0 := hdpos.ne'
  have hZsym : Z.IsSymm := isHermitian_iff_isSymm.mp hZ.1
  have hrow : (fun i : Fin m => Z (Fin.last m) i.castSucc) = b :=
    funext fun i => (hZsym.apply _ _)
  have hdetZ : IsUnit Z.det := isUnit_det_of_isUnit hZ.isUnit
  have hdetA : IsUnit A.det := isUnit_det_of_isUnit hA.isUnit
  have hZx : Z *ᵥ (Z⁻¹ *ᵥ Pβ) = Pβ := by
    rw [mulVec_mulVec, mul_nonsing_inv Z hdetZ, one_mulVec]
  set x := Z⁻¹ *ᵥ Pβ
  have hxcast : A *ᵥ (fun j => x j.castSucc) =
      fun i => Pβ i.castSucc - x (Fin.last m) * b i := by
    ext i
    have := congrArg (fun v => v i.castSucc) hZx
    have hx := mulVec_sum_castSucc Z x i
    simp only [x] at hx this
    linarith
  have hxlead : (fun j => x j.castSucc) =
      A⁻¹ *ᵥ fun i => Pβ i.castSucc - x (Fin.last m) * b i := by
    have := congrArg (fun w => A⁻¹ *ᵥ w) hxcast
    rw [mulVec_mulVec, nonsing_inv_mul A hdetA, one_mulVec] at this
    exact this
  have hxlast_eq :
      b ⬝ᵥ (fun j => x j.castSucc) + Z (Fin.last m) (Fin.last m) * x (Fin.last m) =
        Pβ (Fin.last m) := by
    have := congrArg (fun v => v (Fin.last m)) hZx
    rw [mulVec_sum_last, hrow] at this
    exact this
  have hbAu :
      b ⬝ᵥ (A⁻¹ *ᵥ fun i => Pβ i.castSucc) =
        (fun i : Fin m => Pβ i.castSucc) ⬝ᵥ (A⁻¹ *ᵥ b) :=
    dotProduct_nonsing_inv_comm hA.1 hA.isUnit _ _
  have hxlast : x (Fin.last m) = resP Pβ / d := by
    have hlast' := hxlast_eq
    rw [hxlead] at hlast'
    have hlin :
        b ⬝ᵥ (A⁻¹ *ᵥ fun i => Pβ i.castSucc - x (Fin.last m) * b i) =
          b ⬝ᵥ (A⁻¹ *ᵥ fun i => Pβ i.castSucc) -
            x (Fin.last m) * (b ⬝ᵥ (A⁻¹ *ᵥ b)) := by
      have hfun :
          (fun i => Pβ i.castSucc - x (Fin.last m) * b i) =
            (fun i => Pβ i.castSucc) - x (Fin.last m) • b := by
        funext i
        simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hfun, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [hlin, hbAu] at hlast'
    have hddef : d =
        Z (Fin.last m) (Fin.last m) - b ⬝ᵥ (A⁻¹ *ᵥ b) := by
      simp [d, schurComplementEntry, A, b, hrow]
    have hmuld : x (Fin.last m) * d = resP Pβ := by
      simp only [resP]
      linear_combination hlast' + x (Fin.last m) * hddef
    exact (eq_div_iff hd0).2 hmuld
  have hLHS : Pα ⬝ᵥ x =
      (fun i : Fin m => Pα i.castSucc) ⬝ᵥ (fun j => x j.castSucc) +
        Pα (Fin.last m) * x (Fin.last m) :=
    dotProduct_sum_castSucc Pα x
  rw [hLHS, hxlead]
  have hlinα :
      (fun i : Fin m => Pα i.castSucc) ⬝ᵥ
          (A⁻¹ *ᵥ fun i => Pβ i.castSucc - x (Fin.last m) * b i) =
        (fun i : Fin m => Pα i.castSucc) ⬝ᵥ (A⁻¹ *ᵥ fun i => Pβ i.castSucc) -
          x (Fin.last m) *
            ((fun i : Fin m => Pα i.castSucc) ⬝ᵥ (A⁻¹ *ᵥ b)) := by
    have hfun :
        (fun i => Pβ i.castSucc - x (Fin.last m) * b i) =
          (fun i => Pβ i.castSucc) - x (Fin.last m) • b := by
      funext i
      simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hlinα, hxlast]
  unfold resP
  field_simp [hd0]
  ring

/--
@isnad1 id=posdef.4h7v.s6.005fdb1c012e from=translated src=- shape=a082e34d vocab=1c4c1e60
-/
lemma elimZLead_posDef (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (hm : m ≤ k) :
    (elimZLead s t ρ x hm).PosDef :=
  MX_zBlock_leading_posDef s t ρ x hs ht hρ hm

/--
@isnad1 id=eq.1h7v.s6.d1fdb8b77ef2 from=translated src=- shape=bdc06b55 vocab=c3a64fd1
-/
lemma elimZLead_castSucc (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) :
    (elimZLead s t ρ x hm).submatrix Fin.castSucc Fin.castSucc =
      elimZLead s t ρ x (Nat.le_of_succ_le hm) := by
  ext i j
  simp [elimZLead, submatrix_apply]

/--
@isnad1 id=eq.1h8v.s6.c8aa605dfdcd from=translated src=- shape=f54841fc vocab=8b6033e0
-/
lemma elimColZLead_castSucc (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) (α : ConfigIdx k p) :
    (fun i : Fin m => elimColZLead s t ρ x hm α i.castSucc) =
      elimColZLead s t ρ x (Nat.le_of_succ_le hm) α := by
  funext i
  simp [elimColZLead]

/--
@isnad1 id=eq.1h8v.s7.e81973c29bc7 from=translated src=- shape=dbc40cbd vocab=6a05e504
-/
lemma elimColZLead_last (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) (α : ConfigIdx k p) :
    elimColZLead s t ρ x hm α (Fin.last m) =
      M (Xconfig s t ρ x) α (idxZ ⟨m, Nat.lt_of_succ_le hm⟩) := by
  simp only [elimColZLead]
  exact congrArg (fun z : Fin k => M (Xconfig s t ρ x) α (idxZ z))
    (Fin.ext (by simp))

/--
@isnad1 id=eq.1h8v.s7.e9a6255b7dc6 from=translated src=- shape=f2dd5ad4 vocab=d02892b8
-/
lemma elimZLead_last_col (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) (i : Fin m) :
    elimZLead s t ρ x hm i.castSucc (Fin.last m) =
      M (Xconfig s t ρ x)
        (idxZ (Fin.castLE (Nat.le_of_succ_le hm) i))
        (idxZ ⟨m, Nat.lt_of_succ_le hm⟩) := by
  simp only [elimZLead, submatrix_apply, Fin.castLE_castSucc]
  apply congrArg₂ (M (Xconfig s t ρ x))
  · exact congrArg idxZ (Fin.ext (by simp))
  · exact congrArg idxZ (Fin.ext (by simp))

/--
@isnad1 id=eq.1h8v.s7.595d20ecfd3c from=translated src=- shape=69ff5af6 vocab=6216f421
-/
lemma elimRes_succ (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) (α : ConfigIdx k p) :
    elimRes s t ρ x ⟨m, Nat.lt_of_succ_le hm⟩ α =
      elimColZLead s t ρ x hm α (Fin.last m) -
        elimColZLead s t ρ x (Nat.le_of_succ_le hm) α ⬝ᵥ
          (elimZLead s t ρ x (Nat.le_of_succ_le hm))⁻¹ *ᵥ
            fun i => elimZLead s t ρ x hm i.castSucc (Fin.last m) := by
  have hcast : Fin.castLE (Nat.le_of_lt (⟨m, Nat.lt_of_succ_le hm⟩ : Fin k).isLt) =
      Fin.castLE (Nat.le_of_succ_le hm) :=
    castLE_proof_irrel _ _
  have hcomp : Fin.castLE (Nat.le_of_succ_le hm) =
      Fin.castLE hm ∘ Fin.castSucc :=
    funext fun _ => Fin.ext rfl
  have he :
      idxZ (p := p) ∘ Fin.castLE (Nat.le_of_lt (⟨m, Nat.lt_of_succ_le hm⟩ : Fin k).isLt) =
        idxZ (p := p) ∘ Fin.castLE hm ∘ Fin.castSucc := by
    rw [hcast, hcomp]
  have hlast : Fin.castLE hm (Fin.last m) = ⟨m, Nat.lt_of_succ_le hm⟩ :=
    Fin.ext (by simp)
  have h1 : M (Xconfig s t ρ x) α (idxZ ⟨m, Nat.lt_of_succ_le hm⟩) =
      elimColZLead s t ρ x hm α (Fin.last m) := by
    simp [elimColZLead, hlast]
  have h2 :
      (fun i => M (Xconfig s t ρ x) α
        ((idxZ (p := p) ∘ Fin.castLE hm ∘ Fin.castSucc) i)) =
        elimColZLead s t ρ x (Nat.le_of_succ_le hm) α := by
    funext i
    simp [elimColZLead]
  have h3 :
      (M (Xconfig s t ρ x)).submatrix
          (idxZ (p := p) ∘ Fin.castLE hm ∘ Fin.castSucc)
          (idxZ (p := p) ∘ Fin.castLE hm ∘ Fin.castSucc) =
        elimZLead s t ρ x (Nat.le_of_succ_le hm) := by
    ext i j
    simp [elimZLead, submatrix_apply]
  have h4 :
      (fun i =>
        M (Xconfig s t ρ x)
          ((idxZ (p := p) ∘ Fin.castLE hm ∘ Fin.castSucc) i)
          (idxZ ⟨m, Nat.lt_of_succ_le hm⟩)) =
        fun i => elimZLead s t ρ x hm i.castSucc (Fin.last m) := by
    funext i
    simp [elimZLead, submatrix_apply, hlast]
  simp only [elimRes, schurComplementEntry]
  rw [he, h1, h2, h3, h4]

/--
@isnad1 id=eq.1h7v.s6.19fb0fd3878b from=translated src=- shape=9b8d2d1b vocab=49df4e00
-/
lemma elimPivot_succ (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    {m : ℕ} (hm : m + 1 ≤ k) :
    elimPivot s t ρ x ⟨m, Nat.lt_of_succ_le hm⟩ =
      schurComplementEntry (elimZLead s t ρ x hm) Fin.castSucc
        (Fin.last m) (Fin.last m) := by
  have hcast : Fin.castLE (Nat.le_of_lt (⟨m, Nat.lt_of_succ_le hm⟩ : Fin k).isLt) =
      Fin.castLE (Nat.le_of_succ_le hm) :=
    castLE_proof_irrel _ _
  have hcomp : Fin.castLE (Nat.le_of_succ_le hm) =
      Fin.castLE hm ∘ Fin.castSucc :=
    funext fun _ => Fin.ext rfl
  have hlast : Fin.castLE hm (Fin.last m) = ⟨m, Nat.lt_of_succ_le hm⟩ :=
    Fin.ext (by simp)
  have hR :
      schurComplementEntry (elimZLead s t ρ x hm) Fin.castSucc
        (Fin.last m) (Fin.last m) =
        schurComplementEntry
          ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))
          (Fin.castLE hm ∘ Fin.castSucc)
          (Fin.castLE hm (Fin.last m)) (Fin.castLE hm (Fin.last m)) := by
    simpa [elimZLead] using
      schurComplementEntry_submatrix
        ((M (Xconfig s t ρ x)).submatrix (idxZ (p := p)) (idxZ (p := p)))
        (Fin.castLE hm) Fin.castSucc (Fin.last m) (Fin.last m)
  rw [elimPivot, hR, hcast, hcomp, hlast]

/--
@isnad1 id=eq.4h7v.s8.52a374070f2a from=translated src=- shape=fc8859fa vocab=bf705c50
-/
lemma elimGramZLead_succ (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    {m : ℕ} (hm : m + 1 ≤ k) :
    elimGramZLead s t ρ x hm =
      elimGramZLead s t ρ x (Nat.le_of_succ_le hm) +
        (1 / elimPivot s t ρ x ⟨m, Nat.lt_of_succ_le hm⟩) •
          vecMulVec (elimRes s t ρ x ⟨m, Nat.lt_of_succ_le hm⟩)
            (elimRes s t ρ x ⟨m, Nat.lt_of_succ_le hm⟩) := by
  ext α β
  have hZ := elimZLead_posDef s t ρ x hs ht hρ hm
  have hstep :=
    gram_inv_castSucc_step (elimZLead s t ρ x hm) hZ
      (elimColZLead s t ρ x hm α) (elimColZLead s t ρ x hm β)
  have hA := elimZLead_castSucc s t ρ x hm
  have hPα := elimColZLead_castSucc s t ρ x hm α
  have hPβ := elimColZLead_castSucc s t ρ x hm β
  have hresα := elimRes_succ s t ρ x hm α
  have hresβ := elimRes_succ s t ρ x hm β
  have hpiv := elimPivot_succ s t ρ x hm
  simp only [elimGramZLead, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply]
  rw [hstep, hA, hPα, hPβ, hpiv, hresα, hresβ]
  ring

/--
@isnad1 id=eq.4h7v.s7.dc056a45e399 from=translated src=- shape=4dd7ae22 vocab=5fcd9b93
-/
lemma elimGramZLead_eq_sum (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) :
    ∀ (m : ℕ) (hm : m ≤ k),
      elimGramZLead s t ρ x hm =
        ∑ j : Fin m,
          (1 / elimPivot s t ρ x (Fin.castLE hm j)) •
            vecMulVec (elimRes s t ρ x (Fin.castLE hm j))
              (elimRes s t ρ x (Fin.castLE hm j)) := by
  intro m
  induction m with
  | zero =>
    intro hm
    ext α β
    simp [elimGramZLead, elimColZLead, dotProduct, mulVec]
  | succ m ih =>
    intro hm
    have hm' : m ≤ k := Nat.le_of_succ_le hm
    have hcastj : ∀ j : Fin m, Fin.castLE hm j.castSucc = Fin.castLE hm' j :=
      fun j => Fin.ext (by simp)
    have hlast : Fin.castLE hm (Fin.last m) = ⟨m, Nat.lt_of_succ_le hm⟩ :=
      Fin.ext (by simp)
    simp [elimGramZLead_succ s t ρ x hs ht hρ hm, ih hm', Fin.sum_univ_castSucc,
      hcastj, hlast]

/--
@isnad1 id=eq.1h3v.s6.19f50bbc9dc4 from=translated src=- shape=2aeefff4 vocab=4f97ec77
-/
lemma vecMulVec_div_sqrt {n : Type*} (v : n → ℝ) {d : ℝ} (hd : 0 < d) :
    vecMulVec (fun i => v i / Real.sqrt d) (fun i => v i / Real.sqrt d) =
      d⁻¹ • vecMulVec v v := by
  ext i j
  simp [vecMulVec_apply, Matrix.smul_apply, div_mul_div_comm, Real.mul_self_sqrt hd.le]
  ring

/--
@isnad1 id=eq.4h6v.s9.149a2e5f5762 from=translated src=- shape=593126d7 vocab=d633b21e
-/
lemma elimC0_eq_sum_scaled (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    elimC0 s t ρ x =
      (M (Xconfig s t ρ x) idxZ0 idxZ0)⁻¹ •
          vecMulVec (fun α => M (Xconfig s t ρ x) α idxZ0)
            (fun α => M (Xconfig s t ρ x) α idxZ0) +
        ∑ j : Fin k,
          (elimPivot s t ρ x j)⁻¹ •
            vecMulVec (elimRes s t ρ x j) (elimRes s t ρ x j) := by
  have h00 := MX_z0_z0_pos s t ρ x hs hx
  unfold elimC0
  rw [Fin.sum_univ_succ]
  simp only [elimC0Factor, Fin.cons_zero, Fin.cons_succ]
  congr 1
  · exact vecMulVec_div_sqrt (fun α => M (Xconfig s t ρ x) α idxZ0) h00
  · refine Fintype.sum_congr _ _ fun j => ?_
    exact vecMulVec_div_sqrt (elimRes s t ρ x j)
      (elimPivot_pos s t ρ x hs ht hρ j)

/--
@isnad1 id=eq.3h6v.s7.da2368b2917b from=translated src=- shape=b493d008 vocab=5d7e98e8
-/
lemma elimGramZLead_full (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) :
    elimGramZLead s t ρ x le_rfl =
      ∑ j : Fin k,
        (elimPivot s t ρ x j)⁻¹ •
          vecMulVec (elimRes s t ρ x j) (elimRes s t ρ x j) := by
  simpa [one_div] using elimGramZLead_eq_sum s t ρ x hs ht hρ k le_rfl

/--
@isnad1 id=eq.4h6v.s6.24c122fea66c from=translated src=- shape=cfe7941c vocab=e6008d73
-/
lemma elimC0_eq_elimGramE (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    elimC0 s t ρ x = elimGramE s t ρ x := by
  ext α β
  have h00 := (MX_z0_z0_pos s t ρ x hs hx).ne'
  rw [elimC0_eq_sum_scaled s t ρ x hs ht hρ hx,
    elimGramE_eq_z0_add_Z s t ρ x hs ht hρ hx, elimGramZLead_full s t ρ x hs ht hρ]
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply,
    mul_left_comm]

/--
@isnad1 id=eq.0h7v.s5.c70072a161d5 from=translated src=- shape=f5c7fd7f vocab=accf2ae8
-/
lemma elimColE_embed (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (a : Option (Fin k)) :
    elimColE s t ρ x (elimEEmbed a) = fun b => elimEE s t ρ x a b := by
  funext b
  rfl

/--
@isnad1 id=eq.4h8v.s6.feff53acdc42 from=translated src=- shape=d3119263 vocab=3bffbcfa
-/
lemma elimGramE_embed (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) (a b : Option (Fin k)) :
    elimGramE s t ρ x (elimEEmbed a) (elimEEmbed b) = elimEE s t ρ x a b := by
  have hU : IsUnit (elimEE s t ρ x) := (elimEE_posDef s t ρ x hs ht hρ hx).isUnit
  have hmul := mul_inv_of_isUnit_real hU
  have hsym := elimEE_isSymm s t ρ x
  simp only [elimGramE, elimColE_embed]
  have hcol : (fun i => elimEE s t ρ x b i) = fun i => elimEE s t ρ x i b :=
    funext fun i => hsym.apply i b
  rw [hcol]
  have hdot :
      (fun i => elimEE s t ρ x a i) ⬝ᵥ
          ((elimEE s t ρ x)⁻¹ *ᵥ fun i => elimEE s t ρ x i b) =
        (elimEE s t ρ x *ᵥ
          ((elimEE s t ρ x)⁻¹ *ᵥ fun i => elimEE s t ρ x i b)) a := by
    simp [mulVec, dotProduct]
  rw [hdot, mulVec_mulVec, hmul, one_mulVec]

/--
@isnad1 id=eq.4h8v.s6.38e9146821ad from=translated src=- shape=f846f198 vocab=ac05c204
-/
lemma elimGramE_embed_y (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) (a : Option (Fin k)) (ℓ : Fin p) :
    elimGramE s t ρ x (elimEEmbed a) (idxY ℓ) = elimET s t ρ x a ℓ := by
  have hU : IsUnit (elimEE s t ρ x) := (elimEE_posDef s t ρ x hs ht hρ hx).isUnit
  have hmul := mul_inv_of_isUnit_real hU
  simp only [elimGramE]
  rw [elimColE_embed]
  have hcol : elimColE s t ρ x (idxY ℓ) =
      fun i => M (Xconfig s t ρ x) (idxY ℓ) (elimEEmbed i) := rfl
  rw [hcol]
  have hdot :
      (fun i => elimEE s t ρ x a i) ⬝ᵥ
          Matrix.mulVec (elimEE s t ρ x)⁻¹
            (fun i => M (Xconfig s t ρ x) (idxY ℓ) (elimEEmbed i)) =
        Matrix.mulVec (elimEE s t ρ x)
          (Matrix.mulVec (elimEE s t ρ x)⁻¹
            (fun i => M (Xconfig s t ρ x) (idxY ℓ) (elimEEmbed i))) a := by
    simp [mulVec, dotProduct]
  rw [hdot, mulVec_mulVec, hmul, one_mulVec]
  simp only [elimET, submatrix_apply]
  exact (MX_isSymm s t ρ x).apply _ _

/--
@isnad1 id=eq.4h8v.s6.9917e41df2c1 from=translated src=- shape=7e614b25 vocab=df879b4a
-/
lemma elimGramE_y_embed (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) (j : Fin p) (b : Option (Fin k)) :
    elimGramE s t ρ x (idxY j) (elimEEmbed b) = elimTE s t ρ x j b := by
  have hU : IsUnit (elimEE s t ρ x) := (elimEE_posDef s t ρ x hs ht hρ hx).isUnit
  simp only [elimGramE]
  have hrow : elimColE s t ρ x (idxY j) = fun i => elimTE s t ρ x j i := rfl
  have hcol : elimColE s t ρ x (elimEEmbed b) = fun i => elimEE s t ρ x i b := by
    funext i
    simp only [elimColE, elimEE, submatrix_apply]
    exact (MX_isSymm s t ρ x).apply _ _
  rw [hrow, hcol]
  have hcolb :
      Matrix.mulVec (elimEE s t ρ x)⁻¹ (fun i => elimEE s t ρ x i b) =
        (Pi.single b (1 : ℝ) : Option (Fin k) → ℝ) := by
    have : (fun i => elimEE s t ρ x i b) =
        Matrix.mulVec (elimEE s t ρ x) (Pi.single b (1 : ℝ)) := by
      ext i
      simp
    rw [this, mulVec_mulVec, inv_mul_of_isUnit_real hU, one_mulVec]
  rw [hcolb, dotProduct_single_one]

/--
@isnad1 id=eq.0h9v.s6.badd9aa8dd4c from=translated src=- shape=8db03a3c vocab=7f46dd84
-/
lemma mul_mul_col_apply {l m n o : Type*} [Fintype m] [Fintype n]
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) (C : Matrix n o ℝ) (i : l) (j : o) :
    (A * B * C) i j = (fun a => A i a) ⬝ᵥ (B *ᵥ fun k => C k j) := by
  simp only [Matrix.mul_apply, sum_mul, mul_assoc, dotProduct, mulVec, mul_sum]
  exact Finset.sum_comm

/--
@isnad1 id=eq.0h8v.s7.aca1a0030997 from=translated src=- shape=45269778 vocab=ea38821e
-/
lemma elimGramE_y_y (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (j ℓ : Fin p) :
    elimGramE s t ρ x (idxY j) (idxY ℓ) =
      (elimTE s t ρ x * (elimEE s t ρ x)⁻¹ * elimET s t ρ x) j ℓ := by
  have hL : elimColE s t ρ x (idxY j) = fun i => elimTE s t ρ x j i := rfl
  have hR : elimColE s t ρ x (idxY ℓ) = fun i => elimET s t ρ x i ℓ := by
    funext i
    exact (MX_isSymm s t ρ x).apply _ _
  simp only [elimGramE]
  rw [hL, hR]
  exact (mul_mul_col_apply (elimTE s t ρ x) (elimEE s t ρ x)⁻¹
    (elimET s t ρ x) j ℓ).symm

/-- EL13: `M = C₀ + extendByZero R` with `R` the `T`-Schur complement of `E`.
@isnad1 id=eq.4h6v.s7.f0bea64c88d9 from=translated src=- shape=b2b96fbf vocab=1d198fbc
-/
lemma M_eq_elimGramE_add_extend (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    M (Xconfig s t ρ x) =
      elimGramE s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x) := by
  ext α β
  refine elim_configIdx_cases
      (P := fun α =>
        M (Xconfig s t ρ x) α β =
          (elimGramE s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x)) α β)
      α ?_ ?_ ?_
  · refine elim_configIdx_cases
        (P := fun β =>
          M (Xconfig s t ρ x) idxZ0 β =
            (elimGramE s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x))
              idxZ0 β)
        β ?_ ?_ ?_
    · change M (Xconfig s t ρ x) idxZ0 idxZ0 =
          elimGramE s t ρ x idxZ0 idxZ0 +
            extendByZeroT (k := k) (elimSchurR s t ρ x) idxZ0 idxZ0
      rw [extendByZeroT_z0_left, add_zero]
      calc
        M (Xconfig s t ρ x) idxZ0 idxZ0
            = elimEE s t ρ x none none := (elimEE_none_none s t ρ x).symm
        _ = elimGramE s t ρ x (elimEEmbed none) (elimEEmbed none) :=
            (elimGramE_embed s t ρ x hs ht hρ hx none none).symm
        _ = elimGramE s t ρ x idxZ0 idxZ0 := by
            rw [elimEEmbed_none]
    · intro i
      change M (Xconfig s t ρ x) idxZ0 (idxZ i) =
          elimGramE s t ρ x idxZ0 (idxZ i) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) idxZ0 (idxZ i)
      rw [extendByZeroT_z_right, add_zero]
      calc
        M (Xconfig s t ρ x) idxZ0 (idxZ i)
            = 0 := MX_z0_z s t ρ x i
        _ = elimEE s t ρ x none (some i) := (elimEE_none_some s t ρ x i).symm
        _ = elimGramE s t ρ x (elimEEmbed none) (elimEEmbed (some i)) :=
            (elimGramE_embed s t ρ x hs ht hρ hx none (some i)).symm
        _ = elimGramE s t ρ x idxZ0 (idxZ i) := by
            rw [elimEEmbed_none, elimEEmbed_some]
    · intro ℓ
      change M (Xconfig s t ρ x) idxZ0 (idxY ℓ) =
          elimGramE s t ρ x idxZ0 (idxY ℓ) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) idxZ0 (idxY ℓ)
      rw [extendByZeroT_z0_left, add_zero]
      calc
        M (Xconfig s t ρ x) idxZ0 (idxY ℓ)
            = elimET s t ρ x none ℓ := rfl
        _ = elimGramE s t ρ x (elimEEmbed none) (idxY ℓ) :=
            (elimGramE_embed_y s t ρ x hs ht hρ hx none ℓ).symm
        _ = elimGramE s t ρ x idxZ0 (idxY ℓ) := by
            rw [elimEEmbed_none]
  · intro i
    refine elim_configIdx_cases
        (P := fun β =>
          M (Xconfig s t ρ x) (idxZ i) β =
            (elimGramE s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x))
              (idxZ i) β)
        β ?_ ?_ ?_
    · change M (Xconfig s t ρ x) (idxZ i) idxZ0 =
          elimGramE s t ρ x (idxZ i) idxZ0 +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxZ i) idxZ0
      rw [extendByZeroT_z0_right, add_zero]
      calc
        M (Xconfig s t ρ x) (idxZ i) idxZ0
            = 0 := MX_z_z0 s t ρ x i
        _ = elimEE s t ρ x (some i) none := (elimEE_some_none s t ρ x i).symm
        _ = elimGramE s t ρ x (elimEEmbed (some i)) (elimEEmbed none) :=
            (elimGramE_embed s t ρ x hs ht hρ hx (some i) none).symm
        _ = elimGramE s t ρ x (idxZ i) idxZ0 := by
            rw [elimEEmbed_some, elimEEmbed_none]
    · intro h
      change M (Xconfig s t ρ x) (idxZ i) (idxZ h) =
          elimGramE s t ρ x (idxZ i) (idxZ h) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxZ i) (idxZ h)
      rw [extendByZeroT_z_right, add_zero]
      calc
        M (Xconfig s t ρ x) (idxZ i) (idxZ h)
            = elimEE s t ρ x (some i) (some h) :=
              (elimEE_some_some s t ρ x i h).symm
        _ = elimGramE s t ρ x (elimEEmbed (some i)) (elimEEmbed (some h)) :=
            (elimGramE_embed s t ρ x hs ht hρ hx (some i) (some h)).symm
        _ = elimGramE s t ρ x (idxZ i) (idxZ h) := by
            rw [elimEEmbed_some, elimEEmbed_some]
    · intro ℓ
      change M (Xconfig s t ρ x) (idxZ i) (idxY ℓ) =
          elimGramE s t ρ x (idxZ i) (idxY ℓ) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxZ i) (idxY ℓ)
      rw [extendByZeroT_z_left, add_zero]
      calc
        M (Xconfig s t ρ x) (idxZ i) (idxY ℓ)
            = elimET s t ρ x (some i) ℓ := rfl
        _ = elimGramE s t ρ x (elimEEmbed (some i)) (idxY ℓ) :=
            (elimGramE_embed_y s t ρ x hs ht hρ hx (some i) ℓ).symm
        _ = elimGramE s t ρ x (idxZ i) (idxY ℓ) := by
            rw [elimEEmbed_some]
  · intro j
    refine elim_configIdx_cases
        (P := fun β =>
          M (Xconfig s t ρ x) (idxY j) β =
            (elimGramE s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x))
              (idxY j) β)
        β ?_ ?_ ?_
    · change M (Xconfig s t ρ x) (idxY j) idxZ0 =
          elimGramE s t ρ x (idxY j) idxZ0 +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxY j) idxZ0
      rw [extendByZeroT_z0_right, add_zero]
      calc
        M (Xconfig s t ρ x) (idxY j) idxZ0
            = elimTE s t ρ x j none := rfl
        _ = elimGramE s t ρ x (idxY j) (elimEEmbed none) :=
            (elimGramE_y_embed s t ρ x hs ht hρ hx j none).symm
        _ = elimGramE s t ρ x (idxY j) idxZ0 := by
            rw [elimEEmbed_none]
    · intro h
      change M (Xconfig s t ρ x) (idxY j) (idxZ h) =
          elimGramE s t ρ x (idxY j) (idxZ h) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxY j) (idxZ h)
      rw [extendByZeroT_z_right, add_zero]
      calc
        M (Xconfig s t ρ x) (idxY j) (idxZ h)
            = elimTE s t ρ x j (some h) := rfl
        _ = elimGramE s t ρ x (idxY j) (elimEEmbed (some h)) :=
            (elimGramE_y_embed s t ρ x hs ht hρ hx j (some h)).symm
        _ = elimGramE s t ρ x (idxY j) (idxZ h) := by
            rw [elimEEmbed_some]
    · intro ℓ
      change M (Xconfig s t ρ x) (idxY j) (idxY ℓ) =
          elimGramE s t ρ x (idxY j) (idxY ℓ) +
            extendByZeroT (k := k) (elimSchurR s t ρ x) (idxY j) (idxY ℓ)
      rw [extendByZeroT_y_y, elimGramE_y_y s t ρ x]
      simp [elimSchurR, elimTT, submatrix_apply, elimT, Matrix.sub_apply]

/--
@isnad1 id=eq.4h6v.s7.0102fa03eed1 from=translated src=- shape=b2b96fbf vocab=41823c00
-/
lemma M_eq_elimC0_add_extend (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j)
    (hx : ∀ j, 0 ≤ x j) :
    M (Xconfig s t ρ x) =
      elimC0 s t ρ x + extendByZeroT (k := k) (elimSchurR s t ρ x) := by
  rw [elimC0_eq_elimGramE s t ρ x hs ht hρ hx,
    M_eq_elimGramE_add_extend s t ρ x hs ht hρ hx]

end

end BollobasNikiforov
