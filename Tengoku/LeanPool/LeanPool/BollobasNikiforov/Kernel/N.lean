/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Tengoku.LeanPool.LeanPool.BollobasNikiforov.Kernel.Data
public import Tengoku.LeanPool.LeanPool.BollobasNikiforov.TN.Convex
public import Tengoku

/-!
# Nonnegativity of `N`

The identity `N = det(I + Q W)` of `docs/sol.tex` §3, the factorization of
`W` through two totally nonnegative three-column matrices, and `1 ≤ N x`
for `x ≥ 0`.
-/

@[expose] public section

namespace BollobasNikiforov

open Function Matrix Set
open scoped Matrix

noncomputable section

/-! ### KR18: auxiliary matrix `D(x)` -/

/-- The matrix with columns `c₀, c₁, c₂`. -/
def fromThreeCols (c0 c1 c2 : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if j = 0 then c0 i else if j = 1 then c1 i else c2 i

/--
@isnad1 id=eq.0h4v.s5.9e966e607f3c from=translated src=- shape=4cd2433e vocab=fa28e22c
-/
lemma fromThreeCols_apply_zero (c0 c1 c2 : Fin 3 → ℝ) (i : Fin 3) :
    fromThreeCols c0 c1 c2 i 0 = c0 i := rfl

/--
@isnad1 id=eq.0h4v.s5.404f8305d3ea from=translated src=- shape=3a0f3e41 vocab=fa28e22c
-/
lemma fromThreeCols_apply_one (c0 c1 c2 : Fin 3 → ℝ) (i : Fin 3) :
    fromThreeCols c0 c1 c2 i 1 = c1 i := rfl

/--
@isnad1 id=eq.0h4v.s5.98582272eed0 from=translated src=- shape=24eadc05 vocab=fa28e22c
-/
lemma fromThreeCols_apply_two (c0 c1 c2 : Fin 3 → ℝ) (i : Fin 3) :
    fromThreeCols c0 c1 c2 i 2 = c2 i := rfl

/--
@isnad1 id=eq.0h6v.s8.04709ebce4a7 from=translated src=- shape=5a019c2f vocab=87e95f33
-/
lemma fromThreeCols_add (u0 u1 u2 v0 v1 v2 : Fin 3 → ℝ) :
    fromThreeCols (u0 + v0) (u1 + v1) (u2 + v2) =
      fromThreeCols u0 u1 u2 + fromThreeCols v0 v1 v2 := by
  ext i j
  fin_cases j <;> simp [fromThreeCols, Matrix.add_apply]

/--
@isnad1 id=eq.0h4v.s7.c49eabedc68a from=translated src=- shape=8a087623 vocab=7141ac11
-/
lemma fromThreeCols_smul (c : ℝ) (u0 u1 u2 : Fin 3 → ℝ) :
    fromThreeCols (c • u0) (c • u1) (c • u2) = c • fromThreeCols u0 u1 u2 := by
  ext i j
  fin_cases j <;> simp [fromThreeCols, Matrix.smul_apply]

/--
@isnad1 id=eq.0h5v.s7.587b9d0e8f4f from=translated src=- shape=65addaf5 vocab=26a8d194
-/
lemma fromThreeCols_sum {ι : Type*} (s : Finset ι)
    (f0 f1 f2 : ι → Fin 3 → ℝ) :
    fromThreeCols (∑ i ∈ s, f0 i) (∑ i ∈ s, f1 i) (∑ i ∈ s, f2 i) =
      ∑ i ∈ s, fromThreeCols (f0 i) (f1 i) (f2 i) := by
  ext a b
  fin_cases b <;> simp [fromThreeCols, Matrix.sum_apply]

/-- `D(x)` has columns `e₀, e₁, b(x)`. -/
def D (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fromThreeCols (Pi.single 0 1) (Pi.single 1 1) (b x)

/--
@isnad1 id=eq.0h1v.s5.04145d1faa4f from=translated src=- shape=548109e9 vocab=27a8bf7f
-/
lemma det_D (x : ℝ) : (D x).det = 1 := by
  rw [det_fin_three]
  simp [D, fromThreeCols, b]

/--
@isnad1 id=isunit.0h1v.s4.5fd012059105 from=translated src=- shape=a95ca5c6 vocab=9f847e7b
-/
lemma D_isUnit (x : ℝ) : IsUnit (D x).det := by
  simp [det_D]

/-- Explicit inverse of the upper-triangular unipotent matrix `D x`. -/
def Dinv (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, -x ^ 2; 0, 1, -Real.sqrt 2 * x; 0, 0, 1]

/--
@isnad1 id=eq.0h1v.s7.95f0ff5c7ff6 from=translated src=- shape=432bb48e vocab=6561e5f3
-/
lemma D_mul_Dinv (x : ℝ) : D x * Dinv x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [D, Dinv, fromThreeCols, b, mul_apply, Fin.sum_univ_three, one_apply]

/--
@isnad1 id=eq.0h1v.s5.1a9cc6ebd2dd from=translated src=- shape=cfe8a7d9 vocab=ac34c9c1
-/
lemma D_inv (x : ℝ) : (D x)⁻¹ = Dinv x :=
  inv_eq_right_inv (D_mul_Dinv x)

/-! ### Feature columns `cᵢ(x)` -/

/-- `cᵢ(x) = (1, -√2 tᵢ, aᵢ(x))ᵀ`. -/
def cVec (ti x : ℝ) : Fin 3 → ℝ :=
  ![1, -Real.sqrt 2 * ti, truncSq ti x]

/--
@isnad1 id=eq.0h2v.s4.a0e67d09ba75 from=translated src=- shape=c8bf5ce2 vocab=3aa850e2
-/
@[simp] lemma cVec_zero (ti x : ℝ) : cVec ti x 0 = 1 := by simp [cVec]
/--
@isnad1 id=eq.0h2v.s5.7f7708cdc69e from=translated src=- shape=3ec0900f vocab=11a3c84c
-/
@[simp] lemma cVec_one (ti x : ℝ) : cVec ti x 1 = -Real.sqrt 2 * ti := by simp [cVec]
/--
@isnad1 id=eq.0h2v.s4.bbd9c2c31177 from=translated src=- shape=27d07ba1 vocab=f62d8728
-/
@[simp] lemma cVec_two (ti x : ℝ) : cVec ti x 2 = truncSq ti x := by
  simp [cVec, cons_val_two, vecHead, vecTail]

/--
@isnad1 id=eq.0h2v.s7.12b581bb0e7a from=translated src=- shape=e6f12149 vocab=6795045b
-/
lemma vecMulVec_eq_fromThreeCols (u v : Fin 3 → ℝ) :
    vecMulVec u v = fromThreeCols (v 0 • u) (v 1 • u) (v 2 • u) := by
  ext i j
  fin_cases j <;> simp [vecMulVec_apply, fromThreeCols, smul_eq_mul, mul_comm]

variable {k : ℕ} (t : Fin k → ℝ) (q : Fin k → ℝ)

/-! ### KR19: Cramer for `N` -/

/--
@isnad1 id=eq.0h2v.s7.47bf70bfebdc from=translated src=- shape=0d16bd45 vocab=82478a84
-/
lemma updateCol_two_eq_fromThreeCols (A : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) :
    A.updateCol 2 w =
      fromThreeCols (A *ᵥ Pi.single 0 1) (A *ᵥ Pi.single 1 1) w := by
  ext i j
  rw [updateCol_apply]
  fin_cases j
  · simp [fromThreeCols, col_apply]
  · simp [fromThreeCols, col_apply]
  · simp [fromThreeCols]

/--
@isnad1 id=eq.1h4v.s7.3c49150d827d from=translated src=- shape=0bd1b371 vocab=22a484ba
-/
lemma N_eq_det_fromThreeCols (hq : ∀ i, 0 < q i) (x : ℝ) :
    N t q x =
      (fromThreeCols (𝒜 t q *ᵥ Pi.single 0 1) (𝒜 t q *ᵥ Pi.single 1 1)
        (bhat t q x)).det := by
  have hA : IsUnit (𝒜 t q).det := (isUnit_iff_isUnit_det _).mp (𝒜_isUnit t q hq)
  have hcramer := det_smul_inv_mulVec_eq_cramer (𝒜 t q) (bhat t q x) hA
  unfold N Δ
  have hsmul :
      (𝒜 t q).det * ((𝒜 t q)⁻¹ *ᵥ bhat t q x) 2 =
        ((𝒜 t q).det • (𝒜 t q)⁻¹ *ᵥ bhat t q x) 2 := by
    rw [Pi.smul_apply, smul_eq_mul]
  rw [hsmul, hcramer, cramer_apply, updateCol_two_eq_fromThreeCols]

/--
@isnad1 id=eq.0h3v.s8.4b4ac7a5a87c from=translated src=- shape=9ba25d60 vocab=8b2848eb
-/
lemma 𝒜_mulVec_single_zero :
    𝒜 t q *ᵥ Pi.single 0 1 =
      Pi.single 0 1 + ∑ i, q i • v (t i) := by
  unfold 𝒜
  rw [add_mulVec, one_mulVec, sum_mulVec]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [smul_mulVec, mulVec_vecMulVec_self, dotProduct_single, v_zero]
  simp

/--
@isnad1 id=eq.0h3v.s8.fc850c75bda9 from=translated src=- shape=2e4f36c8 vocab=a95472b9
-/
lemma 𝒜_mulVec_single_one :
    𝒜 t q *ᵥ Pi.single 1 1 =
      Pi.single 1 1 + ∑ i, (q i * (-Real.sqrt 2 * t i)) • v (t i) := by
  unfold 𝒜
  rw [add_mulVec, one_mulVec, sum_mulVec]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [smul_mulVec, mulVec_vecMulVec_self, dotProduct_single, v_one]
  simp [smul_smul, mul_comm]

/--
@isnad1 id=eq.0h4v.s8.dfa453621da2 from=translated src=- shape=000f35fe vocab=79676837
-/
lemma fromThreeCols_eq_D_add_sum (x : ℝ) :
    fromThreeCols (𝒜 t q *ᵥ Pi.single 0 1) (𝒜 t q *ᵥ Pi.single 1 1) (bhat t q x) =
      D x + ∑ i, q i • vecMulVec (v (t i)) (cVec (t i) x) := by
  have hsum :
      (∑ i, q i • vecMulVec (v (t i)) (cVec (t i) x)) =
        fromThreeCols (∑ i, q i • v (t i))
          (∑ i, (q i * (-Real.sqrt 2 * t i)) • v (t i))
          (∑ i, (q i * truncSq (t i) x) • v (t i)) := by
    ext a b
    fin_cases b <;>
      simp [fromThreeCols, Matrix.sum_apply, cVec,
        smul_eq_mul, mul_left_comm, mul_comm]
  rw [𝒜_mulVec_single_zero, 𝒜_mulVec_single_one, bhat, hsum, D, ← fromThreeCols_add]

/-! ### KR20: Sylvester `N = det(I + Q W)` -/

/-- Columns are the feature vectors `v(tⱼ)`. -/
def vCols : Matrix (Fin 3) (Fin k) ℝ :=
  fun r j => v (t j) r

/-- Rows are `qᵢ cᵢ(x)ᵀ`. -/
def qcRows (x : ℝ) : Matrix (Fin k) (Fin 3) ℝ :=
  fun i s => q i * cVec (t i) x s

/-- `W(x)ᵢⱼ = cᵢ(x)ᵀ D(x)⁻¹ v(tⱼ)`. -/
def W (x : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => cVec (t i) x ⬝ᵥ (D x)⁻¹ *ᵥ v (t j)

/--
@isnad1 id=eq.0h4v.s7.c5e525908d0d from=translated src=- shape=0a9a5b1e vocab=8ba122c7
-/
lemma vCols_mul_qcRows (x : ℝ) :
    vCols t * qcRows t q x = ∑ i, q i • vecMulVec (v (t i)) (cVec (t i) x) := by
  ext a b
  simp only [mul_apply, vCols, qcRows, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/--
@isnad1 id=eq.0h4v.s7.cd76761f968d from=translated src=- shape=d75a6404 vocab=c055b108
-/
lemma qcRows_mul_invD_vCols (x : ℝ) :
    qcRows t q x * (D x)⁻¹ * vCols t = diagonal q * W t x := by
  rw [Matrix.mul_assoc]
  ext i j
  have hv (s : Fin 3) : ((D x)⁻¹ * vCols t) s j = ((D x)⁻¹ *ᵥ v (t j)) s := by
    simp [mul_apply, vCols, mulVec, dotProduct]
  have hR : (diagonal q * W t x) i j = q i * W t x i j := by
    simp only [mul_apply, diagonal_apply]
    rw [Fintype.sum_eq_single i]
    · simp
    · intro k hk
      simp [Ne.symm hk]
  rw [hR, mul_apply]
  simp only [qcRows, hv, W, dotProduct]
  simp [mul_assoc, Finset.mul_sum]

/--
@isnad1 id=eq.1h4v.s7.ab1d9ad9dcd1 from=translated src=- shape=69eb500a vocab=800f8f49
-/
lemma N_eq_det_one_add (hq : ∀ i, 0 < q i) (x : ℝ) :
    N t q x = (1 + diagonal q * W t x).det := by
  have hD : IsUnit (D x).det := D_isUnit x
  rw [N_eq_det_fromThreeCols t q hq x, fromThreeCols_eq_D_add_sum,
    ← vCols_mul_qcRows]
  rw [det_add_mul (vCols t) (qcRows t q x) hD, det_D, one_mul]
  rw [qcRows_mul_invD_vCols]

/-! ### KR21: formula for `W` -/

/-- Paper `f_x(t) = t² - (t-x)₊²`. -/
def fKernel (x t : ℝ) : ℝ :=
  t ^ 2 - (max (t - x) 0) ^ 2

/--
@isnad1 id=eq.1h2v.s5.fb5425a08d62 from=translated src=- shape=10ad78f3 vocab=c442618f
-/
lemma fKernel_eq_sq {x t : ℝ} (htx : t ≤ x) : fKernel x t = t ^ 2 := by
  unfold fKernel
  have : max (t - x) 0 = 0 := max_eq_right (sub_nonpos.mpr htx)
  rw [this]
  ring

/--
@isnad1 id=eq.1h2v.s6.01aaee31ab4e from=translated src=- shape=eebc67e4 vocab=443548b1
-/
lemma fKernel_eq_linear {x t : ℝ} (hxt : x ≤ t) :
    fKernel x t = 2 * x * t - x ^ 2 := by
  unfold fKernel
  have : max (t - x) 0 = t - x := max_eq_left (sub_nonneg.mpr hxt)
  rw [this]
  ring

/--
@isnad1 id=eq.0h2v.s6.a77ee7897a49 from=translated src=- shape=7019be4e vocab=34400d24
-/
lemma fKernel_eq_trunc (ti x : ℝ) :
    fKernel x ti = 2 * ti * x - x ^ 2 + truncSq ti x := by
  rcases le_total ti x with htx | hxt
  · rw [fKernel_eq_sq htx]
    have : truncSq ti x = (x - ti) ^ 2 := by
      simp [truncSq, max_eq_left (sub_nonneg.mpr htx)]
    rw [this]
    ring
  · rw [fKernel_eq_linear hxt]
    have : truncSq ti x = 0 := by
      simp [truncSq, max_eq_right (sub_nonpos.mpr hxt)]
    rw [this]
    ring

/--
@isnad1 id=eq.0h2v.s7.bec93b523071 from=translated src=- shape=10dff220 vocab=ac22273f
-/
lemma Dinv_mulVec_v (x tj : ℝ) :
    Dinv x *ᵥ v tj =
      ![1 - x ^ 2 * tj ^ 2, -Real.sqrt 2 * tj - Real.sqrt 2 * x * tj ^ 2, tj ^ 2] := by
  ext i
  fin_cases i <;>
    simp [Dinv, mulVec, dotProduct, Fin.sum_univ_three, v] <;> ring

/--
@isnad1 id=eq.0h5v.s6.dd17b5b8a40d from=translated src=- shape=2a83a4ae vocab=58aa7289
-/
lemma W_apply (x : ℝ) (i j : Fin k) :
    W t x i j = 1 + 2 * t i * t j + fKernel x (t i) * t j ^ 2 := by
  unfold W
  rw [D_inv, Dinv_mulVec_v]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [dotProduct, Fin.sum_univ_three, cVec_zero, cVec_one, cVec_two]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, neg_mul, Fin.isValue, cons_val_zero, one_mul,
    cons_val_one, cons_val_two, vecHead, vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    cons_val_fin_one]
  rw [fKernel_eq_trunc]
  ring_nf
  simp
  ring

/-! ### KR22: convexity of `fKernel x` -/

/--
@isnad1 id=eq.1h1v.s4.a1f95121f634 from=translated src=- shape=cb752352 vocab=5692154a
-/
lemma fKernel_zero {x : ℝ} (hx : 0 ≤ x) : fKernel x 0 = 0 := by
  unfold fKernel
  have : max (0 - x) 0 = 0 := max_eq_right (sub_nonpos.mpr hx)
  rw [this]
  simp

/--
@isnad1 id=le.2h2v.s5.618e9221068e from=translated src=- shape=6c67d60b vocab=5692154a
-/
lemma fKernel_nonneg {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) : 0 ≤ fKernel x t := by
  rcases le_total t x with htx | hxt
  · rw [fKernel_eq_sq htx]
    exact sq_nonneg _
  · rw [fKernel_eq_linear hxt]
    nlinarith

/--
@isnad1 id=convexon.0h1v.s4.0b1e5a3503c1 from=translated src=- shape=067e64ef vocab=613dd845
-/
lemma fKernel_convexOn (x : ℝ) :
    ConvexOn ℝ (Ici (0 : ℝ)) (fKernel x) := by
  refine convexOn_of_slope_mono_adjacent (convex_Ici 0) ?_
  intro a b c ha hc hab hbc
  have ha0 : 0 ≤ a := mem_Ici.mp ha
  have hab0 : 0 < b - a := sub_pos.mpr hab
  have hbc0 : 0 < c - b := sub_pos.mpr hbc
  rw [div_le_div_iff₀ hab0 hbc0]
  rcases le_or_gt c x with hcx | hxc
  · have hax : a ≤ x := hab.le.trans (hbc.le.trans hcx)
    have hbx : b ≤ x := hbc.le.trans hcx
    rw [fKernel_eq_sq hax, fKernel_eq_sq hbx, fKernel_eq_sq hcx]
    have hL : (b ^ 2 - a ^ 2) * (c - b) = (b - a) * (c - b) * (a + b) := by ring
    have hR : (c ^ 2 - b ^ 2) * (b - a) = (b - a) * (c - b) * (b + c) := by ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hab0.le hbc0.le)
  · rcases le_or_gt x a with hxa | hax
    · have hxb : x ≤ b := hxa.trans hab.le
      have hxc' : x ≤ c := hxa.trans (hab.le.trans hbc.le)
      rw [fKernel_eq_linear hxa, fKernel_eq_linear hxb, fKernel_eq_linear hxc']
      ring_nf
      nlinarith
    · rcases le_or_gt b x with hbx | hxb
      · have hax' : a ≤ x := hax.le
        rw [fKernel_eq_sq hax', fKernel_eq_sq hbx, fKernel_eq_linear hxc.le]
        have hL : (b ^ 2 - a ^ 2) * (c - b) = (b - a) * (a + b) * (c - b) := by ring
        rw [hL]
        have hcancel : (a + b) * (c - b) ≤ 2 * x * c - x ^ 2 - b ^ 2 := by
          have hneg : a + b - 2 * x ≤ 0 := by nlinarith
          have hcmp : (a + b - 2 * x) * c ≤ (a + b - 2 * x) * x :=
            mul_le_mul_of_nonpos_left hxc.le hneg
          nlinarith [sq_nonneg (x - a), sq_nonneg (x - b), hcmp]
        have h1 : (b - a) * (a + b) * (c - b) =
            (b - a) * ((a + b) * (c - b)) := by ring
        have h2 : (2 * x * c - x ^ 2 - b ^ 2) * (b - a) =
            (b - a) * (2 * x * c - x ^ 2 - b ^ 2) := by ring
        rw [h1, h2]
        exact mul_le_mul_of_nonneg_left hcancel hab0.le
      · have hax' : a ≤ x := hax.le
        have hxc' : x ≤ c := hxb.le.trans hbc.le
        rw [fKernel_eq_sq hax', fKernel_eq_linear hxb.le, fKernel_eq_linear hxc']
        nlinarith [sq_nonneg (x - a)]

/-! ### KR23: two 3-column TN matrices -/

/--
@isnad1 id=istotall.2h4v.s6.d14f7341320b from=translated src=- shape=f9511631 vocab=fe9c1127
-/
lemma IsTotallyNonneg.mul_diagonal {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    [Fintype κ] [DecidableEq κ] {A : Matrix ι κ ℝ}
    (hA : IsTotallyNonneg A) {d : κ → ℝ} (hd : ∀ j, 0 ≤ d j) :
    IsTotallyNonneg (A * diagonal d) := by
  intro r I J hI hJ
  have hmat : (A * diagonal d).submatrix I J =
      A.submatrix I J * diagonal (d ∘ J) := by
    ext a b
    simp [submatrix_apply, mul_apply, diagonal_apply]
  rw [hmat, det_mul, det_diagonal]
  exact mul_nonneg (hA r I J hI hJ) (Finset.prod_nonneg fun _ _ ↦ hd _)

/-- Rows `(1, tᵢ, fₓ(tᵢ))`. -/
def fKernelRows (x : ℝ) : Matrix (Fin k) (Fin 3) ℝ :=
  convexRowMatrix (fKernel x) t

/-- Rows `(1, 2 tᵢ, tᵢ²)`. -/
def sqRows : Matrix (Fin k) (Fin 3) ℝ :=
  fun i j => (![1, 2 * t i, t i ^ 2] : Fin 3 → ℝ) j

/--
@isnad1 id=istotall.3h3v.s6.92a52a88352a from=translated src=- shape=9b59b300 vocab=9b82b187
-/
lemma isTotallyNonneg_fKernelRows (x : ℝ) (hx : 0 ≤ x)
    (htmono : Monotone t) (htpos : ∀ i, 0 < t i) :
    IsTotallyNonneg (fKernelRows t x) :=
  isTotallyNonneg_convexRowMatrix (fKernel_convexOn x) (fKernel_zero hx)
    (fun _s hs ↦ fKernel_nonneg hx hs) htmono htpos

/--
@isnad1 id=eq.0h2v.s7.b1fe2f162c45 from=translated src=- shape=a82fcf53 vocab=8c9ddaff
-/
lemma sqRows_eq_scale :
    sqRows t =
      convexRowMatrix (fun s : ℝ ↦ s ^ 2) t * diagonal (![(1 : ℝ), 2, 1]) := by
  ext i j
  simp only [sqRows, convexRowMatrix, mul_apply, diagonal_apply, Fin.sum_univ_three]
  fin_cases j <;> simp [row3, cons_val_zero, cons_val_one, cons_val_two, vecHead, vecTail, mul_comm]

/--
@isnad1 id=istotall.2h2v.s5.73fede08adc3 from=translated src=- shape=4456dadb vocab=a06bff7e
-/
lemma isTotallyNonneg_sqRows (htmono : Monotone t) (htpos : ∀ i, 0 < t i) :
    IsTotallyNonneg (sqRows t) := by
  have hTN := isTotallyNonneg_convexRowMatrix (f := fun s : ℝ ↦ s ^ 2)
    (convexOn_pow 2) (by simp) (fun s _ ↦ sq_nonneg s) htmono htpos
  have hd : ∀ j : Fin 3, 0 ≤ (![(1 : ℝ), 2, 1]) j := by
    intro j; fin_cases j <;> norm_num
  rw [sqRows_eq_scale]
  exact hTN.mul_diagonal hd

/-! ### KR24: `W` is TN -/

/--
@isnad1 id=eq.0h3v.s6.e31733fcc65f from=translated src=- shape=ac6b4104 vocab=6abd49eb
-/
lemma W_eq_mul_transpose (x : ℝ) :
    W t x = fKernelRows t x * (sqRows t)ᵀ := by
  ext i j
  simp only [W_apply, fKernelRows, sqRows, convexRowMatrix, mul_apply, transpose_apply,
    Fin.sum_univ_three, row3_zero, row3_one, row3_two]
  simp [cons_val_zero, cons_val_one, cons_val_two, vecHead, vecTail]
  ring

/--
@isnad1 id=istotall.3h3v.s5.cdada7a1d48a from=translated src=- shape=25faf7c1 vocab=cd502dc2
-/
lemma W_isTotallyNonneg (x : ℝ) (hx : 0 ≤ x)
    (htmono : Monotone t) (htpos : ∀ i, 0 < t i) :
    IsTotallyNonneg (W t x) := by
  rw [W_eq_mul_transpose]
  exact (isTotallyNonneg_fKernelRows t x hx htmono htpos).mul_transpose
    (isTotallyNonneg_sqRows t htmono htpos)

/-! ### KR25: `1 ≤ N` -/

/--
@isnad1 id=eq.0h3v.s8.df6ff58acf30 from=translated src=- shape=f4c410e9 vocab=dd2acdca
-/
lemma det_one_add_diagonal_mul {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (M : Matrix n n ℝ) :
    (1 + diagonal d * M).det =
      ∑ s : Finset n, (∏ i ∈ s, d i) *
        (M.submatrix (↑) (↑) : Matrix s s ℝ).det := by
  let Dalt := (detRowAlternating : (n → ℝ) [⋀^n]→ₗ[ℝ] ℝ)
  have hrows :
      (fun i ↦ (1 + diagonal d * M) i) =
        (fun i ↦ d i • M i) + fun i ↦ (1 : Matrix n n ℝ) i := by
    ext i j
    simp only [Matrix.add_apply, Matrix.one_apply, mul_apply]
    have hsum : ∑ x, diagonal d i x * M x j = d i * M i j := by
      rw [Fintype.sum_eq_single i]
      · simp
      · intro x hx
        simp [hx.symm]
    rw [hsum]
    simp [Pi.add_apply, Matrix.one_apply, smul_eq_mul]
    ring
  have hdetEq : det (1 + diagonal d * M) = Dalt (fun i ↦ (1 + diagonal d * M) i) := rfl
  rw [hdetEq, hrows, Dalt.map_add_univ]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hsmul :
      s.piecewise (fun i ↦ d i • M i) (fun i ↦ (1 : Matrix n n ℝ) i) =
        fun i ↦ (if i ∈ s then d i else (1 : ℝ)) •
          s.piecewise (fun i ↦ M i) (fun i ↦ (1 : Matrix n n ℝ) i) i := by
    funext i
    by_cases hi : i ∈ s <;> simp [hi, Finset.piecewise]
  rw [hsmul, Dalt.map_smul_univ]
  have hprod : (∏ i, if i ∈ s then d i else (1 : ℝ)) = ∏ i ∈ s, d i := by
    rw [Finset.prod_ite]
    simp [Finset.prod_const_one]
  simp only [smul_eq_mul, hprod]
  have hdet := det_piecewise_one_eq_submatrix_det M s
  have hmat :
      (s.piecewise (fun i ↦ M i) (fun i ↦ (1 : Matrix n n ℝ) i) : Matrix n n ℝ) =
        of (s.piecewise M.row (1 : Matrix n n ℝ).row) := by
    ext i j
    simp [Finset.piecewise, Matrix.row]
  rw [hmat]
  have hDalt : Dalt (of (s.piecewise M.row (1 : Matrix n n ℝ).row)) =
      (of (s.piecewise M.row (1 : Matrix n n ℝ).row)).det := rfl
  rw [hDalt, hdet]

/--
@isnad1 id=le.1h3v.s7.b3fd5f2966d6 from=translated src=- shape=663b1dcc vocab=a732b032
-/
lemma IsTotallyNonneg.det_principal {n : Type*} [LinearOrder n]
    {A : Matrix n n ℝ} (hA : IsTotallyNonneg A) (s : Finset n) :
    0 ≤ (A.submatrix (↑) (↑) : Matrix s s ℝ).det := by
  classical
  let e := s.orderIsoOfFin rfl
  have hmono : StrictMono (Subtype.val ∘ e) :=
    (Subtype.strictMono_coe _).comp e.strictMono
  have hmat :
      ((A.submatrix (↑) (↑) : Matrix s s ℝ).submatrix e.toEquiv e.toEquiv) =
        A.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e) := by
    ext
    simp [submatrix_apply]
  rw [← det_submatrix_equiv_self e.toEquiv]
  rw [hmat]
  exact hA _ _ _ hmono hmono

/--
@isnad1 id=le.4h4v.s6.32a1d128fecf from=translated src=- shape=f685d990 vocab=3b8aae45
-/
lemma N_ge_one (x : ℝ) (hq : ∀ i, 0 < q i) (hx : 0 ≤ x)
    (htmono : Monotone t) (htpos : ∀ i, 0 < t i) :
    1 ≤ N t q x := by
  rw [N_eq_det_one_add t q hq x, det_one_add_diagonal_mul]
  have hW := W_isTotallyNonneg t x hx htmono htpos
  have hnn : ∀ s : Finset (Fin k),
      0 ≤ (∏ i ∈ s, q i) * ((W t x).submatrix (↑) (↑) : Matrix s s ℝ).det := by
    intro s
    exact mul_nonneg (Finset.prod_nonneg fun i _ ↦ (hq i).le) (hW.det_principal s)
  have hempty :
      (∏ i ∈ (∅ : Finset (Fin k)), q i) *
          ((W t x).submatrix (↑) (↑) :
            Matrix {x : Fin k // x ∈ (∅ : Finset (Fin k))}
              {x : Fin k // x ∈ (∅ : Finset (Fin k))} ℝ).det = 1 := by
    simp [det_isEmpty]
  exact hempty.symm.trans_le
    (Finset.single_le_sum (fun s _ ↦ hnn s) (Finset.mem_univ ∅))

end

end BollobasNikiforov
