/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.Normed.Lp.lpSpace
import Tengoku.Seed.Analysis.Normed.Ring.InfiniteSum
import Tengoku.Seed.Analysis.LocallyConvex.SeparatingDual
import Tengoku.LanaOka.Oka.Analytic.Laurent.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Laurent series with weighted `ℓ¹` coefficients

Fix `σ ≥ 1`. An element `a` of `ℓ¹(ℤ, V)` (`Laurent.L1 V`) represents the Laurent series
`∑ⱼ aⱼ σ^{-|j|} wʲ`, with coefficients `Laurent.L1.coeff σ a j = σ^{-|j|} aⱼ`. The series converges
absolutely on the closed annulus `σ⁻¹ ≤ ‖w‖ ≤ σ`, and `‖a‖ = ∑ⱼ σ^{|j|} ‖coeff σ a j‖`. Since
`σ^{|i + j|} ≤ σ^{|i|} σ^{|j|}`, the Cauchy product of Laurent series is a bounded bilinear map, and
the projections onto the terms of degree in a set `S ⊆ ℤ` have norm at most `1`. This makes
`Laurent.L1 V` the natural Banach space for Toeplitz-type operators on Laurent series.

## Main definitions

- `Laurent.L1.coeff σ a j`: the coefficients of the Laurent series represented by `a`.
- `Laurent.L1.proj S`: the projection onto the terms of degree in `S`.
- `Laurent.L1.shift σ m`: multiplication by `wᵐ`.
- `Laurent.L1.conv σ B`: the Cauchy product with respect to a bounded bilinear map `B`.
- `Laurent.L1.eval σ w`: the sum of the Laurent series at `w`, for `σ⁻¹ ≤ ‖w‖ ≤ σ`.
- `Laurent.L1.evalNat V σ w`, `Laurent.L1.evalNeg V σ u`: the parts of nonnegative and of
  nonpositive degree, as continuous linear maps depending holomorphically on `‖w‖ < σ`, resp. on
  the coordinate `u = w⁻¹` at infinity, `‖u‖ < σ`.
- `Laurent.L1.refl`: the substitution `w ↦ w⁻¹`.

## Main results

- `Laurent.L1.coeff_conv`: the coefficients of the Cauchy product.
- `Laurent.L1.eval_conv`, `Laurent.L1.eval_shift`: evaluation is multiplicative.
- `Laurent.L1.eq_of_eval_eq`: a Laurent series is determined by its values on the unit circle.
- `Laurent.L1.coeff_conv_eq_zero_of_lt`, `Laurent.L1.coeff_conv_eq_zero_of_gt`: degree bounds
  for the Cauchy product.
- `Laurent.L1.differentiableOn_evalNat`, `Laurent.L1.eval_eq_evalNat`,
  `Laurent.L1.eval_eq_evalNeg`: the parts of nonnegative and nonpositive degree.
-/

open Set Filter Metric Complex
open scoped Topology

namespace Laurent

/-- The Banach space `ℓ¹(ℤ, V)`. For `σ ≥ 1` its element `a` represents the Laurent series
`∑ⱼ aⱼ σ^{-|j|} wʲ` (see `Laurent.L1.coeff`). -/
abbrev L1 (V : Type*) [NormedAddCommGroup V] : Type _ := lp (fun _ : ℤ ↦ V) 1

namespace L1

section Basic

variable {V : Type*} [NormedAddCommGroup V]

lemma memℓp_one_iff {f : ℤ → V} : Memℓp f 1 ↔ Summable fun j ↦ ‖f j‖ := by
  rw [memℓp_gen_iff (by norm_num)]
  simp

lemma summable_norm (a : L1 V) : Summable fun j ↦ ‖a j‖ :=
  memℓp_one_iff.1 a.2

lemma norm_eq_tsum (a : L1 V) : ‖a‖ = ∑' j, ‖a j‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp

/-- The element of `ℓ¹(ℤ, V)` with entries `f`. -/
def mk (f : ℤ → V) (hf : Summable fun j ↦ ‖f j‖) : L1 V :=
  ⟨f, memℓp_one_iff.2 hf⟩

@[simp]
lemma mk_apply (f : ℤ → V) (hf : Summable fun j ↦ ‖f j‖) (j : ℤ) : mk f hf j = f j := rfl

lemma norm_mk (f : ℤ → V) (hf : Summable fun j ↦ ‖f j‖) : ‖mk f hf‖ = ∑' j, ‖f j‖ :=
  norm_eq_tsum _

lemma norm_apply_le (a : L1 V) (j : ℤ) : ‖a j‖ ≤ ‖a‖ :=
  lp.norm_apply_le_norm (by norm_num) a j

end Basic

/-! ### Weights and coefficients -/

section Weight

/-- The weight `σ ^ |j|`. -/
def wt (σ : ℝ) (j : ℤ) : ℝ := σ ^ j.natAbs

variable {σ : ℝ}

lemma wt_pos (hσ : 0 < σ) (j : ℤ) : 0 < wt σ j := pow_pos hσ _

lemma one_le_wt (hσ : 1 ≤ σ) (j : ℤ) : 1 ≤ wt σ j := one_le_pow₀ hσ

@[simp]
lemma wt_zero : wt σ 0 = 1 := by simp [wt]

lemma wt_neg (j : ℤ) : wt σ (-j) = wt σ j := by simp [wt]

lemma wt_natCast (n : ℕ) : wt σ n = σ ^ n := by simp [wt]

lemma wt_add_le (hσ : 1 ≤ σ) (i j : ℤ) : wt σ (i + j) ≤ wt σ i * wt σ j := by
  rw [wt, wt, wt, ← pow_add]
  exact pow_le_pow_right₀ hσ (Int.natAbs_add_le i j)

lemma wt_le_wt_sub_mul (hσ : 1 ≤ σ) (j m : ℤ) : wt σ j ≤ wt σ (j - m) * wt σ m := by
  simpa using wt_add_le hσ (j - m) m

/-- If `σ⁻¹ ≤ ‖w‖ ≤ σ`, then `‖wʲ‖ ≤ σ^{|j|}`. -/
lemma norm_zpow_le_wt (hσ : 0 < σ) {w : ℂ} (h₁ : σ⁻¹ ≤ ‖w‖) (h₂ : ‖w‖ ≤ σ) (j : ℤ) :
    ‖w ^ j‖ ≤ wt σ j := by
  have hw : 0 < ‖w‖ := (inv_pos.2 hσ).trans_le h₁
  rw [norm_zpow, wt]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · simpa using pow_le_pow_left₀ hw.le h₂ n
  · rw [zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← inv_pow]
    refine pow_le_pow_left₀ (inv_nonneg.2 hw.le) ?_ n
    rw [inv_le_comm₀ hw hσ]
    exact h₁

end Weight

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {σ : ℝ}

/-- The `j`-th coefficient `σ^{-|j|} aⱼ` of the Laurent series represented by `a`. -/
noncomputable def coeff (σ : ℝ) (a : L1 V) (j : ℤ) : V := ((wt σ j : ℂ))⁻¹ • a j

lemma apply_eq_wt_smul_coeff (hσ : 0 < σ) (a : L1 V) (j : ℤ) :
    a j = (wt σ j : ℂ) • coeff σ a j := by
  rw [coeff, smul_smul, mul_inv_cancel₀ (by exact_mod_cast (wt_pos hσ j).ne'), one_smul]

lemma norm_apply_eq (hσ : 0 < σ) (a : L1 V) (j : ℤ) : ‖a j‖ = wt σ j * ‖coeff σ a j‖ := by
  rw [apply_eq_wt_smul_coeff hσ a j, norm_smul, norm_real, Real.norm_of_nonneg (wt_pos hσ j).le]

lemma norm_coeff_le (hσ : 1 ≤ σ) (a : L1 V) (j : ℤ) : ‖coeff σ a j‖ ≤ ‖a j‖ := by
  rw [norm_apply_eq (by linarith) a j]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_wt hσ j)

@[simp]
lemma coeff_add (a b : L1 V) (j : ℤ) : coeff σ (a + b) j = coeff σ a j + coeff σ b j := by
  simp [coeff, smul_add]

@[simp]
lemma coeff_sub (a b : L1 V) (j : ℤ) : coeff σ (a - b) j = coeff σ a j - coeff σ b j := by
  simp [coeff, smul_sub]

@[simp]
lemma coeff_neg (a : L1 V) (j : ℤ) : coeff σ (-a) j = -coeff σ a j := by
  simp [coeff]

@[simp]
lemma coeff_zero (j : ℤ) : coeff σ (0 : L1 V) j = 0 := by
  simp [coeff]

@[simp]
lemma coeff_smul (c : ℂ) (a : L1 V) (j : ℤ) : coeff σ (c • a) j = c • coeff σ a j := by
  simp [coeff, smul_comm c]

lemma ext_coeff (hσ : 0 < σ) {a b : L1 V} (h : ∀ j, coeff σ a j = coeff σ b j) : a = b :=
  lp.ext <| funext fun j ↦ by rw [apply_eq_wt_smul_coeff hσ a, apply_eq_wt_smul_coeff hσ b, h]

lemma norm_eq_tsum_wt (hσ : 0 < σ) (a : L1 V) : ‖a‖ = ∑' j, wt σ j * ‖coeff σ a j‖ := by
  simp only [norm_eq_tsum, norm_apply_eq hσ]

/-- The element of `ℓ¹(ℤ, V)` representing the Laurent series with coefficients `c`. -/
noncomputable def ofCoeff (hσ : 0 < σ) (c : ℤ → V) (hc : Summable fun j ↦ wt σ j * ‖c j‖) :
    L1 V :=
  mk (fun j ↦ (wt σ j : ℂ) • c j) (hc.congr fun j ↦ by
    rw [norm_smul, norm_real, Real.norm_of_nonneg (wt_pos hσ j).le])

@[simp]
lemma coeff_ofCoeff (hσ : 0 < σ) (c : ℤ → V) (hc : Summable fun j ↦ wt σ j * ‖c j‖) (j : ℤ) :
    coeff σ (ofCoeff hσ c hc) j = c j := by
  rw [coeff, ofCoeff, mk_apply, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (wt_pos hσ j).ne'),
    one_smul]

/-! ### Reindexing operators: projections and shifts -/

section Reindex

lemma summable_norm_smul_apply_equiv (e : ℤ ≃ ℤ) {c : ℤ → ℂ} {C : ℝ} (hc : ∀ j, ‖c j‖ ≤ C)
    (a : L1 V) : Summable fun j ↦ ‖c j • a (e j)‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun j ↦ (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _)))
    (((summable_norm a).comp_injective e.injective).mul_left C)

lemma tsum_norm_smul_apply_equiv_le (e : ℤ ≃ ℤ) {c : ℤ → ℂ} {C : ℝ} (hc : ∀ j, ‖c j‖ ≤ C)
    (a : L1 V) : ∑' j, ‖c j • a (e j)‖ ≤ C * ‖a‖ :=
  calc ∑' j, ‖c j • a (e j)‖ ≤ ∑' j, C * ‖a (e j)‖ :=
        Summable.tsum_le_tsum
          (fun j ↦ (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _)))
          (summable_norm_smul_apply_equiv e hc a)
          (((summable_norm a).comp_injective e.injective).mul_left C)
    _ = C * ‖a‖ := by
      rw [tsum_mul_left, norm_eq_tsum, e.tsum_eq (fun j ↦ ‖a j‖)]

variable (V)

/-- The operator `a ↦ (c j • a (e j))ⱼ`, of norm at most `C` if `‖c j‖ ≤ C` for all `j`. -/
noncomputable def reindex (e : ℤ ≃ ℤ) (c : ℤ → ℂ) (C : ℝ) (hc : ∀ j, ‖c j‖ ≤ C) :
    L1 V →L[ℂ] L1 V :=
  LinearMap.mkContinuous
    { toFun := fun a ↦ mk (fun j ↦ c j • a (e j)) (summable_norm_smul_apply_equiv e hc a)
      map_add' := fun a b ↦ lp.ext <| funext fun j ↦ by simp [smul_add]
      map_smul' := fun r a ↦ lp.ext <| funext fun j ↦ by simp [smul_comm r] }
    C fun a ↦ by
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, norm_mk] using
        tsum_norm_smul_apply_equiv_le e hc a

variable {V}

@[simp]
lemma reindex_apply (e : ℤ ≃ ℤ) (c : ℤ → ℂ) (C : ℝ) (hc : ∀ j, ‖c j‖ ≤ C) (a : L1 V) (j : ℤ) :
    reindex V e c C hc a j = c j • a (e j) := rfl

lemma norm_reindex_le (e : ℤ ≃ ℤ) (c : ℤ → ℂ) (C : ℝ) (hc : ∀ j, ‖c j‖ ≤ C) :
    ‖reindex V e c C hc‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hc 0)) fun a ↦ by
    rw [norm_eq_tsum]
    exact tsum_norm_smul_apply_equiv_le e hc a

variable (V) in
/-- The projection onto the terms of degree in `S`. -/
noncomputable def proj (S : Set ℤ) : L1 V →L[ℂ] L1 V :=
  reindex V (Equiv.refl ℤ) (S.indicator 1) 1 fun j ↦ by
    by_cases hj : j ∈ S <;> simp [hj]

lemma proj_apply (S : Set ℤ) (a : L1 V) (j : ℤ) : proj V S a j = S.indicator a j := by
  by_cases hj : j ∈ S <;> simp [proj, hj]

@[simp]
lemma coeff_proj (S : Set ℤ) (a : L1 V) (j : ℤ) :
    coeff σ (proj V S a) j = S.indicator (coeff σ a) j := by
  by_cases hj : j ∈ S <;> simp [coeff, proj_apply, hj]

lemma norm_proj_le (S : Set ℤ) : ‖proj V S‖ ≤ 1 :=
  norm_reindex_le _ _ _ _

variable (σ) in
/-- Multiplication of Laurent series by `wᵐ`. -/
noncomputable def shift [hσ : Fact (1 ≤ σ)] (m : ℤ) : L1 V →L[ℂ] L1 V :=
  reindex V (Equiv.subRight m) (fun j ↦ ((wt σ j / wt σ (j - m) : ℝ) : ℂ)) (wt σ m) fun j ↦ by
    have h0 := wt_pos (zero_lt_one.trans_le hσ.out) (j - m)
    rw [norm_real, Real.norm_of_nonneg (div_nonneg (wt_pos (by linarith [hσ.out]) j).le h0.le),
      div_le_iff₀ h0, mul_comm]
    exact wt_le_wt_sub_mul hσ.out j m

@[simp]
lemma coeff_shift [hσ : Fact (1 ≤ σ)] (m : ℤ) (a : L1 V) (j : ℤ) :
    coeff σ (shift σ m a) j = coeff σ a (j - m) := by
  have h0 : (wt σ (j - m) : ℂ) ≠ 0 := by
    exact_mod_cast (wt_pos (zero_lt_one.trans_le hσ.out) (j - m)).ne'
  have h1 : (wt σ j : ℂ) ≠ 0 := by exact_mod_cast (wt_pos (zero_lt_one.trans_le hσ.out) j).ne'
  simp only [coeff, shift, reindex_apply, Equiv.subRight_apply, smul_smul]
  congr 1
  push_cast
  field_simp

variable (V) in
/-- The substitution `w ↦ w⁻¹`, i.e. the reflection `j ↦ -j` of the degrees. -/
noncomputable def refl : L1 V →L[ℂ] L1 V :=
  reindex V (Equiv.neg ℤ) 1 1 fun j ↦ by simp

lemma refl_apply (a : L1 V) (j : ℤ) : refl V a j = a (-j) := by
  simp [refl]

@[simp]
lemma coeff_refl (a : L1 V) (j : ℤ) : coeff σ (refl V a) j = coeff σ a (-j) := by
  simp [coeff, refl, wt_neg]

end Reindex

variable [hσ : Fact (1 ≤ σ)]
/-! ### The Cauchy product -/

section Conv

variable {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup F₂]
  [NormedSpace ℂ F₂] [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]

/-- The reindexing `(m, i) ↦ (i, m - i)` of `ℤ × ℤ`. -/
def antidiagEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, p.1 - p.2)
  invFun q := (q.1 + q.2, q.1)
  left_inv p := by simp
  right_inv q := by simp

omit [NormedSpace ℂ F₁] [NormedSpace ℂ F₂] in
lemma summable_norm_mul_norm_sub (a : L1 F₁) (b : L1 F₂) :
    Summable fun p : ℤ × ℤ ↦ ‖a p.2‖ * ‖b (p.1 - p.2)‖ :=
  (antidiagEquiv.summable_iff (f := fun q : ℤ × ℤ ↦ ‖a q.1‖ * ‖b q.2‖)).2
    ((summable_norm a).mul_of_nonneg (summable_norm b) (fun _ ↦ norm_nonneg _)
      fun _ ↦ norm_nonneg _)

omit [NormedSpace ℂ F₁] [NormedSpace ℂ F₂] in
lemma tsum_tsum_norm_mul_norm_sub (a : L1 F₁) (b : L1 F₂) :
    ∑' m, ∑' i, ‖a i‖ * ‖b (m - i)‖ = ‖a‖ * ‖b‖ := by
  have h := summable_norm_mul_norm_sub a b
  rw [← h.tsum_prod' h.prod_factor]
  refine (antidiagEquiv.tsum_eq (fun q : ℤ × ℤ ↦ ‖a q.1‖ * ‖b q.2‖)).trans ?_
  rw [norm_eq_tsum, norm_eq_tsum, (summable_norm a).tsum_mul_tsum (summable_norm b)
    ((summable_norm a).mul_of_nonneg (summable_norm b) (fun _ ↦ norm_nonneg _)
      fun _ ↦ norm_nonneg _)]

variable (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃)

lemma wt_mul_norm_le (a : L1 F₁) (b : L1 F₂) (m i : ℤ) :
    wt σ m * ‖B (coeff σ a i) (coeff σ b (m - i))‖ ≤ ‖B‖ * (‖a i‖ * ‖b (m - i)‖) := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hw : wt σ m ≤ wt σ i * wt σ (m - i) := by simpa using wt_add_le hσ.out i (m - i)
  rw [norm_apply_eq h0 a, norm_apply_eq h0 b]
  calc wt σ m * ‖B (coeff σ a i) (coeff σ b (m - i))‖
      ≤ (wt σ i * wt σ (m - i)) * (‖B‖ * ‖coeff σ a i‖ * ‖coeff σ b (m - i)‖) :=
        mul_le_mul hw (B.le_opNorm₂ _ _) (norm_nonneg _)
          (mul_nonneg (wt_pos h0 _).le (wt_pos h0 _).le)
    _ = _ := by ring

lemma norm_le_of_coeff (a : L1 F₁) (b : L1 F₂) (m i : ℤ) :
    ‖B (coeff σ a i) (coeff σ b (m - i))‖ ≤ ‖B‖ * (‖a i‖ * ‖b (m - i)‖) :=
  (le_mul_of_one_le_left (norm_nonneg _) (one_le_wt hσ.out m)).trans (wt_mul_norm_le B a b m i)

lemma summable_norm_convTerm (a : L1 F₁) (b : L1 F₂) (m : ℤ) :
    Summable fun i ↦ ‖B (coeff σ a i) (coeff σ b (m - i))‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_le_of_coeff B a b m)
    (((summable_norm_mul_norm_sub a b).prod_factor m).mul_left ‖B‖)

variable (σ) in
/-- The coefficients `∑ᵢ B aᵢ b_{m - i}` of the Cauchy product. -/
noncomputable def convCoeff (a : L1 F₁) (b : L1 F₂) (m : ℤ) : F₃ :=
  ∑' i, B (coeff σ a i) (coeff σ b (m - i))

lemma wt_mul_norm_convCoeff_le (a : L1 F₁) (b : L1 F₂) (m : ℤ) :
    wt σ m * ‖convCoeff σ B a b m‖ ≤ ‖B‖ * ∑' i, ‖a i‖ * ‖b (m - i)‖ := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  calc wt σ m * ‖convCoeff σ B a b m‖
      ≤ wt σ m * ∑' i, ‖B (coeff σ a i) (coeff σ b (m - i))‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (summable_norm_convTerm B a b m))
          (wt_pos h0 m).le
    _ = ∑' i, wt σ m * ‖B (coeff σ a i) (coeff σ b (m - i))‖ := tsum_mul_left.symm
    _ ≤ ∑' i, ‖B‖ * (‖a i‖ * ‖b (m - i)‖) :=
        Summable.tsum_le_tsum (wt_mul_norm_le B a b m)
          ((summable_norm_convTerm B a b m).mul_left _)
          (((summable_norm_mul_norm_sub a b).prod_factor m).mul_left ‖B‖)
    _ = ‖B‖ * ∑' i, ‖a i‖ * ‖b (m - i)‖ := tsum_mul_left

lemma summable_wt_mul_norm_convCoeff (a : L1 F₁) (b : L1 F₂) :
    Summable fun m ↦ wt σ m * ‖convCoeff σ B a b m‖ :=
  Summable.of_nonneg_of_le
    (fun m ↦ mul_nonneg (wt_pos (zero_lt_one.trans_le hσ.out) m).le (norm_nonneg _))
    (wt_mul_norm_convCoeff_le B a b) ((summable_norm_mul_norm_sub a b).prod.mul_left ‖B‖)

variable (σ) in
/-- The Cauchy product of `a` and `b` with respect to `B`. -/
noncomputable def convAux (a : L1 F₁) (b : L1 F₂) : L1 F₃ :=
  ofCoeff (zero_lt_one.trans_le hσ.out) (convCoeff σ B a b) (summable_wt_mul_norm_convCoeff B a b)

lemma coeff_convAux (a : L1 F₁) (b : L1 F₂) (m : ℤ) :
    coeff σ (convAux σ B a b) m = convCoeff σ B a b m :=
  coeff_ofCoeff _ _ _ m

lemma norm_convAux_le (a : L1 F₁) (b : L1 F₂) : ‖convAux σ B a b‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  rw [norm_eq_tsum_wt h0, mul_assoc, ← tsum_tsum_norm_mul_norm_sub, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun m ↦ ?_) ?_ ((summable_norm_mul_norm_sub a b).prod.mul_left _)
  · rw [coeff_convAux]
    exact wt_mul_norm_convCoeff_le B a b m
  · simpa only [coeff_convAux] using summable_wt_mul_norm_convCoeff B a b

lemma hasSum_convCoeff [CompleteSpace F₃] (a : L1 F₁) (b : L1 F₂) (m : ℤ) :
    HasSum (fun i ↦ B (coeff σ a i) (coeff σ b (m - i))) (convCoeff σ B a b m) :=
  (summable_norm_convTerm B a b m).of_norm.hasSum

variable [CompleteSpace F₃]

variable (σ) in
/-- The Cauchy product of Laurent series with respect to a bounded bilinear map `B`. -/
noncomputable def conv : L1 F₁ →L[ℂ] L1 F₂ →L[ℂ] L1 F₃ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (convAux σ B)
      (fun a a' b ↦ ext_coeff (zero_lt_one.trans_le hσ.out) fun m ↦ by
        rw [coeff_convAux, coeff_add, coeff_convAux, coeff_convAux]
        refine Eq.symm <| ((hasSum_convCoeff (σ := σ) B a b m).add
          (hasSum_convCoeff (σ := σ) B a' b m)).unique ?_
        simpa only [coeff_add, map_add, add_apply] using
          hasSum_convCoeff (σ := σ) B (a + a') b m)
      (fun c a b ↦ ext_coeff (zero_lt_one.trans_le hσ.out) fun m ↦ by
        rw [coeff_convAux, coeff_smul, coeff_convAux]
        refine Eq.symm <| ((hasSum_convCoeff (σ := σ) B a b m).const_smul c).unique ?_
        simpa only [coeff_smul, map_smul, smul_apply] using
          hasSum_convCoeff (σ := σ) B (c • a) b m)
      (fun a b b' ↦ ext_coeff (zero_lt_one.trans_le hσ.out) fun m ↦ by
        rw [coeff_convAux, coeff_add, coeff_convAux, coeff_convAux]
        refine Eq.symm <| ((hasSum_convCoeff (σ := σ) B a b m).add
          (hasSum_convCoeff (σ := σ) B a b' m)).unique ?_
        simpa only [coeff_add, map_add] using hasSum_convCoeff (σ := σ) B a (b + b') m)
      (fun c a b ↦ ext_coeff (zero_lt_one.trans_le hσ.out) fun m ↦ by
        rw [coeff_convAux, coeff_smul, coeff_convAux]
        refine Eq.symm <| ((hasSum_convCoeff (σ := σ) B a b m).const_smul c).unique ?_
        simpa only [coeff_smul, map_smul] using hasSum_convCoeff (σ := σ) B a (c • b) m))
    ‖B‖ (norm_convAux_le (σ := σ) B)

@[simp]
lemma coeff_conv (a : L1 F₁) (b : L1 F₂) (m : ℤ) :
    coeff σ (conv σ B a b) m = ∑' i, B (coeff σ a i) (coeff σ b (m - i)) :=
  coeff_convAux B a b m

lemma hasSum_coeff_conv (a : L1 F₁) (b : L1 F₂) (m : ℤ) :
    HasSum (fun i ↦ B (coeff σ a i) (coeff σ b (m - i))) (coeff σ (conv σ B a b) m) := by
  rw [coeff_conv]
  exact hasSum_convCoeff (σ := σ) B a b m

lemma norm_conv_apply_apply_le (a : L1 F₁) (b : L1 F₂) : ‖conv σ B a b‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ :=
  norm_convAux_le (σ := σ) B a b

end Conv
/-! ### Degree bounds for the Cauchy product -/

section Degree

variable {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup F₂]
  [NormedSpace ℂ F₂] [NormedAddCommGroup F₃] [NormedSpace ℂ F₃] [CompleteSpace F₃]
  (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃)

/-- The Cauchy product of series of degree at most `p` and `q` has degree at most `p + q`. -/
lemma coeff_conv_eq_zero_of_gt {a : L1 F₁} {b : L1 F₂} {p q : ℤ}
    (ha : ∀ i, p < i → coeff σ a i = 0) (hb : ∀ j, q < j → coeff σ b j = 0) {m : ℤ}
    (hm : p + q < m) : coeff σ (conv σ B a b) m = 0 := by
  rw [coeff_conv]
  refine (tsum_congr fun i ↦ ?_).trans tsum_zero
  rcases lt_or_ge p i with hi | hi
  · rw [ha i hi, map_zero, zero_apply]
  · rw [hb (m - i) (by omega), map_zero]

/-- The Cauchy product of series of order at least `p` and `q` has order at least `p + q`. -/
lemma coeff_conv_eq_zero_of_lt {a : L1 F₁} {b : L1 F₂} {p q : ℤ}
    (ha : ∀ i, i < p → coeff σ a i = 0) (hb : ∀ j, j < q → coeff σ b j = 0) {m : ℤ}
    (hm : m < p + q) : coeff σ (conv σ B a b) m = 0 := by
  rw [coeff_conv]
  refine (tsum_congr fun i ↦ ?_).trans tsum_zero
  rcases lt_or_ge i p with hi | hi
  · rw [ha i hi, map_zero, zero_apply]
  · rw [hb (m - i) (by omega), map_zero]

end Degree

/-! ### Coefficient functionals and the parts of nonnegative and nonpositive degree -/

section Parts

variable (σ) in
/-- The coefficient `coeff σ · j` as a continuous linear map. -/
noncomputable def coeffCLM (j : ℤ) : L1 V →L[ℂ] V :=
  ((wt σ j : ℂ))⁻¹ • lp.evalCLM ℂ (fun _ : ℤ ↦ V) 1 j

omit hσ in
@[simp]
lemma coeffCLM_apply (j : ℤ) (a : L1 V) : coeffCLM σ j a = coeff σ a j := rfl

lemma norm_coeffCLM_le (j : ℤ) : ‖coeffCLM (V := V) σ j‖ ≤ (wt σ j)⁻¹ := by
  have h0 := wt_pos (zero_lt_one.trans_le hσ.out) j
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 h0.le) fun a ↦ ?_
  rw [coeffCLM_apply, coeff, norm_smul, norm_inv, norm_real, Real.norm_of_nonneg h0.le]
  exact mul_le_mul_of_nonneg_left (norm_apply_le a j) (inv_nonneg.2 h0.le)

lemma norm_pow_smul_coeffCLM_le {w : ℂ} {r : ℝ} (hw : ‖w‖ ≤ r) (n : ℕ) :
    ‖w ^ n • coeffCLM (V := V) σ n‖ ≤ (r / σ) ^ n := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  rw [norm_smul, norm_pow, div_pow, div_eq_mul_inv]
  refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw n) ?_ (norm_nonneg _)
    ((norm_nonneg _).trans hw |> fun h ↦ pow_nonneg h n)
  simpa [wt_natCast] using norm_coeffCLM_le (V := V) (σ := σ) n

lemma norm_pow_smul_coeffCLM_neg_le {w : ℂ} {r : ℝ} (hw : ‖w‖ ≤ r) (n : ℕ) :
    ‖w ^ n • coeffCLM (V := V) σ (-n)‖ ≤ (r / σ) ^ n := by
  rw [norm_smul, norm_pow, div_pow, div_eq_mul_inv]
  refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw n) ?_ (norm_nonneg _)
    ((norm_nonneg _).trans hw |> fun h ↦ pow_nonneg h n)
  simpa [wt_neg, wt_natCast] using norm_coeffCLM_le (V := V) (σ := σ) (-n)

variable [CompleteSpace V]

variable (V σ) in
/-- The part `∑_{n ≥ 0} wⁿ • coeff σ a n` of nonnegative degree, as a continuous linear map; it is
holomorphic in `w` for `‖w‖ < σ`. -/
noncomputable def evalNat (w : ℂ) : L1 V →L[ℂ] V := ∑' n : ℕ, w ^ n • coeffCLM σ n

variable (V σ) in
/-- The part `∑_{n ≥ 0} w⁻ⁿ • coeff σ a (-n)` of nonpositive degree, in the coordinate `w⁻¹` at
infinity: `evalNeg σ u a = ∑_{n ≥ 0} uⁿ • coeff σ a (-n)`. It is holomorphic in `u` for
`‖u‖ < σ`. -/
noncomputable def evalNeg (u : ℂ) : L1 V →L[ℂ] V := ∑' n : ℕ, u ^ n • coeffCLM σ (-n)

omit [CompleteSpace V] in
lemma summable_evalNat {w : ℂ} (hw : ‖w‖ < σ) :
    Summable fun n : ℕ ↦ ‖w ^ n • coeffCLM (V := V) σ n‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_pow_smul_coeffCLM_le le_rfl)
    (summable_geometric_of_lt_one (div_nonneg (norm_nonneg _) (zero_lt_one.trans_le hσ.out).le)
      ((div_lt_one (zero_lt_one.trans_le hσ.out)).2 hw))

omit [CompleteSpace V] in
lemma summable_evalNeg {u : ℂ} (hu : ‖u‖ < σ) :
    Summable fun n : ℕ ↦ ‖u ^ n • coeffCLM (V := V) σ (-n)‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_pow_smul_coeffCLM_neg_le le_rfl)
    (summable_geometric_of_lt_one (div_nonneg (norm_nonneg _) (zero_lt_one.trans_le hσ.out).le)
      ((div_lt_one (zero_lt_one.trans_le hσ.out)).2 hu))

lemma hasSum_evalNat_apply {w : ℂ} (hw : ‖w‖ < σ) (a : L1 V) :
    HasSum (fun n : ℕ ↦ w ^ n • coeff σ a n) (evalNat V σ w a) := by
  have h : HasSum (fun n : ℕ ↦ w ^ n • coeffCLM (V := V) σ n) (evalNat V σ w) :=
    (Summable.of_norm (E := L1 V →L[ℂ] V) (summable_evalNat hw)).hasSum
  exact h.mapL (ContinuousLinearMap.apply ℂ V a)

lemma hasSum_evalNeg_apply {u : ℂ} (hu : ‖u‖ < σ) (a : L1 V) :
    HasSum (fun n : ℕ ↦ u ^ n • coeff σ a (-n)) (evalNeg V σ u a) := by
  have h : HasSum (fun n : ℕ ↦ u ^ n • coeffCLM (V := V) σ (-n)) (evalNeg V σ u) :=
    (Summable.of_norm (E := L1 V →L[ℂ] V) (summable_evalNeg hu)).hasSum
  exact h.mapL (ContinuousLinearMap.apply ℂ V a)

lemma differentiableOn_evalNat : DifferentiableOn ℂ (evalNat V σ) (ball 0 σ) := by
  intro w₀ hw₀
  rw [mem_ball_zero_iff] at hw₀
  set r := (‖w₀‖ + σ) / 2
  have hr : r < σ := by simp only [r]; linarith
  have hr0 : 0 ≤ r / σ := div_nonneg (by simp only [r]; linarith [norm_nonneg w₀])
    (zero_lt_one.trans_le hσ.out).le
  have hd : DifferentiableOn ℂ (evalNat V σ) (ball 0 r) :=
    differentiableOn_tsum_of_summable_norm
      (summable_geometric_of_lt_one hr0 ((div_lt_one (zero_lt_one.trans_le hσ.out)).2 hr))
      (fun n ↦ ((differentiable_pow n).smul_const _).differentiableOn) isOpen_ball
      fun n w hw ↦ norm_pow_smul_coeffCLM_le (mem_ball_zero_iff.1 hw).le n
  exact (hd.differentiableAt (isOpen_ball.mem_nhds (by
    rw [mem_ball_zero_iff]; simp only [r]; linarith))).differentiableWithinAt

lemma differentiableOn_evalNeg : DifferentiableOn ℂ (evalNeg V σ) (ball 0 σ) := by
  intro w₀ hw₀
  rw [mem_ball_zero_iff] at hw₀
  set r := (‖w₀‖ + σ) / 2
  have hr : r < σ := by simp only [r]; linarith
  have hr0 : 0 ≤ r / σ := div_nonneg (by simp only [r]; linarith [norm_nonneg w₀])
    (zero_lt_one.trans_le hσ.out).le
  have hd : DifferentiableOn ℂ (evalNeg V σ) (ball 0 r) :=
    differentiableOn_tsum_of_summable_norm
      (summable_geometric_of_lt_one hr0 ((div_lt_one (zero_lt_one.trans_le hσ.out)).2 hr))
      (fun n ↦ ((differentiable_pow n).smul_const _).differentiableOn) isOpen_ball
      fun n w hw ↦ norm_pow_smul_coeffCLM_neg_le (mem_ball_zero_iff.1 hw).le n
  exact (hd.differentiableAt (isOpen_ball.mem_nhds (by
    rw [mem_ball_zero_iff]; simp only [r]; linarith))).differentiableWithinAt

end Parts

/-! ### Evaluation -/

section Eval

variable (σ) in
/-- The sum `∑ⱼ wʲ • coeff σ a j` of the Laurent series represented by `a`; it converges
absolutely for `σ⁻¹ ≤ ‖w‖ ≤ σ`. -/
noncomputable def eval (w : ℂ) (a : L1 V) : V := ∑' j, w ^ j • coeff σ a j

variable {w : ℂ}

omit hσ in
@[simp]
lemma eval_zero : eval σ w (0 : L1 V) = 0 := by
  simp [eval]

lemma norm_zpow_smul_coeff_le (h₁ : σ⁻¹ ≤ ‖w‖) (h₂ : ‖w‖ ≤ σ) (a : L1 V) (j : ℤ) :
    ‖w ^ j • coeff σ a j‖ ≤ ‖a j‖ := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  rw [norm_smul, norm_apply_eq h0 a j]
  exact mul_le_mul_of_nonneg_right (norm_zpow_le_wt h0 h₁ h₂ j) (norm_nonneg _)

lemma summable_norm_zpow_smul_coeff (h₁ : σ⁻¹ ≤ ‖w‖) (h₂ : ‖w‖ ≤ σ) (a : L1 V) :
    Summable fun j ↦ ‖w ^ j • coeff σ a j‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_zpow_smul_coeff_le h₁ h₂ a)
    (summable_norm a)

variable [CompleteSpace V]

lemma hasSum_eval (h₁ : σ⁻¹ ≤ ‖w‖) (h₂ : ‖w‖ ≤ σ) (a : L1 V) :
    HasSum (fun j ↦ w ^ j • coeff σ a j) (eval σ w a) :=
  (summable_norm_zpow_smul_coeff h₁ h₂ a).of_norm.hasSum

/-- For a series without terms of negative degree, `eval` is the part of nonnegative degree. -/
lemma eval_eq_evalNat (h₁ : σ⁻¹ ≤ ‖w‖) (h₂ : ‖w‖ < σ) {a : L1 V}
    (ha : ∀ j < 0, coeff σ a j = 0) : eval σ w a = evalNat V σ w a := by
  refine (hasSum_eval h₁ h₂.le a).unique ?_
  rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff fun j hj ↦ ?_]
  · change HasSum (fun n : ℕ ↦ w ^ (n : ℤ) • coeff σ a n) _
    simpa only [zpow_natCast] using hasSum_evalNat_apply h₂ a
  · rw [ha j (by by_contra! h; exact hj ⟨j.toNat, Int.toNat_of_nonneg h⟩), smul_zero]

/-- For a series without terms of positive degree, `eval` is the part of nonpositive degree, in
the coordinate `w⁻¹`. -/
lemma eval_eq_evalNeg (h₁ : σ⁻¹ < ‖w‖) (h₂ : ‖w‖ ≤ σ) {a : L1 V}
    (ha : ∀ j, 0 < j → coeff σ a j = 0) : eval σ w a = evalNeg V σ w⁻¹ a := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hw : ‖w⁻¹‖ < σ := by
    rw [norm_inv]
    exact (inv_lt_comm₀ h0 ((inv_pos.2 h0).trans h₁)).1 h₁
  refine (hasSum_eval h₁.le h₂ a).unique ?_
  have hinj : Function.Injective fun n : ℕ ↦ -(n : ℤ) := fun m n h ↦ by simpa using h
  rw [← hinj.hasSum_iff fun j hj ↦ ?_]
  · change HasSum (fun n : ℕ ↦ w ^ (-(n : ℤ)) • coeff σ a (-n)) _
    simpa only [zpow_neg, zpow_natCast, inv_pow] using hasSum_evalNeg_apply hw a
  · rw [ha j (by by_contra! h; exact hj ⟨(-j).toNat, by
      simp only [Int.toNat_of_nonneg (by omega : 0 ≤ -j), neg_neg]⟩),
      smul_zero]

lemma eval_add (h₁ : σ⁻¹ ≤ ‖w‖) (h₂ : ‖w‖ ≤ σ) (a b : L1 V) :
    eval σ w (a + b) = eval σ w a + eval σ w b :=
  (hasSum_eval h₁ h₂ (a + b)).unique <| by
    simpa only [coeff_add, smul_add] using (hasSum_eval h₁ h₂ a).add (hasSum_eval h₁ h₂ b)

lemma eval_sub (h₁ : σ⁻¹ ≤ ‖w‖) (h₂ : ‖w‖ ≤ σ) (a b : L1 V) :
    eval σ w (a - b) = eval σ w a - eval σ w b :=
  (hasSum_eval h₁ h₂ (a - b)).unique <| by
    simpa only [coeff_sub, smul_sub] using (hasSum_eval h₁ h₂ a).sub (hasSum_eval h₁ h₂ b)

lemma eval_refl (h₁ : σ⁻¹ ≤ ‖w‖) (h₂ : ‖w‖ ≤ σ) (a : L1 V) :
    eval σ w (refl V a) = eval σ w⁻¹ a := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hw : 0 < ‖w‖ := (inv_pos.2 h0).trans_le h₁
  have h₁' : σ⁻¹ ≤ ‖w⁻¹‖ := by rw [norm_inv]; exact inv_anti₀ hw h₂
  have h₂' : ‖w⁻¹‖ ≤ σ := by rw [norm_inv]; exact inv_le_of_inv_le₀ h0 h₁
  refine (hasSum_eval h₁ h₂ (refl V a)).unique ?_
  rw [← (Equiv.neg ℤ).hasSum_iff]
  convert hasSum_eval h₁' h₂' a using 1
  funext j
  simp [zpow_neg]

lemma eval_shift (h₁ : σ⁻¹ ≤ ‖w‖) (h₂ : ‖w‖ ≤ σ) (m : ℤ) (a : L1 V) :
    eval σ w (shift σ m a) = w ^ m • eval σ w a := by
  have hw : w ≠ 0 := norm_pos_iff.1 ((inv_pos.2 (zero_lt_one.trans_le hσ.out)).trans_le h₁)
  refine (hasSum_eval h₁ h₂ (shift σ m a)).unique ?_
  rw [← (Equiv.addRight m).hasSum_iff]
  convert (hasSum_eval h₁ h₂ a).const_smul (w ^ m) using 1
  funext j
  simp only [Function.comp_apply, Equiv.coe_addRight, coeff_shift, smul_smul, add_sub_cancel_right]
  rw [← zpow_add₀ hw]
  congr 2
  ring

/-- A Laurent series is determined by its values on the unit circle. -/
theorem eq_of_eval_eq {a b : L1 V} (h : ∀ w : ℂ, ‖w‖ = 1 → eval σ w a = eval σ w b) : a = b := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hσ₁ : σ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hσ.out
  refine ext_coeff h0 fun j ↦ (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ ↦ ?_
  set β : ℤ → ℂ := fun i ↦ ℓ (coeff σ a i) - ℓ (coeff σ b i)
  have hβ : Summable fun i ↦ ‖β i‖ * 1 ^ i := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun i ↦ ?_)
      (((summable_norm a).add (summable_norm b)).mul_left ‖ℓ‖)
    rw [one_zpow, mul_one, mul_add]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_coeff_le hσ.out a i)
        (norm_nonneg _))
    · exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_coeff_le hσ.out b i)
        (norm_nonneg _))
  have hsum : ∀ z ∈ sphere (0 : ℂ) 1, HasSum (fun i ↦ β i * z ^ i) ((fun _ ↦ (0 : ℂ)) z) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have ha := (hasSum_eval (w := z) (hσ₁.trans_eq hz.symm) (hz.trans_le hσ.out) a).mapL ℓ
    have hb := (hasSum_eval (w := z) (hσ₁.trans_eq hz.symm) (hz.trans_le hσ.out) b).mapL ℓ
    have := ha.sub hb
    rw [h z hz, sub_self] at this
    have e : (fun i ↦ β i * z ^ i) = fun i ↦ ℓ (z ^ i • coeff σ a i) - ℓ (z ^ i • coeff σ b i) := by
      funext i
      simp only [β, map_smul, smul_eq_mul]
      ring
    rw [e]
    exact this
  have := Laurent.coeff_eq_of_hasSum zero_lt_one hβ hsum j
  simp only [Laurent.coeff, mul_zero, circleIntegral, smul_zero,
    intervalIntegral.integral_zero] at this
  exact sub_eq_zero.1 this.symm

variable {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup F₂]
  [NormedSpace ℂ F₂] [NormedAddCommGroup F₃] [NormedSpace ℂ F₃] [CompleteSpace F₁]
  [CompleteSpace F₂] [CompleteSpace F₃] (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃)

/-- Evaluation is multiplicative: the value of a Cauchy product is the product of the values. -/
theorem eval_conv (h₁ : σ⁻¹ ≤ ‖w‖) (h₂ : ‖w‖ ≤ σ) (a : L1 F₁) (b : L1 F₂) :
    eval σ w (conv σ B a b) = B (eval σ w a) (eval σ w b) := by
  have hw : w ≠ 0 := norm_pos_iff.1 ((inv_pos.2 (zero_lt_one.trans_le hσ.out)).trans_le h₁)
  set H : ℤ × ℤ → F₃ := fun q ↦ B (w ^ q.1 • coeff σ a q.1) (w ^ q.2 • coeff σ b q.2)
  have hHn : Summable fun q ↦ ‖H q‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun q ↦ (B.le_opNorm₂ _ _).trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (norm_zpow_smul_coeff_le h₁ h₂ a q.1)
          (norm_zpow_smul_coeff_le h₁ h₂ b q.2) (norm_nonneg _) (norm_nonneg _))
          (norm_nonneg B)))
      (((summable_norm a).mul_of_nonneg (summable_norm b) (fun _ ↦ norm_nonneg _)
        fun _ ↦ norm_nonneg _).mul_left ‖B‖)
  have hG : Summable (H ∘ antidiagEquiv) :=
    (antidiagEquiv.summable_iff (f := H)).2 hHn.of_norm
  have hfib : ∀ m, HasSum (fun i ↦ (H ∘ antidiagEquiv) (m, i))
      (w ^ m • coeff σ (conv σ B a b) m) := by
    intro m
    convert (hasSum_coeff_conv B a b m).const_smul (w ^ m) using 1
    funext i
    simp only [H, Function.comp_apply, antidiagEquiv, Equiv.coe_fn_mk, map_smul,
      smul_apply, smul_smul]
    rw [← zpow_add₀ hw]
    congr 2
    ring
  have h1 : eval σ w (conv σ B a b) = ∑' q, H q := by
    rw [← antidiagEquiv.tsum_eq H]
    exact ((hG.hasSum.prod_fiberwise hfib).unique (hasSum_eval h₁ h₂ _)).symm
  rw [h1, hHn.of_norm.tsum_prod' fun i ↦ hHn.of_norm.prod_factor i]
  have hinner : ∀ i, ∑' j, H (i, j) = B.flip (eval σ w b) (w ^ i • coeff σ a i) := fun i ↦
    ((hasSum_eval h₁ h₂ b).mapL (B (w ^ i • coeff σ a i))).tsum_eq
  rw [tsum_congr hinner]
  exact ((hasSum_eval h₁ h₂ a).mapL (B.flip (eval σ w b))).tsum_eq

end Eval

end L1

end Laurent
