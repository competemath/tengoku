/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.NumberTheory.Elementary.ContinuedFractions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# √d 连分数展开的周期性

本文件从初等数论教材的角度处理二次无理数 `√d` 的简单连分数，提供以下接口：

* 连分数的完全商 `ξₙ` 与数位（部分商）`aₙ = ⌊ξₙ⌋` 的定义层；
* 整数序列“最终周期”的谓词及其基本结构引理；
* `√d` 数位序列的最终周期性，走整数状态 `(Pₙ, Qₙ)` 递推加鸽笼；
* 周期长度的显式上界 `L ≤ 2d`（**不是**判别式界：判别式只由 `d` 的无平方因子部分决定，
  见 `exists_cfDigit_sqrt_period_le` 的说明）。

Mathlib 目前没有 `√d` 连分数周期性的承载（`GenContFract.of_sqrt` 不存在，也没有任何二次
无理数连分数周期性的定理），因此本条的周期性陈述与证明都是自建的；只有 `Int.fract`、
`Int.floor` 与 `Real.convergent` 这些底层工具来自 Mathlib。

周期长度与判别式的**精确**关系（周期与基本单位、类数、负 Pell 方程可解性的联系）在本库中
尚未形式化：本条只做到显式上界 `L ≤ 2d`，并在文档中如实登记这一强度。

## 本文件条目

* `number-theory.elementary.sqrt-periodic-cf`
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-! ## 完全商与数位 -/

/-- Gauss 映射（去掉整数部分再取倒数）的第 `n` 次迭代：`ξ` 的第 `n` 个完全商。

`ξ₀ = ξ`，`ξₙ₊₁ = (fract ξₙ)⁻¹`。连分数的第 `n` 个数位就是 `⌊ξₙ⌋`。

> **Entry**: number-theory.elementary.sqrt-periodic-cf-/
noncomputable def cfCompleteQuotient (ξ : ℝ) : ℕ → ℝ
  | 0 => ξ
  | n + 1 => (Int.fract (cfCompleteQuotient ξ n))⁻¹

/-- 连分数展开的第 `n` 个数位（部分商）`aₙ = ⌊ξₙ⌋`。

> **Entry**: number-theory.elementary.sqrt-periodic-cf-/
noncomputable def cfDigit (ξ : ℝ) (n : ℕ) : ℤ := ⌊cfCompleteQuotient ξ n⌋

/-- 整数序列 `a` 最终周期：存在起点 `N` 与正周期 `L`，使 `n ≥ N` 时 `a (n + L) = a n`。

> **Entry**: number-theory.elementary.sqrt-periodic-cf-/
def IsEventuallyPeriodic (a : ℕ → ℤ) : Prop :=
  ∃ N L : ℕ, 0 < L ∧ ∀ n, N ≤ n → a (n + L) = a n

/--
@isnad1 id=eq.0h1v.s3.07251301da5c from=translated src=- shape=bb0110a5 vocab=32f32864
-/
@[simp]
theorem cfCompleteQuotient_zero (ξ : ℝ) : cfCompleteQuotient ξ 0 = ξ := rfl

/--
@isnad1 id=eq.0h2v.s5.70270d45f7db from=translated src=- shape=03e1b239 vocab=69f5eba3
-/
@[simp]
theorem cfCompleteQuotient_succ (ξ : ℝ) (n : ℕ) :
    cfCompleteQuotient ξ (n + 1) = (Int.fract (cfCompleteQuotient ξ n))⁻¹ := rfl

/--
@isnad1 id=eq.0h1v.s4.c643f938ea25 from=translated src=- shape=4c6643d4 vocab=42e15742
-/
theorem cfCompleteQuotient_one (ξ : ℝ) : cfCompleteQuotient ξ 1 = (Int.fract ξ)⁻¹ := rfl

/--
@isnad1 id=eq.0h1v.s4.5bd69549e4bd from=translated src=- shape=a28a88cd vocab=02ac4df6
-/
@[simp]
theorem cfDigit_zero (ξ : ℝ) : cfDigit ξ 0 = ⌊ξ⌋ := rfl

/-- 最终周期性可以从更晚的起点重新陈述。
@isnad1 id=iseventu.3h4v.s5.fba3a05129a5 from=translated src=- shape=41d272eb vocab=b386e884
-/
theorem IsEventuallyPeriodic.mono {a : ℕ → ℤ} {N L : ℕ} (hL : 0 < L)
    (h : ∀ n, N ≤ n → a (n + L) = a n) {N' : ℕ} (hN : N ≤ N') :
    IsEventuallyPeriodic a :=
  ⟨N', L, hL, fun n hn => h n (le_trans hN hn)⟩

/-- 周期 `L` 蕴含周期 `k * L`（`k` 任意）。
@isnad1 id=ex.1h2v.s5.f6026ee6bff4 from=translated src=- shape=0c8d20fe vocab=6a6a794f
-/
theorem IsEventuallyPeriodic.mul_period {a : ℕ → ℤ} (h : IsEventuallyPeriodic a) (k : ℕ) :
    ∃ N L : ℕ, 0 < L ∧ ∀ n, N ≤ n → a (n + k * L) = a n := by
  obtain ⟨N, L, hL, hper⟩ := h
  refine ⟨N, L, hL, fun n hn => ?_⟩
  have key : ∀ k n, N ≤ n → a (n + k * L) = a n := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      have h1 : n + (k + 1) * L = n + k * L + L := by ring
      rw [h1, hper (n + k * L) (le_trans hn (Nat.le_add_right n (k * L))), ih n hn]
  exact key k n hn

/-- 完全商与前置 Entry 的收敛子递推的连接：第 `n + 1` 个收敛子等于 `⌊ξ⌋` 加上
“以第一个完全商 `ξ₁ = (fract ξ)⁻¹` 为起点展开的第 `n` 个收敛子”的倒数。

> **Entry**: number-theory.elementary.sqrt-periodic-cf
@isnad1 id=eq.0h2v.s5.1c5adf3b7038 from=translated src=- shape=2de27a5a vocab=c869e4c8
-/
theorem continuedFractionConvergent_succ_eq (ξ : ℝ) (n : ℕ) :
    continuedFractionConvergent ξ (n + 1) =
      (⌊ξ⌋ : ℤ) + (continuedFractionConvergent (cfCompleteQuotient ξ 1) n)⁻¹ :=
  continuedFractionConvergent_succ ξ n

section GaussMap

/-- 连分数算法的 Gauss 映射：去掉整数部分再取倒数。-/
noncomputable def cfGaussMap (x : ℝ) : ℝ := (Int.fract x)⁻¹

/--
@isnad1 id=eq.0h2v.s4.0be6a86fc4ad from=translated src=- shape=8ad2ba2d vocab=737a3bc4
-/
theorem cfCompleteQuotient_succ_eq_gaussMap (ξ : ℝ) (n : ℕ) :
    cfCompleteQuotient ξ (n + 1) = cfGaussMap (cfCompleteQuotient ξ n) := rfl

/-- 完全商的加法公式：从第 `m` 个完全商出发再迭代 `k` 次 Gauss 映射，得到第 `m + k` 个完全商。
@isnad1 id=eq.0h3v.s4.f699eeda7ac3 from=translated src=- shape=86b1740b vocab=8f49fd70
-/
theorem cfCompleteQuotient_add (ξ : ℝ) (m k : ℕ) :
    cfCompleteQuotient ξ (m + k) = (cfGaussMap^[k]) (cfCompleteQuotient ξ m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, cfCompleteQuotient_succ_eq_gaussMap, ih, Function.iterate_succ_apply']

/-- **一般性周期判据：完全商重复 ⟹ 数位最终周期。**

若第 `N + L` 个完全商回到第 `N` 个完全商（`L > 0`），则数位序列 `aₙ = ⌊ξₙ⌋` 从 `N` 起
以 `L` 为周期。这是"完全商重复 ⇒ 数位周期"的一般陈述，不限于 `√d`；`√d` 的周期性正是
把这条判据用在整数状态递推给出的重复上。

> **Entry**: number-theory.elementary.sqrt-periodic-cf
@isnad1 id=iseventu.2h3v.s5.c807e0d1a57f from=translated src=- shape=d8a0d415 vocab=5e3f6e7e
-/
theorem cfDigit_eventuallyPeriodic_of_completeQuotient_eq {ξ : ℝ} {N L : ℕ} (hL : 0 < L)
    (h : cfCompleteQuotient ξ (N + L) = cfCompleteQuotient ξ N) :
    IsEventuallyPeriodic (cfDigit ξ) := by
  refine ⟨N, L, hL, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : cfCompleteQuotient ξ (N + k) = (cfGaussMap^[k]) (cfCompleteQuotient ξ N) :=
    cfCompleteQuotient_add ξ N k
  have h2 : cfCompleteQuotient ξ (N + L + k) =
      (cfGaussMap^[k]) (cfCompleteQuotient ξ (N + L)) :=
    cfCompleteQuotient_add ξ (N + L) k
  have h3 : cfCompleteQuotient ξ (N + L + k) = cfCompleteQuotient ξ (N + k) := by
    rw [h2, h1, h]
  rw [show N + k + L = N + L + k by omega]
  simp only [cfDigit]
  rw [h3]

end GaussMap

/-! ## √d 的基本事实（内部辅助） -/

private lemma irr_sqrt_natCast (d : ℕ) (_hd : 0 < d) (hns : ¬ IsSquare (d : ℤ)) :
    Irrational (√(d : ℝ)) := by
  have h := (irrational_sqrt_intCast_iff (z := (d : ℤ))).mpr ⟨hns, Int.natCast_nonneg d⟩
  simpa using h

private lemma two_le_of_not_isSquare (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare (d : ℤ)) : 2 ≤ d := by
  have h1 : d ≠ 1 := by
    rintro rfl
    exact hns ⟨1, by norm_num⟩
  exact lt_of_le_of_ne hd (Ne.symm h1)

private lemma one_lt_sqrt_natCast (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare (d : ℤ)) :
    1 < √(d : ℝ) := by
  have h2 : 2 ≤ d := two_le_of_not_isSquare d hd hns
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num
  exact_mod_cast h2

private lemma sqrt_natCast_pos (d : ℕ) (hd : 0 < d) : 0 < √(d : ℝ) :=
  Real.sqrt_pos_of_pos (by exact_mod_cast hd)

/-! ## 整数状态递推 -/

/-- 状态 `(P, Q)` 对应的部分商 `a = ⌊(P + √d)/Q⌋`。-/
noncomputable def sqrtCFPartialQuotient (d : ℕ) (s : ℤ × ℤ) : ℤ :=
  ⌊(((s.1 : ℝ) + √(d : ℝ)) / (s.2 : ℝ))⌋

/-- `√d` 连分数算法的整数状态一步递推：
`(P, Q) ↦ (aQ - P, (d - (aQ - P)²)/Q)`，其中 `a = ⌊(P + √d)/Q⌋`。-/
noncomputable def sqrtCFStep (d : ℕ) (s : ℤ × ℤ) : ℤ × ℤ :=
  (sqrtCFPartialQuotient d s * s.2 - s.1,
    ((d : ℤ) - (sqrtCFPartialQuotient d s * s.2 - s.1) ^ 2) / s.2)

/-- 从初始状态 `(P₀, Q₀) = (0, 1)` 出发迭代 `sqrtCFStep` 得到的整数状态序列。-/
noncomputable def sqrtCFState (d : ℕ) (n : ℕ) : ℤ × ℤ :=
  (sqrtCFStep d)^[n] (0, 1)

/--
@isnad1 id=eq.0h2v.s4.1499d0b162d9 from=translated src=- shape=4beb2f64 vocab=8a06141b
-/
theorem sqrtCFState_eq_iterate (d : ℕ) (n : ℕ) :
    sqrtCFState d n = (sqrtCFStep d)^[n] (0, 1) := rfl

/--
@isnad1 id=eq.0h2v.s6.a2ea732ef8d0 from=translated src=- shape=49293df4 vocab=526391e7
-/
theorem sqrtCFStep_apply (d : ℕ) (s : ℤ × ℤ) :
    sqrtCFStep d s =
      (sqrtCFPartialQuotient d s * s.2 - s.1,
        ((d : ℤ) - (sqrtCFPartialQuotient d s * s.2 - s.1) ^ 2) / s.2) := rfl

/--
@isnad1 id=eq.0h2v.s4.55fa0e3535d8 from=translated src=- shape=461e3f75 vocab=341e6356
-/
theorem sqrtCFState_succ (d : ℕ) (n : ℕ) :
    sqrtCFState d (n + 1) = sqrtCFStep d (sqrtCFState d n) := by
  simp only [sqrtCFState_eq_iterate, Function.iterate_succ_apply']

/-! ## 状态序列的表示不变量 -/

private theorem sqrtCFState_spec (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare (d : ℤ)) (n : ℕ) :
    (sqrtCFState d n).2 ≠ 0 ∧
      (sqrtCFState d n).2 ∣ (d : ℤ) - (sqrtCFState d n).1 ^ 2 ∧
      cfCompleteQuotient (√(d : ℝ)) n =
        (((sqrtCFState d n).1 : ℝ) + √(d : ℝ)) / ((sqrtCFState d n).2 : ℝ) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simp [sqrtCFState]
    · simp [sqrtCFState]
    · simp [sqrtCFState]
  | succ n ih =>
    obtain ⟨hQ, hdvd, hξ⟩ := ih
    set s : ℤ × ℤ := sqrtCFState d n with hs
    set a : ℤ := sqrtCFPartialQuotient d s with ha
    set P' : ℤ := a * s.2 - s.1 with hP'def
    set Q' : ℤ := ((d : ℤ) - P' ^ 2) / s.2 with hQ'def
    have hξs : cfCompleteQuotient (√(d : ℝ)) n = ((s.1 : ℝ) + √(d : ℝ)) / (s.2 : ℝ) := hξ
    have hQℝ : (s.2 : ℝ) ≠ 0 := by exact_mod_cast hQ
    have hstate : sqrtCFState d (n + 1) = (P', Q') := by
      rw [sqrtCFState_succ, sqrtCFStep_apply]
    have ha_eq : a = ⌊cfCompleteQuotient (√(d : ℝ)) n⌋ := by
      rw [ha, sqrtCFPartialQuotient, hξs]
    have hfract : Int.fract (cfCompleteQuotient (√(d : ℝ)) n) =
        (√(d : ℝ) - (P' : ℝ)) / (s.2 : ℝ) := by
      have h2 : cfCompleteQuotient (√(d : ℝ)) n -
            (⌊cfCompleteQuotient (√(d : ℝ)) n⌋ : ℝ) =
          ((s.1 : ℝ) + √(d : ℝ) - ⌊cfCompleteQuotient (√(d : ℝ)) n⌋ * (s.2 : ℝ)) /
            (s.2 : ℝ) := by
        rw [hξs]
        field_simp
      have h3 : (√(d : ℝ) - (P' : ℝ)) / (s.2 : ℝ) =
          ((s.1 : ℝ) + √(d : ℝ) - ⌊cfCompleteQuotient (√(d : ℝ)) n⌋ * (s.2 : ℝ)) /
            (s.2 : ℝ) := by
        rw [hP'def, ha_eq]
        push_cast
        ring
      rw [← Int.self_sub_floor (cfCompleteQuotient (√(d : ℝ)) n), h2, ← h3]
    have hP'_ne : (√(d : ℝ) - (P' : ℝ)) ≠ 0 := by
      intro h0
      have hPeq : (P' : ℝ) = √(d : ℝ) := by linarith
      exact (irr_sqrt_natCast d hd hns).ne_rat (P' : ℚ) (by push_cast; linarith)
    have hinv : (Int.fract (cfCompleteQuotient (√(d : ℝ)) n))⁻¹ =
        (s.2 : ℝ) / (√(d : ℝ) - (P' : ℝ)) := by
      rw [hfract, inv_div]
    have hdvd' : s.2 ∣ (d : ℤ) - P' ^ 2 := by
      obtain ⟨m, hm⟩ := hdvd
      refine ⟨m - a ^ 2 * s.2 + 2 * a * s.1, ?_⟩
      have hkey : (d : ℤ) - P' ^ 2 =
          ((d : ℤ) - s.1 ^ 2) - a ^ 2 * s.2 ^ 2 + 2 * a * s.2 * s.1 := by
        rw [hP'def]; ring
      rw [hkey, hm]; ring
    have hQQ' : s.2 * Q' = (d : ℤ) - P' ^ 2 := by
      rw [hQ'def]; exact Int.mul_ediv_cancel' hdvd'
    have hdP' : (d : ℤ) - P' ^ 2 ≠ 0 := by
      intro h0
      refine hns ⟨P', ?_⟩
      rw [← sq]; linarith
    have hQ'ne : Q' ≠ 0 := by
      intro h0
      have hzero : s.2 * Q' = 0 := by rw [h0, mul_zero]
      rw [hQQ'] at hzero
      exact hdP' hzero
    have hQ'ℝ : (Q' : ℝ) ≠ 0 := by exact_mod_cast hQ'ne
    have hstep : cfCompleteQuotient (√(d : ℝ)) (n + 1) =
        ((P' : ℝ) + √(d : ℝ)) / (Q' : ℝ) := by
      rw [cfCompleteQuotient_succ, hinv, div_eq_div_iff hP'_ne hQ'ℝ]
      have hQQ'ℝ : (s.2 : ℝ) * (Q' : ℝ) = (d : ℝ) - (P' : ℝ) ^ 2 := by
        exact_mod_cast hQQ'
      rw [hQQ'ℝ]
      have hcomm : (P' : ℝ) + √(d : ℝ) = √(d : ℝ) + P' := by ring
      rw [hcomm]
      ring_nf
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ (d : ℝ) by positivity)]
      ring
    rw [hstate]
    exact ⟨hQ'ne, ⟨s.2, by rw [← hQQ', mul_comm]⟩, hstep⟩

/-! ## 小数部分严格为正 -/

private theorem cfCompleteQuotient_sqrt_fract_pos (d : ℕ) (hd : 0 < d)
    (hns : ¬ IsSquare (d : ℤ)) (n : ℕ) :
    0 < Int.fract (cfCompleteQuotient (√(d : ℝ)) n) := by
  refine lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm ?_)
  intro h0
  obtain ⟨hQ, -, hξ⟩ := sqrtCFState_spec d hd hns n
  have hQℝ : ((sqrtCFState d n).2 : ℝ) ≠ 0 := by exact_mod_cast hQ
  have hfloor : cfCompleteQuotient (√(d : ℝ)) n =
      ((⌊cfCompleteQuotient (√(d : ℝ)) n⌋ : ℤ) : ℝ) := by
    have h := Int.floor_add_fract (cfCompleteQuotient (√(d : ℝ)) n)
    rw [h0, add_zero] at h
    exact h.symm
  have hmul : ((sqrtCFState d n).1 : ℝ) + √(d : ℝ) =
      ((⌊cfCompleteQuotient (√(d : ℝ)) n⌋ : ℤ) : ℝ) * ((sqrtCFState d n).2 : ℝ) := by
    have h1 : (((sqrtCFState d n).1 : ℝ) + √(d : ℝ)) / ((sqrtCFState d n).2 : ℝ) =
        ((⌊cfCompleteQuotient (√(d : ℝ)) n⌋ : ℤ) : ℝ) := by
      rw [← hξ]
      exact hfloor
    rwa [div_eq_iff hQℝ] at h1
  have hsqrt : √(d : ℝ) =
      ((⌊cfCompleteQuotient (√(d : ℝ)) n⌋ : ℤ) : ℝ) * ((sqrtCFState d n).2 : ℝ) -
        ((sqrtCFState d n).1 : ℝ) := by
    linarith [hmul]
  exact (irr_sqrt_natCast d hd hns).ne_rat
    (((⌊cfCompleteQuotient (√(d : ℝ)) n⌋ : ℤ) * (sqrtCFState d n).2 -
      (sqrtCFState d n).1 : ℤ) : ℚ)
    (by push_cast; exact hsqrt)

private theorem one_lt_cfCompleteQuotient_sqrt (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare (d : ℤ))
    {n : ℕ} (hn : 1 ≤ n) : 1 < cfCompleteQuotient (√(d : ℝ)) n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [cfCompleteQuotient_succ]
  rw [one_lt_inv₀ (cfCompleteQuotient_sqrt_fract_pos d hd hns k)]
  exact Int.fract_lt_one _

/-! ## 一步递推的界 -/

private theorem sqrtCFStep_bounds (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare (d : ℤ))
    {P Q : ℤ} (hP0 : 0 < P) (hPu : (P : ℝ) < √(d : ℝ)) (hQ0 : 0 < Q)
    (hQu : (Q : ℝ) < 2 * √(d : ℝ)) (hQ : Q ≠ 0) (hdvd : Q ∣ (d : ℤ) - P ^ 2)
    {ξ : ℝ} (hξ : ξ = ((P : ℝ) + √(d : ℝ)) / (Q : ℝ)) (hξ1 : 1 < ξ) :
    0 < ⌊ξ⌋ * Q - P ∧
      ((⌊ξ⌋ * Q - P : ℤ) : ℝ) < √(d : ℝ) ∧
      0 < ((d : ℤ) - (⌊ξ⌋ * Q - P) ^ 2) / Q ∧
      ((((d : ℤ) - (⌊ξ⌋ * Q - P) ^ 2) / Q : ℤ) : ℝ) < 2 * √(d : ℝ) ∧
      (Int.fract ξ)⁻¹ = (Q : ℝ) / (√(d : ℝ) - ((⌊ξ⌋ * Q - P : ℤ) : ℝ)) := by
  set P' : ℤ := ⌊ξ⌋ * Q - P with hP'def
  set Q' : ℤ := ((d : ℤ) - P' ^ 2) / Q with hQ'def
  have hQℝ : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  have hQ0ℝ : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hIrr : Irrational (√(d : ℝ)) := irr_sqrt_natCast d hd hns
  have hP'cast : (P' : ℝ) = (⌊ξ⌋ : ℝ) * (Q : ℝ) - (P : ℝ) := by
    rw [hP'def]; push_cast; ring
  have hfract : Int.fract ξ = (√(d : ℝ) - (P' : ℝ)) / (Q : ℝ) := by
    have h2 : ξ - (⌊ξ⌋ : ℝ) = ((P : ℝ) + √(d : ℝ) - ⌊ξ⌋ * (Q : ℝ)) / (Q : ℝ) := by
      rw [hξ]
      field_simp
    have h3 : (√(d : ℝ) - (P' : ℝ)) / (Q : ℝ) =
        ((P : ℝ) + √(d : ℝ) - ⌊ξ⌋ * (Q : ℝ)) / (Q : ℝ) := by
      rw [hP'def]
      push_cast
      ring
    rw [← Int.self_sub_floor ξ, h2, ← h3]
  have hP'_ne : (√(d : ℝ) - (P' : ℝ)) ≠ 0 := by
    intro h0
    have hPeq : (P' : ℝ) = √(d : ℝ) := by linarith
    exact hIrr.ne_rat (P' : ℚ) (by push_cast; linarith)
  have hinv : (Int.fract ξ)⁻¹ = (Q : ℝ) / (√(d : ℝ) - (P' : ℝ)) := by
    rw [hfract, inv_div]
  have hfract_pos : 0 < Int.fract ξ := by
    refine lt_of_le_of_ne (Int.fract_nonneg ξ) (Ne.symm ?_)
    rw [hfract]
    exact div_ne_zero hP'_ne hQℝ
  have hξ'1 : 1 < (Int.fract ξ)⁻¹ := by
    rw [one_lt_inv₀ hfract_pos]
    exact Int.fract_lt_one ξ
  have hsub : √(d : ℝ) - (P' : ℝ) = (Q : ℝ) / (Int.fract ξ)⁻¹ := by
    rw [hinv]
    field_simp
  have hsub_pos : 0 < √(d : ℝ) - (P' : ℝ) := by
    rw [hsub]
    exact div_pos hQ0ℝ (by positivity)
  have hsub_lt : √(d : ℝ) - (P' : ℝ) < (Q : ℝ) := by
    rw [hsub, div_lt_iff₀ (by positivity : (0 : ℝ) < (Int.fract ξ)⁻¹)]
    nlinarith [hξ'1, hQ0ℝ]
  have hP'lt : (P' : ℝ) < √(d : ℝ) := by linarith
  have hP'pos : 0 < P' := by
    by_contra hcon
    have hle : P' ≤ 0 := not_lt.mp hcon
    have hleℝ : (P' : ℝ) ≤ 0 := by exact_mod_cast hle
    have haQ_le : (⌊ξ⌋ : ℝ) * (Q : ℝ) ≤ (P : ℝ) := by linarith [hP'cast]
    have ha_gt : ξ - 1 < (⌊ξ⌋ : ℝ) := by
      have := Int.lt_floor_add_one ξ
      linarith
    have hξQ : ξ * (Q : ℝ) = (P : ℝ) + √(d : ℝ) := by
      rw [hξ]; field_simp
    have hQ_gt : √(d : ℝ) < (Q : ℝ) := by nlinarith [haQ_le, ha_gt, hQ0ℝ, hξQ]
    have hξ_lt_two : ξ < 2 := by
      rw [hξ, div_lt_iff₀ hQ0ℝ]
      nlinarith [hPu, hQ_gt]
    have ha_one : ⌊ξ⌋ = 1 := by
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩ <;> norm_num <;> linarith
    have hposℝ : (0 : ℝ) < (P' : ℝ) := by
      have : (P' : ℝ) = (Q : ℝ) - (P : ℝ) := by rw [hP'cast, ha_one]; ring
      linarith [hQ_gt, hPu]
    exact absurd (by exact_mod_cast hposℝ : 0 < P') hcon
  have hdvd' : Q ∣ (d : ℤ) - P' ^ 2 := by
    obtain ⟨m, hm⟩ := hdvd
    refine ⟨m - ⌊ξ⌋ ^ 2 * Q + 2 * ⌊ξ⌋ * P, ?_⟩
    have hkey : (d : ℤ) - P' ^ 2 =
        ((d : ℤ) - P ^ 2) - ⌊ξ⌋ ^ 2 * Q ^ 2 + 2 * ⌊ξ⌋ * Q * P := by
      rw [hP'def]; ring
    rw [hkey, hm]; ring
  have hQQ' : Q * Q' = (d : ℤ) - P' ^ 2 := by
    rw [hQ'def]; exact Int.mul_ediv_cancel' hdvd'
  have hdP' : (d : ℤ) - P' ^ 2 ≠ 0 := by
    intro h0
    refine hns ⟨P', ?_⟩
    rw [← sq]; linarith
  have hQ'ne : Q' ≠ 0 := by
    intro h0
    have hzero : Q * Q' = 0 := by rw [h0, mul_zero]
    rw [hQQ'] at hzero
    exact hdP' hzero
  have hcast : (Q' : ℝ) = ((d : ℝ) - (P' : ℝ) ^ 2) / (Q : ℝ) := by
    rw [eq_div_iff hQℝ, mul_comm]
    exact_mod_cast hQQ'
  have hQ'pos : 0 < Q' := by
    have hsq : (P' : ℝ) ^ 2 < (d : ℝ) := by
      have hnn : (0 : ℝ) ≤ (P' : ℝ) := by exact_mod_cast hP'pos.le
      nlinarith [hP'lt, hnn, Real.sq_sqrt (show (0 : ℝ) ≤ (d : ℝ) by positivity)]
    have hpos : (0 : ℝ) < (d : ℝ) - (P' : ℝ) ^ 2 := by linarith
    have : (0 : ℝ) < (Q' : ℝ) := by
      rw [hcast]
      exact div_pos hpos hQ0ℝ
    exact_mod_cast this
  have hQ'lt : (Q' : ℝ) < 2 * √(d : ℝ) := by
    have hD : (d : ℝ) - (P' : ℝ) ^ 2 =
        (√(d : ℝ) - (P' : ℝ)) * (√(d : ℝ) + (P' : ℝ)) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (d : ℝ) by positivity)]
    have h1 : (√(d : ℝ) - (P' : ℝ)) / (Q : ℝ) = 1 / (Int.fract ξ)⁻¹ := by
      rw [hinv]
      field_simp
    rw [hcast, hD, ← div_mul_eq_mul_div, h1, one_div, inv_mul_eq_div]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (Int.fract ξ)⁻¹)]
    nlinarith [hP'lt, hξ'1, sqrt_natCast_pos d hd]
  exact ⟨hP'pos, hP'lt, hQ'pos, hQ'lt, hinv⟩

/-! ## 状态序列的界 -/

private theorem sqrtCFState_bounds (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare (d : ℤ)) :
    ∀ n, 1 ≤ n →
      0 < (sqrtCFState d n).1 ∧ ((sqrtCFState d n).1 : ℝ) < √(d : ℝ) ∧
        0 < (sqrtCFState d n).2 ∧ ((sqrtCFState d n).2 : ℝ) < 2 * √(d : ℝ) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hstate : sqrtCFState d 1 = (⌊√(d : ℝ)⌋, (d : ℤ) - ⌊√(d : ℝ)⌋ ^ 2) := by
        simp [sqrtCFState_eq_iterate, sqrtCFStep, sqrtCFPartialQuotient]
      rw [hstate]
      have hIrr : Irrational (√(d : ℝ)) := irr_sqrt_natCast d hd hns
      have ha0_nonneg : (0 : ℤ) ≤ ⌊√(d : ℝ)⌋ :=
        Int.le_floor.mpr (by push_cast; positivity)
      have ha0_pos : 0 < ⌊√(d : ℝ)⌋ := by
        have h1 : (1 : ℤ) ≤ ⌊√(d : ℝ)⌋ :=
          Int.le_floor.mpr (by push_cast; exact le_of_lt (one_lt_sqrt_natCast d hd hns))
        omega
      have ha0_lt : (⌊√(d : ℝ)⌋ : ℝ) < √(d : ℝ) := by
        refine lt_of_le_of_ne (Int.floor_le _) ?_
        intro h
        exact hIrr.ne_rat (⌊√(d : ℝ)⌋ : ℚ) (by push_cast; exact h.symm)
      refine ⟨ha0_pos, ha0_lt, ?_, ?_⟩
      · have hsq : (√(d : ℝ)) ^ 2 = (d : ℝ) := Real.sq_sqrt (by positivity)
        have h1 : ((⌊√(d : ℝ)⌋ : ℤ) : ℝ) ^ 2 < (d : ℝ) := by
          have hnn : (0 : ℝ) ≤ ((⌊√(d : ℝ)⌋ : ℤ) : ℝ) := by exact_mod_cast ha0_nonneg
          nlinarith [ha0_lt, hnn, hsq]
        have h2 : (((⌊√(d : ℝ)⌋ : ℤ) ^ 2 : ℤ) : ℝ) < ((d : ℤ) : ℝ) := by push_cast; exact h1
        have h3 : (⌊√(d : ℝ)⌋ : ℤ) ^ 2 < (d : ℤ) := by exact_mod_cast h2
        omega
      · have hlt1 : √(d : ℝ) - ((⌊√(d : ℝ)⌋ : ℤ) : ℝ) < 1 := by
          have := Int.lt_floor_add_one (√(d : ℝ)); linarith
        have hlt2 : √(d : ℝ) + ((⌊√(d : ℝ)⌋ : ℤ) : ℝ) ≤ 2 * √(d : ℝ) := by
          have := Int.floor_le (√(d : ℝ)); linarith
        have hprod := mul_lt_mul hlt1 hlt2
          (by positivity : (0 : ℝ) < √(d : ℝ) + ((⌊√(d : ℝ)⌋ : ℤ) : ℝ))
          (by norm_num : (0 : ℝ) ≤ 1)
        have hsq : (√(d : ℝ)) ^ 2 = (d : ℝ) := Real.sq_sqrt (by positivity)
        push_cast
        nlinarith [hprod, hsq]
    · obtain ⟨hP0, hPu, hQ0, hQu⟩ := ih hn
      obtain ⟨hQne, hdvd, hξ⟩ := sqrtCFState_spec d hd hns n
      have hξ1 : 1 < cfCompleteQuotient (√(d : ℝ)) n := one_lt_cfCompleteQuotient_sqrt d hd hns hn
      have hstep := sqrtCFStep_bounds d hd hns hP0 hPu hQ0 hQu hQne hdvd hξ hξ1
      have hstate : sqrtCFState d (n + 1) =
          (⌊cfCompleteQuotient (√(d : ℝ)) n⌋ * (sqrtCFState d n).2 - (sqrtCFState d n).1,
            ((d : ℤ) - (⌊cfCompleteQuotient (√(d : ℝ)) n⌋ * (sqrtCFState d n).2 -
              (sqrtCFState d n).1) ^ 2) / (sqrtCFState d n).2) := by
        rw [sqrtCFState_succ, sqrtCFStep_apply, sqrtCFPartialQuotient, ← hξ]
      have h1 : (sqrtCFState d (n + 1)).1 =
          ⌊cfCompleteQuotient (√(d : ℝ)) n⌋ * (sqrtCFState d n).2 - (sqrtCFState d n).1 := by
        rw [hstate]
      have h2 : (sqrtCFState d (n + 1)).2 =
          ((d : ℤ) - (⌊cfCompleteQuotient (√(d : ℝ)) n⌋ * (sqrtCFState d n).2 -
            (sqrtCFState d n).1) ^ 2) / (sqrtCFState d n).2 := by
        rw [hstate]
      rw [h1, h2]
      exact ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1⟩

/-! ## 鸽笼 -/

private theorem sqrtCFState_mem_box (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare (d : ℤ)) :
    ∀ n, 1 ≤ n → sqrtCFState d n ∈
      Finset.Icc (1 : ℤ) ⌊√(d : ℝ)⌋ ×ˢ Finset.Icc (1 : ℤ) ⌊2 * √(d : ℝ)⌋ := by
  intro n hn
  obtain ⟨hP0, hPu, hQ0, hQu⟩ := sqrtCFState_bounds d hd hns n hn
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨⟨hP0, Int.le_floor.mpr (le_of_lt hPu)⟩, ⟨hQ0, Int.le_floor.mpr (le_of_lt hQu)⟩⟩

private theorem exists_sqrtCFState_repetition (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare (d : ℤ)) :
    ∃ N L : ℕ, 0 < L ∧
      L ≤ (Finset.Icc (1 : ℤ) ⌊√(d : ℝ)⌋ ×ˢ Finset.Icc (1 : ℤ) ⌊2 * √(d : ℝ)⌋).card ∧
      sqrtCFState d N = sqrtCFState d (N + L) := by
  classical
  set T : Finset (ℤ × ℤ) :=
    Finset.Icc (1 : ℤ) ⌊√(d : ℝ)⌋ ×ˢ Finset.Icc (1 : ℤ) ⌊2 * √(d : ℝ)⌋ with hT
  have hmaps : Set.MapsTo (fun i : Fin (T.card + 1) => sqrtCFState d ((i : ℕ) + 1))
      ↑(Finset.univ : Finset (Fin (T.card + 1))) ↑T := by
    intro i _
    exact sqrtCFState_mem_box d hd hns ((i : ℕ) + 1) (by omega)
  have hlt : T.card < (Finset.univ : Finset (Fin (T.card + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i, -, j, -, hij, hst⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset (Fin (T.card + 1)))) (t := T) hlt hmaps
  have hjcard : (j : ℕ) ≤ T.card := by
    have := j.2
    omega
  rcases lt_or_gt_of_ne hij with hltij | hgtij
  · refine ⟨(i : ℕ) + 1, (j : ℕ) - (i : ℕ), by omega, by omega, ?_⟩
    have hidx : (i : ℕ) + 1 + ((j : ℕ) - (i : ℕ)) = (j : ℕ) + 1 := by omega
    rw [hidx]
    exact hst
  · refine ⟨(j : ℕ) + 1, (i : ℕ) - (j : ℕ), by omega, by omega, ?_⟩
    have hidx : (j : ℕ) + 1 + ((i : ℕ) - (j : ℕ)) = (i : ℕ) + 1 := by omega
    rw [hidx]
    exact hst.symm

/-! ## 周期性 -/

private theorem sqrtCF_period_of_state_eq (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare (d : ℤ))
    {N L : ℕ} (hstate : sqrtCFState d N = sqrtCFState d (N + L)) :
    ∀ n, N ≤ n → cfDigit (√(d : ℝ)) (n + L) = cfDigit (√(d : ℝ)) n := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hiter : sqrtCFState d (N + k) = sqrtCFState d (N + L + k) := by
    have h1 : sqrtCFState d (N + k) = (sqrtCFStep d)^[k] (sqrtCFState d N) := by
      rw [sqrtCFState_eq_iterate, Nat.add_comm N k, Function.iterate_add_apply,
        ← sqrtCFState_eq_iterate]
    have h2 : sqrtCFState d (N + L + k) = (sqrtCFStep d)^[k] (sqrtCFState d (N + L)) := by
      rw [sqrtCFState_eq_iterate, Nat.add_comm (N + L) k, Function.iterate_add_apply,
        ← sqrtCFState_eq_iterate]
    rw [h1, h2, hstate]
  have hdigit : ∀ m : ℕ, cfDigit (√(d : ℝ)) m = sqrtCFPartialQuotient d (sqrtCFState d m) := by
    intro m
    simp only [cfDigit, sqrtCFPartialQuotient, (sqrtCFState_spec d hd hns m).2.2]
  rw [show N + k + L = N + L + k by omega, hdigit, hdigit, hiter]

/-- **`√d` 的连分数数位序列最终周期。** 对正整数 `d`，若 `d` 不是完全平方数，
则 `√d` 的连分数数位序列 `aₙ = ⌊ξₙ⌋` 从某项起周期。

证明走整数状态递推：完全商总可写成 `ξₙ = (Pₙ + √d)/Qₙ`，其中 `(Pₙ, Qₙ)` 由
`Pₙ₊₁ = aₙQₙ - Pₙ`、`Qₙ₊₁ = (d - Pₙ₊₁²)/Qₙ` 递推；对 `n ≥ 1` 有 `0 < Pₙ < √d`、
`0 < Qₙ < 2√d`，故状态只落在有限多个整数点上，鸽笼给出重复，而递推的确定性把重复提升为周期。

> **Entry**: number-theory.elementary.sqrt-periodic-cf
@isnad1 id=iseventu.2h1v.s4.4ab7d83137f9 from=translated src=- shape=a9a2f348 vocab=8949ccf6
-/
theorem cfDigit_sqrt_eventuallyPeriodic (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare (d : ℤ)) :
    IsEventuallyPeriodic (cfDigit (√(d : ℝ))) := by
  obtain ⟨N, L, hL, -, hstate⟩ := exists_sqrtCFState_repetition d hd hns
  exact ⟨N, L, hL, sqrtCF_period_of_state_eq d hd hns hstate⟩

/-- **周期长度的显式上界。** `√d` 的连分数数位序列存在周期 `L`，且 `L ≤ 2d`。

这是本条能做到的定量强度。注意 `2d` **不是**判别式界：判别式只由 `d` 的无平方因子部分决定
（若 `d = k²m`、`m` 无平方因子，则 `ℚ(√d)` 的判别式为 `m`（当 `m ≡ 1 mod 4`）或 `4m`），
例如 `d = 18 = 3²·2` 的判别式为 `8 < d`。因此只有当 `d` 无平方因子时才有
`L ≤ 2d ≤ 2·disc`；对一般的非平方 `d`，本条只主张 `L ≤ 2d`。周期长度与判别式的精确关系
（与基本单位、类数、负 Pell 方程可解性的联系）在本库中尚未形式化。

> **Entry**: number-theory.elementary.sqrt-periodic-cf
@isnad1 id=ex.2h1v.s6.0b58789838f9 from=translated src=- shape=3bbebe85 vocab=f791cb1c
-/
theorem exists_cfDigit_sqrt_period_le (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare (d : ℤ)) :
    ∃ N L : ℕ, 0 < L ∧ L ≤ 2 * d ∧
      ∀ n, N ≤ n → cfDigit (√(d : ℝ)) (n + L) = cfDigit (√(d : ℝ)) n := by
  obtain ⟨N, L, hL, hLcard, hstate⟩ := exists_sqrtCFState_repetition d hd hns
  refine ⟨N, L, hL, ?_, sqrtCF_period_of_state_eq d hd hns hstate⟩
  have hcard : (Finset.Icc (1 : ℤ) ⌊√(d : ℝ)⌋ ×ˢ Finset.Icc (1 : ℤ) ⌊2 * √(d : ℝ)⌋).card =
      (⌊√(d : ℝ)⌋).toNat * (⌊2 * √(d : ℝ)⌋).toNat := by
    rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
    norm_num
  rw [hcard] at hLcard
  have hfl1 : (0 : ℤ) ≤ ⌊√(d : ℝ)⌋ := Int.floor_nonneg.mpr (by positivity)
  have hfl2 : (0 : ℤ) ≤ ⌊2 * √(d : ℝ)⌋ := Int.floor_nonneg.mpr (by positivity)
  have h1 : ((⌊√(d : ℝ)⌋).toNat : ℝ) ≤ √(d : ℝ) := by
    have hz : ((⌊√(d : ℝ)⌋).toNat : ℤ) = ⌊√(d : ℝ)⌋ := Int.toNat_of_nonneg hfl1
    have hcast : ((⌊√(d : ℝ)⌋).toNat : ℝ) = (⌊√(d : ℝ)⌋ : ℝ) := by
      rw [← Int.cast_natCast, hz]
    rw [hcast]
    exact Int.floor_le _
  have h2 : ((⌊2 * √(d : ℝ)⌋).toNat : ℝ) ≤ 2 * √(d : ℝ) := by
    have hz : ((⌊2 * √(d : ℝ)⌋).toNat : ℤ) = ⌊2 * √(d : ℝ)⌋ := Int.toNat_of_nonneg hfl2
    have hcast : ((⌊2 * √(d : ℝ)⌋).toNat : ℝ) = (⌊2 * √(d : ℝ)⌋ : ℝ) := by
      rw [← Int.cast_natCast, hz]
    rw [hcast]
    exact Int.floor_le _
  have hreal : (((⌊√(d : ℝ)⌋).toNat * (⌊2 * √(d : ℝ)⌋).toNat : ℕ) : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by
    push_cast
    nlinarith [h1, h2, Real.sq_sqrt (show (0 : ℝ) ≤ (d : ℝ) by positivity)]
  exact le_trans hLcard (by exact_mod_cast hreal)

/-! ## 特例：`d = a² + 1` -/

/-- **`d = a² + 1` 的显式特例。** 当 `a ≥ 1` 时，`√(a² + 1)` 的数位从 `n = 1` 起恒为 `2a`：
`√d + a` 是 Gauss 映射的不动点（因为 `(√d - a)(√d + a) = d - a² = 1`，故 `(√d - a)⁻¹ = √d + a`），
于是完全商从 `ξ₁ = √d + a` 起不再变化，数位恒为 `⌊√d + a⌋ = 2a`。这给出周期长度 `1` 的显式
实例（`d = a² + 1`，如 `a = 1` 时 `d = 2`、`a = 2` 时 `d = 5`）。注意判别式由 `d` 的无平方
因子部分决定，与 `d` 本身可能相差一个平方因子（如 `a = 7` 时 `d = 50 = 2·5²`，判别式为 `8`），
故这里不把周期长度与 `2d` 或判别式直接挂钩。

> **Entry**: number-theory.elementary.sqrt-periodic-cf
@isnad1 id=eq.2h2v.s6.c29242f3f310 from=translated src=- shape=e61722b4 vocab=4eaea031
-/
theorem cfDigit_sqrt_sq_add_one (a : ℕ) (ha : 1 ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    cfDigit (√(((a ^ 2 + 1 : ℕ) : ℝ))) n = 2 * (a : ℤ) := by
  set d : ℕ := a ^ 2 + 1 with hd
  set s : ℝ := √(d : ℝ) with hs
  have hd_pos : (0 : ℝ) < (d : ℝ) := by
    rw [hd]; push_cast; positivity
  have hsq : s ^ 2 = (d : ℝ) := Real.sq_sqrt hd_pos.le
  have ha_lt : (a : ℝ) < s := by
    rw [hs, Real.lt_sqrt (by positivity : (0 : ℝ) ≤ (a : ℝ)), hd]
    push_cast
    linarith
  have ha_one : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hs_lt : s < (a : ℝ) + 1 := by
    rw [hs, Real.sqrt_lt' (by positivity : (0 : ℝ) < (a : ℝ) + 1), hd]
    push_cast
    nlinarith [sq_nonneg (a : ℝ), ha_one]
  have hfloor_s : ⌊s⌋ = (a : ℤ) := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith
  have hfract_s : Int.fract s = s - (a : ℝ) := by
    rw [← Int.self_sub_floor s, hfloor_s]
    push_cast
    ring
  have hinv : (s - (a : ℝ))⁻¹ = s + (a : ℝ) := by
    refine inv_eq_of_mul_eq_one_right ?_
    have h1 : (s - (a : ℝ)) * (s + (a : ℝ)) = s ^ 2 - (a : ℝ) ^ 2 := by ring
    rw [h1, hsq, hd]
    push_cast
    ring
  have hfloor_sa : ⌊s + (a : ℝ)⌋ = 2 * (a : ℤ) := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith
  have hfix : cfGaussMap (s + (a : ℝ)) = s + (a : ℝ) := by
    rw [cfGaussMap]
    have h2 : Int.fract (s + (a : ℝ)) = s - (a : ℝ) := by
      rw [← Int.self_sub_floor (s + (a : ℝ)), hfloor_sa]
      push_cast
      ring
    rw [h2, hinv]
  have hq1 : cfCompleteQuotient s 1 = s + (a : ℝ) := by
    rw [cfCompleteQuotient_succ, cfCompleteQuotient_zero, hfract_s, hinv]
  have hiter : ∀ k : ℕ, (cfGaussMap^[k]) (s + (a : ℝ)) = s + (a : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hquot : cfCompleteQuotient s (1 + k) = s + (a : ℝ) := by
    rw [cfCompleteQuotient_add, hq1, hiter k]
  simp only [cfDigit, hquot, hfloor_sa]

end SandronesLibrary.NumberTheory.Elementary
