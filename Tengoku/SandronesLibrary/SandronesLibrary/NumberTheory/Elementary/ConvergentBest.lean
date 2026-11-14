/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.NumberTheory.Elementary.ContinuedFractions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 收敛子是最佳有理逼近

本文件补上 `ContinuedFractions.lean` 明确留空的那一半：教材中「每个连分数渐近分数都是最佳有理逼近」
这一定理。前置文件只形式化了 Legendre 判别准则（误差足够小 ⇒ 是渐近分数），本文件交付**相反方向**
（是渐近分数 ⇒ 在该分母预算内误差最小）。

## 证明骨架

设 `ξ` 无理，`g = GenContFract.of ξ`，记 `Pₙ = g.nums n`、`Qₙ = g.dens n`。证明分四层：

1. **整数性**：`of ξ` 的部分分子恒为 `1`、部分分母恒为整数，故 continuants 是整数对，
   于是存在整数 `pₙ, qₙ` 使 `Pₙ = ↑pₙ`、`Qₙ = ↑qₙ`。本文件用 `continuantNumerator` /
   `continuantDenominator` 把这对整数抽出来。
2. **幺模性**：`SimpContFract.determinant` 给出 `pₙ qₙ₊₁ - qₙ pₙ₊₁ = ±1`。这条等式让
   `(pₙ, qₙ)`、`(pₙ₊₁, qₙ₊₁)` 构成 `ℤ²` 的一组基，于是任何有理数 `p/q` 都能唯一写成
   `a (pₙ, qₙ) + b (pₙ₊₁, qₙ₊₁)`。
3. **符号交替**：`sub_convs_eq` 给出 `ξ - convs n = (-1)ⁿ / D`（`D > 0`），故
   `δₙ = qₙ ξ - pₙ` 与 `δₙ₊₁` 反号。这是全证明中唯一需要「连分数收敛子交替地从两侧逼近」的地方。
4. **组装**：对 `0 < q ≤ Qₙ < Qₙ₊₁` 的 `p/q` 做基分解。`q = a qₙ + b qₙ₊₁` 与
   `0 < q < Qₙ₊₁` 逼出 `a b ≤ 0` 且 `a ≠ 0`；配合 `δ` 反号得
   `|q ξ - p| = |a| |δₙ| + |b| |δₙ₊₁| ≥ |δₙ|`。除以 `q ≤ Qₙ` 即得结论。

## 边界（必须写清）

* `n = 0` 时命题**为假**：`ξ = 1.7` 的第 0 个收敛子是 `1`，误差 `0.7`；而 `2/1` 的分母也是 `1`，
  误差 `0.3 < 0.7`。所以 `1 ≤ n` 是本质假设，不是形式化噪声。根源是 `Q₀ = 1 ≤ Q₁` 可能取等号
  （`Q₁ = ⌊1/fract ξ⌋ = 1` 当 `fract ξ ∈ (1/2, 1)`），而证明中 `Qₙ < Qₙ₊₁` 正是从 `n ≥ 1` 才成立。
* 结论按**分母预算**（第一类最佳逼近）比较误差，允许并列；它不强于「第二类最佳逼近」
  （`|q ξ - p| ≥ |qₙ ξ - pₙ|`，本文件的核心引理 `abs_sub_convergent_le_of_decomposition` 实际证明了后者）。

## 与 `number-theory.elementary.legendre-criterion` 的方向关系

* Legendre 判别准则：`IsLegendreApproximation ξ q ⇒ ∃ n, q = continuedFractionConvergent ξ n`
  （误差足够小 ⇒ 是收敛子），是**充分**判据。
* 本文件：`IsBestRationalApproximation ξ (continuedFractionConvergent ξ n)`（`n ≥ 1`）
  （是收敛子 ⇒ 最佳逼近），是**另一条轴**上的陈述。
* 两者互不蕴含，是两条不同的轴：
  * 本条的假设「是收敛子」不蕴含「误差 < 1/(2 q.den²)」：`ξ = [0; 100, 1, 1, 1, …]` 的第 1 个
    收敛子 `1/100` 误差约 `6.14×10⁻⁵`，大于阈值 `5×10⁻⁵`；
  * Legendre 的结论「是某个收敛子」只是身份，不含分母预算下的最优性，而且允许 `n = 0`，
    而本条在 `n = 0` 时是假的。
* 第一类最佳逼近的**逆命题为假**：`√2` 的 `4/3`（收敛子 `1/1` 与 `3/2` 的中介分数）在分母预算
  `≤ 3` 内误差最小，却不在收敛子序列 `1/1, 3/2, 7/5, 17/12, …` 中。注意方向：`4/3` 是**真**
  最佳逼近，所以 `¬ IsBestRationalApproximation (√2) (4/3)` 是假命题，不能写成定理。
  这两个反例本条均未形式化，只在文档里作未经形式化的说明。

## 本文件条目

* `number-theory.elementary.convergent-best`
-/

namespace SandronesLibrary.NumberTheory.Elementary

open GenContFract

/-- 结构引理（整数性）：`of ξ` 的 continuants `⟨Aₙ, Bₙ⟩` 都是整数对。

`of ξ` 的部分分子恒为 `1`（`of_partNum_eq_one`），部分分母恒为整数
（`exists_int_eq_of_partDen`）；continuants 由 `⟨1, 0⟩`、`⟨⌊ξ⌋, 1⟩` 出发按这两个数递推，
故每一步都保持整数性。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=ex.0h2v.s5.3e4a7ec62496 from=translated src=- shape=4b028adf vocab=29e7166c
-/
theorem exists_int_contsAux (ξ : ℝ) (n : ℕ) :
    ∃ a b : ℤ, (GenContFract.of ξ).contsAux n = ⟨(a : ℝ), (b : ℝ)⟩ := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨1, 0, by simp [GenContFract.contsAux]⟩
  | one =>
    refine ⟨⌊ξ⌋, 1, ?_⟩
    simp [GenContFract.contsAux, GenContFract.of_h_eq_floor]
  | more n ih1 ih2 =>
    obtain ⟨a₁, b₁, h₁⟩ := ih1
    obtain ⟨a₂, b₂, h₂⟩ := ih2
    rcases h : (GenContFract.of ξ).s.get? n with _ | gp
    · refine ⟨a₂, b₂, ?_⟩
      simp only [GenContFract.contsAux, h]
      exact h₂
    · obtain ⟨hga, z, hz⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq h
      refine ⟨z * a₂ + a₁, z * b₂ + b₁, ?_⟩
      rw [GenContFract.contsAux_recurrence h h₁ h₂, hga, hz]
      simp

/-- 结构引理（整数性）：`of ξ` 的第 `n` 个分子 `Aₙ` 是某个整数的像。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=ex.0h2v.s4.312aa14804d5 from=translated src=- shape=dff55127 vocab=5b7c61c6
-/
theorem exists_int_nums (ξ : ℝ) (n : ℕ) :
    ∃ z : ℤ, (GenContFract.of ξ).nums n = (z : ℝ) := by
  obtain ⟨a, bb, h⟩ := exists_int_contsAux ξ (n + 1)
  refine ⟨a, ?_⟩
  rw [GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux, h]

/-- 结构引理（整数性）：`of ξ` 的第 `n` 个分母 `Bₙ` 是某个整数的像。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=ex.0h2v.s4.b932adc62f14 from=translated src=- shape=dff55127 vocab=5d1b6c66
-/
theorem exists_int_dens (ξ : ℝ) (n : ℕ) :
    ∃ z : ℤ, (GenContFract.of ξ).dens n = (z : ℝ) := by
  obtain ⟨a, bb, h⟩ := exists_int_contsAux ξ (n + 1)
  refine ⟨bb, ?_⟩
  rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, h]

/-- 无理数的连分数展开永不终止。

若 `of ξ` 在第 `n` 步终止，则它整体终止；`of_correctness_of_terminates` 说明终止的连分数
在第 `m` 个收敛子处精确等于原值，而收敛子是实数（由 `Real.convs_eq_convergent` 等于
`↑(ξ.convergent m)`），与 `Irrational ξ` 矛盾。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=not.1h2v.s4.721f64e65eec from=translated src=- shape=6e24495c vocab=7a50ed90
-/
theorem of_irrational_not_terminatedAt {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) :
    ¬(GenContFract.of ξ).TerminatedAt n := by
  intro h
  obtain ⟨m, hm⟩ := GenContFract.of_correctness_of_terminates (v := ξ) ⟨n, h⟩
  refine hξ ⟨ξ.convergent m, ?_⟩
  rw [Real.convs_eq_convergent] at hm
  exact hm.symm

/-- 结构引理：`of ξ` 的分母 `Qₙ = Bₙ` 恒为正。

由 `succ_nth_fib_le_of_nth_den` 得 `fib (n+1) ≤ Bₙ`，而 `fib (n+1) > 0`。
非终止性由此处第一次被用到（`n ≥ 1` 时要排除终止分支）。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=lt.1h2v.s4.68fe5735f973 from=translated src=- shape=f73e952b vocab=326386fa
-/
theorem dens_pos {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) :
    0 < (GenContFract.of ξ).dens n := by
  have h : (Nat.fib (n + 1) : ℝ) ≤ (GenContFract.of ξ).dens n := by
    rcases n with _ | n
    · exact GenContFract.succ_nth_fib_le_of_nth_den (Or.inl rfl)
    · exact GenContFract.succ_nth_fib_le_of_nth_den (Or.inr (of_irrational_not_terminatedAt hξ n))
  have h2 : (0 : ℝ) < (Nat.fib (n + 1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
  linarith

/-- 结构引理：分母的两步递推 `Bₙ₊₂ = bₙ₊₁ Bₙ₊₁ + Bₙ`（`bₙ₊₁` 是第 `n+1` 个部分分母）。

直接来自 `contsAux_recurrence`（此时部分分子为 `1`）。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=eq.1h3v.s6.37a8c344af7c from=translated src=- shape=240cbc67 vocab=41d5b8b0
-/
theorem dens_add_two (ξ : ℝ) (n : ℕ) {gp : GenContFract.Pair ℝ}
    (h : (GenContFract.of ξ).s.get? (n + 1) = some gp) :
    (GenContFract.of ξ).dens (n + 2) =
      gp.b * (GenContFract.of ξ).dens (n + 1) + (GenContFract.of ξ).dens n := by
  have hrec := GenContFract.contsAux_recurrence (g := GenContFract.of ξ) h rfl rfl
  have hpa : gp.a = 1 :=
    GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a h)
  simp only [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
  rw [hrec, hpa]
  simp

/-- 结构引理：`n ≥ 1` 时分母严格递增，`Qₙ < Qₙ₊₁`。

递推给出 `Qₙ₊₁ = bₙ Qₙ + Qₙ₋₁`，其中 `bₙ ≥ 1`、`Qₙ₋₁ > 0`，故 `Qₙ₊₁ > Qₙ`。
**`n = 0` 时不成立**（`Q₀ = Q₁ = 1` 可能出现，例如 `ξ = 1.7`），这正是主定理必须假设 `1 ≤ n` 的原因。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=lt.2h2v.s5.9af41d7f72e3 from=translated src=- shape=f95164b2 vocab=8014ee14
-/
theorem dens_lt_dens_succ {ξ : ℝ} (hξ : Irrational ξ) {n : ℕ} (hn : 1 ≤ n) :
    (GenContFract.of ξ).dens n < (GenContFract.of ξ).dens (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨gp, hgp⟩ : ∃ gp, (GenContFract.of ξ).s.get? (m + 1) = some gp := by
    have h : ¬(GenContFract.of ξ).TerminatedAt (m + 1) :=
      of_irrational_not_terminatedAt hξ (m + 1)
    rw [GenContFract.terminatedAt_iff_s_none] at h
    exact Option.ne_none_iff_exists'.mp h
  have hpart : (GenContFract.of ξ).partDens.get? (m + 1) = some gp.b := by
    simp [GenContFract.partDens, hgp]
  have hb1 : (1 : ℝ) ≤ gp.b := GenContFract.of_one_le_get?_partDen hpart
  rw [dens_add_two ξ m hgp]
  have h1 : (GenContFract.of ξ).dens (m + 1) ≤ gp.b * (GenContFract.of ξ).dens (m + 1) := by
    simpa using mul_le_mul_of_nonneg_right hb1 (le_of_lt (dens_pos hξ (m + 1)))
  linarith [dens_pos hξ m]

/-- `of ξ` 的第 `n` 个 continuant 分子 `Aₙ` 对应的整数 `pₙ`（`Pₙ = ↑pₙ`）。

它一般**不是**收敛子 `continuedFractionConvergent ξ n` 的约分分子：`Pₙ / Qₙ` 可能与
`pₙ / qₙ` 相差一个公因子。本文件只用它做 `ℤ²` 基分解，分母预算的比较另由
`convergent_den_le_continuantDenominator` 桥接。

> **Entry**: number-theory.elementary.convergent-best-/
noncomputable def continuantNumerator (ξ : ℝ) (n : ℕ) : ℤ := (exists_int_nums ξ n).choose

/-- `continuantNumerator` 的选取性质：`Pₙ = ↑(continuantNumerator ξ n)`。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=eq.0h2v.s4.c7bc779b5c85 from=translated src=- shape=dab02e07 vocab=26cddd54
-/
theorem nums_eq_continuantNumerator (ξ : ℝ) (n : ℕ) :
    (GenContFract.of ξ).nums n = (continuantNumerator ξ n : ℝ) :=
  (exists_int_nums ξ n).choose_spec

/-- `of ξ` 的第 `n` 个 continuant 分母 `Bₙ` 对应的整数 `qₙ`（`Qₙ = ↑qₙ`）。

> **Entry**: number-theory.elementary.convergent-best-/
noncomputable def continuantDenominator (ξ : ℝ) (n : ℕ) : ℤ := (exists_int_dens ξ n).choose

/-- `continuantDenominator` 的选取性质：`Qₙ = ↑(continuantDenominator ξ n)`。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=eq.0h2v.s4.e2899408aa17 from=translated src=- shape=dab02e07 vocab=a0ed7dc1
-/
theorem dens_eq_continuantDenominator (ξ : ℝ) (n : ℕ) :
    (GenContFract.of ξ).dens n = (continuantDenominator ξ n : ℝ) :=
  (exists_int_dens ξ n).choose_spec

/-- 结构引理（幺模性）：`pₙ qₙ₊₁ - qₙ pₙ₊₁ = (-1)ⁿ⁺¹`，特别地绝对值为 `1`。

由 `SimpContFract.determinant` 与无理数导致的非终止性得到。这条等式说明
`(pₙ, qₙ)` 与 `(pₙ₊₁, qₙ₊₁)` 构成 `ℤ²` 的一组基（行列式是单位），
从而任何有理数都能用它们线性表示——这是主证明的代数支点。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=eq.1h2v.s6.197504f0e34b from=translated src=- shape=d2377707 vocab=29ab2926
-/
theorem continuant_determinant (ξ : ℝ) (hξ : Irrational ξ) (n : ℕ) :
    continuantNumerator ξ n * continuantDenominator ξ (n + 1)
      - continuantDenominator ξ n * continuantNumerator ξ (n + 1) = (-1 : ℤ) ^ (n + 1) := by
  have h : (GenContFract.of ξ).nums n * (GenContFract.of ξ).dens (n + 1)
      - (GenContFract.of ξ).dens n * (GenContFract.of ξ).nums (n + 1) = (-1 : ℝ) ^ (n + 1) :=
    SimpContFract.determinant (s := SimpContFract.of ξ) (n := n)
      (of_irrational_not_terminatedAt hξ n)
  rw [nums_eq_continuantNumerator, dens_eq_continuantDenominator,
    nums_eq_continuantNumerator, dens_eq_continuantDenominator] at h
  exact_mod_cast h

/-- 侦察引理：非终止性保证第 `n` 个 `IntFractPair` 存在且其小数部分非零。

`sub_convs_eq` 需要「`stream ξ n = some ifp` 且 `ifp.fr ≠ 0`」这个假设，
本引理从 `stream ξ (n+1) ≠ none` 反推出它（`succ_nth_stream_eq_some_iff` 的第二项正是 `fr ≠ 0`）。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=ex.1h2v.s5.91fe7a231ca2 from=translated src=- shape=50aeb232 vocab=c51d8858
-/
theorem exists_stream_fr_ne_zero (ξ : ℝ) (hξ : Irrational ξ) (n : ℕ) :
    ∃ ifp : GenContFract.IntFractPair ℝ,
      GenContFract.IntFractPair.stream ξ n = some ifp ∧ ifp.fr ≠ 0 := by
  have h : GenContFract.IntFractPair.stream ξ (n + 1) ≠ none := by
    have h' := of_irrational_not_terminatedAt hξ n
    rwa [GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none] at h'
  obtain ⟨ifp, hifp⟩ := Option.ne_none_iff_exists'.mp h
  obtain ⟨ifp_n, hstream, hfr, -⟩ :=
    GenContFract.IntFractPair.succ_nth_stream_eq_some_iff.mp hifp
  exact ⟨ifp_n, hstream, hfr⟩

/-- 结构引理（误差符号）：`ξ - convs n = (-1)ⁿ / D`，其中 `D > 0`。

这是 `sub_convs_eq` 的直接改写：分母 `B (fr⁻¹ B + B')` 由 `B > 0`、`fr > 0`、`B' ≥ 0` 保证为正。
本文件对 `ξ` 的误差符号只此一个来源。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=ex.1h2v.s6.cf16c20891af from=translated src=- shape=23b19c06 vocab=8fbd7ef9
-/
theorem sub_convs_eq_neg_one_pow_div (ξ : ℝ) (hξ : Irrational ξ) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ξ - (GenContFract.of ξ).convs n = (-1) ^ n / D := by
  obtain ⟨ifp, hstream, hfr⟩ := exists_stream_fr_ne_zero ξ hξ n
  refine ⟨((GenContFract.of ξ).contsAux (n + 1)).b *
    (ifp.fr⁻¹ * ((GenContFract.of ξ).contsAux (n + 1)).b +
      ((GenContFract.of ξ).contsAux n).b), ?_, ?_⟩
  · have hB : 0 < ((GenContFract.of ξ).contsAux (n + 1)).b := by
      have hBeq : ((GenContFract.of ξ).contsAux (n + 1)).b = (GenContFract.of ξ).dens n := by
        rw [← GenContFract.nth_cont_eq_succ_nth_contAux, ← GenContFract.den_eq_conts_b]
      rw [hBeq]
      exact dens_pos hξ n
    have hfr0 : 0 < ifp.fr :=
      lt_of_le_of_ne (GenContFract.IntFractPair.nth_stream_fr_nonneg hstream) (Ne.symm hfr)
    have hpB : 0 ≤ ((GenContFract.of ξ).contsAux n).b := GenContFract.zero_le_of_contsAux_b
    positivity
  · rw [GenContFract.sub_convs_eq hstream, ite_eq_right hfr]

/-- 结构引理（符号交替）：`δₙ = Qₙ ξ - Pₙ` 与 `δₙ₊₁ = Qₙ₊₁ ξ - Pₙ₊₁` 反号，即 `δₙ δₙ₊₁ < 0`。

由 `δₙ = Qₙ (ξ - convs n)`（`Qₙ > 0`）与 `ξ - convs n = (-1)ⁿ / D`（`D > 0`）相乘得到。
几何含义：收敛子交替地从 `ξ` 的两侧逼近。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=lt.1h2v.s6.dfd58a4ab0ff from=translated src=- shape=c345ddbe vocab=c9a3996a
-/
theorem delta_mul_delta_succ_neg (ξ : ℝ) (hξ : Irrational ξ) (n : ℕ) :
    ((GenContFract.of ξ).dens n * ξ - (GenContFract.of ξ).nums n) *
      ((GenContFract.of ξ).dens (n + 1) * ξ - (GenContFract.of ξ).nums (n + 1)) < 0 := by
  obtain ⟨D₁, hD₁, h₁⟩ := sub_convs_eq_neg_one_pow_div ξ hξ n
  obtain ⟨D₂, hD₂, h₂⟩ := sub_convs_eq_neg_one_pow_div ξ hξ (n + 1)
  have e₁ : (GenContFract.of ξ).dens n * ξ - (GenContFract.of ξ).nums n
      = (GenContFract.of ξ).dens n * (ξ - (GenContFract.of ξ).convs n) := by
    rw [GenContFract.conv_eq_num_div_den]
    field_simp [ne_of_gt (dens_pos hξ n)]
  have e₂ : (GenContFract.of ξ).dens (n + 1) * ξ - (GenContFract.of ξ).nums (n + 1)
      = (GenContFract.of ξ).dens (n + 1) * (ξ - (GenContFract.of ξ).convs (n + 1)) := by
    rw [GenContFract.conv_eq_num_div_den]
    field_simp [ne_of_gt (dens_pos hξ (n + 1))]
  rw [e₁, e₂, h₁, h₂]
  have hQ₁ : 0 < (GenContFract.of ξ).dens n := dens_pos hξ n
  have hQ₂ : 0 < (GenContFract.of ξ).dens (n + 1) := dens_pos hξ (n + 1)
  have hnum : (GenContFract.of ξ).dens n * (GenContFract.of ξ).dens (n + 1) *
      ((-1 : ℝ) ^ n * (-1) ^ (n + 1)) < 0 := by
    rcases Nat.even_or_odd n with h | h
    · rw [h.neg_one_pow, h.add_one.neg_one_pow]
      nlinarith
    · rw [h.neg_one_pow, h.add_one.neg_one_pow]
      nlinarith
  have key : (GenContFract.of ξ).dens n * ((-1 : ℝ) ^ n / D₁) *
      ((GenContFract.of ξ).dens (n + 1) * ((-1 : ℝ) ^ (n + 1) / D₂))
      = ((GenContFract.of ξ).dens n * (GenContFract.of ξ).dens (n + 1) *
          ((-1 : ℝ) ^ n * (-1) ^ (n + 1))) / (D₁ * D₂) := by
    field_simp
  rw [key]
  exact div_neg_of_neg_of_pos hnum (mul_pos hD₁ hD₂)

/-- 桥：`↑(continuedFractionConvergent ξ n) = Pₙ / Qₙ`，即收敛子作为实数等于 continuant 之比。

由 `Real.convs_eq_convergent` 与 `conv_eq_num_div_den` 复合而成。这里 `continuedFractionConvergent`
是前置文件里 `Real.convergent` 的别名，`rw` 不展开它，故证明先 `change`。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=eq.0h2v.s5.d718ace1d7ec from=translated src=- shape=d90af01d vocab=f5d17fdf
-/
theorem convergent_cast_eq (ξ : ℝ) (n : ℕ) :
    ((continuedFractionConvergent ξ n : ℚ) : ℝ) =
      (continuantNumerator ξ n : ℝ) / (continuantDenominator ξ n : ℝ) := by
  change ((Real.convergent ξ n : ℚ) : ℝ) = _
  rw [← Real.convs_eq_convergent, GenContFract.conv_eq_num_div_den,
    nums_eq_continuantNumerator, dens_eq_continuantDenominator]

/-- 桥（分母预算）：约分后的分母不超过 continuant 分母，`(continuedFractionConvergent ξ n).den ≤ qₙ`。

`↑(conv n) = pₙ / qₙ`（`convergent_cast_eq` + `Rat.cast_divInt`）说明 `conv n = Rat.divInt pₙ qₙ`；
`Rat.den_dvd` 给出 `(conv n).den ∣ qₙ`，再用 `qₙ > 0` 与 `Int.le_of_dvd` 转成不等式。
这一步把「主证明里的整数分母预算」与「公开定义里的 `Rat.den`」接上。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=le.1h2v.s4.e8c7d696ee9f from=translated src=- shape=c73fc09b vocab=426b90f1
-/
theorem convergent_den_le_continuantDenominator (ξ : ℝ) (hξ : Irrational ξ) (n : ℕ) :
    ((continuedFractionConvergent ξ n).den : ℤ) ≤ continuantDenominator ξ n := by
  have hpos : 0 < continuantDenominator ξ n := by
    rw [← Int.cast_pos (R := ℝ), ← dens_eq_continuantDenominator]
    exact dens_pos hξ n
  have hq : continuedFractionConvergent ξ n
      = Rat.divInt (continuantNumerator ξ n) (continuantDenominator ξ n) := by
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_divInt, convergent_cast_eq]
  rw [hq]
  exact Int.le_of_dvd hpos (Rat.den_dvd _ _)

/-- **核心引理（第二类最佳逼近）**：若整数 `(p, q)` 沿基 `(pₙ, qₙ)`, `(pₙ₊₁, qₙ₊₁)` 分解为
`a (pₙ, qₙ) + b (pₙ₊₁, qₙ₊₁)`，且 `0 < q < Qₙ₊₁`，则 `|Qₙ ξ - Pₙ| ≤ |q ξ - p|`。

证明：`q ξ - p = a δₙ + b δₙ₊₁`（`δ` 反号）。`q = a qₙ + b qₙ₊₁ ∈ (0, Qₙ₊₁)` 排除了
`a b > 0`（同号则 `q ≥ Qₙ + Qₙ₊₁ > Qₙ₊₁` 或 `q < 0`）与 `a = 0`（否则 `0 < b < 1` 与整数矛盾），
故 `a b ≤ 0`，此时 `a δₙ` 与 `b δₙ₊₁` 同号，`|a δₙ + b δₙ₊₁| = |a| |δₙ| + |b| |δₙ₊₁| ≥ |δₙ|`。

这是教材中比主定理更强的「第二类」陈述；主定理只需把它除以分母预算。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=le.5h6v.s7.9c82626193e5 from=translated src=- shape=184d823e vocab=c6db5489
-/
theorem abs_sub_convergent_le_of_decomposition (ξ : ℝ) (hξ : Irrational ξ) (n : ℕ)
    {p q a b : ℤ}
    (hp : (p : ℝ) = (a : ℝ) * (continuantNumerator ξ n : ℝ)
      + (b : ℝ) * (continuantNumerator ξ (n + 1) : ℝ))
    (hq : (q : ℝ) = (a : ℝ) * (continuantDenominator ξ n : ℝ)
      + (b : ℝ) * (continuantDenominator ξ (n + 1) : ℝ))
    (hq0 : 0 < (q : ℝ))
    (hqlt : (q : ℝ) < (continuantDenominator ξ (n + 1) : ℝ)) :
    |(continuantDenominator ξ n : ℝ) * ξ - (continuantNumerator ξ n : ℝ)| ≤
      |(q : ℝ) * ξ - (p : ℝ)| := by
  have hδ : ((continuantDenominator ξ n : ℝ) * ξ - (continuantNumerator ξ n : ℝ)) *
      ((continuantDenominator ξ (n + 1) : ℝ) * ξ -
        (continuantNumerator ξ (n + 1) : ℝ)) < 0 := by
    have h := delta_mul_delta_succ_neg ξ hξ n
    rwa [dens_eq_continuantDenominator, nums_eq_continuantNumerator,
      dens_eq_continuantDenominator, nums_eq_continuantNumerator] at h
  have hQn : 0 < (continuantDenominator ξ n : ℝ) := by
    rw [← dens_eq_continuantDenominator]; exact dens_pos hξ n
  have hQn1 : 0 < (continuantDenominator ξ (n + 1) : ℝ) := by
    rw [← dens_eq_continuantDenominator]; exact dens_pos hξ (n + 1)
  have hdecomp : (q : ℝ) * ξ - (p : ℝ) =
      (a : ℝ) * ((continuantDenominator ξ n : ℝ) * ξ - (continuantNumerator ξ n : ℝ)) +
      (b : ℝ) * ((continuantDenominator ξ (n + 1) : ℝ) * ξ -
        (continuantNumerator ξ (n + 1) : ℝ)) := by
    rw [hp, hq]; ring
  have hab : (a : ℝ) * (b : ℝ) ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    rcases (mul_pos_iff.mp hcon) with ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩
    · have haZ : (0 : ℤ) < a := by exact_mod_cast ha0
      have hbZ : (0 : ℤ) < b := by exact_mod_cast hb0
      have ha1 : (1 : ℝ) ≤ (a : ℝ) := by
        exact_mod_cast (show (1 : ℤ) ≤ a by omega)
      have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
        exact_mod_cast (show (1 : ℤ) ≤ b by omega)
      have h1 := mul_le_mul_of_nonneg_right ha1 (le_of_lt hQn)
      have h2 := mul_le_mul_of_nonneg_right hb1 (le_of_lt hQn1)
      linarith
    · have haZ : a < (0 : ℤ) := by exact_mod_cast ha0
      have hbZ : b < (0 : ℤ) := by exact_mod_cast hb0
      have ha1 : (a : ℝ) ≤ -1 := by
        exact_mod_cast (show a ≤ (-1 : ℤ) by omega)
      have hb1 : (b : ℝ) ≤ -1 := by
        exact_mod_cast (show b ≤ (-1 : ℤ) by omega)
      have h1 := mul_le_mul_of_nonneg_right ha1 (le_of_lt hQn)
      have h2 := mul_le_mul_of_nonneg_right hb1 (le_of_lt hQn1)
      linarith
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha] at hq
    simp only [Int.cast_zero, zero_mul, zero_add] at hq
    have hbR0 : 0 < (b : ℝ) := by
      have h := hq0; rw [hq] at h
      exact pos_of_mul_pos_left h (le_of_lt hQn1)
    have hbR1 : (b : ℝ) < 1 := by
      have h := hqlt; rw [hq] at h
      exact (mul_lt_mul_iff_left₀ hQn1).mp (by simpa using h)
    have hbZ : (1 : ℤ) ≤ b := by
      have : (0 : ℤ) < b := by exact_mod_cast hbR0
      omega
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbZ
    linarith
  have hsign : 0 ≤ ((a : ℝ) * ((continuantDenominator ξ n : ℝ) * ξ -
      (continuantNumerator ξ n : ℝ))) *
      ((b : ℝ) * ((continuantDenominator ξ (n + 1) : ℝ) * ξ -
        (continuantNumerator ξ (n + 1) : ℝ))) := by
    have h1 : 0 ≤ ((a : ℝ) * (b : ℝ)) *
        (((continuantDenominator ξ n : ℝ) * ξ - (continuantNumerator ξ n : ℝ)) *
         ((continuantDenominator ξ (n + 1) : ℝ) * ξ -
          (continuantNumerator ξ (n + 1) : ℝ))) :=
      mul_nonneg_of_nonpos_of_nonpos hab (le_of_lt hδ)
    calc 0 ≤ ((a : ℝ) * (b : ℝ)) *
        (((continuantDenominator ξ n : ℝ) * ξ - (continuantNumerator ξ n : ℝ)) *
         ((continuantDenominator ξ (n + 1) : ℝ) * ξ -
          (continuantNumerator ξ (n + 1) : ℝ))) := h1
      _ = ((a : ℝ) * ((continuantDenominator ξ n : ℝ) * ξ -
            (continuantNumerator ξ n : ℝ))) *
          ((b : ℝ) * ((continuantDenominator ξ (n + 1) : ℝ) * ξ -
            (continuantNumerator ξ (n + 1) : ℝ))) := by ring
  have htri : |(a : ℝ) * ((continuantDenominator ξ n : ℝ) * ξ -
        (continuantNumerator ξ n : ℝ))| ≤
      |(a : ℝ) * ((continuantDenominator ξ n : ℝ) * ξ - (continuantNumerator ξ n : ℝ)) +
        (b : ℝ) * ((continuantDenominator ξ (n + 1) : ℝ) * ξ -
          (continuantNumerator ξ (n + 1) : ℝ))| := by
    rw [(abs_add_eq_add_abs_iff _ _).mpr (mul_nonneg_iff.mp hsign)]
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hone : |((continuantDenominator ξ n : ℝ) * ξ - (continuantNumerator ξ n : ℝ))| ≤
      |(a : ℝ) * ((continuantDenominator ξ n : ℝ) * ξ - (continuantNumerator ξ n : ℝ))| := by
    rw [abs_mul]
    have ha1 : (1 : ℝ) ≤ |(a : ℝ)| := by
      have : (1 : ℤ) ≤ |a| := Int.one_le_abs ha0
      exact_mod_cast this
    calc |(continuantDenominator ξ n : ℝ) * ξ - (continuantNumerator ξ n : ℝ)|
        = 1 * |(continuantDenominator ξ n : ℝ) * ξ - (continuantNumerator ξ n : ℝ)| := by ring
      _ ≤ |(a : ℝ)| * |(continuantDenominator ξ n : ℝ) * ξ -
            (continuantNumerator ξ n : ℝ)| :=
          mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
  rw [hdecomp]
  linarith

/-- **主定理：每个（`n ≥ 1` 的）收敛子都是最佳有理逼近。**

若 `hξ : Irrational ξ`、`hn : 1 ≤ n`，则 `continuedFractionConvergent ξ n` 的逼近误差不大于任何
分母不超过它的有理数的误差。

组装方式：对 `r : ℚ` 用 `continuantNumerator` / `continuantDenominator` 做基分解，取
`a = D (r.num qₙ₊₁ - r.den pₙ₊₁)`、`b = D (r.den pₙ - r.num qₙ)`（`D = pₙ qₙ₊₁ - qₙ pₙ₊₁`，`D² = 1`），
套核心引理得 `|δₙ| ≤ |r.den · ξ - r.num|`，再由 `r.den ≤ (conv n).den ≤ qₙ` 除以分母即得。

**边界**：`n = 0` 时命题为假（`ξ = 1.7`，第 0 个收敛子 `1` 被 `2/1` 击败），`1 ≤ n` 不可去。

> **Entry**: number-theory.elementary.convergent-best
@isnad1 id=isbestra.2h2v.s4.98b1be969413 from=translated src=- shape=38d05ad2 vocab=4b314356
-/
theorem convergent_isBestRationalApproximation {ξ : ℝ} (hξ : Irrational ξ) {n : ℕ} (hn : 1 ≤ n) :
    IsBestRationalApproximation ξ (continuedFractionConvergent ξ n) := by
  intro r hr
  set P : ℤ := continuantNumerator ξ n with hP
  set Q : ℤ := continuantDenominator ξ n with hQ
  set P' : ℤ := continuantNumerator ξ (n + 1) with hP'
  set Q' : ℤ := continuantDenominator ξ (n + 1) with hQ'
  have hQpos : 0 < (Q : ℝ) := by rw [hQ, ← dens_eq_continuantDenominator]; exact dens_pos hξ n
  have hQ'pos : 0 < (Q' : ℝ) := by
    rw [hQ', ← dens_eq_continuantDenominator]; exact dens_pos hξ (n + 1)
  have hQlt : (Q : ℝ) < (Q' : ℝ) := by
    have h := dens_lt_dens_succ hξ hn
    rwa [dens_eq_continuantDenominator, dens_eq_continuantDenominator] at h
  have hdle : (r.den : ℤ) ≤ Q :=
    le_trans (by exact_mod_cast hr) (convergent_den_le_continuantDenominator ξ hξ n)
  have hqle : (r.den : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hdle
  have hq0 : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hqlt : (r.den : ℝ) < (Q' : ℝ) := lt_of_le_of_lt hqle hQlt
  have hdet : P * Q' - Q * P' = (-1 : ℤ) ^ (n + 1) := by
    rw [hP, hQ, hP', hQ']; exact continuant_determinant ξ hξ n
  have hDsq : (P * Q' - Q * P') * (P * Q' - Q * P') = 1 := by
    rw [hdet]
    rcases Nat.even_or_odd (n + 1) with h | h
    · rw [h.neg_one_pow]; ring
    · rw [h.neg_one_pow]; ring
  have hpZ : r.num = (P * Q' - Q * P') * (r.num * Q' - r.den * P') * P +
      (P * Q' - Q * P') * (r.den * P - r.num * Q) * P' := by
    have h : (P * Q' - Q * P') * (r.num * Q' - r.den * P') * P +
        (P * Q' - Q * P') * (r.den * P - r.num * Q) * P'
        = (P * Q' - Q * P') * (P * Q' - Q * P') * r.num := by ring
    rw [h, hDsq, one_mul]
  have hqZ : r.den = (P * Q' - Q * P') * (r.num * Q' - r.den * P') * Q +
      (P * Q' - Q * P') * (r.den * P - r.num * Q) * Q' := by
    have h : (P * Q' - Q * P') * (r.num * Q' - r.den * P') * Q +
        (P * Q' - Q * P') * (r.den * P - r.num * Q) * Q'
        = (P * Q' - Q * P') * (P * Q' - Q * P') * r.den := by ring
    rw [h, hDsq, one_mul]
  have hpR : (r.num : ℝ) =
      (((P * Q' - Q * P') * (r.num * Q' - r.den * P') : ℤ) : ℝ) * (P : ℝ) +
      (((P * Q' - Q * P') * (r.den * P - r.num * Q) : ℤ) : ℝ) * (P' : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hpZ
    simpa using h
  have hqR : (r.den : ℝ) =
      (((P * Q' - Q * P') * (r.num * Q' - r.den * P') : ℤ) : ℝ) * (Q : ℝ) +
      (((P * Q' - Q * P') * (r.den * P - r.num * Q) : ℤ) : ℝ) * (Q' : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hqZ
    simpa using h
  have hcore := abs_sub_convergent_le_of_decomposition ξ hξ n
    (p := r.num) (q := r.den)
    (a := (P * Q' - Q * P') * (r.num * Q' - r.den * P'))
    (b := (P * Q' - Q * P') * (r.den * P - r.num * Q))
    hpR hqR hq0 hqlt
  · have e1 : rationalApproximationError ξ (continuedFractionConvergent ξ n) =
        |(Q : ℝ) * ξ - (P : ℝ)| / (Q : ℝ) := by
      rw [rationalApproximationError, convergent_cast_eq]
      have hcast : (continuantNumerator ξ n : ℝ) = (P : ℝ) := by rw [hP]
      have hcast' : (continuantDenominator ξ n : ℝ) = (Q : ℝ) := by rw [hQ]
      rw [hcast, hcast']
      have : ξ - (P : ℝ) / (Q : ℝ) = ((Q : ℝ) * ξ - (P : ℝ)) / (Q : ℝ) := by
        field_simp
      rw [this, abs_div, abs_of_pos hQpos]
    have e2 : rationalApproximationError ξ r =
        |(r.den : ℝ) * ξ - (r.num : ℝ)| / (r.den : ℝ) := by
      rw [rationalApproximationError, Rat.cast_def]
      have : ξ - (r.num : ℝ) / (r.den : ℝ) =
          ((r.den : ℝ) * ξ - (r.num : ℝ)) / (r.den : ℝ) := by field_simp
      rw [this, abs_div, abs_of_pos hq0]
    rw [e1, e2]
    rw [div_le_div_iff₀ hQpos hq0]
    have h1 : |(Q : ℝ) * ξ - (P : ℝ)| * (r.den : ℝ) ≤
        |(r.den : ℝ) * ξ - (r.num : ℝ)| * (r.den : ℝ) :=
      mul_le_mul_of_nonneg_right hcore (le_of_lt hq0)
    have h2 : |(r.den : ℝ) * ξ - (r.num : ℝ)| * (r.den : ℝ) ≤
        |(r.den : ℝ) * ξ - (r.num : ℝ)| * (Q : ℝ) :=
      mul_le_mul_of_nonneg_left hqle (abs_nonneg _)
    linarith

end SandronesLibrary.NumberTheory.Elementary
