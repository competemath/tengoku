/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.NumberTheory.Elementary.ContinuedFractions
import Tengoku.SandronesLibrary.SandronesLibrary.NumberTheory.Elementary.Pell
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 连分数与 Pell 解之间的桥

本文件把本库的连分数接口（`continuedFractionConvergent`、`IsLegendreApproximation`、
`legendreApproximation_is_convergent`）与 Pell 解接口（`PellSolution`）显式连起来，并且
**把两个方向分开陈述、分开证明**，不允许一个方向冒充另一个方向。

* **方向 I（主交付，真正证明）**：正 Pell 方程 `x² - d y² = 1` 的每个正非平凡解，其比值
  `x / y` 必是 `√d` 的某个连分数渐近分数。证明路线是：由方程读出 `IsCoprime x y`，于是
  `Rat.den_div_eq_of_coprime` 给出该比值的既约分母就是 `y`；再用 Pell 方程做代数估计
  `|√d - x/y| < 1/(2y²)`；最后套 Legendre 判别准则。
* **方向 II（次交付）**：`√d` 的每个渐近分数 `q` 都满足 Pell 形式有界
  `|q.num² - d q.den²| ≤ 2√d + 1`。这是“渐近分数的分子分母对不会给出太大的 Pell 形式值”，
  **不是**“渐近分数都是 Pell 解”，更不是“`√d` 的渐近分数产生 Pell 解”。

本文件**没有**做“`√d` 连分数展开的周期末端渐近分数给出基本解”这一经典结论：它需要 `√d`
的部分商序列的周期性，而当前 Mathlib 没有 `GenContFract.of_sqrt`（已实测不存在），本库也还
没有周期层（由另一窗口负责）。因此本条目不是“`√d` 渐近分数产生 Pell 解”的完整实现。
本文件同样不涉及负 Pell 方程 `x² - d y² = -1` 的任何结论。

## 本文件条目

* `number-theory.elementary.pell-cf-bridge`
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-- **方向 I：Pell 正解的比值是 `√d` 的渐近分数。**

若整数 `d > 0` 不是平方数，`a` 是正 Pell 方程 `x² - d y² = 1` 的一个解，并且
`1 < a.x`、`0 < a.y`，则比值 `a.x / a.y` 必等于 `√d` 的某个连分数渐近分数
`continuedFractionConvergent (√d) n`。

`hns` 在证明里只用来把 `0 < d` 加强成 `1 < d`（`d = 1` 时 `IsSquare 1` 成立）。除此之外
证明不需要非平方假设：当 `d` 本身是整数平方时，`x² - d y² = 1` 强制 `y = 0`，假设 `0 < a.y`
已经不可满足，所以结论是空真的。保留 `hns` 是为了与前置 Entry
`number-theory.elementary.pell-positive-existence` 的 `(0 < d, ¬IsSquare d)` 口径一致。

> **Entry**: number-theory.elementary.pell-cf-bridge
@isnad1 id=ex.4h2v.s6.fa8d5827c401 from=translated src=- shape=e2a25c64 vocab=9e3eeb8f
-/
theorem pellSolution_ratio_isConvergent {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {a : PellSolution d} (hx : 1 < a.x) (hy : 0 < a.y) :
    ∃ n, ((a.x : ℚ) / (a.y : ℚ)) = continuedFractionConvergent (√(d : ℝ)) n := by
  -- `d > 0` 且非平方 ⟹ `1 < d`；`d = 1` 时 `IsSquare 1` 成立。
  have hd1 : 1 < d := by
    have hle : (1 : ℤ) ≤ d := by omega
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · subst h
      exact absurd (show IsSquare (1 : ℤ) from ⟨1, by ring⟩) hns
  set q : ℚ := (a.x : ℚ) / (a.y : ℚ) with hq
  -- 方程 `x·x + (-(d y))·y = 1` 直接给出 Bézout 关系，故 `x`、`y` 互素。
  have hcop : IsCoprime a.x a.y := by
    refine ⟨a.x, -(d * a.y), ?_⟩
    rw [← a.equation]
    ring
  have hgcd : Int.gcd a.x a.y = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hnat : Nat.Coprime a.x.natAbs a.y.natAbs := by
    simpa [Nat.Coprime, Int.gcd_def] using hgcd
  -- 互素使 `x / y` 已经是既约分数，既约分母就是 `y`。
  have hden : (q.den : ℤ) = a.y := by
    rw [hq]
    exact Rat.den_div_eq_of_coprime hy hnat
  have hdenR : (q.den : ℝ) = (a.y : ℝ) := by exact_mod_cast hden
  have hcast : (q : ℝ) = (a.x : ℝ) / (a.y : ℝ) := by
    rw [hq]; push_cast; ring
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by linarith
  have hsq : √(d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hd0
  have hyR : (0 : ℝ) < (a.y : ℝ) := by exact_mod_cast hy
  have hxR : (1 : ℝ) < (a.x : ℝ) := by exact_mod_cast hx
  have heq : (a.x : ℝ) ^ 2 - (d : ℝ) * (a.y : ℝ) ^ 2 = 1 := by exact_mod_cast a.equation
  -- 代数估计：`|√d - x/y| < 1/(2y²)`。
  have hmain : |√(d : ℝ) - (a.x : ℝ) / (a.y : ℝ)| < 1 / (2 * (a.y : ℝ) ^ 2) := by
    set r : ℝ := (a.x : ℝ) / (a.y : ℝ) with hr
    have hrpos : 0 < r := by positivity
    have hr2 : r ^ 2 = (a.x : ℝ) ^ 2 / (a.y : ℝ) ^ 2 := by rw [hr]; field_simp
    -- 关键恒等式：`(√d - r)(√d + r) = d - r² = -1/y²`。
    have hprod : (√(d : ℝ) - r) * (√(d : ℝ) + r) = -(1 / (a.y : ℝ) ^ 2) := by
      rw [show (√(d : ℝ) - r) * (√(d : ℝ) + r) = (√(d : ℝ)) ^ 2 - r ^ 2 by ring]
      rw [hsq, hr2]
      field_simp
      linarith [heq]
    have hsum_pos : 0 < √(d : ℝ) + r := by
      linarith [Real.sqrt_nonneg (d : ℝ), hrpos]
    have habs : |√(d : ℝ) - r| * (√(d : ℝ) + r) = 1 / (a.y : ℝ) ^ 2 := by
      rw [← abs_of_pos hsum_pos, ← abs_mul, hprod, abs_neg]
      exact abs_of_pos (one_div_pos.mpr (pow_pos hyR 2))
    have hkey : |√(d : ℝ) - r| = (1 / (a.y : ℝ) ^ 2) / (√(d : ℝ) + r) := by
      rw [eq_div_iff (ne_of_gt hsum_pos)]
      exact habs
    have hsqrt_gt_one : 1 < √(d : ℝ) := by
      have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hdR
      simpa using this
    -- `x² = 1 + d y² > d y²` 且 `y > 0` 给出 `x/y > √d`。
    have hr_gt : √(d : ℝ) < r := by
      have hr2' : r ^ 2 = (d : ℝ) + 1 / (a.y : ℝ) ^ 2 := by
        rw [hr2]
        field_simp
        linarith [heq]
      have hsqlt : (√(d : ℝ)) ^ 2 < r ^ 2 := by
        rw [hsq, hr2']
        have : 0 < 1 / (a.y : ℝ) ^ 2 := one_div_pos.mpr (pow_pos hyR 2)
        linarith
      have := sq_lt_sq.mp hsqlt
      rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hrpos] at this
    have hsum_gt_two : 2 < √(d : ℝ) + r := by linarith
    rw [hkey]
    have hpos1 : 0 < 1 / (a.y : ℝ) ^ 2 := one_div_pos.mpr (pow_pos hyR 2)
    have hstep : (1 / (a.y : ℝ) ^ 2) / (√(d : ℝ) + r) < (1 / (a.y : ℝ) ^ 2) / 2 :=
      div_lt_div_of_pos_left hpos1 (by norm_num) hsum_gt_two
    have hfin : (1 / (a.y : ℝ) ^ 2) / 2 = 1 / (2 * (a.y : ℝ) ^ 2) := by ring
    linarith [hstep, hfin]
  apply legendreApproximation_is_convergent
  change |√(d : ℝ) - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2)
  rw [hcast, hdenR]
  exact hmain

/-- `√d` 的第 `n` 个渐近分数在 `GenContFract` 侧的 continuant 对 `(Aₙ, Bₙ)` 都是整数。

这是方向 II 的技术核心：Mathlib 的 `GenContFract.nums`/`dens` 取值在系数域 `K`（此处是 `ℝ`），
并没有直接给出整性；但 `of v` 的偏分子恒为 `1`、偏分母是 `IntFractPair.b`（一个整数），
所以对 `contsAux` 做归纳可以把每一层 continuant 都写成 `⟨(A : ℝ), (B : ℝ)⟩`。有了它，
渐近分数的既约分母 `q.den` 才能与 `dens n` 比较。-/
private theorem exists_int_contsAux (v : ℝ) (n : ℕ) :
    ∃ A B : ℤ, (GenContFract.of v).contsAux n = (⟨(A : ℝ), (B : ℝ)⟩ : GenContFract.Pair ℝ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · exact ⟨1, 0, by simp [GenContFract.contsAux]⟩
    · exact ⟨⌊v⌋, 1, by simp [GenContFract.contsAux, GenContFract.of_h_eq_floor]⟩
    · rcases h : (GenContFract.of v).s.get? n with _ | gp
      · obtain ⟨A, B, hAB⟩ := ih (n + 1) (by omega)
        exact ⟨A, B, by simp only [GenContFract.contsAux, h]; exact hAB⟩
      · obtain ⟨A₁, B₁, h1⟩ := ih (n + 1) (by omega)
        obtain ⟨A₀, B₀, h0⟩ := ih n (by omega)
        obtain ⟨ifp, hstream, hb⟩ :=
          GenContFract.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some h
        have ha : gp.a = 1 := GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a h)
        refine ⟨ifp.b * A₁ + A₀, ifp.b * B₁ + B₀, ?_⟩
        rw [GenContFract.contsAux_recurrence h h0 h1]
        cases gp with
        | mk a b => simp_all

/-- 若 `q` 是 `√d` 一类实数的渐近分数、且该渐近分数的 `GenContFract` 分母非零，则 `q` 的
既约分母不超过该 `GenContFract` 分母。

证明把 `convs n = nums n / dens n` 的两项都用 `exists_int_contsAux` 写成整数之比，于是
`q = A / B`（`A B : ℤ`），由 `Rat.den_dvd` 得 `q.den ∣ B`，再由 `Int.le_of_dvd` 得
`q.den ≤ B = dens n`。-/
private theorem rat_den_le_dens {v : ℝ} {q : ℚ} {n : ℕ}
    (hconv : (GenContFract.of v).convs n = (q : ℝ))
    (hpos : 0 < (GenContFract.of v).dens n) :
    q.den ≤ (GenContFract.of v).dens n := by
  obtain ⟨A, B, hAB⟩ := exists_int_contsAux v (n + 1)
  have hnums : (GenContFract.of v).nums n = (A : ℝ) := by
    rw [GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux, hAB]
  have hdens : (GenContFract.of v).dens n = (B : ℝ) := by
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, hAB]
  have hqAB : q = (A : ℚ) / (B : ℚ) := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    rw [← hconv, GenContFract.conv_eq_num_div_den, hnums, hdens]
  have hBpos : 0 < B := by
    have : (0 : ℝ) < (B : ℝ) := by rw [← hdens]; exact hpos
    exact_mod_cast this
  have hdvd : (q.den : ℤ) ∣ B := by
    have h := Rat.den_dvd A B
    rw [← Rat.intCast_div_eq_divInt] at h
    rwa [← hqAB] at h
  have hle : (q.den : ℤ) ≤ B := Int.le_of_dvd hBpos hdvd
  have hleNat : q.den ≤ B.toNat := by omega
  have hBnat : ((B.toNat : ℕ) : ℝ) = (B : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hBpos.le
  rw [hdens, ← hBnat]
  exact_mod_cast hleNat

/-- 有理数 `q` 的分子满足 `q.num = q · q.den`（在 `ℝ` 中）。-/
private theorem rat_num_eq_mul_den (q : ℚ) :
    (q.num : ℝ) = (q : ℝ) * (q.den : ℝ) := by
  have h := congrArg (fun r : ℚ => (r : ℝ)) (Rat.num_div_den q)
  push_cast at h
  rw [div_eq_iff (by exact_mod_cast q.den_nz : (q.den : ℝ) ≠ 0)] at h
  exact h

/-- **方向 II：渐近分数的 Pell 形式有界。**

若 `q : ℚ` 是 `√d`（`d > 0`）的某个连分数渐近分数，则它的分子分母对满足
`|q.num² - d·q.den²| ≤ 2√d + 1`。

这是一条**单向上界**：它只说渐近分数的 Pell 形式不会太大，**没有**断言渐近分数一定是 Pell
解，也没有断言 `√d` 的渐近分数会产生 Pell 解。等号右端用 `≤` 而不是 `<`：本证明给出的
放缩链是 `|q.num² - d q.den²| ≤ 2√d + 1/q.den² ≤ 2√d + 1`，两条都是非严格不等式，
所以陈述如实写成 `≤`。

> **Entry**: number-theory.elementary.pell-cf-bridge
@isnad1 id=le.2h2v.s7.9594872236ab from=translated src=- shape=f7fd4916 vocab=b4e91143
-/
theorem convergent_pellForm_bounded {d : ℤ} (hd : 0 < d) {q : ℚ}
    (hq : ∃ n, q = continuedFractionConvergent (√(d : ℝ)) n) :
    |(q.num : ℝ) ^ 2 - (d : ℝ) * (q.den : ℝ) ^ 2| ≤ 2 * √(d : ℝ) + 1 := by
  obtain ⟨n, rfl⟩ := hq
  set q : ℚ := continuedFractionConvergent (√(d : ℝ)) n with hqdef
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.le
  have hsq : (√(d : ℝ)) ^ 2 = (d : ℝ) := Real.sq_sqrt hd0
  have hqconv : (q : ℝ) = ((Real.convergent (√(d : ℝ)) n : ℚ) : ℝ) := by
    rw [hqdef]
    rfl
  have hconv : (GenContFract.of (√(d : ℝ))).convs n = (q : ℝ) :=
    (Real.convs_eq_convergent (√(d : ℝ)) n).trans hqconv.symm
  -- 把 `q.num² - d q.den²` 换成 `q.den² · (q² - (√d)²)`。
  have hnum := rat_num_eq_mul_den q
  have hform : (q.num : ℝ) ^ 2 - (d : ℝ) * (q.den : ℝ) ^ 2
      = (q.den : ℝ) ^ 2 * ((q : ℝ) ^ 2 - (√(d : ℝ)) ^ 2) := by
    have h2 : (d : ℝ) * (q.den : ℝ) ^ 2 = (√(d : ℝ)) ^ 2 * (q.den : ℝ) ^ 2 := by rw [hsq]
    rw [hnum, h2]; ring
  have hfac : (q : ℝ) ^ 2 - (√(d : ℝ)) ^ 2
      = ((q : ℝ) - √(d : ℝ)) * ((q : ℝ) + √(d : ℝ)) := by ring
  by_cases hterm : (GenContFract.of (√(d : ℝ))).TerminatedAt n
  · -- 终止情形：`√d` 是有理数，`q` 就是 `√d`，Pell 形式恰为 0。
    have hvq : (q : ℝ) = √(d : ℝ) := by
      have h := GenContFract.of_correctness_of_terminatedAt (v := √(d : ℝ)) hterm
      rw [hconv] at h
      exact h.symm
    have hqd : (q : ℝ) ^ 2 = (√(d : ℝ)) ^ 2 := by rw [hvq]
    rw [hform, hqd, sub_self, mul_zero, abs_zero]
    positivity
  · have hdens_pos : 0 < (GenContFract.of (√(d : ℝ))).dens n := by
      have hfib := GenContFract.succ_nth_fib_le_of_nth_den (v := √(d : ℝ)) (n := n)
        (Or.inr (mt (GenContFract.terminated_stable (Nat.pred_le n)) hterm))
      have hpos : (0 : ℝ) < (Nat.fib (n + 1) : ℝ) := by
        exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
      linarith
    have hdenle : q.den ≤ (GenContFract.of (√(d : ℝ))).dens n :=
      rat_den_le_dens hconv hdens_pos
    -- 收敛子的误差界：`|√d - q| ≤ 1/(Bₙ Bₙ₊₁)`。
    have hb : |√(d : ℝ) - (q : ℝ)|
        ≤ 1 / ((GenContFract.of (√(d : ℝ))).dens n
            * (GenContFract.of (√(d : ℝ))).dens (n + 1)) := by
      have h := GenContFract.abs_sub_convs_le (v := √(d : ℝ)) (n := n) hterm
      rwa [hconv] at h
    have hmono : (GenContFract.of (√(d : ℝ))).dens n
        ≤ (GenContFract.of (√(d : ℝ))).dens (n + 1) := GenContFract.of_den_mono
    have hdenleR : (q.den : ℝ) ≤ (GenContFract.of (√(d : ℝ))).dens n := by exact_mod_cast hdenle
    have hmonoR : (GenContFract.of (√(d : ℝ))).dens n
        ≤ (GenContFract.of (√(d : ℝ))).dens (n + 1) := by exact_mod_cast hmono
    have hprod : (q.den : ℝ) ^ 2
        ≤ (GenContFract.of (√(d : ℝ))).dens n
            * (GenContFract.of (√(d : ℝ))).dens (n + 1) := by
      have h2 : (q.den : ℝ) ≤ (GenContFract.of (√(d : ℝ))).dens (n + 1) :=
        hdenleR.trans hmonoR
      have h := mul_le_mul hdenleR h2 (by positivity) (by positivity)
      simpa [sq] using h
    have hb1 : |(q : ℝ) - √(d : ℝ)| ≤ 1 / (q.den : ℝ) ^ 2 := by
      have h := hb.trans (one_div_le_one_div_of_le
        (by positivity : (0 : ℝ) < (q.den : ℝ) ^ 2) hprod)
      rwa [abs_sub_comm] at h
    have h1 : (q.den : ℝ) ^ 2 * |(q : ℝ) - √(d : ℝ)| ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hb1 (sq_nonneg (q.den : ℝ))
      rwa [mul_one_div, div_self (by positivity : (q.den : ℝ) ^ 2 ≠ 0)] at h
    have h2 : |(q : ℝ) + √(d : ℝ)| ≤ 2 * √(d : ℝ) + 1 / (q.den : ℝ) ^ 2 := by
      have hsplit : (q : ℝ) + √(d : ℝ) = ((q : ℝ) - √(d : ℝ)) + 2 * √(d : ℝ) := by ring
      rw [hsplit]
      calc |((q : ℝ) - √(d : ℝ)) + 2 * √(d : ℝ)|
          ≤ |(q : ℝ) - √(d : ℝ)| + |2 * √(d : ℝ)| := abs_add_le _ _
        _ = |(q : ℝ) - √(d : ℝ)| + 2 * √(d : ℝ) := by
              rw [show |2 * √(d : ℝ)| = 2 * √(d : ℝ) from abs_of_nonneg (by positivity)]
        _ ≤ 1 / (q.den : ℝ) ^ 2 + 2 * √(d : ℝ) := by linarith
        _ = 2 * √(d : ℝ) + 1 / (q.den : ℝ) ^ 2 := by ring
    have h3 : 1 / (q.den : ℝ) ^ 2 ≤ 1 := by
      have hge : (1 : ℝ) ≤ (q.den : ℝ) ^ 2 := by
        have h1 : (1 : ℝ) ≤ (q.den : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ne_of_gt q.pos)
        nlinarith
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hge
      simpa using h
    have key : (q.den : ℝ) ^ 2 * |(q : ℝ) - √(d : ℝ)| * |(q : ℝ) + √(d : ℝ)|
        ≤ 2 * √(d : ℝ) + 1 := by
      calc (q.den : ℝ) ^ 2 * |(q : ℝ) - √(d : ℝ)| * |(q : ℝ) + √(d : ℝ)|
          ≤ 1 * (2 * √(d : ℝ) + 1 / (q.den : ℝ) ^ 2) :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 2 * √(d : ℝ) + 1 / (q.den : ℝ) ^ 2 := by ring
        _ ≤ 2 * √(d : ℝ) + 1 := by linarith
    rw [hform, hfac, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (q.den : ℝ))]
    linarith [key]

end SandronesLibrary.NumberTheory.Elementary
