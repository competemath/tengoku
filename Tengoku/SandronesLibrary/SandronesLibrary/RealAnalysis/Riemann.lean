/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.Continuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / Riemann —— 黎曼积分与 Lebesgue 判据（数学分析第二学期 R5.5）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **real-analysis.riemann.def**（黎曼积分定义：达布分划/上下和/黎曼可积/均匀分划/积分值）✅。
* **real-analysis.riemann.cont-integrable**（连续 ⟹ 黎曼可积，均匀分划 + 一致连续）✅。
* **real-analysis.riemann.eq-lebesgue**（连续函数黎曼积分值 = Lebesgue 区间积分）✅：
  达布和=阶梯积分 → 下和≤∫≤上和 → riemannIntegral = intervalIntegral，全自证。
* **real-analysis.riemann.lebesgue-criterion**（黎曼可积 ⟺ 几乎处处连续）：待续。

> **语言说明**：mathlib **没有**黎曼积分定义，全部自建。这是锻炼"论文定理自证"能力
> （Playbook §4.1）的实战。用 `sSup`/`sInf`（区间上下确界）、`Finset` 求和、`volume`。
-/

namespace SandronesLibrary

namespace RealAnalysis.Riemann

open MeasureTheory
open SandronesLibrary.Analysis.Continuity
open scoped ENNReal Interval BigOperators

/-- **达布分划**：区间 [a,b] 的一个分划是点列 a = x₀ < x₁ < ... < xₙ = b。

> **Entry**: real-analysis.riemann.def-/
structure DarbouxPartition (a b : ℝ) where
  n : ℕ
  x : ℕ → ℝ
  x0 : x 0 = a
  xN : x n = b
  strict : ∀ i, i < n → x i < x (i + 1)

/-- **达布下和**：Σᵢ (xᵢ₊₁ − xᵢ) · inf f on [xᵢ, xᵢ₊₁]。-/
noncomputable def lowerSum (f : ℝ → ℝ) {a b : ℝ} (P : DarbouxPartition a b) : ℝ :=
  ∑ i ∈ Finset.range P.n, (P.x (i + 1) - P.x i) * sInf (f '' Set.Icc (P.x i) (P.x (i + 1)))

/-- **达布上和**：Σᵢ (xᵢ₊₁ − xᵢ) · sup f on [xᵢ, xᵢ₊₁]。-/
noncomputable def upperSum (f : ℝ → ℝ) {a b : ℝ} (P : DarbouxPartition a b) : ℝ :=
  ∑ i ∈ Finset.range P.n, (P.x (i + 1) - P.x i) * sSup (f '' Set.Icc (P.x i) (P.x (i + 1)))

/-- **黎曼可积**：上下和可任意逼近（上积分 = 下积分）。
  教材定义：∀ ε > 0，存在分划使上和 − 下和 < ε。 
> **Entry**: real-analysis.riemann.def-/
def RiemannIntegrable (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ P : DarbouxPartition a b, upperSum f P - lowerSum f P < ε

/-- **黎曼积分值**：下积分的上确界（教材定义）。当 f 黎曼可积时，
  它等于上积分的下确界，即黎曼积分。-/
noncomputable def riemannIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sSup { x : ℝ | ∃ P : DarbouxPartition a b, x = lowerSum f P }

/-- **均匀分划**：将 [a,b] 等分为 n 段（xᵢ = a + i·(b−a)/n）。
  用于"连续 ⟹ 可积"中控制上下和之差。-/
noncomputable def uniformPartition (a b : ℝ) (n : ℕ) (hab : a < b) (hpos : 0 < n) :
    DarbouxPartition a b where
  n := n
  x := fun i => a + (i : ℝ) * ((b - a) / (n : ℝ))
  x0 := by simp
  xN := by
    field_simp
    ring
  strict := by
    intro i hi
    have hd : 0 < (b - a) / (n : ℝ) := by
      exact div_pos (sub_pos.mpr hab) (Nat.cast_pos.mpr hpos)
    have : (i : ℝ) < (i + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self i
    nlinarith

/-- **均匀分划的步长**：相邻两点距离 = (b−a)/n（等分性质）。
@isnad1 id=eq.3h4v.s6.dbc59ac172d6 from=translated src=- shape=177f8a21 vocab=a69da38a
-/
theorem uniformPartition_step {a b : ℝ} {n : ℕ} (hab : a < b) (hpos : 0 < n)
    (i : ℕ) (_hi : i < n) :
    (uniformPartition a b n hab hpos).x (i + 1) - (uniformPartition a b n hab hpos).x i =
      (b - a) / (n : ℝ) := by
  simp [uniformPartition]
  ring

/-- **均匀分划步长和**：∑ᵢ (b−a)/n = b − a（均匀分划所有步长之和为区间长）。
@isnad1 id=eq.2h3v.s5.d62538c7aab9 from=translated src=- shape=a6d8f99a vocab=feda1a1c
-/
lemma step_sum {a b : ℝ} {n : ℕ} (_hab : a < b) (hpos : 0 < n) :
    ∑ i ∈ Finset.range n, ((b - a) / (n : ℝ)) = b - a := by
  rw [Finset.sum_const]
  -- s.card • d = n • d
  have hcard : (Finset.range n).card = n := Finset.card_range n
  rw [hcard]
  -- n • ((b-a)/n) = b-a（n ≠ 0）
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  -- nsmul_eq_mul
  rw [nsmul_eq_mul]
  field_simp [hn]

/-- **均匀分划点属于区间**：xᵢ = a + i·(b−a)/n ∈ [a,b]（对 i ≤ n）。
@isnad1 id=mem.3h4v.s6.2e7a1f8f6de6 from=translated src=- shape=c076880b vocab=8c051a53
-/
lemma uniform_x_mem {a b : ℝ} {n : ℕ} (hab : a < b) (hpos : 0 < n)
    (i : ℕ) (hi : i ≤ n) :
    a + (i : ℝ) * ((b - a) / (n : ℝ)) ∈ Set.Icc a b := by
  constructor
  · -- a ≤ a + i·d（d ≥ 0）
    have hd : 0 ≤ (b - a) / (n : ℝ) := by
      exact div_nonneg (le_of_lt (sub_pos.mpr hab)) (Nat.cast_nonneg n)
    nlinarith
  · -- a + i·d ≤ a + n·d = b
    have hd : 0 ≤ (b - a) / (n : ℝ) := by
      exact div_nonneg (le_of_lt (sub_pos.mpr hab)) (Nat.cast_nonneg n)
    have hile : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi
    have : a + (i : ℝ) * ((b - a) / (n : ℝ)) ≤ a + (n : ℝ) * ((b - a) / (n : ℝ)) := by
      nlinarith
    have : a + (n : ℝ) * ((b - a) / (n : ℝ)) = b := by
      have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
      field_simp [hn]
      ring
    linarith

/-- **区间宽度引理**：x, y ∈ [p,q]（p ≤ q）⟹ |x − y| ≤ q − p。
  用于控制子区间内两点距离不超过区间长。
@isnad1 id=le.3h4v.s6.33caed56865a from=translated src=- shape=cb6fc9c4 vocab=6ccb0102
-/
lemma interval_width {p q x y : ℝ} (_hpq : p ≤ q)
    (hx : x ∈ Set.Icc p q) (hy : y ∈ Set.Icc p q) :
    |x - y| ≤ q - p := by
  rw [abs_le]
  constructor
  · have : p - q ≤ x - y := by linarith [hx.1, hy.2]
    simpa using this
  · have : x - y ≤ q - p := by linarith [hx.2, hy.1]
    exact this

/-- **振荡界（B3）**：区间内任意两点 f 值差 ≤ ε ⟹ sSup(f''I) − sInf(f''I) ≤ 2ε。
  用下确界逼近（exists_lt_of_lt_csSup 思路）。
> **Entry**: real-analysis.riemann.cont-integrable
@isnad1 id=le.3h3v.s6.866ea97f5027 from=translated src=- shape=ff02dfd3 vocab=a3488db6
-/
lemma b3_osc {f : ℝ → ℝ} {I : Set ℝ} (hI : I.Nonempty)
    {ε : ℝ} (hε : 0 < ε)
    (hosc : ∀ x ∈ I, ∀ y ∈ I, |f x - f y| ≤ ε) :
    sSup (f '' I) ≤ sInf (f '' I) + 2 * ε := by
  have hinf_approx : ∀ δ > 0, ∃ y ∈ I, f y < sInf (f '' I) + δ := by
    intro δ hδ
    by_contra h
    push Not at h
    have : sInf (f '' I) + δ ≤ sInf (f '' I) := by
      apply le_csInf
      · exact Set.image_nonempty.mpr hI
      · intro w hw
        rcases hw with ⟨y, hy, rfl⟩
        exact h y hy
    nlinarith
  apply csSup_le
  · exact Set.image_nonempty.mpr hI
  · intro m hm
    rcases hm with ⟨z, hz, rfl⟩
    rcases hinf_approx (ε / 2) (by positivity) with ⟨y, hy, hfy⟩
    have hzy : |f z - f y| ≤ ε := hosc z hz y hy
    have hfzy : f z ≤ f y + ε := by linarith [abs_le.mp hzy]
    nlinarith

/-- **子区间振荡界（C2）**：f 一致连续（huni 给振荡 < ε）且子区间宽度 < δ ⟹
  sSup(f''[p,q]) − sInf(f''[p,q]) ≤ 2ε。用于控制达布上下和差。
@isnad1 id=le.6h7v.s7.27160f446c90 from=translated src=- shape=710feb18 vocab=d1190fe3
-/
lemma C2_subinterval {f : ℝ → ℝ} {a b : ℝ} {ε δ : ℝ}
    (huni : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |x - y| < δ → |f x - f y| < ε)
    {p q : ℝ} (hpq : p ≤ q) (hp : p ∈ Set.Icc a b) (hq : q ∈ Set.Icc a b)
    (hwidth : |p - q| < δ) (hε : 0 < ε) :
    sSup (f '' Set.Icc p q) - sInf (f '' Set.Icc p q) ≤ 2 * ε := by
  have hosc : ∀ x ∈ Set.Icc p q, ∀ y ∈ Set.Icc p q, |f x - f y| ≤ ε := by
    intro x hx y hy
    have hxy : |x - y| ≤ q - p := interval_width hpq hx hy
    -- q - p ≤ |p - q|（p ≤ q）
    have hqp : q - p ≤ |p - q| := by
      simpa [abs_of_nonpos (sub_nonpos.mpr hpq)]
    have hxy_lt : |x - y| < δ := lt_of_le_of_lt (le_trans hxy hqp) hwidth
    have hx_ab : x ∈ Set.Icc a b := Set.Icc_subset_Icc hp.1 hq.2 hx
    have hy_ab : y ∈ Set.Icc a b := Set.Icc_subset_Icc hp.1 hq.2 hy
    exact le_of_lt (huni x hx_ab y hy_ab hxy_lt)
  have hI : (Set.Icc p q).Nonempty := ⟨p, ⟨le_rfl, hpq⟩⟩
  have hB3 := b3_osc hI (by linarith) hosc
  linarith

/-- **连续函数黎曼可积（a<b）**：f 在 [a,b] 连续 ⟹ 黎曼可积。
  一致连续 + 均匀分划 + 振荡界 + 求和，完全自证。
@isnad1 id=riemanni.2h3v.s5.7225ec4121d5 from=translated src=- shape=7525c359 vocab=990f2010
-/
theorem continuous_on_riemannIntegrable_lt {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) : RiemannIntegrable f a b := by
  intro ε hε
  -- ε' = ε/(4(b-a))
  let ε' := ε / (4 * (b - a))
  have hε' : 0 < ε' := by
    unfold ε'
    positivity
  -- 一致连续
  have hK : IsCompact (Set.Icc a b) := isCompact_Icc
  have hne : (Set.Icc a b).Nonempty := ⟨a, ⟨le_rfl, le_of_lt hab⟩⟩
  have huni := continuousOn_compact_uniformContinuousOn (s := Set.Icc a b) hK hne hf
  rcases Metric.uniformContinuousOn_iff.mp huni ε' hε' with ⟨δ, hδ, hδδ⟩
  -- 选 n 使步长 < δ
  rcases exists_nat_gt ((b - a) / δ) with ⟨n, hn⟩
  have hn_pos : 0 < n := by
    have hpos : 0 < (b - a) / δ := div_pos (sub_pos.mpr hab) hδ
    have hcast : 0 < (n : ℝ) := lt_of_lt_of_le hpos (le_of_lt hn)
    exact_mod_cast hcast
  have hstep_lt : (b - a) / (n : ℝ) < δ := by
    have hcast : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have h1 : b - a < (n : ℝ) * δ := by
      rwa [div_lt_iff₀ hδ] at hn
    exact (div_lt_iff₀' hcast).mpr h1
  let P := uniformPartition a b n hab hn_pos
  refine ⟨P, ?_⟩
  -- 展开成求和
  have hdiff : upperSum f P - lowerSum f P =
      ∑ i ∈ Finset.range n, (P.x (i + 1) - P.x i) *
        (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) - sInf (f '' Set.Icc (P.x i) (P.x (i + 1)))) := by
    unfold upperSum lowerSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  -- 逐项 ≤ 步长·2ε'
  have hterm : ∀ i ∈ Finset.range n,
      (P.x (i + 1) - P.x i) *
        (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) - sInf (f '' Set.Icc (P.x i) (P.x (i + 1)))) ≤
      (P.x (i + 1) - P.x i) * (2 * ε') := by
    intro i hi
    have hi_lt : i < n := Finset.mem_range.mp hi
    have hxi : P.x i ∈ Set.Icc a b := by
      have := uniform_x_mem hab hn_pos i (le_of_lt hi_lt)
      simpa [P, uniformPartition] using this
    have hxi1 : P.x (i + 1) ∈ Set.Icc a b := by
      have := uniform_x_mem hab hn_pos (i + 1) (by omega)
      simpa [P, uniformPartition] using this
    have hwidth_abs : |P.x (i + 1) - P.x i| < δ := by
      have hstep : P.x (i + 1) - P.x i = (b - a) / (n : ℝ) := uniformPartition_step hab hn_pos i hi_lt
      rw [hstep]
      have hnon : 0 ≤ (b - a) / (n : ℝ) := by
        exact div_nonneg (le_of_lt (sub_pos.mpr hab)) (Nat.cast_nonneg n)
      rw [abs_of_nonneg hnon]
      exact hstep_lt
    have hwidth : |P.x i - P.x (i + 1)| < δ := by
      rw [abs_sub_comm]
      exact hwidth_abs
    have hosc0 : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |x - y| < δ → |f x - f y| < ε' := hδδ
    have hC2 := C2_subinterval (a := a) (b := b) (ε := ε') (δ := δ)
      (huni := hosc0) (hpq := (P.strict i hi_lt).le) (hp := hxi) (hq := hxi1)
      (hwidth := hwidth) (hε := hε')
    have hosc_bound : sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) ≤ 2 * ε' := hC2
    have hstep_nonneg : 0 ≤ P.x (i + 1) - P.x i := sub_nonneg.mpr (P.strict i hi_lt).le
    exact mul_le_mul_of_nonneg_left hosc_bound hstep_nonneg
  -- 求和 = 2ε'·(b-a) = ε/2
  have hsum_step : (∑ i ∈ Finset.range n,
      (P.x (i + 1) - P.x i) : ℝ) = b - a := by
    have hcong : (∑ i ∈ Finset.range n,
        ((P.x (i + 1) - P.x i) : ℝ)) =
        (∑ i ∈ Finset.range n, ((b - a) / (n : ℝ)) : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact uniformPartition_step hab hn_pos i (Finset.mem_range.mp hi)
    exact hcong.trans (step_sum hab hn_pos)
  have hsum : (∑ i ∈ Finset.range n, (P.x (i + 1) - P.x i) * (2 * ε')) = 2 * ε' * (b - a) := by
    calc
      (∑ i ∈ Finset.range n, (P.x (i + 1) - P.x i) * (2 * ε')) =
          (∑ i ∈ Finset.range n, (P.x (i + 1) - P.x i)) * (2 * ε') := by
            exact (Finset.sum_mul _ _ (2 * ε')).symm
      _ = (b - a) * (2 * ε') := by rw [hsum_step]
      _ = 2 * ε' * (b - a) := by ring
  have hsum_val : (∑ i ∈ Finset.range n, (P.x (i + 1) - P.x i) * (2 * ε')) = ε / 2 := by
    rw [hsum]
    unfold ε'
    have hba_ne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_lt hab).symm
    field_simp [hba_ne]
    ring
  -- 最终: ≤ Σ步长·2ε' = ε/2 < ε
  rw [hdiff]
  have hle : (∑ i ∈ Finset.range n, (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) - sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))) ≤
      (∑ i ∈ Finset.range n, (P.x (i + 1) - P.x i) * (2 * ε')) :=
    Finset.sum_le_sum hterm
  have : (∑ i ∈ Finset.range n, (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) - sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))) < ε := by
    calc
      _ ≤ (∑ i ∈ Finset.range n, (P.x (i + 1) - P.x i) * (2 * ε')) := hle
      _ = ε / 2 := hsum_val
      _ < ε := by linarith
  exact this

/-- **连续函数 Lebesgue 区间可积**：f 在 [a,b] 连续（a ≤ b）⟹ IntervalIntegrable f volume a b。
@isnad1 id=interval.2h3v.s5.3d17a408688b from=translated src=- shape=183b5b83 vocab=440b7691
-/
theorem continuous_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) : IntervalIntegrable f volume a b := by
  have hf' : ContinuousOn f (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact hf
  exact ContinuousOn.intervalIntegrable (μ := volume) hf'
/-- **单区间常数 indicator 积分**：∫ (c·1_{Ioc a b}) = c·(b−a)（a ≤ b）。
  达布和 = 阶梯函数积分的原子引理。
> **Entry**: real-analysis.riemann.eq-lebesgue
@isnad1 id=eq.1h3v.s6.9c512ff84332 from=translated src=- shape=ea31f77e vocab=c1f9cbc9
-/
theorem integral_indicator_const_Ioc {a b c : ℝ} (hab : a ≤ b) :
    (∫ x : ℝ, (Set.Ioc a b).indicator (fun _ : ℝ => c) x ∂volume) = c * (b - a) := by
  rw [integral_indicator (hs := measurableSet_Ioc)]
  -- ∫_{Ioc a b} c = (volume.restrict (Ioc a b)).real univ • c
  rw [integral_const]
  -- 证 (volume.restrict (Ioc a b)).real Set.univ = b - a
  have hrestr : (volume.restrict (Set.Ioc a b)).real Set.univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply (s := Set.Ioc a b) (t := Set.univ) (ht := MeasurableSet.univ)]
    -- (volume.restrict (Ioc a b)) univ = volume (univ ∩ Ioc a b) = volume (Ioc a b)
    rw [Set.univ_inter]
    rw [Real.volume_Ioc]
    -- toReal (ofReal (b-a)) = max (b-a) 0
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  -- 目标: (volume.restrict (Ioc a b)).real univ • c = c·(b-a)
  rw [hrestr]
  -- (b-a) • c = c·(b-a)
  simp [smul_eq_mul, mul_comm]

/-- **求和 indicator 积分**：∫ (∑ᵢ cᵢ·1_{Ioc xᵢ xᵢ₊₁}) = ∑ᵢ cᵢ·(xᵢ₊₁−xᵢ)。
  阶梯函数（indicator 常数和）的 Lebesgue 积分 = 达布和形式。
@isnad1 id=eq.1h3v.s7.3832f31c4131 from=translated src=- shape=c9f3e2c5 vocab=46730c98
-/
theorem integral_sum_indicator_Ioc {n : ℕ} {x : ℕ → ℝ} {c : ℕ → ℝ}
    (hstep : ∀ i ∈ Finset.range n, x i ≤ x (i+1)) :
    (∫ t : ℝ, (∑ i ∈ Finset.range n,
        (Set.Ioc (x i) (x (i+1))).indicator (fun _ : ℝ => c i) t) ∂volume) =
      ∑ i ∈ Finset.range n, c i * (x (i+1) - x i) := by
  -- 求和积分
  have hf : ∀ i ∈ Finset.range n, Integrable
      (fun t : ℝ => (Set.Ioc (x i) (x (i+1))).indicator (fun _ : ℝ => c i) t) volume := by
    intro i hi
    -- 用 integrable_indicator_iff + integrableOn_const
    rw [integrable_indicator_iff (hs := measurableSet_Ioc)]
    have hfin : volume (Set.Ioc (x i) (x (i+1))) ≠ ∞ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    exact integrableOn_const (μ := volume) (s := Set.Ioc (x i) (x (i+1))) (C := c i) (hs := hfin)
  -- ∫(∑) = ∑∫
  have hsum_integral : (∫ t : ℝ, (∑ i ∈ Finset.range n,
      (Set.Ioc (x i) (x (i+1))).indicator (fun _ : ℝ => c i) t) ∂volume) =
      ∑ i ∈ Finset.range n, (∫ t : ℝ,
        (Set.Ioc (x i) (x (i+1))).indicator (fun _ : ℝ => c i) t ∂volume) := by
    exact integral_finsetSum (s := Finset.range n) (f := fun i => fun t : ℝ =>
      (Set.Ioc (x i) (x (i+1))).indicator (fun _ : ℝ => c i) t) (μ := volume) hf
  -- 逐项: ∫(cᵢ·1_{Ioc xᵢ xᵢ₊₁}) = cᵢ·(xᵢ₊₁-xᵢ)
  calc
    (∫ t : ℝ, (∑ i ∈ Finset.range n,
        (Set.Ioc (x i) (x (i+1))).indicator (fun _ : ℝ => c i) t) ∂volume)
        = ∑ i ∈ Finset.range n, (∫ t : ℝ,
            (Set.Ioc (x i) (x (i+1))).indicator (fun _ : ℝ => c i) t ∂volume) := hsum_integral
    _ = ∑ i ∈ Finset.range n, c i * (x (i+1) - x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      -- ∫(cᵢ·1_{Ioc}) = cᵢ·(xᵢ₊₁-xᵢ)（D3a，需 x i ≤ x(i+1)）
      exact integral_indicator_const_Ioc (c := c i) (hstep i hi)

/-- **阶梯函数逐点 ≤ f**：t ∈ Ioc p q 时 sInf(f''[p,q]) ≤ f t（f 连续 on [p,q]）。
  达布下和对应阶梯函数 ≤ f 的逐点依据。
@isnad1 id=le.3h4v.s6.081ba1561d64 from=translated src=- shape=8e352f9b vocab=e5a40966
-/
lemma step_le_f_pointwise {f : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hf : ContinuousOn f (Set.Icc p q)) {t : ℝ} (ht : t ∈ Set.Ioc p q) :
    sInf (f '' Set.Icc p q) ≤ f t := by
  have htm : f t ∈ f '' Set.Icc p q := by
    refine ⟨t, ⟨le_of_lt ht.1, ht.2⟩, rfl⟩
  have hK : IsCompact (f '' Set.Icc p q) := IsCompact.image_of_continuousOn isCompact_Icc hf
  exact csInf_le (IsCompact.bddBelow hK) htm

/-- **受限区间常数积分**：∫ x in Ioc p q, c = c·(q−p)（p ≤ q）。
  受限测度（restrict）下的常数积分。
@isnad1 id=eq.1h3v.s6.f21646816d0d from=translated src=- shape=e3d2ac78 vocab=457fc679
-/
theorem restricted_integral_const_Ioc {p q c : ℝ} (hpq : p ≤ q) :
    (∫ x : ℝ in Set.Ioc p q, c ∂volume) = c * (q - p) := by
  rw [integral_const]
  -- (restrict (Ioc p q)).real univ = volume.real (Ioc p q) = q-p
  have hres : (volume.restrict (Set.Ioc p q)).real Set.univ = volume.real (Set.Ioc p q) := by
    rw [measureReal_def, Measure.restrict_apply (s := Set.Ioc p q) (t := Set.univ) (ht := MeasurableSet.univ)]
    rw [Set.univ_inter]
    rw [measureReal_def]
  have hvol : volume.real (Set.Ioc p q) = q - p := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hpq)]
  rw [hres, hvol]
  simp [smul_eq_mul, mul_comm]

/-- **阶梯函数 indicator 恒等**：子区间 ⊆ Ioc a b 时 (Ioc a b).indicator sP = sP（逐点）。
  阶梯函数在 Ioc a b 外为 0，indicator 不改变它。
@isnad1 id=eq.1h6v.s7.34595e627394 from=translated src=- shape=79a9e2fb vocab=93e7ef46
-/
theorem step_indicator_identity {n : ℕ} {x : ℕ → ℝ} {c : ℕ → ℝ} {a b : ℝ}
    (hsub : ∀ i ∈ Finset.range n, Set.Ioc (x i) (x (i+1)) ⊆ Set.Ioc a b) :
    ∀ t : ℝ, (Set.Ioc a b).indicator
        (fun u => ∑ i ∈ Finset.range n,
          (Set.Ioc (x i) (x (i+1))).indicator (fun _ : ℝ => c i) u) t
        = (∑ i ∈ Finset.range n,
          (Set.Ioc (x i) (x (i+1))).indicator (fun _ : ℝ => c i) t) := by
  intro t
  by_cases ht : t ∈ Set.Ioc a b
  · simp [Set.indicator, ht]
  · have hsP : (∑ i ∈ Finset.range n,
        (Set.Ioc (x i) (x (i+1))).indicator (fun _ : ℝ => c i) t) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hsubi := hsub i hi
      have htnot : t ∉ Set.Ioc (x i) (x (i+1)) := fun hti => ht (hsubi hti)
      exact Set.indicator_of_notMem htnot (fun _ : ℝ => c i)
    simpa [Set.indicator, ht] using hsP.symm

/-- **下和 ≤ 区间积分（抽象组装）**：∫ sP ≤ ∫_s f，当 sP·1_s = sP（恒等）、
  sP·1_s ≤ f·1_s（逐点）、且可积。用 integral_congr + integral_mono + integral_indicator。
@isnad1 id=le.5h3v.s7.82854dea1c24 from=translated src=- shape=74186dd5 vocab=f5345ef6
-/
theorem lower_sum_le_interval {f sP : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s)
    (hsP : ∀ t, s.indicator sP t = sP t)
    (hf_mono : ∀ t, s.indicator sP t ≤ s.indicator f t)
    (hisP : Integrable (s.indicator sP) volume)
    (hif : Integrable (s.indicator f) volume) :
    (∫ t : ℝ, sP t ∂volume) ≤ (∫ t : ℝ in s, f t ∂volume) := by
  have h1ae : sP =ᵐ[volume] (s.indicator sP) := by
    filter_upwards [ae_of_all volume hsP] with t ht
    exact ht.symm
  have h1 : (∫ t : ℝ, sP t ∂volume) = (∫ t : ℝ, s.indicator sP t ∂volume) :=
    integral_congr_ae h1ae
  have h2 : (∫ t : ℝ, s.indicator sP t ∂volume) ≤ (∫ t : ℝ, s.indicator f t ∂volume) :=
    integral_mono hisP hif hf_mono
  have h3 : (∫ t : ℝ, s.indicator f t ∂volume) = (∫ t : ℝ in s, f t ∂volume) :=
    integral_indicator hs
  calc
    (∫ t : ℝ, sP t ∂volume) = (∫ t : ℝ, s.indicator sP t ∂volume) := h1
    _ ≤ (∫ t : ℝ, s.indicator f t ∂volume) := h2
    _ = (∫ t : ℝ in s, f t ∂volume) := h3

/-- **连续函数的 indicator 可积**：f 连续 on [a,b] ⟹ (Ioc a b).indicator f 可积。
@isnad1 id=integrab.2h3v.s6.6c0d557454c8 from=translated src=- shape=d4a940d8 vocab=03f9407d
-/
theorem continuous_indicator_integrable {f : ℝ → ℝ} {a b : ℝ} (_hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    Integrable ((Set.Ioc a b).indicator f) volume := by
  -- integrable_indicator_iff: Integrable (s.indicator f) ↔ IntegrableOn f s
  rw [integrable_indicator_iff (hs := measurableSet_Ioc)]
  -- IntegrableOn f (Ioc a b)：从 Icc 限制（Ioc ⊆ Icc）
  have hcc : IntegrableOn f (Set.Icc a b) volume := ContinuousOn.integrableOn_Icc hf
  -- Ioc a b ⊆ Icc a b
  exact hcc.mono_set (Set.Ioc_subset_Icc_self)

/-- **分划覆盖引理**：t ∈ Ioc a b（x₀=a, xₙ=b, 严格增）⟹ ∃ i < n, xᵢ < t ≤ xᵢ₊₁。
  用 Nat.find 找最小 i 使 t ≤ xᵢ。
@isnad1 id=ex.4h5v.s6.0572f9c8475d from=translated src=- shape=533c2a74 vocab=75d3ac73
-/
lemma partition_cover {n : ℕ} {x : ℕ → ℝ} {a b : ℝ} {t : ℝ}
    (x0 : x 0 = a) (xN : x n = b) (hx : ∀ i, i < n → x i < x (i+1))
    (ht : t ∈ Set.Ioc a b) :
    ∃ i, i < n ∧ x i < t ∧ t ≤ x (i+1) := by
  -- 用 Nat.find: 最小 i 使 t ≤ x i
  let p : ℕ → Prop := fun i => t ≤ x i
  have hex : ∃ i, p i := by
    refine ⟨n, ?_⟩
    change t ≤ x n
    rw [xN]
    exact ht.2
  let j := Nat.find hex
  have hpj : p j := Nat.find_spec hex
  -- j ≠ 0（x 0 = a < t）
  have hj0 : j ≠ 0 := by
    intro hj
    have h0 : p 0 := by simpa [hj, j] using hpj
    change t ≤ x 0 at h0
    have : t ≤ a := by simpa [x0] using h0
    linarith [this, ht.1]
  -- j ≤ n（最小性 + p n）
  have hjn : j ≤ n := Nat.find_min' hex (by
    change t ≤ x n
    rw [xN]
    exact ht.2)
  -- i = j-1 < n
  let i := j - 1
  have hi_lt : i < n := by
    dsimp [i]
    omega
  -- x i < t（find_min：i < j ⟹ ¬p i）
  have hxi : x i < t := by
    dsimp [i]
    have hnj : i < j := by dsimp [i]; omega
    have hnotp : ¬p i := Nat.find_min hex hnj
    -- ¬p i : ¬(t ≤ x i) ⟹ x i < t
    exact lt_of_not_ge hnotp
  -- t ≤ x (i+1)：j = i+1，p j
  have hxj : t ≤ x (i+1) := by
    have : i + 1 = j := by dsimp [i]; omega
    simpa [this] using hpj
  refine ⟨i, hi_lt, hxi, hxj⟩

/-- **阶梯函数求值**：t 恰在子区间 Ioc xᵢ xᵢ₊₁ 内（其他子区间不含 t）时，
  ∑ⱼ cⱼ·1_{Ioc xⱼ xⱼ₊₁}(t) = cᵢ（sum_eq_single）。
@isnad1 id=eq.3h5v.s7.f93708a44c29 from=translated src=- shape=a2303fa8 vocab=0ad1b769
-/
theorem step_eval_at {n i : ℕ} {x : ℕ → ℝ} {c : ℕ → ℝ} {t : ℝ} (hi : i < n)
    (ht : t ∈ Set.Ioc (x i) (x (i+1)))
    (hdisj : ∀ j, j < n → j ≠ i → t ∉ Set.Ioc (x j) (x (j+1))) :
    (∑ j ∈ Finset.range n,
      (Set.Ioc (x j) (x (j+1))).indicator (fun _ : ℝ => c j) t) = c i := by
  rw [Finset.sum_eq_single]
  · -- j = i 项
    rw [Set.indicator_of_mem ht]
  · -- j ≠ i 项为 0
    intro j hj hji
    have hnot : t ∉ Set.Ioc (x j) (x (j+1)) := hdisj j (Finset.mem_range.mp hj) hji
    exact Set.indicator_of_notMem hnot (fun _ : ℝ => c j)
  · -- i ∉ range n → 项为 0（不可能，因 hi）
    intro hi_not
    exact False.elim (hi_not (Finset.mem_range.mpr hi))

/-- **有限严格增序列传递**：x 严格增（k<n）且 i+1 ≤ j < n ⟹ x(i+1) ≤ x j。
  分划点单调性的多步传递。
@isnad1 id=le.3h4v.s6.e5f431cb1803 from=translated src=- shape=9152800e vocab=cba06ccd
-/
lemma fin_strict_mono_le {n i j : ℕ} {x : ℕ → ℝ}
    (hx : ∀ k, k < n → x k < x (k+1)) (hij : i + 1 ≤ j) (hj : j < n) :
    x (i+1) ≤ x j := by
  -- F2: 传递链：对 k 从 i+1 到 j，x(i+1) ≤ x k
  -- f k := k ≤ j → x (i+1) ≤ x k
  have hchain : ∀ k, i + 1 ≤ k → k ≤ j → x (i+1) ≤ x k := by
    -- 用 Nat.le_induction，P k := k ≤ j → x(i+1) ≤ x k
    have hbase : i + 1 ≤ j → x (i+1) ≤ x (i+1) := by
      intro _
      rfl
    have hstep : ∀ k, i + 1 ≤ k → (k ≤ j → x (i+1) ≤ x k) → (k+1 ≤ j → x (i+1) ≤ x (k+1)) := by
      intro k hik hfk hkj
      -- k+1 ≤ j ⟹ k < n
      have hkn : k < n := by omega
      have hle_k : x (i+1) ≤ x k := hfk (le_trans (Nat.le_succ k) hkj)
      have hk1 : x k ≤ x (k+1) := le_of_lt (hx k hkn)
      exact le_trans hle_k hk1
    intro k hik hkj
    exact Nat.le_induction (m := i + 1) hbase (fun n hmn hfn => hstep n hmn hfn) k hik hkj
  exact hchain j hij le_rfl

/-- **分划子区间两两不交**：i ≠ j 时 Ioc xᵢ xᵢ₊₁ 与 Ioc xⱼ xⱼ₊₁ 不交。
  阶梯函数唯一性的关键。
@isnad1 id=not.5h5v.s6.96c392148610 from=translated src=- shape=16a49dcc vocab=33f03cf5
-/
lemma partition_disjoint {n i j : ℕ} {x : ℕ → ℝ} {t : ℝ}
    (hx : ∀ k, k < n → x k < x (k+1)) (hi : i < n) (hj : j < n) (hij : i ≠ j)
    (hti : t ∈ Set.Ioc (x i) (x (i+1))) : t ∉ Set.Ioc (x j) (x (j+1)) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · -- i < j：x(i+1) ≤ x j（fin_strict_mono_le），t ≤ x(i+1) ⟹ t ≤ x j，但 Ioc xⱼ 需 x j < t
    intro htj
    have hle : x (i+1) ≤ x j := fin_strict_mono_le hx (Nat.succ_le_of_lt hlt) hj
    have htx : t ≤ x j := le_trans hti.2 hle
    have hxj : x j < t := htj.1
    linarith
  · -- j < i：对称
    intro hti2
    have hle : x (j+1) ≤ x i := fin_strict_mono_le hx (Nat.succ_le_of_lt hgt) hi
    have htj : t ≤ x i := le_trans hti2.2 hle
    have hxi : x i < t := hti.1
    linarith

/-- **分划点单调**：m ≤ j < n 且 x 严格增（k<n）⟹ x m ≤ x j。
@isnad1 id=le.3h4v.s5.23fa03472046 from=translated src=- shape=8dce5f0b vocab=cba06ccd
-/
lemma mono_x_le {n m j : ℕ} {x : ℕ → ℝ}
    (hx : ∀ k, k < n → x k < x (k+1)) (hmj : m ≤ j) (hj : j < n) :
    x m ≤ x j := by
  -- P k := k ≤ j → x m ≤ x k
  have hchain : ∀ k, m ≤ k → k ≤ j → x m ≤ x k := by
    have hbase : m ≤ j → x m ≤ x m := by
      intro _
      rfl
    have hstep : ∀ k, m ≤ k → (k ≤ j → x m ≤ x k) → (k+1 ≤ j → x m ≤ x (k+1)) := by
      intro k hk hfk hkj
      have hkn : k < n := by omega
      have hle_k : x m ≤ x k := hfk (le_trans (Nat.le_succ k) hkj)
      have hk1 : x k ≤ x (k+1) := le_of_lt (hx k hkn)
      exact le_trans hle_k hk1
    intro k hk hkj
    exact Nat.le_induction (m := m) hbase (fun n hmn hfn => hstep n hmn hfn) k hk hkj
  exact hchain j hmj le_rfl

/-- **分划点单调（到端点）**：m ≤ j ≤ n 且 x 严格增 ⟹ x m ≤ x j（允许 j=n，xₙ=b）。
@isnad1 id=le.3h4v.s5.dbb57a7ef07f from=translated src=- shape=5f92bdb3 vocab=cba06ccd
-/
lemma mono_x_le_le {n m j : ℕ} {x : ℕ → ℝ}
    (hx : ∀ k, k < n → x k < x (k+1)) (hmj : m ≤ j) (hj : j ≤ n) :
    x m ≤ x j := by
  -- 直接 Nat.le_induction 从 m 到 j，步进 k < n（k+1 ≤ j ≤ n）
  have hchain : ∀ k, m ≤ k → k ≤ j → x m ≤ x k := by
    have hbase : m ≤ j → x m ≤ x m := by intro _; rfl
    have hstep : ∀ k, m ≤ k → (k ≤ j → x m ≤ x k) → (k+1 ≤ j → x m ≤ x (k+1)) := by
      intro k hk hfk hkj
      have hkn : k < n := by omega  -- k+1 ≤ j ≤ n
      have hle_k : x m ≤ x k := hfk (le_trans (Nat.le_succ k) hkj)
      have hk1 : x k ≤ x (k+1) := le_of_lt (hx k hkn)
      exact le_trans hle_k hk1
    intro k hk hkj
    exact Nat.le_induction (m := m) hbase (fun n hmn hfn => hstep n hmn hfn) k hk hkj
  exact hchain j hmj le_rfl

/-- **分划点属于区间**：x₀=a 严格增 xₙ=b ⟹ x i ∈ [a,b]（对 i ≤ n）。
@isnad1 id=mem.5h5v.s6.9d1b6444b466 from=translated src=- shape=b05a8b0d vocab=5c25823f
-/
lemma partition_point_mem {n i : ℕ} {x : ℕ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (x0 : x 0 = a) (xN : x n = b) (hx : ∀ k, k < n → x k < x (k+1))
    (hi : i ≤ n) :
    x i ∈ Set.Icc a b := by
  constructor
  · have hle : x 0 ≤ x i := mono_x_le_le hx (Nat.zero_le i) hi
    simpa [x0] using hle
  · have hle : x i ≤ x n := mono_x_le_le hx hi (le_rfl)
    simpa [xN] using hle

/-- **阶梯函数 ≤ f（逐点）**：t ∈ Ioc a b 时达布下和阶梯函数 ≤ f t。
  分划覆盖 + step_eval_at + step_le_f_pointwise。
@isnad1 id=le.4h5v.s7.3740b1564930 from=translated src=- shape=080e36b7 vocab=d193d37c
-/
lemma step_le_f_upper {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (P : DarbouxPartition a b)
    (hsub : ∀ i ∈ Finset.range P.n, Set.Ioc (P.x i) (P.x (i+1)) ⊆ Set.Ioc a b) :
    ∀ t ∈ Set.Ioc a b,
      (∑ i ∈ Finset.range P.n,
        (Set.Ioc (P.x i) (P.x (i+1))).indicator
          (fun _ : ℝ => sInf (f '' Set.Icc (P.x i) (P.x (i+1)))) t) ≤ f t := by
  intro t ht
  -- 1. 分划覆盖：t 落子区间 Ioc xᵢ xᵢ₊₁
  rcases partition_cover P.x0 P.xN P.strict ht with ⟨i, hi_lt, hxi, hxi1⟩
  -- 2. sP t = infᵢ（step_eval_at，需 hdisj 唯一）
  have hdisj_all : ∀ j, j < P.n → j ≠ i → t ∉ Set.Ioc (P.x j) (P.x (j+1)) := by
    intro j hj ji
    exact partition_disjoint P.strict hi_lt hj ji.symm ⟨hxi, hxi1⟩
  have hsum : (∑ j ∈ Finset.range P.n,
      (Set.Ioc (P.x j) (P.x (j+1))).indicator
        (fun _ : ℝ => sInf (f '' Set.Icc (P.x j) (P.x (j+1)))) t) =
      sInf (f '' Set.Icc (P.x i) (P.x (i+1))) := by
    exact step_eval_at hi_lt ⟨hxi, hxi1⟩ hdisj_all
  -- 3. infᵢ ≤ f t（D4a，需 f 连续 on Icc xᵢ xᵢ₊₁ 且 t ∈ Ioc xᵢ xᵢ₊₁）
  have hle : sInf (f '' Set.Icc (P.x i) (P.x (i+1))) ≤ f t := by
    -- 需 ContinuousOn f (Icc xᵢ xᵢ₊₁)：子区间 ⊆ Icc a b（分划点在区间内）
    have hxi_ab : P.x i ∈ Set.Icc a b := by
      exact partition_point_mem hab P.x0 P.xN P.strict (le_of_lt hi_lt)
    have hxi1_ab : P.x (i+1) ∈ Set.Icc a b := by
      exact partition_point_mem hab P.x0 P.xN P.strict (Nat.succ_le_of_lt hi_lt)
    have hf_sub : ContinuousOn f (Set.Icc (P.x i) (P.x (i+1))) := by
      exact hf.mono (Set.Icc_subset_Icc hxi_ab.1 hxi1_ab.2)
    exact step_le_f_pointwise (P.strict i hi_lt).le hf_sub ⟨hxi, hxi1⟩
  -- 组装
  rw [hsum]
  exact hle

/-- **下和阶梯函数积分 = 达布下和**：∫ (∑ infᵢ·1_{Ioc xᵢ xᵢ₊₁}) = lowerSum f P。
@isnad1 id=eq.1h4v.s7.baa16b52702a from=translated src=- shape=7479c384 vocab=4e04f37b
-/
lemma step_integral_eq_lowerSum {f : ℝ → ℝ} (P : DarbouxPartition a b)
    (hstep : ∀ i ∈ Finset.range P.n, P.x i ≤ P.x (i+1)) :
    (∫ t : ℝ,
      (∑ i ∈ Finset.range P.n,
        (Set.Ioc (P.x i) (P.x (i+1))).indicator
          (fun _ : ℝ => sInf (f '' Set.Icc (P.x i) (P.x (i+1)))) t) ∂volume) =
      lowerSum f P := by
  -- D3b: ∫(∑ cᵢ·1_{Ioc}) = ∑ cᵢ·步长
  have hD3b := integral_sum_indicator_Ioc (x := P.x)
    (c := fun i => sInf (f '' Set.Icc (P.x i) (P.x (i+1)))) hstep
  rw [hD3b]
  -- 目标: ∑ sInfᵢ·步长 = lowerSum f P
  unfold lowerSum
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- **达布下和 ≤ 区间积分**：f 连续 on [a,b]，任意分划 P ⟹ lowerSum f P ≤ ∫_Ioc a b f。
  数值相等的下界方向。
@isnad1 id=le.4h4v.s7.966d58385aa4 from=translated src=- shape=76a3c64f vocab=45ed2748
-/
theorem darboux_lower_le_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (P : DarbouxPartition a b)
    (hstep : ∀ i ∈ Finset.range P.n, P.x i ≤ P.x (i+1))
    (hsub : ∀ i ∈ Finset.range P.n, Set.Ioc (P.x i) (P.x (i+1)) ⊆ Set.Ioc a b) :
    lowerSum f P ≤ (∫ x : ℝ in Set.Ioc a b, f x ∂volume) := by
  let sP : ℝ → ℝ := fun t => ∑ i ∈ Finset.range P.n,
    (Set.Ioc (P.x i) (P.x (i+1))).indicator (fun _ : ℝ => sInf (f '' Set.Icc (P.x i) (P.x (i+1)))) t
  -- 元件: hsP（恒等）
  have hsP : ∀ t, (Set.Ioc a b).indicator sP t = sP t := by
    intro t
    exact step_indicator_identity (c := fun i => sInf (f '' Set.Icc (P.x i) (P.x (i+1)))) hsub t
  -- 元件: hf_mono（sP ≤ f，逐点 indicator 形式）
  have hf_mono : ∀ t, (Set.Ioc a b).indicator sP t ≤ (Set.Ioc a b).indicator f t := by
    intro t
    by_cases ht : t ∈ Set.Ioc a b
    · -- t ∈ Ioc a b：sP t ≤ f t（step_le_f_upper）
      have hsP_le : sP t ≤ f t := step_le_f_upper hab hf P hsub t ht
      -- indicator 在 s 内取原值
      simpa [Set.indicator, ht] using hsP_le
    · -- t ∉ Ioc a b：indicator 都 0
      simp [Set.indicator, ht]
  -- 元件: hisP/hif（可积）
  have hisP : Integrable ((Set.Ioc a b).indicator sP) volume := by
    -- 用 hisP4 的模式：Integrable sP（全局）+ 恒等 congr
    have hsP_int : Integrable sP volume := by
      have hin : ∀ i ∈ Finset.range P.n, Integrable
          ((Set.Ioc (P.x i) (P.x (i+1))).indicator
            (fun _ : ℝ => sInf (f '' Set.Icc (P.x i) (P.x (i+1))))) volume := by
        intro i hi
        rw [integrable_indicator_iff (hs := measurableSet_Ioc)]
        have hfin : volume (Set.Ioc (P.x i) (P.x (i+1))) ≠ ∞ := by
          rw [Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top
        exact integrableOn_const (μ := volume) (s := Set.Ioc (P.x i) (P.x (i+1)))
          (C := sInf (f '' Set.Icc (P.x i) (P.x (i+1)))) (hs := hfin)
      exact integrable_finsetSum (s := Finset.range P.n) hin
    have hident : (Set.Ioc a b).indicator sP = sP := by
      funext t
      exact hsP t
    rw [hident]
    exact hsP_int
  have hif : Integrable ((Set.Ioc a b).indicator f) volume := by
    rw [integrable_indicator_iff (hs := measurableSet_Ioc)]
    have hcc : IntegrableOn f (Set.Icc a b) volume := ContinuousOn.integrableOn_Icc hf
    exact hcc.mono_set (Set.Ioc_subset_Icc_self)
  -- 用抽象组装
  have h_main := lower_sum_le_interval (f := f) (sP := sP) (s := Set.Ioc a b)
    (hs := measurableSet_Ioc) (hsP := hsP) (hf_mono := hf_mono) (hisP := hisP) (hif := hif)
  -- h_main : ∫ sP ≤ ∫_Ioc f
  have h_int : (∫ t : ℝ, sP t ∂volume) = lowerSum f P :=
    step_integral_eq_lowerSum P hstep
  -- 组装
  calc
    lowerSum f P = (∫ t : ℝ, sP t ∂volume) := h_int.symm
    _ ≤ (∫ x : ℝ in Set.Ioc a b, f x ∂volume) := h_main

/-- **分划子区间包含**：分划 P 的子区间 Ioc xᵢ xᵢ₊₁ ⊆ Ioc a b（由 P 端点与严格增）。
@isnad1 id=le.3h4v.s6.48906ddb090f from=translated src=- shape=e075f9e1 vocab=6ae94345
-/
lemma partition_subinterval_sub {a b : ℝ} (hab : a ≤ b) (P : DarbouxPartition a b)
    (_hstep : ∀ i ∈ Finset.range P.n, P.x i ≤ P.x (i+1)) :
    ∀ i ∈ Finset.range P.n, Set.Ioc (P.x i) (P.x (i+1)) ⊆ Set.Ioc a b := by
  intro i hi
  intro t ht
  -- t ∈ Ioc xᵢ xᵢ₊₁：a < t 且 t ≤ b
  constructor
  · -- a < t：x₀ = a ≤ xᵢ < t？需 a ≤ xᵢ（mono_x_le_le）+ xᵢ < t
    have hxi_ab : P.x i ∈ Set.Icc a b := partition_point_mem hab P.x0 P.xN P.strict (le_of_lt (Finset.mem_range.mp hi))
    have : a ≤ P.x i := hxi_ab.1
    have : P.x i < t := ht.1
    linarith
  · -- t ≤ b：t ≤ xᵢ₊₁ ≤ xₙ = b
    have hxi1_ab : P.x (i+1) ∈ Set.Icc a b := partition_point_mem hab P.x0 P.xN P.strict (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
    have : t ≤ P.x (i+1) := ht.2
    have : P.x (i+1) ≤ b := hxi1_ab.2
    linarith

/-- **黎曼积分值 ≤ 区间积分**：riemannIntegral f a b = sSup{lowerSum} ≤ ∫_Ioc a b f。
@isnad1 id=le.2h3v.s6.d5c55f524845 from=translated src=- shape=70849223 vocab=00ed71ee
-/
theorem riemannIntegral_le_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    riemannIntegral f a b ≤ (∫ x : ℝ in Set.Ioc a b, f x ∂volume) := by
  unfold riemannIntegral
  apply csSup_le
  · -- 集合非空：uniformPartition 给 P
    exact ⟨lowerSum f (uniformPartition a b 1 hab (by norm_num)), ⟨uniformPartition a b 1 hab (by norm_num), rfl⟩⟩
  · -- 每个元素 ≤ ∫
    intro m hm
    rcases hm with ⟨P, rfl⟩
    -- lowerSum f P ≤ ∫（darboux_lower_le_interval）
    have hstep : ∀ i ∈ Finset.range P.n, P.x i ≤ P.x (i+1) := by
      intro i hi
      exact (P.strict i (Finset.mem_range.mp hi)).le
    have hsub := partition_subinterval_sub (le_of_lt hab) P hstep
    exact darboux_lower_le_interval (le_of_lt hab) hf P hstep hsub

/-- **f ≤ 上阶梯函数逐点**：t ∈ Ioc p q 时 f t ≤ sSup(f''[p,q])（f 连续 on [p,q]）。
  达布上和对应阶梯函数 ≥ f 的逐点依据。
@isnad1 id=le.3h4v.s6.bf9cc47d2ded from=translated src=- shape=61a0253c vocab=d5d193d5
-/
lemma f_le_step_sup_pointwise {f : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hf : ContinuousOn f (Set.Icc p q)) {t : ℝ} (ht : t ∈ Set.Ioc p q) :
    f t ≤ sSup (f '' Set.Icc p q) := by
  -- f t ∈ f''Icc ⟹ f t ≤ sSup（csSup_le 的对称：le_csSup）
  have htm : f t ∈ f '' Set.Icc p q := by
    refine ⟨t, ⟨le_of_lt ht.1, ht.2⟩, rfl⟩
  -- f t ≤ sSup (f''Icc)：用 le_csSup（需 BddAbove）
  exact le_csSup (IsCompact.bddAbove (IsCompact.image_of_continuousOn isCompact_Icc hf)) htm

/-- **f ≤ 上阶梯函数（逐点）**：t ∈ Ioc a b 时 f t ≤ 达布上和阶梯函数。
  分划覆盖 + step_eval_at + f_le_step_sup_pointwise。
@isnad1 id=le.4h5v.s7.c6bf2eb7db9e from=translated src=- shape=24420d28 vocab=1cf514fe
-/
lemma step_ge_f_upper {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (P : DarbouxPartition a b)
    (hsub : ∀ i ∈ Finset.range P.n, Set.Ioc (P.x i) (P.x (i+1)) ⊆ Set.Ioc a b) :
    ∀ t ∈ Set.Ioc a b,
      f t ≤ (∑ i ∈ Finset.range P.n,
        (Set.Ioc (P.x i) (P.x (i+1))).indicator
          (fun _ : ℝ => sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) t) := by
  intro t ht
  rcases partition_cover P.x0 P.xN P.strict ht with ⟨i, hi_lt, hxi, hxi1⟩
  have hdisj_all : ∀ j, j < P.n → j ≠ i → t ∉ Set.Ioc (P.x j) (P.x (j+1)) := by
    intro j hj ji
    exact partition_disjoint P.strict hi_lt hj ji.symm ⟨hxi, hxi1⟩
  have hsum : (∑ j ∈ Finset.range P.n,
      (Set.Ioc (P.x j) (P.x (j+1))).indicator
        (fun _ : ℝ => sSup (f '' Set.Icc (P.x j) (P.x (j+1)))) t) =
      sSup (f '' Set.Icc (P.x i) (P.x (i+1))) := by
    exact step_eval_at (c := fun j => sSup (f '' Set.Icc (P.x j) (P.x (j+1)))) hi_lt ⟨hxi, hxi1⟩ hdisj_all
  have hle : f t ≤ sSup (f '' Set.Icc (P.x i) (P.x (i+1))) := by
    have hxi_ab : P.x i ∈ Set.Icc a b := by
      exact partition_point_mem hab P.x0 P.xN P.strict (le_of_lt hi_lt)
    have hxi1_ab : P.x (i+1) ∈ Set.Icc a b := by
      exact partition_point_mem hab P.x0 P.xN P.strict (Nat.succ_le_of_lt hi_lt)
    have hf_sub : ContinuousOn f (Set.Icc (P.x i) (P.x (i+1))) := by
      exact hf.mono (Set.Icc_subset_Icc hxi_ab.1 hxi1_ab.2)
    exact f_le_step_sup_pointwise (P.strict i hi_lt).le hf_sub ⟨hxi, hxi1⟩
  rw [hsum]
  exact hle

/-- **f·1 ≤ 上阶梯·1（逐点）**：连续 f 的 indicator ≤ 达布上和阶梯函数的 indicator。
  上和方向夹逼的保序前提。
@isnad1 id=le.3h5v.s7.4e7a0e8950e2 from=translated src=- shape=3c5e02e8 vocab=1cf514fe
-/
lemma indicator_f_le_indicator_uP {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (P : DarbouxPartition a b)
    (hsub : ∀ i ∈ Finset.range P.n, Set.Ioc (P.x i) (P.x (i+1)) ⊆ Set.Ioc a b) :
    ∀ t, (Set.Ioc a b).indicator f t ≤
      (Set.Ioc a b).indicator
        (fun t => ∑ i ∈ Finset.range P.n,
          (Set.Ioc (P.x i) (P.x (i+1))).indicator
            (fun _ : ℝ => sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) t) t := by
  intro t
  by_cases ht : t ∈ Set.Ioc a b
  · -- pos: t ∈ Ioc ⟹ f t ≤ uP t（step_ge_f_upper）
    rw [Set.indicator_of_mem ht]
    rw [Set.indicator_of_mem ht]
    -- 目标: f t ≤ ∑ ...，用 step_ge_f_upper
    exact step_ge_f_upper hab hf P hsub t ht
  · -- neg: 都 0
    simp [Set.indicator, ht]

/-- **上和阶梯函数积分 = 达布上和**：∫ (∑ supᵢ·1_{Ioc xᵢ xᵢ₊₁}) = upperSum f P。
@isnad1 id=eq.1h4v.s7.60519abe2910 from=translated src=- shape=7479c384 vocab=ffc5ffc2
-/
lemma step_sup_integral_eq_upperSum {f : ℝ → ℝ} (P : DarbouxPartition a b)
    (hstep : ∀ i ∈ Finset.range P.n, P.x i ≤ P.x (i+1)) :
    (∫ t : ℝ,
      (∑ i ∈ Finset.range P.n,
        (Set.Ioc (P.x i) (P.x (i+1))).indicator
          (fun _ : ℝ => sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) t) ∂volume) =
      upperSum f P := by
  have hD3b := integral_sum_indicator_Ioc (x := P.x)
    (c := fun i => sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) hstep
  rw [hD3b]
  unfold upperSum
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- **区间积分 ≤ 达布上和**：f 连续 on [a,b]，任意分划 P ⟹ ∫_Ioc a b f ≤ upperSum f P。
  数值相等的上界方向（对称于 darboux_lower）。
@isnad1 id=le.4h4v.s7.275af9a98554 from=translated src=- shape=2d789b77 vocab=ec13f396
-/
theorem darboux_upper_ge_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (P : DarbouxPartition a b)
    (hstep : ∀ i ∈ Finset.range P.n, P.x i ≤ P.x (i+1))
    (hsub : ∀ i ∈ Finset.range P.n, Set.Ioc (P.x i) (P.x (i+1)) ⊆ Set.Ioc a b) :
    (∫ x : ℝ in Set.Ioc a b, f x ∂volume) ≤ upperSum f P := by
  let uP : ℝ → ℝ := fun t => ∑ i ∈ Finset.range P.n,
    (Set.Ioc (P.x i) (P.x (i+1))).indicator (fun _ : ℝ => sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) t
  -- ∫_Ioc f = ∫ (f·1) ≤ ∫ (uP·1) = ∫ uP = upperSum
  -- 用抽象: ∫ (f·1) ≤ ∫ (uP·1)（保序，f ≤ uP）
  -- 先证 f·1 ≤ uP·1（逐点）
  have hf_uP : ∀ t, (Set.Ioc a b).indicator f t ≤ (Set.Ioc a b).indicator uP t := by
    intro t
    -- 用独立引理（uP 是求和，indicator_f_le_indicator_uP 内联求和）
    simpa [uP] using indicator_f_le_indicator_uP hab hf P hsub t  -- ∫ (f·1) ≤ ∫ (uP·1)（全局保序，需可积）
  have hf_int : (∫ t : ℝ, (Set.Ioc a b).indicator f t ∂volume) ≤
      (∫ t : ℝ, (Set.Ioc a b).indicator uP t ∂volume) := by
    have hif : Integrable ((Set.Ioc a b).indicator f) volume := by
      rw [integrable_indicator_iff (hs := measurableSet_Ioc)]
      have hcc : IntegrableOn f (Set.Icc a b) volume := ContinuousOn.integrableOn_Icc hf
      exact hcc.mono_set (Set.Ioc_subset_Icc_self)
    have hiuP : Integrable ((Set.Ioc a b).indicator uP) volume := by
      -- uP·1 可积：uP 全局可积 + 恒等
      have huP_int : Integrable uP volume := by
        have hin : ∀ i ∈ Finset.range P.n, Integrable
            ((Set.Ioc (P.x i) (P.x (i+1))).indicator
              (fun _ : ℝ => sSup (f '' Set.Icc (P.x i) (P.x (i+1))))) volume := by
          intro i hi
          rw [integrable_indicator_iff (hs := measurableSet_Ioc)]
          have hfin : volume (Set.Ioc (P.x i) (P.x (i+1))) ≠ ∞ := by
            rw [Real.volume_Ioc]
            exact ENNReal.ofReal_ne_top
          exact integrableOn_const (μ := volume) (s := Set.Ioc (P.x i) (P.x (i+1)))
            (C := sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) (hs := hfin)
        exact integrable_finsetSum (s := Finset.range P.n) hin
      have hident : (Set.Ioc a b).indicator uP = uP := by
        funext t
        exact step_indicator_identity (c := fun i => sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) hsub t
      rw [hident]
      exact huP_int
    exact integral_mono hif hiuP hf_uP
  -- ∫_Ioc f = ∫ (f·1)（integral_indicator）
  have h3 : (∫ x : ℝ in Set.Ioc a b, f x ∂volume) = (∫ t : ℝ, (Set.Ioc a b).indicator f t ∂volume) :=
    (integral_indicator (hs := measurableSet_Ioc)).symm
  -- ∫ (uP·1) = ∫ uP = upperSum
  have h4 : (∫ t : ℝ, (Set.Ioc a b).indicator uP t ∂volume) = upperSum f P := by
    -- uP·1 = uP（恒等）
    have hident : (Set.Ioc a b).indicator uP = uP := by
      funext t
      exact step_indicator_identity (c := fun i => sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) hsub t
    -- ∫ uP = upperSum（对称 D3c）
    have hUP_sum : (∫ t : ℝ, uP t ∂volume) = upperSum f P := by
      rw [show uP = (fun t => ∑ i ∈ Finset.range P.n,
          (Set.Ioc (P.x i) (P.x (i+1))).indicator
            (fun _ : ℝ => sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) t) by rfl]
      exact step_sup_integral_eq_upperSum P hstep
    rw [hident]
    exact hUP_sum
  calc
    (∫ x : ℝ in Set.Ioc a b, f x ∂volume) = (∫ t : ℝ, (Set.Ioc a b).indicator f t ∂volume) := h3
    _ ≤ (∫ t : ℝ, (Set.Ioc a b).indicator uP t ∂volume) := hf_int
    _ = upperSum f P := h4

/-- **区间积分 ≤ 下和上确界 + ε**：∀ε>0, ∫_Ioc a b f ≤ sSup{lowerSum} + ε。
  用连续⟹可积（上下和差小）+ 上界方向。
@isnad1 id=le.3h4v.s6.f2b4f7198d06 from=translated src=- shape=b9f11941 vocab=885c6f7d
-/
theorem interval_le_sSup_lowerSum_add {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (ε : ℝ) (hε : 0 < ε) :
    (∫ x : ℝ in Set.Ioc a b, f x ∂volume) ≤
      sSup {x : ℝ | ∃ P : DarbouxPartition a b, x = lowerSum f P} + ε := by
  have hR := continuous_on_riemannIntegrable_lt hab hf ε hε
  rcases hR with ⟨P, hPd⟩
  have hstep : ∀ i ∈ Finset.range P.n, P.x i ≤ P.x (i+1) := by
    intro i hi
    exact (P.strict i (Finset.mem_range.mp hi)).le
  have hsub := partition_subinterval_sub (le_of_lt hab) P hstep
  have hU : (∫ x : ℝ in Set.Ioc a b, f x ∂volume) ≤ upperSum f P :=
    darboux_upper_ge_interval (le_of_lt hab) hf P hstep hsub
  have hUs : upperSum f P < lowerSum f P + ε := by linarith
  have hL : lowerSum f P ≤ sSup {x : ℝ | ∃ P : DarbouxPartition a b, x = lowerSum f P} := by
    have hmem : lowerSum f P ∈ {x : ℝ | ∃ P : DarbouxPartition a b, x = lowerSum f P} := ⟨P, rfl⟩
    have hbdd : BddAbove {x : ℝ | ∃ P : DarbouxPartition a b, x = lowerSum f P} := by
      refine ⟨(∫ x : ℝ in Set.Ioc a b, f x ∂volume), ?_⟩
      intro y hy
      rcases hy with ⟨P, rfl⟩
      have hstep' : ∀ i ∈ Finset.range P.n, P.x i ≤ P.x (i+1) := by
        intro i hi
        exact (P.strict i (Finset.mem_range.mp hi)).le
      have hsub' := partition_subinterval_sub (le_of_lt hab) P hstep'
      exact darboux_lower_le_interval (le_of_lt hab) hf P hstep' hsub'
    exact le_csSup hbdd hmem
  exact le_of_lt (calc
    (∫ x : ℝ in Set.Ioc a b, f x ∂volume) ≤ upperSum f P := hU
    _ < lowerSum f P + ε := hUs
    _ ≤ sSup {x : ℝ | ∃ P : DarbouxPartition a b, x = lowerSum f P} + ε := by linarith)

/-- **黎曼积分值 = Lebesgue 区间积分**：连续函数 f 的黎曼积分（下和上确界）
  = Lebesgue 区间积分。达布和=阶梯函数积分 + 上下夹逼，完全自证（mathlib 无此定理）。
> **Entry**: real-analysis.riemann.eq-lebesgue
@isnad1 id=eq.2h3v.s6.f3adfdcd6a1d from=translated src=- shape=70849223 vocab=5daf804c
-/
theorem riemannIntegral_eq_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    riemannIntegral f a b = (∫ x : ℝ in Set.Ioc a b, f x ∂volume) := by
  -- 方向1: riemannIntegral ≤ ∫
  have hle1 : riemannIntegral f a b ≤ (∫ x : ℝ in Set.Ioc a b, f x ∂volume) :=
    riemannIntegral_le_interval hab hf
  -- 方向2: ∫ ≤ riemannIntegral
  have hle2 : (∫ x : ℝ in Set.Ioc a b, f x ∂volume) ≤ riemannIntegral f a b := by
    -- 用 le_of_forall_pos_le_add: ∀ε, ∫ ≤ sSup + ε
    unfold riemannIntegral
    apply le_of_forall_pos_le_add
    intro ε hε
    exact interval_le_sSup_lowerSum_add hab hf ε hε
  exact le_antisymm hle1 hle2

end RealAnalysis.Riemann

end SandronesLibrary
