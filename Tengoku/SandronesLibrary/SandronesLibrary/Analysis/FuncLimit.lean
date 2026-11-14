/-
Copyright (c) 2026 Sandrones's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrones' Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter Topology
open scoped Filter Topology

/-!
# Analysis / FuncLimit —— 函数极限基础条目（第四章）

本文件当前条目（§0 铁律4：一次一条，逐条编译）：

* **analysis.func-limit.definition**（函数极限定义/ε-δ 判据）。
* **analysis.func-limit.const**（常数函数趋于常数）。
* **analysis.func-limit.identity**（恒等函数连续）。
* **analysis.func-limit.unique**（函数极限唯一）。
* **analysis.func-limit.congr**（最终相等替换）。
* **analysis.func-limit.add**（函数极限加法）。
* **analysis.func-limit.sub**（函数极限减法）。
* **analysis.func-limit.mul**（函数极限乘法）。
* **analysis.func-limit.div**（函数极限除法，分母极限非零）。
* **analysis.func-limit.const-mul**（常数数乘）。
* **analysis.func-limit.le**（极限保序）。
* **analysis.func-limit.heine**（Heine 归结原理）。
* **analysis.func-limit.at-top**（无穷极限）。
* **analysis.func-limit.comp**（复合函数极限：g 连续时 lim g(f(x))=g(L)）。
-/

namespace SandronesLibrary

namespace Analysis.FuncLimit

/-- 实函数 `f` 在点 `a` 的去心邻域趋于 `L` 的教材 ε-δ 定义。
> **Entry**: analysis.func-limit.definition-/
def FunctionConvergesToAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → x ≠ a → |f x - L| < ε

/-- 展开本库函数有限点极限定义。
@isnad1 id=iff.0h3v.s6.04822fc8b768 from=translated src=- shape=73350bb1 vocab=6dc045cd
-/
theorem functionConvergesToAt_iff_epsilon_delta {f : ℝ → ℝ} {a L : ℝ} :
    FunctionConvergesToAt f a L ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → x ≠ a → |f x - L| < ε :=
  Iff.rfl

/-- 去心邻域上的“最终成立”换成 ε-δ 判据：`∀ᶠ x in 𝓝[≠] a, p x` ⟺
  存在 δ>0 使 a 的 δ 去心邻域内p 都成立。 
> **Entry**: analysis.func-limit.definition
@isnad1 id=iff.0h2v.s6.f993bbcae119 from=translated src=- shape=1d36bf48 vocab=6ac58dd3
-/
lemma eventually_nhds_within_iff_delta (a : ℝ) (p : ℝ → Prop) :
    (∀ᶠ x in 𝓝[≠] a, p x) ↔ ∃ δ > 0, ∀ x, |x - a| < δ → x ≠ a → p x := by
  rw [Filter.Eventually]
  rw [Metric.mem_nhdsWithin_iff]
  constructor
  · rintro ⟨ε, hε, hball⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx hxne
    exact hball ⟨by simpa [Real.dist_eq] using hx, hxne⟩
  · rintro ⟨δ, hδ, hδp⟩
    refine ⟨δ, hδ, ?_⟩
    rintro x ⟨hx, hxne⟩
    exact hδp x (by simpa [Real.dist_eq] using hx) hxne

/-- 函数极限定义：f 在 a 的去心邻域上趋于 L（ε-δ 判据）。 
> **Entry**: analysis.func-limit.definition
@isnad1 id=iff.0h3v.s6.9286645437cc from=translated src=- shape=aa022389 vocab=0f3fed03
-/
lemma tendsto_nhds_iff_eps_delta {f : ℝ → ℝ} {a L : ℝ} :
    Tendsto f (𝓝[≠] a) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → x ≠ a → |f x - L| < ε := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    exact (eventually_nhds_within_iff_delta a (fun x => |f x - L| < ε)).mp (h ε hε)
  · intro h ε hε
    exact (eventually_nhds_within_iff_delta a (fun x => |f x - L| < ε)).mpr (h ε hε)

/-- 本库 ε-δ 函数极限定义与 Mathlib 去心邻域 `Tendsto` 接口完全等价。
@isnad1 id=iff.0h3v.s5.e1b0f6c3588a from=translated src=- shape=93846b6c vocab=bdbf3fef
-/
theorem functionConvergesToAt_iff_tendsto {f : ℝ → ℝ} {a L : ℝ} :
    FunctionConvergesToAt f a L ↔ Tendsto f (𝓝[≠] a) (𝓝 L) := by
  simpa [FunctionConvergesToAt] using
    (tendsto_nhds_iff_eps_delta (f := f) (a := a) (L := L)).symm

/-- 教材 ε-δ 接口下的函数极限唯一性。
@isnad1 id=eq.2h4v.s4.11bffecfb5d8 from=translated src=- shape=811c725b vocab=4da68eca
-/
theorem functionConvergesToAt_unique {f : ℝ → ℝ} {a L M : ℝ}
    (hL : FunctionConvergesToAt f a L) (hM : FunctionConvergesToAt f a M) : L = M := by
  exact tendsto_nhds_unique (functionConvergesToAt_iff_tendsto.mp hL)
    (functionConvergesToAt_iff_tendsto.mp hM)

/-- 常数函数在任意滤子下趋近该常数。 
> **Entry**: analysis.func-limit.const
@isnad1 id=tendsto.0h2v.s4.484ef1a131d6 from=translated src=- shape=a4fd74db vocab=74aea0aa
-/
lemma tendsto_const_fun {c : ℝ} {f : Filter ℝ} :
    Tendsto (fun _ : ℝ => c) f (𝓝 c) :=
  tendsto_const_nhds

/-- 恒等函数在 a 处连续（趋近 a）。 
> **Entry**: analysis.func-limit.identity
@isnad1 id=tendsto.0h1v.s4.f5189b2c1a8a from=translated src=- shape=7b086735 vocab=b8afaf7c
-/
lemma tendsto_id_nhds (a : ℝ) : Tendsto id (𝓝 a) (𝓝 a) :=
  tendsto_id

/-- 函数极限唯一：同一趋近方向下两个极限必相等。 
> **Entry**: analysis.func-limit.unique
@isnad1 id=eq.2h4v.s6.08e8cfa879f9 from=translated src=- shape=ba315c5a vocab=41a47820
-/
lemma func_lim_unique {f : ℝ → ℝ} {a : ℝ} {L M : ℝ}
    (hL : Tendsto f (𝓝[≠] a) (𝓝 L)) (hM : Tendsto f (𝓝[≠] a) (𝓝 M)) : L = M :=
  tendsto_nhds_unique hL hM

/-- 最终相等替换：在 a 的去心邻域上 f = g，则 f 与 g 的极限相同。 
> **Entry**: analysis.func-limit.congr
@isnad1 id=tendsto.2h4v.s6.fc84e3500d73 from=translated src=- shape=3a055a7f vocab=ca811dc4
-/
lemma func_lim_congr {f g : ℝ → ℝ} {a : ℝ} {L : ℝ}
    (hfg : ∀ᶠ x in 𝓝[≠] a, f x = g x)
    (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) : Tendsto g (𝓝[≠] a) (𝓝 L) :=
  hf.congr' hfg

/-- 和的极限 = 极限的和。 
> **Entry**: analysis.func-limit.add
@isnad1 id=tendsto.2h5v.s7.4ea62df4e22c from=translated src=- shape=e43c8476 vocab=3d52a64f
-/
lemma func_lim_add {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) (hg : Tendsto g (𝓝[≠] a) (𝓝 M)) :
    Tendsto (fun x => f x + g x) (𝓝[≠] a) (𝓝 (L + M)) :=
  hf.add hg

/-- 差的极限 = 极限的差。 
> **Entry**: analysis.func-limit.sub
@isnad1 id=tendsto.2h5v.s7.7a519723c8f0 from=translated src=- shape=e43c8476 vocab=58020ef3
-/
lemma func_lim_sub {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) (hg : Tendsto g (𝓝[≠] a) (𝓝 M)) :
    Tendsto (fun x => f x - g x) (𝓝[≠] a) (𝓝 (L - M)) :=
  hf.sub hg

/-- 积的极限 = 极限的积。 
> **Entry**: analysis.func-limit.mul
@isnad1 id=tendsto.2h5v.s7.f2c179ce81c7 from=translated src=- shape=e43c8476 vocab=96dccd5c
-/
lemma func_lim_mul {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) (hg : Tendsto g (𝓝[≠] a) (𝓝 M)) :
    Tendsto (fun x => f x * g x) (𝓝[≠] a) (𝓝 (L * M)) :=
  hf.mul hg

/-- 商的极限 = 极限的商（分母极限非零）。 
> **Entry**: analysis.func-limit.div
@isnad1 id=tendsto.3h5v.s7.af0d7e6069be from=translated src=- shape=145a6ccf vocab=71e80ed1
-/
lemma func_lim_div {f g : ℝ → ℝ} {a L M : ℝ} (hM : M ≠ 0)
    (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) (hg : Tendsto g (𝓝[≠] a) (𝓝 M)) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 (L / M)) :=
  hf.div hg hM

/-- 常数数乘可提出极限：lim (c·f) = c·lim f。 
> **Entry**: analysis.func-limit.const-mul
@isnad1 id=tendsto.1h4v.s6.9d5f1bb2907b from=translated src=- shape=72294840 vocab=96dccd5c
-/
lemma func_lim_const_mul {f : ℝ → ℝ} {a L : ℝ} (c : ℝ)
    (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) :
    Tendsto (fun x => c * f x) (𝓝[≠] a) (𝓝 (c * L)) :=
  hf.const_mul c

/-- 极限保序：去心邻域上 f ≤ g 且 f→L、g→M，则 L ≤ M。
  证明：g − f → M − L，且 g − f ≥ 0 最终，极限取不等式（ge_of_tendsto）。 
> **Entry**: analysis.func-limit.le
@isnad1 id=le.3h5v.s6.157ec1452f96 from=translated src=- shape=be7c4053 vocab=68e81940
-/
lemma func_lim_le {f g : ℝ → ℝ} {a L M : ℝ}
    (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) (hg : Tendsto g (𝓝[≠] a) (𝓝 M))
    (hfg : ∀ᶠ x in 𝓝[≠] a, f x ≤ g x) : L ≤ M := by
  have hsub : Tendsto (fun x => g x - f x) (𝓝[≠] a) (𝓝 (M - L)) := hg.sub hf
  have hnonneg : ∀ᶠ x in 𝓝[≠] a, (0 : ℝ) ≤ g x - f x := by
    filter_upwards [hfg] with x hx
    linarith
  have h0 : 0 ≤ M - L := ge_of_tendsto hsub hnonneg
  linarith

/-- Heine 归结原理的 (⇒) 方向：函数极限 ⟹ 沿序列的极限。 
> **Entry**: analysis.func-limit.heine
@isnad1 id=tendsto.3h4v.s6.e65397a08446 from=translated src=- shape=c533feb7 vocab=9f800eca
-/
lemma heine_forward {f : ℝ → ℝ} {a L : ℝ}
    (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) :
    ∀ u : ℕ → ℝ, Tendsto u atTop (𝓝 a) → (∀ n, u n ≠ a) →
      Tendsto (f ∘ u) atTop (𝓝 L) := by
  intro u hu hua
  have hu' : Tendsto u atTop (𝓝[≠] a) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hu, Filter.Eventually.of_forall (fun n => (hua n))⟩
  exact hf.comp hu'

/-- Heine 归结原理的 (⇐) 方向：沿序列的极限 ⟹ 函数极限。
  反证：若 f 在 a 的去心邻域上不趋于 L，取 ε₀，对每个 n 取 xₙ 满足
  |xₙ−a|<1/(n+1) ∧ xₙ≠a ∧ ε₀≤|f(xₙ)−L|；于是 xₙ→a 且 xₙ≠a，
  但 f∘x 不趋于 L，与前提矛盾。 
> **Entry**: analysis.func-limit.heine
@isnad1 id=tendsto.1h3v.s6.9f45d352d9e6 from=translated src=- shape=ce1e67ff vocab=9f800eca
-/
lemma heine_backward {f : ℝ → ℝ} {a L : ℝ}
    (h : ∀ u : ℕ → ℝ, Tendsto u atTop (𝓝 a) → (∀ n, u n ≠ a) →
      Tendsto (f ∘ u) atTop (𝓝 L)) :
    Tendsto f (𝓝[≠] a) (𝓝 L) := by
  rw [tendsto_nhds_iff_eps_delta]
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨ε, hεpos, hbad⟩
  let u : ℕ → ℝ := fun n => Classical.choose (hbad (1 / (n + 1 : ℝ)) (by positivity))
  have hu : ∀ n, |u n - a| < 1 / (n + 1 : ℝ) ∧ u n ≠ a ∧ ε ≤ |f (u n) - L| := by
    intro n
    exact Classical.choose_spec (hbad (1 / (n + 1 : ℝ)) (by positivity))
  have hua : Tendsto u atTop (𝓝 a) := by
    rw [Metric.tendsto_atTop]
    intro δ' hδ'
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have hcomp : Tendsto (fun n : ℕ => (1 : ℝ) / ↑(n + 1)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat.comp (Filter.tendsto_add_atTop_nat (1 : ℕ))
      convert hcomp using 1
      funext n
      simp [Nat.cast_add]
    rcases Metric.tendsto_atTop.mp h0 δ' hδ' with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have hd : dist ((1 : ℝ) / ((n : ℝ) + 1)) 0 < δ' := hN n hn
    have hlt : (1 : ℝ) / ((n : ℝ) + 1) < δ' := by
      simpa [Real.dist_eq, abs_of_pos hpos] using hd
    have hbnd : |u n - a| < δ' := lt_trans (hu n).1 hlt
    simpa [Real.dist_eq] using hbnd
  have hun : ∀ n, u n ≠ a := fun n => (hu n).2.1
  have hlim : Tendsto (f ∘ u) atTop (𝓝 L) := h u hua hun
  have hcontra : ¬ Tendsto (f ∘ u) atTop (𝓝 L) := by
    rw [Metric.tendsto_atTop]
    push Not
    refine ⟨ε, hεpos, ?_⟩
    intro N
    refine ⟨N + 1, by omega, ?_⟩
    rw [Real.dist_eq]
    exact (hu (N + 1)).2.2
  exact hcontra hlim

/-- Heine 归结原理：函数极限 ⟺ 沿所有去心收敛序列取极限。 
> **Entry**: analysis.func-limit.heine
@isnad1 id=iff.0h3v.s6.a44cf4ed7298 from=translated src=- shape=34f049ba vocab=9f800eca
-/
lemma heine {f : ℝ → ℝ} {a L : ℝ} :
    Tendsto f (𝓝[≠] a) (𝓝 L) ↔
      ∀ u : ℕ → ℝ, Tendsto u atTop (𝓝 a) → (∀ n, u n ≠ a) →
        Tendsto (f ∘ u) atTop (𝓝 L) :=
  ⟨heine_forward, heine_backward⟩

/-- `x → +∞` 时 `f x → L` 的教材 ε-M 定义。
> **Entry**: analysis.func-limit.at-top-/
def FunctionConvergesAtTopTo (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ M : ℝ, ∀ x, M ≤ x → |f x - L| < ε

/-- `x → a` 时 `f x → +∞` 的教材 M-δ 定义。-/
def FunctionDivergesToAtTopAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ M : ℝ, ∃ δ > 0, ∀ x, |x - a| < δ → x ≠ a → M ≤ f x

/-- `x → -∞` 时 `f x → L` 的教材 ε-M 定义。-/
def FunctionConvergesAtBotTo (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ M : ℝ, ∀ x, x ≤ M → |f x - L| < ε

/-- `x → a` 时 `f x → -∞` 的教材 M-δ 定义。-/
def FunctionDivergesToAtBotAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ M : ℝ, ∃ δ > 0, ∀ x, |x - a| < δ → x ≠ a → f x ≤ M

/-- 展开正无穷远有限极限的教材 ε-M 量词。
@isnad1 id=iff.0h2v.s5.fd8a8920e4f0 from=translated src=- shape=fe34509b vocab=bdb8f75a
-/
theorem functionConvergesAtTopTo_iff {f : ℝ → ℝ} {L : ℝ} :
    FunctionConvergesAtTopTo f L ↔
      ∀ ε > 0, ∃ M : ℝ, ∀ x, M ≤ x → |f x - L| < ε :=
  Iff.rfl

/-- 展开有限点处趋于正无穷的教材 M-δ 量词。
@isnad1 id=iff.0h2v.s5.2400c108d4f9 from=translated src=- shape=ea14b901 vocab=a8fd0ba7
-/
theorem functionDivergesToAtTopAt_iff {f : ℝ → ℝ} {a : ℝ} :
    FunctionDivergesToAtTopAt f a ↔
      ∀ M : ℝ, ∃ δ > 0, ∀ x, |x - a| < δ → x ≠ a → M ≤ f x :=
  Iff.rfl

/-- 展开负无穷远有限极限的教材 ε-M 量词。
@isnad1 id=iff.0h2v.s5.f1cf6a6afa3c from=translated src=- shape=4f93c85d vocab=1cf77f16
-/
theorem functionConvergesAtBotTo_iff {f : ℝ → ℝ} {L : ℝ} :
    FunctionConvergesAtBotTo f L ↔
      ∀ ε > 0, ∃ M : ℝ, ∀ x, x ≤ M → |f x - L| < ε :=
  Iff.rfl

/-- 展开有限点处趋于负无穷的教材 M-δ 量词。
@isnad1 id=iff.0h2v.s5.69884298fdbb from=translated src=- shape=3bf02120 vocab=58787952
-/
theorem functionDivergesToAtBotAt_iff {f : ℝ → ℝ} {a : ℝ} :
    FunctionDivergesToAtBotAt f a ↔
      ∀ M : ℝ, ∃ δ > 0, ∀ x, |x - a| < δ → x ≠ a → f x ≤ M :=
  Iff.rfl

/-- 自变量趋于正无穷时的极限：f (x) → L 当 x → ∞（ε-N 判据）。 
> **Entry**: analysis.func-limit.at-top
@isnad1 id=iff.0h2v.s6.b1d7b2788a88 from=translated src=- shape=b1114439 vocab=1f863c05
-/
lemma tendsto_atTop_iff_eps_N {f : ℝ → ℝ} {L : ℝ} :
    Tendsto f atTop (𝓝 L) ↔
      ∀ ε > 0, ∃ M, ∀ x, M ≤ x → |f x - L| < ε := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro x hx
    simpa [Real.dist_eq] using hM x hx
  · intro h ε hε
    rcases h ε hε with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro x hx
    simpa [Real.dist_eq] using hM x hx

/-- 教材 ε-M 定义与 Mathlib 的正无穷远有限极限接口等价。
@isnad1 id=iff.0h2v.s4.858a1ba30161 from=translated src=- shape=3210e062 vocab=0cdaa202
-/
theorem functionConvergesAtTopTo_iff_tendsto {f : ℝ → ℝ} {L : ℝ} :
    FunctionConvergesAtTopTo f L ↔ Tendsto f atTop (𝓝 L) := by
  simpa [FunctionConvergesAtTopTo] using
    (tendsto_atTop_iff_eps_N (f := f) (L := L)).symm

/-- 教材接口下，正无穷远有限极限唯一。
@isnad1 id=eq.2h3v.s4.0d27edb8f5e4 from=translated src=- shape=a11c7c58 vocab=1e96d791
-/
theorem functionConvergesAtTopTo_unique {f : ℝ → ℝ} {L M : ℝ}
    (hL : FunctionConvergesAtTopTo f L) (hM : FunctionConvergesAtTopTo f M) : L = M := by
  exact tendsto_nhds_unique (functionConvergesAtTopTo_iff_tendsto.mp hL)
    (functionConvergesAtTopTo_iff_tendsto.mp hM)

/-- 函数在 a 处发散到正无穷：f (x) → ∞ 当 x → a：对任意 M 最终有 M ≤ f x。 
> **Entry**: analysis.func-limit.at-top
@isnad1 id=iff.0h2v.s6.edd9e86b5aba from=translated src=- shape=f6db31e0 vocab=a4e5ef7d
-/
lemma tendsto_nhds_atTop_iff {f : ℝ → ℝ} {a : ℝ} :
    Tendsto f (𝓝[≠] a) atTop ↔
      ∀ M : ℝ, ∃ δ > 0, ∀ x, |x - a| < δ → x ≠ a → M ≤ f x := by
  constructor
  · intro h
    intro M
    rcases (eventually_nhds_within_iff_delta a (fun x => M ≤ f x)).mp (tendsto_atTop.mp h M) with ⟨δ, hδpos, hδ⟩
    exact ⟨δ, hδpos, hδ⟩
  · intro h
    exact tendsto_atTop.mpr (fun (M : ℝ) => (eventually_nhds_within_iff_delta a (fun x => M ≤ f x)).mpr (h M))

/-- 教材 M-δ 定义与 Mathlib 的函数值趋于 `+∞` 接口等价。
@isnad1 id=iff.0h2v.s5.b97afa36f51b from=translated src=- shape=028f1647 vocab=e01103b3
-/
theorem functionDivergesToAtTopAt_iff_tendsto {f : ℝ → ℝ} {a : ℝ} :
    FunctionDivergesToAtTopAt f a ↔ Tendsto f (𝓝[≠] a) atTop := by
  simpa [FunctionDivergesToAtTopAt] using (tendsto_nhds_atTop_iff (f := f) (a := a)).symm

/-- 教材发散定义直接给出每个下界最终成立。
@isnad1 id=eventual.1h3v.s5.66cf7839ee88 from=translated src=- shape=6817149a vocab=e6bde400
-/
theorem functionDivergesToAtTopAt_eventually_ge {f : ℝ → ℝ} {a : ℝ}
    (h : FunctionDivergesToAtTopAt f a) (M : ℝ) : ∀ᶠ x in 𝓝[≠] a, M ≤ f x := by
  exact tendsto_atTop.mp (functionDivergesToAtTopAt_iff_tendsto.mp h) M

/-- 教材 ε-M 定义与 Mathlib 的负无穷远有限极限等价。
@isnad1 id=iff.0h2v.s4.19b950cc7a50 from=translated src=- shape=3210e062 vocab=20a54db0
-/
theorem functionConvergesAtBotTo_iff_tendsto {f : ℝ → ℝ} {L : ℝ} :
    FunctionConvergesAtBotTo f L ↔ Tendsto f atBot (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨M, hM⟩
    rw [eventually_atBot]
    exact ⟨M, fun x hx => by simpa [Real.dist_eq] using hM x hx⟩
  · intro h ε hε
    have hev := h ε hε
    rw [eventually_atBot] at hev
    rcases hev with ⟨M, hM⟩
    exact ⟨M, fun x hx => by simpa [Real.dist_eq] using hM x hx⟩

/-- 教材接口下，负无穷远有限极限唯一。
@isnad1 id=eq.2h3v.s4.156469953f0d from=translated src=- shape=a11c7c58 vocab=6be69ead
-/
theorem functionConvergesAtBotTo_unique {f : ℝ → ℝ} {L M : ℝ}
    (hL : FunctionConvergesAtBotTo f L) (hM : FunctionConvergesAtBotTo f M) : L = M := by
  exact tendsto_nhds_unique (functionConvergesAtBotTo_iff_tendsto.mp hL)
    (functionConvergesAtBotTo_iff_tendsto.mp hM)

/-- 教材 M-δ 定义与 Mathlib 的函数值趋于 `-∞` 接口等价。
@isnad1 id=iff.0h2v.s5.7fc5d5f859c8 from=translated src=- shape=028f1647 vocab=6606c64f
-/
theorem functionDivergesToAtBotAt_iff_tendsto {f : ℝ → ℝ} {a : ℝ} :
    FunctionDivergesToAtBotAt f a ↔ Tendsto f (𝓝[≠] a) atBot := by
  constructor
  · intro h
    exact tendsto_atBot.mpr fun M =>
      (eventually_nhds_within_iff_delta a (fun x => f x ≤ M)).mpr (h M)
  · intro h M
    exact (eventually_nhds_within_iff_delta a (fun x => f x ≤ M)).mp
      (tendsto_atBot.mp h M)

/-- 教材负无穷发散定义给出每个上界最终成立。
@isnad1 id=eventual.1h3v.s5.150792f98b5b from=translated src=- shape=4928d316 vocab=02f8c207
-/
theorem functionDivergesToAtBotAt_eventually_le {f : ℝ → ℝ} {a : ℝ}
    (h : FunctionDivergesToAtBotAt f a) (M : ℝ) : ∀ᶠ x in 𝓝[≠] a, f x ≤ M := by
  exact tendsto_atBot.mp (functionDivergesToAtBotAt_iff_tendsto.mp h) M

/-- 单调递增到无穷的定义：r > 1 时 rⁿ → ∞。 
> **Entry**: analysis.func-limit.at-top
@isnad1 id=tendsto.1h1v.s5.625c4a517602 from=translated src=- shape=f371c4e1 vocab=ba3e5b6d
-/
lemma tendsto_pow_atTop_atTop {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt hr

/-- **复合函数极限**：若 f(x) → L（x → a 去心）且 g 在 L 连续，
  则 g(f(x)) → g(L)。即极限与连续函数可换序。 
> **Entry**: analysis.func-limit.comp
@isnad1 id=tendsto.2h4v.s6.4205e91dc5ca from=translated src=- shape=6334604c vocab=ae020505
-/
theorem func_lim_comp {f : ℝ → ℝ} {g : ℝ → ℝ} {a L : ℝ}
    (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) (hg : ContinuousAt g L) :
    Tendsto (fun x => g (f x)) (𝓝[≠] a) (𝓝 (g L)) :=
  hg.tendsto.comp hf

end Analysis.FuncLimit

end SandronesLibrary
