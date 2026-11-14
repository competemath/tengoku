/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Statistics.Density
import Tengoku.Seed.Order.Filter.Extr

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 似然函数与最大似然估计

统计模型 `P : Kernel Θ 𝓧` 被参考测度 `ν` 支配时，`statistics.model.density` 已把联合可测的
Radon--Nikodym 密度固定为 `P.rnDeriv (Kernel.const Θ ν) θ x`。把它看作固定观测 `x` 下参数
`θ` 的函数，就是课程中的**似然函数**；`likelihood P ν θ x` 只是给这个已经存在的一手对象起的
正式名字，不新建第二个密度载体。

**最大似然估计**在观测 `x` 处取似然函数的最大值点。逐点最大化并不稳健：密度只在 `ν`-几乎处处
唯一，零测集上改版本不改变概率却会改变逐点 argmax。因此本条目把最大似然估计定义成

`IsMaximumLikelihoodEstimator P ν θhat`：`θhat` 可测，并且对 `ν`-几乎处处的 `x`，`θhat x` 在
整个参数空间上最大化似然。极大值性质复用 Mathlib 的 `IsMaxOn f Set.univ`，不另建 argmax 结构；
"几乎处处"是定义的组成部分，而不是事后补的正则性假设。

本文件证明：似然联合可测且总积分为一（似然确实是密度的函数层视角）、最大似然估计给出合法的
确定性估计量、任一严格单调变换不改变最大化点（对数似然等价性是其原型）、参数双射下最大化点按逆像对应、
两个最大似然估计的似然值几乎处处相等；并在有限参数、可数样本空间上给出一个显式存在且可测的
最大似然估计。

本条目严格止于定义、一般订单性质与有限存在性。它不证明似然**函数**在观测外的可测最大化选择
定理（一般可测选择）、不证明最大似然估计的相合性、渐近正态性或 Fisher 信息不等式，也不宣称
任意模型的最大似然估计存在或唯一。有限存在性结论额外需要可数样本空间，正是"任意样本空间上
可测 argmax"这一未解决问题的诚实边界。

> **Entry**: statistics.maximum-likelihood
-/

namespace SandronesLibrary.Statistics

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- 严格单调变换不改变最大值点。`Real.log` 在 `Set.Ioi 0` 上严格单调，正是这条引理的教材原型
（"最大化似然等价于最大化对数似然"）；这里把订单层事实抽成对任意严格单调 `φ` 的一般引理，
不为对数单独复制一份 argmax 论证。
@isnad1 id=iff.1h6v.s6.862910554309 from=translated src=- shape=6fecfbf3 vocab=88c1c414
-/
theorem isMaxOn_univ_comp_strictMono_iff {α β γ : Type*} [LinearOrder β] [Preorder γ]
    (φ : β → γ) (hφ : StrictMono φ) (f : α → β) (a : α) :
    IsMaxOn (fun x => φ (f x)) Set.univ a ↔ IsMaxOn f Set.univ a := by
  rw [isMaxOn_univ_iff, isMaxOn_univ_iff]
  exact ⟨fun h x => (hφ.le_iff_le).mp (h x), fun h x => (hφ.le_iff_le).mpr (h x)⟩

/-- 参数双射下最大值点按逆像对应：`θhat'` 最大化 `θ' ↦ p (e θ')` 当且仅当 `e θhat'` 最大化
`p`。这是最大似然估计在换参数下保持不变的订单层核心。
@isnad1 id=iff.0h6v.s6.852074eb778e from=translated src=- shape=f4093e9d vocab=06afe7f9
-/
theorem isMaxOn_univ_comp_equiv_iff {Θ Θ' 𝓧 : Type*} [Preorder 𝓧]
    (e : Θ' ≃ Θ) (p : Θ → 𝓧) (θ' : Θ') :
    IsMaxOn (fun θ' => p (e θ')) Set.univ θ' ↔
      IsMaxOn p Set.univ (e θ') := by
  rw [isMaxOn_univ_iff, isMaxOn_univ_iff]
  constructor
  · intro h θ
    obtain ⟨θ'', rfl⟩ := e.surjective θ
    exact h θ''
  · intro h θ''
    exact h (e θ'')

section Definition

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
  [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]

/-- 观测 `x` 下参数 `θ` 处的似然值：支配模型的联合可测 Radon--Nikodym 密度。

这是给 `statistics.model.density` 已固定的密度一个函数层名字，使"似然函数"
`θ ↦ likelihood P ν θ x`、它的联合可测性以及后续最大化都能落在同一个对象上。`CountableOrCountablyGenerated`
边界与密度条目完全一致，不额外放松。-/
noncomputable def likelihood (P : Kernel Θ 𝓧) (ν : Measure 𝓧) (θ : Θ) (x : 𝓧) : ℝ≥0∞ :=
  P.rnDeriv (Kernel.const Θ ν) θ x

/-- 最大似然估计：可测映射 `θhat : 𝓧 → Θ`，且对 `ν`-几乎处处的观测 `x`，`θhat x` 在整个
参数空间上最大化似然。

"几乎处处"与"可测"都在定义内：前者排除零测集上密度版本差异造成的伪 argmax，后者保证它确实
是一个（确定性）估计量。极大值性质直接用 `IsMaxOn (fun θ ↦ likelihood P ν θ x) Set.univ`。

**支配性边界。** 本谓词刻意**不**把模型支配 `∀ θ, P θ ≪ ν` 作为字段：估计量的身份不应依赖模型的
正则性。但在非支配模型上 `likelihood` 只表示 `P θ` 绝对连续部分的密度，逐点 argmax 会退化
（最极端地，`ν = 0` 时对任意可测 `θhat` 都恒真），此时它**不承载统计意义**。支配性在所有语义
定理（`likelihood_lintegral_eq_one`、`withDensity_likelihood_eq`）中显式假设，因此使用本谓词作
统计结论时必须同时给出支配假设。-/
def IsMaximumLikelihoodEstimator (P : Kernel Θ 𝓧) (ν : Measure 𝓧)
    (θhat : 𝓧 → Θ) : Prop :=
  Measurable θhat ∧ ∀ᵐ x ∂ν, IsMaxOn (fun θ => likelihood P ν θ x) Set.univ (θhat x)

/-- 似然作为 `(θ,x)` 的函数联合可测。
@isnad1 id=measurab.0h4v.s5.3e3e457b78d1 from=translated src=- shape=5ee6fdea vocab=3c3ea812
-/
theorem likelihood_jointlyMeasurable (P : Kernel Θ 𝓧) (ν : Measure 𝓧) :
    Measurable (fun p : Θ × 𝓧 => likelihood P ν p.1 p.2) := by
  simpa [likelihood] using Kernel.measurable_rnDeriv P (Kernel.const Θ ν)

/-- 支配概率模型的似然关于参考测度的总积分为一。这条结论把 `likelihood` 与
`statistics.model.density` 的归一化事实锁在一起，说明它不是自由的任意函数。
@isnad1 id=eq.1h5v.s6.4997345bf7c0 from=translated src=- shape=d64d1484 vocab=bf5b5bdd
-/
theorem likelihood_lintegral_eq_one
    (P : Kernel Θ 𝓧) [IsMarkovKernel P] (ν : Measure 𝓧) [IsFiniteMeasure ν]
    (θ : Θ) (hPν : P θ ≪ ν) :
    ∫⁻ x, likelihood P ν θ x ∂ν = 1 := by
  simpa [likelihood] using statisticalModel_lintegral_density_eq_one P ν θ hPν

/-- 最大似然估计的定义展开：`θhat` 可测，且几乎处处 `∀ θ, likelihood θ ≤ likelihood (θhat x)`。
@isnad1 id=iff.0h5v.s6.2cafeb456086 from=translated src=- shape=5f3d094a vocab=f0a459f8
-/
theorem isMaximumLikelihoodEstimator_iff
    (P : Kernel Θ 𝓧) (ν : Measure 𝓧) (θhat : 𝓧 → Θ) :
    IsMaximumLikelihoodEstimator P ν θhat ↔
      Measurable θhat ∧ ∀ᵐ x ∂ν, ∀ θ,
        likelihood P ν θ x ≤ likelihood P ν (θhat x) x := by
  simp [IsMaximumLikelihoodEstimator, isMaxOn_univ_iff]

/-- 最大似然估计经 Dirac kernel 给出合法的确定性估计量，从而接入
`statistics.estimator.definition` 的随机化估计量接口。

本引理只使用定义中的可测性分量 `h.1`，argmax 分量不参与证明；它唯一的职责是把 MLE 送进
`Kernel`/`IsMarkovKernel` 接口，而不是产生新的数学内容。
@isnad1 id=ismarkov.1h5v.s5.e588d35bfb7d from=translated src=- shape=68deba20 vocab=f11f24fe
-/
theorem maximumLikelihoodEstimator_isMarkov
    (P : Kernel Θ 𝓧) (ν : Measure 𝓧) (θhat : 𝓧 → Θ)
    (h : IsMaximumLikelihoodEstimator P ν θhat) :
    IsMarkovKernel (Kernel.deterministic θhat h.1) :=
  inferInstance

/-- 两个最大似然估计的似然值几乎处处相等。

存在多个 argmax 时，逐点取值可能不同，但它们给出的最大似然值在 `ν` 下一致；这正是"最大似然
估计在似然值层面几乎处处唯一"的正式陈述。
@isnad1 id=eventual.2h6v.s6.96c1fd1b61d5 from=translated src=- shape=77046758 vocab=6235ff6d
-/
theorem maximumLikelihoodEstimator_likelihood_eq_ae
    (P : Kernel Θ 𝓧) (ν : Measure 𝓧) {θhat θhat' : 𝓧 → Θ}
    (h : IsMaximumLikelihoodEstimator P ν θhat)
    (h' : IsMaximumLikelihoodEstimator P ν θhat') :
    (fun x => likelihood P ν (θhat x) x) =ᵐ[ν]
      fun x => likelihood P ν (θhat' x) x := by
  filter_upwards [h.2, h'.2] with x hx hx'
  exact le_antisymm ((isMaxOn_univ_iff.mp hx') (θhat x))
    ((isMaxOn_univ_iff.mp hx) (θhat' x))

/-- 支配模型的似然加权参考测度恰好重建每个参数纤维。这是似然相对密度的消费者：它证明
`likelihood` 确实承载 `statistics.model.density` 的概率重建语义。
@isnad1 id=eq.1h5v.s6.dc4098aa7543 from=translated src=- shape=4c9b00ea vocab=92373c53
-/
theorem withDensity_likelihood_eq
    (P : Kernel Θ 𝓧) [IsMarkovKernel P] (ν : Measure 𝓧) [IsFiniteMeasure ν]
    (hPν : ∀ θ, P θ ≪ ν) (θ : Θ) :
    ν.withDensity (likelihood P ν θ) = P θ := by
  change ν.withDensity (fun x => P.rnDeriv (Kernel.const Θ ν) θ x) = P θ
  exact statisticalModel_withDensity_eq P ν θ (hPν θ)

/-- 似然不依赖参数时，任何可测映射都是最大似然估计。这是定义的退化解压：常数模型下不存在
唯一的最大似然估计，接口不会伪造唯一性。
@isnad1 id=ismaximu.2h5v.s6.3e97bd3f7485 from=translated src=- shape=0857a6c4 vocab=c709a5a1
-/
theorem isMaximumLikelihoodEstimator_of_const_likelihood
    (P : Kernel Θ 𝓧) (ν : Measure 𝓧) {θhat : 𝓧 → Θ}
    (hconst : ∀ θ θ' x, likelihood P ν θ x = likelihood P ν θ' x)
    (hθ : Measurable θhat) :
    IsMaximumLikelihoodEstimator P ν θhat := by
  refine ⟨hθ, ?_⟩
  filter_upwards with x
  rw [isMaxOn_univ_iff]
  intro θ
  rw [hconst]

end Definition

section Reparametrization

variable {Θ Θ' 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace Θ'] [MeasurableSpace 𝓧]
  [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]

/-- 参数双射换元保持最大似然估计：`θhat` 是 `P` 的最大似然估计，当且仅当它的逆像
`e.symm ∘ θhat` 可测且最大化换元后的似然 `θ' ↦ likelihood P ν (e θ')`。

右端用换元后的似然函数（而不是某个重参数化 kernel）表述，因为本库尚未冻结一般参数 comap 的
kernel 载体；把订单层结论与 kernel 层构造分开，避免在载体未定时伪造等价。
@isnad1 id=iff.0h7v.s7.194067f8d26a from=translated src=- shape=34700287 vocab=14838f7e
-/
theorem maximumLikelihoodEstimator_reparametrize
    (P : Kernel Θ 𝓧) (ν : Measure 𝓧) (e : Θ' ≃ᵐ Θ) (θhat : 𝓧 → Θ) :
    IsMaximumLikelihoodEstimator P ν θhat ↔
      Measurable (fun x => e.symm (θhat x)) ∧
        ∀ᵐ x ∂ν, IsMaxOn (fun θ' => likelihood P ν (e θ') x) Set.univ
          (e.symm (θhat x)) := by
  constructor
  · intro h
    refine ⟨e.symm.measurable.comp h.1, ?_⟩
    filter_upwards [h.2] with x hx
    have hiff := isMaxOn_univ_comp_equiv_iff (e : Θ' ≃ Θ)
      (fun θ => likelihood P ν θ x) (e.symm (θhat x))
    exact hiff.mpr (by simpa using hx)
  · rintro ⟨hmeas, hae⟩
    refine ⟨?_, ?_⟩
    · have h' : Measurable (fun x => e (e.symm (θhat x))) := e.measurable.comp hmeas
      simpa using h'
    · filter_upwards [hae] with x hx
      have hiff := isMaxOn_univ_comp_equiv_iff (e : Θ' ≃ Θ)
        (fun θ => likelihood P ν θ x) (e.symm (θhat x))
      simpa using hiff.mp hx

end Reparametrization

section Finite

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- 有限参数空间上，逐点最大值一定可取到。

这是"有限集合上数值函数有最大值"的 `ℝ≥0∞` 版本，不涉及可测选择；可测性在下一个定理中另行
处理。
@isnad1 id=ex.0h5v.s5.07d4e6c34645 from=translated src=- shape=d6408761 vocab=72693b9e
-/
theorem exists_maxOn_likelihood_of_finite [Finite Θ] [Nonempty Θ]
    [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]
    (P : Kernel Θ 𝓧) (ν : Measure 𝓧) (x : 𝓧) :
    ∃ θ, IsMaxOn (fun θ => likelihood P ν θ x) Set.univ θ := by
  obtain ⟨θ, -, hθ⟩ :=
    Set.exists_max_image (Set.univ : Set Θ) (fun θ => likelihood P ν θ x)
      Set.finite_univ Set.univ_nonempty
  exact ⟨θ, isMaxOn_univ_iff.mpr (fun θ' => hθ θ' (Set.mem_univ _))⟩

/-- 从有限参数的逐个 argmax 中作经典选择，得到显式的最大似然映射。-/
noncomputable def maximumLikelihoodMapOfFinite [Finite Θ] [Nonempty Θ]
    [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]
    (P : Kernel Θ 𝓧) (ν : Measure 𝓧) : 𝓧 → Θ :=
  fun x => Classical.choose (exists_maxOn_likelihood_of_finite P ν x)

/-- 有限参数、可数样本空间上，上述 argmax 映射是最大似然估计。

可数样本空间是"任意样本空间上可测 argmax"这一未解问题的真实代价：当 `𝓧` 可数且单点可测时，
任何从 `𝓧` 出发的映射都可测，于是经典选择给出的 argmax 映射自动合法。
@isnad1 id=ismaximu.0h4v.s5.a152aabf5783 from=translated src=- shape=0b3fb306 vocab=b0de5ac8
-/
theorem maximumLikelihoodEstimator_of_finite [Finite Θ] [Nonempty Θ]
    [Countable 𝓧] [MeasurableSingletonClass 𝓧]
    (P : Kernel Θ 𝓧) (ν : Measure 𝓧) :
    IsMaximumLikelihoodEstimator P ν (maximumLikelihoodMapOfFinite P ν) := by
  refine ⟨measurable_of_countable _, ?_⟩
  filter_upwards with x
  simpa [maximumLikelihoodMapOfFinite] using
    Classical.choose_spec (exists_maxOn_likelihood_of_finite P ν x)

end Finite

end SandronesLibrary.Statistics
