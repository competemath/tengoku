/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.CLTCenteredStandardized
import Tengoku.Seed.Probability.ProductMeasure
import Tengoku.Seed.Probability.Independence.InfinitePi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 中心极限定理（Pr3.5）具体正例

本文件为 `probability.clt.central-limit-theorem`（Wave R1 集成的一般 iid 中心极限定理）
建立具体概率空间：标准正态坐标的无限乘积空间。坐标随机变量独立同分布、均值为 `0`、
方差为 `1`，可直接代入一般 CLT，得到标准化和弱收敛到标准正态；再经 Lévy 连续性接口读回
特征函数层的逐点极限 `exp (-t²/2)`。

> **Entry**: examples.probability.clt
-/

noncomputable section

namespace SandronesLibrary.Examples.CentralLimit

open MeasureTheory ProbabilityTheory Filter
open SandronesLibrary.Probability
open scoped Topology

/-- **坐标概率空间**：`ℕ → ℝ` 上各坐标独立同标准正态的无限乘积测度。
用 `abbrev` 以便类型类实例（概率测度）在归约时可见。-/
abbrev gaussianSpace : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1

/-- **坐标随机变量** `X k (ω) = ω k`。-/
abbrev coordinate (k : ℕ) : (ℕ → ℝ) → ℝ := fun ω => ω k

/-- 坐标随机变量可测。-/
theorem coordinate_measurable (k : ℕ) : Measurable (coordinate k) :=
  measurable_pi_apply k

/-- 坐标随机变量几乎处处可测（可测性的推论，供概率接口使用）。-/
theorem coordinate_aemeasurable (k : ℕ) : AEMeasurable (coordinate k) gaussianSpace :=
  (coordinate_measurable k).aemeasurable

/-- **每个坐标的分布都是标准正态**：`(gaussianSpace).map (coordinate k) = gaussianReal 0 1`。-/
theorem coordinate_law (k : ℕ) :
    gaussianSpace.map (coordinate k) = gaussianReal 0 1 := by
  simpa [gaussianSpace, coordinate] using
    Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) k

/-- **独立性**：坐标随机变量族 `iIndepFun`。这是乘积测度的定义性性质。-/
theorem coordinate_iIndepFun : iIndepFun coordinate gaussianSpace := by
  simpa [gaussianSpace, coordinate] using
    (iIndepFun_infinitePi (Ω := fun _ : ℕ => ℝ) (𝓧 := fun _ : ℕ => ℝ)
      (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ => id)
      (fun _ => measurable_id))

/-- **同分布**：任意两个坐标同分布（由 `coordinate_law` 都等于标准正态）。-/
theorem coordinate_identDistrib (i : ℕ) :
    IdentDistrib (coordinate i) (coordinate 0) gaussianSpace gaussianSpace where
  aemeasurable_fst := coordinate_aemeasurable i
  aemeasurable_snd := coordinate_aemeasurable 0
  map_eq := by rw [coordinate_law i, coordinate_law 0]

/-- **二阶矩有限**：`coordinate 0 ∈ L²(gaussianSpace)`。-/
theorem coordinate_memLp_two : MemLp (coordinate 0) 2 gaussianSpace := by
  have h := (memLp_map_measure_iff (μ := gaussianSpace) (f := coordinate 0) (g := id)
    (p := 2) aestronglyMeasurable_id (coordinate_aemeasurable 0)).1 ?_
  · simpa [Function.comp_def] using h
  · rw [coordinate_law 0]
    exact memLp_id_gaussianReal 2

/-- **均值计算**：`𝔼[coordinate 0] = 0`。-/
theorem coordinate_integral : gaussianSpace[coordinate 0] = 0 := by
  have h : gaussianSpace[coordinate 0] =
      ∫ x : ℝ, x ∂(gaussianSpace.map (coordinate 0)) :=
    (integral_map (coordinate_aemeasurable 0) aestronglyMeasurable_id).symm
  rw [h, coordinate_law 0]
  exact integral_id_gaussianReal

/-- **方差计算**：`Var[coordinate 0] = 1`。-/
theorem coordinate_variance : variance (coordinate 0) gaussianSpace = 1 := by
  have h : variance (coordinate 0) gaussianSpace =
      Var[id; gaussianSpace.map (coordinate 0)] :=
    (variance_map (X := id) (Y := coordinate 0) measurable_id.aemeasurable
      (coordinate_aemeasurable 0)).symm
  rw [h, coordinate_law 0]
  exact variance_id_gaussianReal

/-- **一般 CLT 在具体正态坐标空间上的实例化**：中心化按 `σ√n`（此处 `μ=0`、`σ=1`）缩放的
前 `n` 项和之分布弱收敛到标准正态。这是 `probability.clt.central-limit-theorem` 的一个
可直接核对的真实使用者。-/
theorem clt_gaussianCoordinates :
    Tendsto
      (fun n : ℕ => centeredScaledSumLaw coordinate
        (fun i => (coordinate_identDistrib i).aemeasurable_fst) 0 1 n)
      atTop (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  iid_centeredScaled_clt coordinate_iIndepFun coordinate_identDistrib coordinate_memLp_two
    coordinate_integral (by simpa using coordinate_variance) (by norm_num)

/-- **接上 Lévy 连续性接口**：标准化和的特征函数逐点收敛到标准正态特征函数
`exp (-t²/2)`。-/
theorem clt_gaussianCoordinates_charFun (t : ℝ) :
    Tendsto
      (fun n : ℕ => charFun (centeredScaledSumLaw coordinate
        (fun i => (coordinate_identDistrib i).aemeasurable_fst) 0 1 n) t)
      atTop (𝓝 (Complex.exp (-(t ^ 2) / 2))) := by
  have h := (probabilityMeasure_tendsto_iff_charFun.mp clt_gaussianCoordinates) t
  simpa [charFun_gaussianReal, neg_div] using h

end SandronesLibrary.Examples.CentralLimit
