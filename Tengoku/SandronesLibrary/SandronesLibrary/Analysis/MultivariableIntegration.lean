/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.ConstantRank
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.ProductMeasure
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 多重积分：矩形区域上的教材接口

本模块把抽象乘积测度上的 Fubini 定理转成矩形区域二重积分接口，并作为后续多元
Riemann 积分数值桥、换元公式和向量积分的 Lebesgue/Bochner 地基。

-/

noncomputable section

namespace SandronesLibrary.Analysis.Multivariable

open Set MeasureTheory
open scoped Interval

/-- 闭矩形 `[a,b] × [c,d]`。

> **Entry**: analysis.multivariable.rectangle-integral-/
def closedRectangle (a b c d : ℝ) : Set (ℝ × ℝ) := Icc a b ×ˢ Icc c d

/-- 闭矩形上的二重积分，底层采用两个 Lebesgue 测度的乘积测度。-/
def rectangleIntegral (f : ℝ × ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  ∫ z in closedRectangle a b c d, f z ∂(volume.prod volume)

/-- 连续函数在闭矩形上可积。
@isnad1 id=integrab.1h5v.s6.5ee55b487afd from=translated src=- shape=bc06a284 vocab=217c13ef
-/
theorem continuousOn_integrableOn_closedRectangle {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hf : ContinuousOn f (closedRectangle a b c d)) :
    IntegrableOn f (closedRectangle a b c d) (volume.prod volume) := by
  exact hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- Fubini 的矩形区域教材形式：二重积分等于先对 `y`、再对 `x` 的迭代积分。
@isnad1 id=eq.1h5v.s7.71f14e3ad30b from=translated src=- shape=4e3ba585 vocab=6cd941e2
-/
theorem rectangleIntegral_eq_iterated {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hf : IntegrableOn f (closedRectangle a b c d) (volume.prod volume)) :
    rectangleIntegral f a b c d =
      ∫ x in Icc a b, ∫ y in Icc c d, f (x, y) := by
  exact MeasureTheory.setIntegral_prod f hf

/-- 闭矩形上可积时，两种有向区间迭代积分相等。
@isnad1 id=eq.1h5v.s7.c397b85e3c91 from=translated src=- shape=4b8f541b vocab=0c9a9ebd
-/
theorem intervalIntegral_rectangle_swap {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hf : IntegrableOn f.uncurry (uIoc a b ×ˢ uIoc c d)) :
    (∫ x in a..b, ∫ y in c..d, f x y) =
      ∫ y in c..d, ∫ x in a..b, f x y := by
  exact MeasureTheory.intervalIntegral_intervalIntegral_swap hf

/-- 常函数 `1` 在正向闭矩形上的积分就是面积 `(b-a)(d-c)`。
@isnad1 id=eq.2h4v.s5.3189744a68db from=translated src=- shape=0762d9e8 vocab=4b9e2f88
-/
theorem rectangleIntegral_one {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    rectangleIntegral (fun _ ↦ 1) a b c d = (b - a) * (d - c) := by
  rw [rectangleIntegral, setIntegral_one_eq_measureReal]
  change (volume.prod volume).real (Icc a b ×ˢ Icc c d) = _
  rw [measureReal_def, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_mul]
  simp [hab, hcd]

end SandronesLibrary.Analysis.Multivariable
