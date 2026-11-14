/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.BanachAlgebraFoundation
import Tengoku.Seed.Analysis.Normed.Algebra.Spectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 谱与预解集的定义层

本文件直接解释 Mathlib 的 `spectrum`、`resolventSet`、`resolvent` 与 `spectralRadius`，并给出
教材所用的可逆性和双边逆桥。它不重定义谱，也不提前证明复 Banach 代数的谱非空紧致。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Set
open scoped ENNReal NNReal

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [CompleteSpace A] [NormOneClass A]

omit [CompleteSpace A] [NormOneClass A] in
/-- 谱是预解集在标量域中的补集。

> **Entry**: functional-analysis.spectrum.definition-/
theorem spectrum_eq_compl_resolventSet (a : A) :
    spectrum ℂ a = (resolventSet ℂ a)ᶜ :=
  rfl

omit [CompleteSpace A] [NormOneClass A] in
/-- `z` 属于预解集，当且仅当 `z·1-a` 在 Banach 代数中可逆。-/
theorem mem_resolventSet_iff_isUnit (a : A) (z : ℂ) :
    z ∈ resolventSet ℂ a ↔ IsUnit (algebraMap ℂ A z - a) :=
  spectrum.mem_resolventSet_iff

omit [CompleteSpace A] [NormOneClass A] in
/-- `z` 属于谱，当且仅当 `z·1-a` 不可逆。-/
theorem mem_spectrum_iff_not_isUnit (a : A) (z : ℂ) :
    z ∈ spectrum ℂ a ↔ ¬ IsUnit (algebraMap ℂ A z - a) :=
  spectrum.mem_iff

omit [CompleteSpace A] [NormOneClass A] in
/-- Mathlib 的预解映射在预解集外约定为零，并由 `Ring.inverse` 统一承载。-/
theorem resolvent_eq_ringInverse (a : A) (z : ℂ) :
    resolvent a z = Ring.inverse (algebraMap ℂ A z - a) :=
  rfl

omit [CompleteSpace A] [NormOneClass A] in
/-- 在预解集上，预解元是 `z·1-a` 的右逆。-/
theorem spectralParameter_sub_mul_resolvent (a : A) (z : ℂ)
    (hz : z ∈ resolventSet ℂ a) :
    (algebraMap ℂ A z - a) * resolvent a z = 1 := by
  rw [spectrum.resolvent_eq hz]
  exact hz.unit.val_inv

omit [CompleteSpace A] [NormOneClass A] in
/-- 在预解集上，预解元也是 `z·1-a` 的左逆。-/
theorem resolvent_mul_spectralParameter_sub (a : A) (z : ℂ)
    (hz : z ∈ resolventSet ℂ a) :
    resolvent a z * (algebraMap ℂ A z - a) = 1 := by
  rw [spectrum.resolvent_eq hz]
  exact hz.unit.inv_val

omit [CompleteSpace A] [NormOneClass A] in
/-- 谱半径是谱中标量范数的 `ℝ≥0∞` 上确界；空谱时该上确界为零。-/
theorem spectralRadius_eq_iSup_norm (a : A) :
    spectralRadius ℂ a =
      ⨆ z ∈ spectrum ℂ a, (‖z‖₊ : ℝ≥0∞) :=
  rfl

section OperatorSpectrum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

omit [CompleteSpace E] [Nontrivial E] in
/-- 有界算子谱的可逆性解释使用连续线性自同态代数本身，不建立平行算子谱。-/
theorem operator_mem_resolventSet_iff_isUnit (T : E →L[ℂ] E) (z : ℂ) :
    z ∈ resolventSet ℂ T ↔
      IsUnit (algebraMap ℂ (E →L[ℂ] E) z - T) :=
  spectrum.mem_resolventSet_iff

omit [CompleteSpace E] [Nontrivial E] in
/-- 有界算子谱的互补定义。-/
theorem operator_mem_spectrum_iff_not_isUnit (T : E →L[ℂ] E) (z : ℂ) :
    z ∈ spectrum ℂ T ↔
      ¬ IsUnit (algebraMap ℂ (E →L[ℂ] E) z - T) :=
  spectrum.mem_iff

end OperatorSpectrum

end SandronesLibrary.FunctionalAnalysis
