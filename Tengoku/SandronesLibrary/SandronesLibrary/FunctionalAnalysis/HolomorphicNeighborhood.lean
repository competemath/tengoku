/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.SpectrumNonemptyCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 谱邻域上的全纯函数

本文件只冻结全纯函数演算的输入条件：一个复函数必须在 Banach 代数元素之谱的某个开邻域上全纯。
这里不定义函数在代数元素上的取值，也不引入 Dunford 积分或函数 germ。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Set

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- `f` 在复 Banach 代数元素 `a` 的谱的某个开邻域上全纯。

该定义保留教材中的存在量词：调用者不必指定一个全局固定的邻域。显式的
`[CompleteSpace A]` 参数把 carrier 冻结为 Main 指定的复 Banach 代数。

> **Entry**: functional-analysis.functional-calculus.holomorphic-neighborhood-/
def HolomorphicOnNhdSpectrum (a : A) (f : ℂ → ℂ) [CompleteSpace A] : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ spectrum ℂ a ⊆ U ∧ DifferentiableOn ℂ f U

variable [CompleteSpace A]

/-- 一个显式的开谱邻域及其上的全纯性给出 `HolomorphicOnNhdSpectrum`。
@isnad1 id=holomorp.3h4v.s7.38066c68b336 from=translated src=- shape=7eeb6af3 vocab=1a824398
-/
theorem holomorphicOnNhdSpectrum_of_open {a : A} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (haU : spectrum ℂ a ⊆ U) (hf : DifferentiableOn ℂ f U) :
    HolomorphicOnNhdSpectrum a f :=
  ⟨U, hU, haU, hf⟩

/-- 可以把全纯性的已知定义域缩小到仍含谱的开子集。
@isnad1 id=holomorp.4h5v.s7.2ce0a89e4dc8 from=translated src=- shape=18846c90 vocab=1a824398
-/
theorem holomorphicOnNhdSpectrum_of_subset {a : A} {f : ℂ → ℂ} {U V : Set ℂ}
    (hV : IsOpen V) (haV : spectrum ℂ a ⊆ V) (hVU : V ⊆ U)
    (hf : DifferentiableOn ℂ f U) : HolomorphicOnNhdSpectrum a f :=
  holomorphicOnNhdSpectrum_of_open hV haV (hf.mono hVU)

/-- 两个谱邻域全纯函数可以在两个见证邻域的交集上共同处理。
@isnad1 id=ex.2h4v.s7.4dc3004f0e3e from=translated src=- shape=d45fbbe4 vocab=1a824398
-/
theorem HolomorphicOnNhdSpectrum.exists_inter {a : A} {f g : ℂ → ℂ}
    (hf : HolomorphicOnNhdSpectrum a f) (hg : HolomorphicOnNhdSpectrum a g) :
    ∃ U : Set ℂ, IsOpen U ∧ spectrum ℂ a ⊆ U ∧
      DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g U := by
  obtain ⟨U, hUo, haU, hfU⟩ := hf
  obtain ⟨V, hVo, haV, hgV⟩ := hg
  exact ⟨U ∩ V, hUo.inter hVo, subset_inter haU haV,
    hfU.mono inter_subset_left, hgV.mono inter_subset_right⟩

/-- 常函数在每个元素的谱邻域上全纯。
@isnad1 id=holomorp.0h3v.s5.c712ab8d642e from=translated src=- shape=efc9a0dd vocab=f53759a2
-/
theorem HolomorphicOnNhdSpectrum.const (a : A) (c : ℂ) :
    HolomorphicOnNhdSpectrum a (fun _ => c) :=
  ⟨univ, isOpen_univ, subset_univ _, differentiableOn_const c⟩

/-- 恒等函数在每个元素的谱邻域上全纯。
@isnad1 id=holomorp.0h2v.s5.d15f1e5f23c5 from=translated src=- shape=a43f9e70 vocab=ec6bc7a2
-/
theorem HolomorphicOnNhdSpectrum.id (a : A) :
    HolomorphicOnNhdSpectrum a id :=
  ⟨univ, isOpen_univ, subset_univ _, differentiable_id.differentiableOn⟩

/-- 谱邻域全纯函数对逐点加法封闭；共同定义域由交集见证。
@isnad1 id=holomorp.2h4v.s6.a9ea9b6cb48d from=translated src=- shape=71cb243f vocab=72101fcc
-/
theorem HolomorphicOnNhdSpectrum.add {a : A} {f g : ℂ → ℂ}
    (hf : HolomorphicOnNhdSpectrum a f) (hg : HolomorphicOnNhdSpectrum a g) :
    HolomorphicOnNhdSpectrum a (f + g) := by
  obtain ⟨U, hU, haU, hfU, hgU⟩ := hf.exists_inter hg
  exact ⟨U, hU, haU, hfU.add hgU⟩

/-- 谱邻域全纯函数对逐点乘法封闭；共同定义域由交集见证。
@isnad1 id=holomorp.2h4v.s6.30b40ac3b151 from=translated src=- shape=71cb243f vocab=65642139
-/
theorem HolomorphicOnNhdSpectrum.mul {a : A} {f g : ℂ → ℂ}
    (hf : HolomorphicOnNhdSpectrum a f) (hg : HolomorphicOnNhdSpectrum a g) :
    HolomorphicOnNhdSpectrum a (f * g) := by
  obtain ⟨U, hU, haU, hfU, hgU⟩ := hf.exists_inter hg
  exact ⟨U, hU, haU, hfU.mul hgU⟩

/-- 复多项式函数在每个元素的谱邻域上全纯。
@isnad1 id=holomorp.0h3v.s5.a5e32a1a472f from=translated src=- shape=19613815 vocab=4ae6d4b1
-/
theorem HolomorphicOnNhdSpectrum.polynomial (a : A) (p : Polynomial ℂ) :
    HolomorphicOnNhdSpectrum a (fun z => p.eval z) :=
  ⟨univ, isOpen_univ, subset_univ _, p.differentiable.differentiableOn⟩

end SandronesLibrary.FunctionalAnalysis
