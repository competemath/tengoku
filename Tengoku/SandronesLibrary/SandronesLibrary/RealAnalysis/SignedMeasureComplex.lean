/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.SignedMeasureDefinition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / SignedMeasureComplex —— 复测度（Folland RA-F1）

本文件当前条目（引理清单）：

* **real-analysis.signed-measure.complex**（复测度作为 `ℂ`-值向量测度；实部／虚部为有符号
  测度，点式分解 `c i = re c i + i · im c i`；与有符号测度对的线性同构
  `ComplexMeasure.equivSignedMeasure`）✅。

> **语言说明**：教材（Folland §3.1）把复测度定义为取复值的 σ-可加集函数，且
> `|ν(E)| < ∞`。Mathlib 的 `MeasureTheory.ComplexMeasure α` 是
> `VectorMeasure α ℂ` 的缩写，即“值域为复数、在可测集上可数可加、非可测集取零”的集函数，
> 与教材语义一致，故本库直接复用该载体，并把“复测度 ↔ 一对有符号测度”作为核心定理。

### Mathlib 角色（本文件）

* `MeasureTheory.ComplexMeasure`（= `VectorMeasure α ℂ`）：**正式公开承载**。
* `ComplexMeasure.re` / `ComplexMeasure.im`：**语义一致的展开后端**（取实部／虚部的线性映射）。
* `SignedMeasure.toComplexMeasure`：由一对有符号测度造复测度（教材的 `ν_r + i ν_i`）。
* `ComplexMeasure.equivSignedMeasure`：复测度与有符号测度对的 **Mathlib 侧等价**，
  本库以具名推论 `complexMeasure_equiv_signedMeasure` 暴露。
-/

noncomputable section

namespace SandronesLibrary

namespace RealAnalysis.SignedMeasure

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. 复测度与其实部、虚部 -/

/-- **复测度的点式分解**。复测度 `c` 在任意集合 `i` 上的取值可分解为其实部与虚部
（均为有符号测度）的取值：`c i = re c i + (im c i) * I`。这就是 Folland 把复测度
写成 `ν = ν_r + i ν_i` 的 Lean 形式。
> **Entry**: real-analysis.signed-measure.complex
@isnad1 id=eq.0h3v.s9.388b4a5c4371 from=translated src=- shape=2e7bc288 vocab=660bc287
-/
theorem complexMeasure_re_add_im (c : ComplexMeasure α) (i : Set α) :
    c i = (ComplexMeasure.re c i : ℂ) + (ComplexMeasure.im c i : ℂ) * Complex.I := by
  rw [← Complex.re_add_im (c i), ComplexMeasure.re_apply, ComplexMeasure.im_apply]
  rfl

/-- **复测度实部的取值**。`(re c) i = (c i).re`：实部就是逐点取实部得到的有符号测度。
> **Entry**: real-analysis.signed-measure.complex
@isnad1 id=eq.0h3v.s8.70320ab675d8 from=translated src=- shape=840d15d8 vocab=62acc118
-/
theorem complexMeasure_re_apply (c : ComplexMeasure α) (i : Set α) :
    (ComplexMeasure.re c) i = (c i).re := by
  simp only [ComplexMeasure.re_apply]
  rfl

/-- **复测度虚部的取值**。`(im c) i = (c i).im`：虚部就是逐点取虚部得到的有符号测度。
> **Entry**: real-analysis.signed-measure.complex
@isnad1 id=eq.0h3v.s8.a500eb184fa6 from=translated src=- shape=840d15d8 vocab=0e0c0a59
-/
theorem complexMeasure_im_apply (c : ComplexMeasure α) (i : Set α) :
    (ComplexMeasure.im c) i = (c i).im := by
  simp only [ComplexMeasure.im_apply]
  rfl

/-- **由实部、虚部重建复测度**。任意复测度都等于其自身实部与虚部通过
`SignedMeasure.toComplexMeasure` 拼回的复测度：`(re c).toComplexMeasure (im c) = c`。
这是 `ν = ν_r + i ν_i` 的“还原”方向。
> **Entry**: real-analysis.signed-measure.complex
@isnad1 id=eq.0h2v.s8.ff7266b55b90 from=translated src=- shape=7a230344 vocab=d30a32d2
-/
theorem complexMeasure_toComplexMeasure_re_im (c : ComplexMeasure α) :
    SignedMeasure.toComplexMeasure (ComplexMeasure.re c) (ComplexMeasure.im c) = c :=
  c.toComplexMeasure_to_signedMeasure

/-- **拼回复测度的实部**。`re (s.toComplexMeasure t) = s`：先拼后取实部回到第一个有符号测度。
> **Entry**: real-analysis.signed-measure.complex
@isnad1 id=eq.0h3v.s8.b51be6af28ad from=translated src=- shape=ab7c8ba1 vocab=7dd17679
-/
theorem complexMeasure_re_toComplexMeasure (s t : SignedMeasure α) :
    ComplexMeasure.re (SignedMeasure.toComplexMeasure s t) = s :=
  s.re_toComplexMeasure t

/-- **拼回复测度的虚部**。`im (s.toComplexMeasure t) = t`：先拼后取虚部回到第二个有符号测度。
> **Entry**: real-analysis.signed-measure.complex
@isnad1 id=eq.0h3v.s8.f2b81f78f47f from=translated src=- shape=8b59062b vocab=5b3c8ede
-/
theorem complexMeasure_im_toComplexMeasure (s t : SignedMeasure α) :
    ComplexMeasure.im (SignedMeasure.toComplexMeasure s t) = t :=
  s.im_toComplexMeasure t

/-- **拼回复测度的取值公式**。`(s.toComplexMeasure t) i = s i + (t i) * I`，
即 `ν_r + i ν_i` 在集合上的取值。
> **Entry**: real-analysis.signed-measure.complex
@isnad1 id=eq.0h4v.s6.9cea9458a138 from=translated src=- shape=0135d130 vocab=0f78e080
-/
theorem complexMeasure_apply_toComplexMeasure (s t : SignedMeasure α) (i : Set α) :
    (SignedMeasure.toComplexMeasure s t) i = (s i : ℂ) + (t i : ℂ) * Complex.I := by
  rw [SignedMeasure.toComplexMeasure_apply]
  apply Complex.ext <;> simp

/-! ## 2. 复测度与有符号测度对的对应 -/

/-- **复测度为零的判定**。复测度 `c` 为零当且仅当其实部与虚部同时为零有符号测度。
> **Entry**: real-analysis.signed-measure.complex
@isnad1 id=iff.0h2v.s9.dcd5fffc6ae6 from=translated src=- shape=670caa54 vocab=841782e0
-/
theorem complexMeasure_eq_zero_iff (c : ComplexMeasure α) :
    c = 0 ↔ ComplexMeasure.re c = 0 ∧ ComplexMeasure.im c = 0 := by
  constructor
  · intro h
    exact ⟨by rw [h, map_zero], by rw [h, map_zero]⟩
  · rintro ⟨hr, hi⟩
    rw [← c.toComplexMeasure_to_signedMeasure, hr, hi]
    ext i _
    rw [SignedMeasure.toComplexMeasure_apply]
    rfl

/-- **复测度的外延性**。若两复测度的实部相等且虚部相等，则两复测度相等：实部与虚部
共同决定一个复测度。
> **Entry**: real-analysis.signed-measure.complex
@isnad1 id=eq.2h3v.s9.dc0a39357a9d from=translated src=- shape=b70ef720 vocab=841782e0
-/
theorem complexMeasure_ext {c d : ComplexMeasure α}
    (hre : ComplexMeasure.re c = ComplexMeasure.re d)
    (him : ComplexMeasure.im c = ComplexMeasure.im d) : c = d := by
  rw [← c.toComplexMeasure_to_signedMeasure, ← d.toComplexMeasure_to_signedMeasure, hre, him]

/-- **复测度与有符号测度对的等价**。`c ↦ (re c, im c)` 给出复测度类型与有符号测度对类型
之间的等价（其逆为 `(s, t) ↦ s.toComplexMeasure t`）。这是 Folland 把复测度归结为
有符号测度的现代形式，也是本库后续复测度理论的入口。
> **Entry**: real-analysis.signed-measure.complex-/
def complexMeasure_equiv_signedMeasure :
    ComplexMeasure α ≃ SignedMeasure α × SignedMeasure α :=
  ComplexMeasure.equivSignedMeasure

/-- **复测度取值为零的逐点判定**。`c i = 0` 当且仅当 `re c` 与 `im c` 在 `i` 上都取零；
这是点式分解 `c i = re c i + i · im c i` 的直接推论，也是实部／虚部概念的真实使用者。
> **Entry**: real-analysis.signed-measure.complex
@isnad1 id=iff.0h3v.s9.1713ee02ca3d from=translated src=- shape=d68d763c vocab=3fa98d45
-/
theorem complexMeasure_apply_eq_zero_iff (c : ComplexMeasure α) (i : Set α) :
    c i = 0 ↔ ComplexMeasure.re c i = 0 ∧ ComplexMeasure.im c i = 0 := by
  rw [complexMeasure_re_add_im, complexMeasure_re_apply, complexMeasure_im_apply]
  constructor
  · intro h
    exact ⟨by simpa using congrArg Complex.re h, by simpa using congrArg Complex.im h⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb]
    simp

end RealAnalysis.SignedMeasure

end SandronesLibrary
