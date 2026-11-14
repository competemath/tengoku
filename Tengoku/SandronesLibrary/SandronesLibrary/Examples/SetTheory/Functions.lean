/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Function
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Set
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 集合论：像、原像与单射／满射／双射的具体计算

本文件为理论条目 `settheory.function.inj-comp`、`settheory.function.surj-comp`、
`settheory.function.image-preimage.preimage-union`、
`settheory.function.image-preimage.preimage-inter` 与
`settheory.function.inject-surject.bijective-iff-inverse` 补齐具体计算例：命名线性函数
`doubleAddOne n = 2n+1`、折半函数 `half n = n/2`、平方函数 `sq n = n²` 与平移函数
`shift n = n+1`，逐元素算出它们的像与原像，并给出三组精确反例：单射不必满射
（`doubleAddOne`）、满射不必单射（`half`）、像不保持交（`sq` 在 `{-1}` 与 `{1}` 上）。

> **Entry**: examples.settheory.functions
-/

noncomputable section

namespace SandronesLibrary.Examples.SetTheory.Functions

open Set

/-- **线性（仿射）函数**：`doubleAddOne n = 2n + 1`，把自然数映到奇数。-/
def doubleAddOne (n : ℕ) : ℕ := 2 * n + 1

/-- **折半函数**：`half n = n / 2`（自然数除法，向下取整）。-/
def half (n : ℕ) : ℕ := n / 2

/-- **平方函数**：`sq n = n ^ 2`，定义在整数上（负数的平方会与正数“撞车”）。-/
def sq (n : ℤ) : ℤ := n ^ 2

/-- **平移函数**：`shift n = n + 1`，整数上的双射原型。-/
def shift (n : ℤ) : ℤ := n + 1

/-- **具体集合 S**：`S = {0,1,2} ⊂ ℕ`，用于线性函数的像与原像计算。-/
abbrev S : Set ℕ := {0, 1, 2}

/-- **具体集合 T**：`T = {1,2,3} ⊂ ℕ`，与 `S` 的交 `{1,2}` 用于“单射保交”的正例。-/
abbrev T : Set ℕ := {1, 2, 3}

/-- **具体集合 negOne**：`{-1} ⊂ ℤ`，平方反例的左片。-/
abbrev negOne : Set ℤ := {-1}

/-- **具体集合 posOne**：`{1} ⊂ ℤ`，平方反例的右片。-/
abbrev posOne : Set ℤ := {1}

/-- **定义展开**：`doubleAddOne n = 2 * n + 1`。
@isnad1 id=eq.0h1v.s4.91382adbde55 from=translated src=- shape=71ad29f1 vocab=520833f3
-/
theorem doubleAddOne_apply (n : ℕ) : doubleAddOne n = 2 * n + 1 := rfl

/-- **定义展开**：`half n = n / 2`。
@isnad1 id=eq.0h1v.s4.eaf425454e50 from=translated src=- shape=31421b16 vocab=5401c3fd
-/
theorem half_apply (n : ℕ) : half n = n / 2 := rfl

/-- **定义展开**：`sq n = n ^ 2`。
@isnad1 id=eq.0h1v.s4.9dc1c4abe83b from=translated src=- shape=91c44b26 vocab=e905d6cf
-/
theorem sq_apply (n : ℤ) : sq n = n ^ 2 := rfl

/-- **定义展开**：`shift n = n + 1`。
@isnad1 id=eq.0h1v.s4.6041bea775a2 from=translated src=- shape=31421b16 vocab=4ab52555
-/
theorem shift_apply (n : ℤ) : shift n = n + 1 := rfl

/-- **线性函数的像（逐元素计算）**：`doubleAddOne '' {0,1,2} = {1,3,5}`。
@isnad1 id=eq.0h0v.s5.39349b0a0c68 from=translated src=- shape=dfeada1a vocab=521f629e
-/
theorem image_doubleAddOne_S : doubleAddOne '' S = ({1, 3, 5} : Set ℕ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> norm_num [doubleAddOne]
  · intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨0, by simp [S], by norm_num [doubleAddOne]⟩
    · exact ⟨1, by simp [S], by norm_num [doubleAddOne]⟩
    · exact ⟨2, by simp [S], by norm_num [doubleAddOne]⟩

/-- **线性函数的原像（逐元素计算）**：`doubleAddOne ⁻¹' {1,3,5} = {0,1,2}`。
把“像在 `{1,3,5}` 里”翻译回“自变量在 `{0,1,2}` 里”，逐元素求解 `2n+1 ∈ {1,3,5}`。
@isnad1 id=eq.0h0v.s5.1d76a5c7f21e from=translated src=- shape=cbcfb2f4 vocab=dc7c1246
-/
theorem preimage_doubleAddOne : doubleAddOne ⁻¹' ({1, 3, 5} : Set ℕ) = S := by
  ext x
  simp only [Set.mem_preimage, S, Set.mem_insert_iff, Set.mem_singleton_iff, doubleAddOne]
  omega

/-- **线性函数的原像（逐元素计算）**：`doubleAddOne ⁻¹' {1,3} = {0,1}`。
@isnad1 id=eq.0h0v.s5.312768ba8e8c from=translated src=- shape=7ec0e1b6 vocab=1a06f3c3
-/
theorem preimage_doubleAddOne_13 : doubleAddOne ⁻¹' ({1, 3} : Set ℕ) = ({0, 1} : Set ℕ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, doubleAddOne]
  omega

/-- **线性函数的原像（逐元素计算）**：`doubleAddOne ⁻¹' {3,5} = {1,2}`。
@isnad1 id=eq.0h0v.s5.05198421bc68 from=translated src=- shape=7ec0e1b6 vocab=1a06f3c3
-/
theorem preimage_doubleAddOne_35 : doubleAddOne ⁻¹' ({3, 5} : Set ℕ) = ({1, 2} : Set ℕ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, doubleAddOne]
  omega

/-- **线性函数的原像（逐元素计算）**：`doubleAddOne ⁻¹' {3,5,7} = T = {1,2,3}`。
@isnad1 id=eq.0h0v.s5.2da0a1cade50 from=translated src=- shape=cbcfb2f4 vocab=49c98ca1
-/
theorem preimage_doubleAddOne_T : doubleAddOne ⁻¹' ({3, 5, 7} : Set ℕ) = T := by
  ext x
  simp only [Set.mem_preimage, T, Set.mem_insert_iff, Set.mem_singleton_iff, doubleAddOne]
  omega

/-- **原像保并（左侧计算）**：`doubleAddOne ⁻¹' ({1,3} ∪ {3,5}) = {0,1,2}`。
@isnad1 id=eq.0h0v.s6.b760a2e2d19f from=translated src=- shape=a71c3c6b vocab=c43af5f9
-/
theorem preimage_doubleAddOne_union :
    doubleAddOne ⁻¹' (({1, 3} : Set ℕ) ∪ {3, 5}) = ({0, 1, 2} : Set ℕ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    doubleAddOne]
  omega

/-- **原像保并的具体验证**：
`doubleAddOne ⁻¹' ({1,3} ∪ {3,5}) = doubleAddOne ⁻¹' {1,3} ∪ doubleAddOne ⁻¹' {3,5}`
——两侧各自逐元素算成 `{0,1,2}`（理论条目 `settheory.function.image-preimage.preimage-union`
的实例）。
@isnad1 id=eq.0h0v.s6.82612c4137ff from=translated src=- shape=28d9a54d vocab=c43af5f9
-/
theorem preimage_union_instance :
    doubleAddOne ⁻¹' (({1, 3} : Set ℕ) ∪ {3, 5}) =
      doubleAddOne ⁻¹' ({1, 3} : Set ℕ) ∪ doubleAddOne ⁻¹' ({3, 5} : Set ℕ) := by
  rw [preimage_doubleAddOne_13, preimage_doubleAddOne_35, preimage_doubleAddOne_union]
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **原像保交（左侧计算）**：`doubleAddOne ⁻¹' ({1,3,5} ∩ {3,5,7}) = {1,2}`。
@isnad1 id=eq.0h0v.s6.f0fa1fe79df6 from=translated src=- shape=125e233c vocab=7e4a0ce3
-/
theorem preimage_doubleAddOne_inter :
    doubleAddOne ⁻¹' (({1, 3, 5} : Set ℕ) ∩ {3, 5, 7}) = ({1, 2} : Set ℕ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    doubleAddOne]
  omega

/-- **原像保交的具体验证**：
`doubleAddOne ⁻¹' ({1,3,5} ∩ {3,5,7}) = doubleAddOne ⁻¹' {1,3,5} ∩ doubleAddOne ⁻¹' {3,5,7}`
（理论条目 `settheory.function.image-preimage.preimage-inter` 的实例）。
@isnad1 id=eq.0h0v.s7.987ce04a0da3 from=translated src=- shape=47d4f52b vocab=7e4a0ce3
-/
theorem preimage_inter_instance :
    doubleAddOne ⁻¹' (({1, 3, 5} : Set ℕ) ∩ {3, 5, 7}) =
      doubleAddOne ⁻¹' ({1, 3, 5} : Set ℕ) ∩ doubleAddOne ⁻¹' ({3, 5, 7} : Set ℕ) := by
  rw [preimage_doubleAddOne, preimage_doubleAddOne_T, preimage_doubleAddOne_inter]
  ext x
  simp only [Set.mem_inter_iff, S, T, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **线性函数在 `T` 上的像（逐元素计算）**：`doubleAddOne '' {1,2,3} = {3,5,7}`。
@isnad1 id=eq.0h0v.s5.5d88fda33366 from=translated src=- shape=dfeada1a vocab=e650c35c
-/
theorem image_doubleAddOne_T : doubleAddOne '' T = ({3, 5, 7} : Set ℕ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> norm_num [doubleAddOne]
  · intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨1, by simp [T], by norm_num [doubleAddOne]⟩
    · exact ⟨2, by simp [T], by norm_num [doubleAddOne]⟩
    · exact ⟨3, by simp [T], by norm_num [doubleAddOne]⟩

/-- **交集（逐元素计算）**：`S ∩ T = {1,2}`。
@isnad1 id=eq.0h0v.s5.9d427af35bae from=translated src=- shape=e9eb382d vocab=7d74d11d
-/
theorem inter_S_T : S ∩ T = ({1, 2} : Set ℕ) := by
  ext x
  simp only [S, T, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **像与交（逐元素计算）**：`doubleAddOne '' (S ∩ T) = {3,5}`。
@isnad1 id=eq.0h0v.s5.61599523ba3c from=translated src=- shape=0615d146 vocab=445d7770
-/
theorem image_doubleAddOne_inter : doubleAddOne '' (S ∩ T) = ({3, 5} : Set ℕ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [inter_S_T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> norm_num [doubleAddOne]
  · intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨1, by simp [inter_S_T], by norm_num [doubleAddOne]⟩
    · exact ⟨2, by simp [inter_S_T], by norm_num [doubleAddOne]⟩

/-- **正例（单射时像保交）**：`doubleAddOne '' (S ∩ T) = doubleAddOne '' S ∩ doubleAddOne '' T`。
两侧各自逐元素算成 `{3,5}`：`doubleAddOne` 在 `S ∪ T` 上单射，所以交集不被压掉。
@isnad1 id=eq.0h0v.s4.40a00850bd40 from=translated src=- shape=114a0431 vocab=b0789e0d
-/
theorem image_inter_doubleAddOne :
    doubleAddOne '' (S ∩ T) = doubleAddOne '' S ∩ doubleAddOne '' T := by
  rw [image_doubleAddOne_inter, image_doubleAddOne_S, image_doubleAddOne_T]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **平方函数的像（逐元素计算）**：`sq '' {0,1,2} = {0,1,4}`。
@isnad1 id=eq.0h0v.s6.75f12a9e7b87 from=translated src=- shape=eba23ff4 vocab=5752aa2f
-/
theorem image_sq_zero_one_two : sq '' ({0, 1, 2} : Set ℤ) = ({0, 1, 4} : Set ℤ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> norm_num [sq]
  · intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨0, by simp, by norm_num [sq]⟩
    · exact ⟨1, by simp, by norm_num [sq]⟩
    · exact ⟨2, by simp, by norm_num [sq]⟩

/-- **平方函数的原像（逐元素计算）**：`sq ⁻¹' {1} = {-1,1}`。
原像里有两个元素——这正是平方函数不单射的几何含义。
@isnad1 id=eq.0h0v.s5.2caae9ab7409 from=translated src=- shape=209dbaf6 vocab=21cc342e
-/
theorem preimage_sq_one : sq ⁻¹' ({1} : Set ℤ) = ({-1, 1} : Set ℤ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff, sq]
  constructor
  · intro h
    have hfac : (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h1
    · right; linarith
    · left; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- **平方函数的原像（逐元素计算）**：`sq ⁻¹' {4} = {-2,2}`。
@isnad1 id=eq.0h0v.s5.2a1501340a57 from=translated src=- shape=209dbaf6 vocab=21cc342e
-/
theorem preimage_sq_four : sq ⁻¹' ({4} : Set ℤ) = ({-2, 2} : Set ℤ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff, sq]
  constructor
  · intro h
    have hfac : (x - 2) * (x + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h1
    · right; linarith
    · left; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- **像（逐元素计算）**：`sq '' {-1} = {1}`。
@isnad1 id=eq.0h0v.s4.7c116a7a97d1 from=translated src=- shape=2cc3055c vocab=d04a212b
-/
theorem image_sq_negOne : sq '' negOne = ({1} : Set ℤ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [negOne, Set.mem_singleton_iff] at hx
    subst hx
    norm_num [sq]
  · intro hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨-1, by simp [negOne], by norm_num [sq]⟩

/-- **像（逐元素计算）**：`sq '' {1} = {1}`。
@isnad1 id=eq.0h0v.s4.a2a5c369c90f from=translated src=- shape=2cc3055c vocab=92a04f39
-/
theorem image_sq_posOne : sq '' posOne = ({1} : Set ℤ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [posOne, Set.mem_singleton_iff] at hx
    subst hx
    norm_num [sq]
  · intro hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨1, by simp [posOne], by norm_num [sq]⟩

/-- **像（逐元素计算）**：`sq '' ({-1} ∩ {1}) = sq '' ∅ = ∅`——两片不交，像为空。
@isnad1 id=eq.0h0v.s4.d6c95957fe3d from=translated src=- shape=dda940f5 vocab=e4bc1e6a
-/
theorem image_sq_inter_empty : sq '' (negOne ∩ posOne) = (∅ : Set ℤ) := by
  have hempty : negOne ∩ posOne = (∅ : Set ℤ) := by
    ext x
    simp only [negOne, posOne, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false]
    omega
  rw [hempty, Set.image_empty]

/-- **正方向（包含总是成立）**：`sq '' (A ∩ B) ⊆ sq '' A ∩ sq '' B` 在具体集合上成立。
这是“像保交”唯一无条件成立的方向；等式方向需要单射（见下一条反例）。
@isnad1 id=le.0h0v.s4.c825d0ce1b10 from=translated src=- shape=114a0431 vocab=008aeda6
-/
theorem image_sq_inter_subset :
    sq '' (negOne ∩ posOne) ⊆ sq '' negOne ∩ sq '' posOne :=
  Set.image_inter_subset sq negOne posOne

/-- **反例（像不保持交）**：`sq '' ({-1} ∩ {1}) ≠ sq '' {-1} ∩ sq '' {1}`。
具体见证：`1 = sq 1 = sq (-1)` 落在右边（两个像的交）但不落在左边
（`{-1} ∩ {1} = ∅`，其像为空）。它反驳“像总保持交”的误命题。
@isnad1 id=ne.0h0v.s4.63a9a2f110a8 from=translated src=- shape=114a0431 vocab=8fea370e
-/
theorem sq_image_inter_ne :
    sq '' (negOne ∩ posOne) ≠ sq '' negOne ∩ sq '' posOne := by
  intro h
  have hmem : (1 : ℤ) ∈ sq '' negOne ∩ sq '' posOne :=
    ⟨⟨-1, by simp [negOne], by norm_num [sq]⟩,
      ⟨1, by simp [posOne], by norm_num [sq]⟩⟩
  rw [← h] at hmem
  rcases hmem with ⟨x, hx, _⟩
  simp only [negOne, posOne, Set.mem_inter_iff, Set.mem_singleton_iff] at hx
  omega

/-- **反例（一般否定命题）**：存在 `A B : Set ℤ` 使 `sq '' (A ∩ B) ≠ sq '' A ∩ sq '' B`。
@isnad1 id=ex.0h0v.s5.c48c935fa031 from=translated src=- shape=21f144a9 vocab=4f2dbd67
-/
theorem exists_image_inter_ne :
    ∃ A B : Set ℤ, sq '' (A ∩ B) ≠ sq '' A ∩ sq '' B :=
  ⟨negOne, posOne, sq_image_inter_ne⟩

/-- **单射（线性函数）**：`doubleAddOne` 在 `ℕ` 上单射（`2a+1 = 2b+1 ⟹ a = b`）。
@isnad1 id=injectiv.0h0v.s2.30f1ffc5a4c1 from=translated src=- shape=e3d48bcb vocab=44c49475
-/
theorem doubleAddOne_injective : Function.Injective doubleAddOne := by
  intro a b h
  simp only [doubleAddOne] at h
  omega

/-- **反例（单射不必满射）**：`doubleAddOne` 单射但不满射——偶数 `0` 没有原像
（`2n+1` 恒为奇数）。
@isnad1 id=not.0h0v.s2.96e565749e62 from=translated src=- shape=8524eaa4 vocab=18a7a7d5
-/
theorem doubleAddOne_not_surjective : ¬ Function.Surjective doubleAddOne := by
  intro h
  rcases h 0 with ⟨n, hn⟩
  simp only [doubleAddOne] at hn
  omega

/-- **反例（精确陈述）**：`doubleAddOne` 满足单射（前件）但不满足满射（后件），
故“单射 ⟹ 满射”为假。
@isnad1 id=and.0h0v.s3.8cdebe841bfe from=translated src=- shape=6b5fd7c2 vocab=58062105
-/
theorem doubleAddOne_injective_not_surjective :
    Function.Injective doubleAddOne ∧ ¬ Function.Surjective doubleAddOne :=
  ⟨doubleAddOne_injective, doubleAddOne_not_surjective⟩

/-- **满射（折半函数）**：`half` 满射——任意 `m` 都有原像 `2m`（`(2m)/2 = m`）。
@isnad1 id=surjecti.0h0v.s2.12fdac98e68a from=translated src=- shape=e3d48bcb vocab=1eedc5d1
-/
theorem half_surjective : Function.Surjective half := by
  intro m
  refine ⟨2 * m, ?_⟩
  simp only [half]
  exact Nat.mul_div_right m (by norm_num : 0 < 2)

/-- **反例（满射不必单射）**：`half` 满射但不单射——`0` 与 `1` 都映到 `0`。
@isnad1 id=not.0h0v.s2.9df8b61b9178 from=translated src=- shape=8524eaa4 vocab=a8567353
-/
theorem half_not_injective : ¬ Function.Injective half := by
  intro h
  have h01 : half 0 = half 1 := by norm_num [half]
  have hEq : (0 : ℕ) = 1 := h h01
  omega

/-- **反例（精确陈述）**：`half` 满足满射（前件）但不满足单射（后件），
故“满射 ⟹ 单射”为假。
@isnad1 id=and.0h0v.s3.2a9191c150d9 from=translated src=- shape=6b5fd7c2 vocab=4e1426ef
-/
theorem half_surjective_not_injective :
    Function.Surjective half ∧ ¬ Function.Injective half :=
  ⟨half_surjective, half_not_injective⟩

/-- **平移的左逆**：`g n = n - 1` 是 `shift` 的左逆（`g (shift n) = n`）。
@isnad1 id=leftinve.0h0v.s4.5cc05fab6a3a from=translated src=- shape=192f3801 vocab=374e777a
-/
theorem shift_leftInverse : Function.LeftInverse (fun n : ℤ => n - 1) shift := by
  intro n
  simp only [shift]
  ring

/-- **平移的右逆**：`g n = n - 1` 同时是 `shift` 的右逆（`shift (g n) = n`）。
@isnad1 id=rightinv.0h0v.s4.84c5add1739a from=translated src=- shape=192f3801 vocab=f35ea69f
-/
theorem shift_rightInverse : Function.RightInverse (fun n : ℤ => n - 1) shift := by
  intro n
  simp only [shift]
  ring

/-- **正例（双射的等价刻画）**：把理论条目
`settheory.function.inject-surject.bijective-iff-inverse` 用在具体函数 `shift` 上——
`shift` 双射当且仅当存在同时是左逆与右逆的映射 `g`。
@isnad1 id=iff.0h0v.s4.46a36e1132e3 from=translated src=- shape=3e290cc9 vocab=2613bd14
-/
theorem shift_bijective_iff_inverse :
    Function.Bijective shift ↔
      ∃ g : ℤ → ℤ, Function.LeftInverse g shift ∧ Function.RightInverse g shift :=
  SandronesLibrary.SetTheory.Function.bijective_iff_inverse shift

/-- **正例（双射）**：`shift n = n + 1` 是双射；见证逆映射 `g n = n - 1`。
@isnad1 id=bijectiv.0h0v.s2.3dff4d316c3f from=translated src=- shape=e3d48bcb vocab=b77160a1
-/
theorem shift_bijective : Function.Bijective shift :=
  shift_bijective_iff_inverse.mpr ⟨fun n : ℤ => n - 1, shift_leftInverse, shift_rightInverse⟩

/-- **单射（平移）**：`shift` 单射（双射的第一半）。
@isnad1 id=injectiv.0h0v.s2.c31cfd3d12ba from=translated src=- shape=e3d48bcb vocab=901c3b8d
-/
theorem shift_injective : Function.Injective shift := shift_bijective.1

/-- **满射（平移）**：`shift` 满射（双射的第二半）。
@isnad1 id=surjecti.0h0v.s2.0c1b5ca93298 from=translated src=- shape=e3d48bcb vocab=0c1eb081
-/
theorem shift_surjective : Function.Surjective shift := shift_bijective.2

/-- **复合的具体求值**：`(shift ∘ shift) 0 = 2`（复合就是 `n ↦ n + 2`）。
@isnad1 id=eq.0h0v.s4.4fae090b0ac8 from=translated src=- shape=ced0d032 vocab=0086d44e
-/
theorem shift_comp_apply : (shift ∘ shift) 0 = 2 := by
  norm_num [Function.comp, shift]

/-- **正例（单射的复合）**：`shift ∘ shift` 单射，由理论条目
`settheory.function.inj-comp` 作用在两条 `shift` 单射性上得到。
@isnad1 id=injectiv.0h0v.s3.efc742c45162 from=translated src=- shape=690c58ab vocab=124970e3
-/
theorem shift_comp_injective : Function.Injective (shift ∘ shift) :=
  SandronesLibrary.SetTheory.Function.injective_comp shift_injective shift_injective

/-- **正例（满射的复合）**：`shift ∘ shift` 满射，由理论条目
`settheory.function.surj-comp` 作用在两条 `shift` 满射性上得到。
@isnad1 id=surjecti.0h0v.s3.4d5218c27e3e from=translated src=- shape=690c58ab vocab=f5a5bd2b
-/
theorem shift_comp_surjective : Function.Surjective (shift ∘ shift) :=
  SandronesLibrary.SetTheory.Function.surjective_comp shift_surjective shift_surjective

/-- **正例（双射的复合）**：`shift ∘ shift` 双射。
@isnad1 id=bijectiv.0h0v.s3.cf09831b076a from=translated src=- shape=690c58ab vocab=f6d1dfa5
-/
theorem shift_comp_bijective : Function.Bijective (shift ∘ shift) :=
  ⟨shift_comp_injective, shift_comp_surjective⟩

/-! ## 理论接口的直接调用

上面的像／原像计算是逐元素做出来的；这一节把 `SetTheory/Set.lean` 与
`SetTheory/Function.lean` 的**一般定理**直接作用在具体集合与具体函数上，使本 Entry 与
`settheory.set.ext`、`settheory.function.image-preimage.*` 之间有真实的**声明级依赖**。
-/

/-- **外延性原理**（`settheory.set.ext`）作用在具体集合上：`S = T ↔ ∀ x, x ∈ S ↔ x ∈ T`。
@isnad1 id=iff.0h0v.s4.dea1b13876da from=translated src=- shape=5d85b45b vocab=2ae7bede
-/
theorem set_ext_instance : S = T ↔ ∀ x : ℕ, x ∈ S ↔ x ∈ T :=
  SandronesLibrary.SetTheory.Set.set_ext S T

/-- **原像保并**（`settheory.function.image-preimage.preimage-union`）作用在具体函数与集合上。
@isnad1 id=eq.0h0v.s6.82612c4137ff from=translated src=- shape=28d9a54d vocab=c43af5f9
-/
theorem preimage_union_via_theory :
    doubleAddOne ⁻¹' (({1, 3} : Set ℕ) ∪ {3, 5}) =
      doubleAddOne ⁻¹' ({1, 3} : Set ℕ) ∪ doubleAddOne ⁻¹' ({3, 5} : Set ℕ) :=
  SandronesLibrary.SetTheory.Function.preimage_union doubleAddOne {1, 3} {3, 5}

/-- **原像保交**（`settheory.function.image-preimage.preimage-inter`）作用在具体函数与集合上。
@isnad1 id=eq.0h0v.s7.987ce04a0da3 from=translated src=- shape=47d4f52b vocab=7e4a0ce3
-/
theorem preimage_inter_via_theory :
    doubleAddOne ⁻¹' (({1, 3, 5} : Set ℕ) ∩ {3, 5, 7}) =
      doubleAddOne ⁻¹' ({1, 3, 5} : Set ℕ) ∩ doubleAddOne ⁻¹' ({3, 5, 7} : Set ℕ) :=
  SandronesLibrary.SetTheory.Function.preimage_inter doubleAddOne {1, 3, 5} {3, 5, 7}

end SandronesLibrary.Examples.SetTheory.Functions
