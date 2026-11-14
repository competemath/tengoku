/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenRightAnchoredGrid

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen Pushout 字母词与拼接环路

本文件把二开集 Pushout 元素表示为带覆盖标签的有限基本群字母词，为每个字母选择实际环境基点环路，
并以反序 `Path.concat` 构造与群乘法方向匹配的拼接环路。

当前条目：

* `topology.fundamental-group.van-kampen-letter-word`。

本文件不另建自由积、商群或道路同伦承载，也尚未证明拼接环路的类等于字母词、kernel 元素零伦或
van Kampen 单射。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 二开集 van Kampen Pushout 的一个字母：选择一侧覆盖成员及其中的一个基本群元素。

> **Entry**: topology.fundamental-group.van-kampen-letter-word-/
abbrev BinaryVanKampenLetter (U V : Set X) {x₀ : X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) :=
  Σ b : Bool, FundamentalGroup (binaryOpenCoverPiece U V b)
    (binaryOpenCoverBasepoint hxU hxV b)

/-- 按列表从左到右解释有限个覆盖成员字母。-/
def binaryVanKampenLetterWord (U V : Set X) {x₀ : X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) :
    List (BinaryVanKampenLetter U V hxU hxV) →
      binaryVanKampenPushout U V hxU hxV
  | [] => 1
  | ⟨b, g⟩ :: rest =>
      Monoid.PushoutI.of b g * binaryVanKampenLetterWord U V hxU hxV rest

private theorem binaryVanKampenLetterWord_append (U V : Set X) {x₀ : X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (first second : List (BinaryVanKampenLetter U V hxU hxV)) :
    binaryVanKampenLetterWord U V hxU hxV (first ++ second) =
      binaryVanKampenLetterWord U V hxU hxV first *
        binaryVanKampenLetterWord U V hxU hxV second := by
  induction first with
  | nil => simp [binaryVanKampenLetterWord]
  | cons head rest ih =>
      rcases head with ⟨b, g⟩
      simp only [List.cons_append, binaryVanKampenLetterWord, ih, mul_assoc]

/-- 每个二开集 van Kampen Pushout 元素都严格等于有限个单侧基本群字母的有序乘积。
证明直接使用 Mathlib `Monoid.PushoutI.induction_on`；交集生成元由任一侧（这里固定 `false`）吸收。
@isnad1 id=ex.2h5v.s6.fdbb660f88d8 from=translated src=- shape=a7e259af vocab=1a6b81b4
-/
theorem exists_binaryVanKampenLetterWord (U V : Set X) {x₀ : X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (a : binaryVanKampenPushout U V hxU hxV) :
    ∃ letters : List (BinaryVanKampenLetter U V hxU hxV),
      binaryVanKampenLetterWord U V hxU hxV letters = a := by
  induction a using Monoid.PushoutI.induction_on with
  | of b g =>
      exact ⟨[⟨b, g⟩], by simp [binaryVanKampenLetterWord]⟩
  | base h =>
      refine ⟨[⟨false, binaryOpenCoverIntersectionMaps U V hxU hxV false h⟩], ?_⟩
      simp [binaryVanKampenLetterWord, Monoid.PushoutI.of_apply_eq_base]
  | mul a b ha hb =>
      rcases ha with ⟨wa, hwa⟩
      rcases hb with ⟨wb, hwb⟩
      exact ⟨wa ++ wb, by rw [binaryVanKampenLetterWord_append, hwa, hwb]⟩

/-- 为一个基本群元素选择实际的基点环路代表。-/
noncomputable def fundamentalGroupPathRepresentative
    {Y : Type*} [TopologicalSpace Y] (y : Y) (g : FundamentalGroup Y y) :
    Path y y :=
  Classical.choose (Path.Homotopic.Quotient.mk_surjective g)

/--
@isnad1 id=eq.0h3v.s5.9d471686e6f9 from=translated src=- shape=a50df1cb vocab=f35245c0
-/
@[simp] theorem fundamentalGroupPathRepresentative_mk
    {Y : Type*} [TopologicalSpace Y] (y : Y) (g : FundamentalGroup Y y) :
    FundamentalGroup.fromPath
      ⟦fundamentalGroupPathRepresentative y g⟧ = g :=
  Classical.choose_spec (Path.Homotopic.Quotient.mk_surjective g)

/-- 将一个单侧字母的道路代表沿覆盖成员包含映入环境空间。-/
noncomputable def BinaryVanKampenLetter.ambientLoop
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letter : BinaryVanKampenLetter U V hxU hxV) : Path x₀ x₀ := by
  rcases letter with ⟨b, g⟩
  let mapped := (fundamentalGroupPathRepresentative
      (binaryOpenCoverBasepoint hxU hxV b) g).map
    (binaryOpenCoverPieceToSpace U V b).continuous
  cases b
  · exact mapped.cast rfl rfl
  · exact mapped.cast rfl rfl

/-- 单侧字母经 van Kampen 规范同态后的像，严格由其所选环境环路代表。
@isnad1 id=eq.2h5v.s12.3440bb510462 from=translated src=- shape=0c65c0da vocab=0db2968f
-/
theorem binaryVanKampenCanonicalMap_of_letter
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letter : BinaryVanKampenLetter U V hxU hxV) :
    binaryVanKampenCanonicalMap U V hxU hxV
        (Monoid.PushoutI.of letter.1 letter.2) =
      FundamentalGroup.fromPath ⟦letter.ambientLoop hxU hxV⟧ := by
  rcases letter with ⟨b, g⟩
  rw [binaryVanKampenCanonicalMap, Monoid.PushoutI.lift_of]
  cases b <;>
    change FundamentalGroup.map (binaryOpenCoverPieceToSpace U V _) _ g = _ <;>
    nth_rewrite 1 [← fundamentalGroupPathRepresentative_mk
      (binaryOpenCoverBasepoint hxU hxV _) g] <;>
    rfl

/-- 基本群中的单位元等式可无损还原为一个端点相对道路同伦。
@isnad1 id=homotopi.1h3v.s6.5559c175c07e from=translated src=- shape=64869a26 vocab=7d131fa5
-/
theorem pathHomotopic_refl_of_fromPath_eq_one
    {Y : Type*} [TopologicalSpace Y] {y : Y} (p : Path y y)
    (h : FundamentalGroup.fromPath ⟦p⟧ = 1) :
    p.Homotopic (Path.refl y) := by
  apply Path.Homotopic.Quotient.exact
  change FundamentalGroup.fromPath ⟦p⟧ = 1
  exact h

/-- 将字母列表反序后用 Mathlib `Path.concat` 递归拼接。反序补偿
`FundamentalGroup.mul_def` 中群乘法与道路拼接的方向差异。注意 `Path.concat` 使用左结合
`Path.trans`，其断点是 dyadic，而不是等长 `n` 等分。-/
noncomputable def binaryVanKampenLetterConcatLoop
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV)) : Path x₀ x₀ :=
  let reversed := letters.reverse
  Path.concat (fun _ : Fin (reversed.length + 1) => x₀)
    (fun i : Fin reversed.length =>
      (reversed.get i).ambientLoop hxU hxV)

/--
@isnad1 id=eq.2h6v.s9.e6e65af8b213 from=translated src=- shape=f21cbdf4 vocab=497ab2bc
-/
@[simp] theorem BinaryVanKampenLetter.ambientLoop_apply
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letter : BinaryVanKampenLetter U V hxU hxV) (t : unitInterval) :
    letter.ambientLoop hxU hxV t =
      ((fundamentalGroupPathRepresentative
        (binaryOpenCoverBasepoint hxU hxV letter.1) letter.2 t :
          binaryOpenCoverPiece U V letter.1) : X) := by
  rcases letter with ⟨b, g⟩
  cases b <;> rfl

/-- 每个字母的环境环路逐点位于该字母指定的覆盖成员中。-/
private theorem BinaryVanKampenLetter.ambientLoop_mem_piece
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letter : BinaryVanKampenLetter U V hxU hxV) (t : unitInterval) :
    letter.ambientLoop hxU hxV t ∈ binaryOpenCoverPiece U V letter.1 := by
  rcases letter with ⟨b, g⟩
  rw [BinaryVanKampenLetter.ambientLoop_apply]
  exact (fundamentalGroupPathRepresentative
    (binaryOpenCoverBasepoint hxU hxV b) g t).property

/-- `Path.concat` 的第 `i` 个输入 segment 使用反序列表中的标签。
@isnad1 id=mem.2h7v.s7.f128b471992c from=translated src=- shape=72b3c8a9 vocab=d841d744
-/
theorem binaryVanKampenLetterConcatLoop_segment_mem
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (i : Fin letters.reverse.length) (t : unitInterval) :
    (letters.reverse.get i).ambientLoop hxU hxV t ∈
      binaryOpenCoverPiece U V (letters.reverse.get i).1 :=
  (letters.reverse.get i).ambientLoop_mem_piece hxU hxV t

end SandronesLibrary.Topology
