/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenKernelWord

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 二开集 Seifert--van Kampen 定理

本文件把前序字母词与 kernel 消去链组装成规范同态的单射性，再与已证明的满射性合成群同构。
结论适用于道路连通开二覆盖且交集道路连通的版本，不声称多开集或非连通交集推广。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 字母词规范同态像也可直接写成各字母环境环路类的列表乘积。-/
private theorem binaryVanKampenCanonicalMap_letterWord_eq_prod
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) :
    ∀ letters : List (BinaryVanKampenLetter U V hxU hxV),
      binaryVanKampenCanonicalMap U V hxU hxV
          (binaryVanKampenLetterWord U V hxU hxV letters) =
        (letters.map (fun letter => FundamentalGroup.fromPath
          ⟦letter.ambientLoop hxU hxV⟧)).prod
  | [] => by simp [binaryVanKampenLetterWord]
  | letter :: rest => by
      rw [binaryVanKampenLetterWord, map_mul,
        binaryVanKampenCanonicalMap_of_letter hxU hxV letter,
        binaryVanKampenCanonicalMap_letterWord_eq_prod hxU hxV rest]
      rfl

/-- `Path.concat` 环路的基本群类严格等于原 Pushout 字母词的规范同态像。

> **Entry**: topology.fundamental-group.van-kampen-theorem
@isnad1 id=eq.2h5v.s9.6b0c65b971e3 from=translated src=- shape=413e308a vocab=92d2e8ae
-/
theorem binaryVanKampenCanonicalMap_letterWord_eq_concatLoop
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV)) :
    binaryVanKampenCanonicalMap U V hxU hxV
        (binaryVanKampenLetterWord U V hxU hxV letters) =
      FundamentalGroup.fromPath
        ⟦binaryVanKampenLetterConcatLoop hxU hxV letters⟧ := by
  let reversed := letters.reverse
  let q : Fin (reversed.length + 1) → X := fun _ => x₀
  let F : (i : Fin reversed.length) → Path (q i.castSucc) (q i.succ) :=
    fun i => (reversed.get i).ambientLoop hxU hxV
  let connector : (i : Fin (reversed.length + 1)) → Path x₀ (q i) :=
    fun _ => Path.refl x₀
  have hconcat := Path.correctedLoopWord_eq_concat q F connector
  have hfold := reverseDfoldl_reverse_get_eq_map_prod
    (fun letter : BinaryVanKampenLetter U V hxU hxV =>
      FundamentalGroup.fromPath ⟦letter.ambientLoop hxU hxV⟧) letters
  rw [binaryVanKampenCanonicalMap_letterWord_eq_prod hxU hxV letters]
  unfold Path.correctedLoopWord at hconcat
  have hleft : Fin.dfoldl reversed.length (fun _ => FundamentalGroup X x₀)
      (fun i acc => FundamentalGroup.fromPath
        ⟦Path.correctedLoop (connector i.castSucc) (F i) (connector i.succ)⟧ * acc) 1 =
      Fin.dfoldl reversed.length (fun _ => FundamentalGroup X x₀)
        (fun i acc => FundamentalGroup.fromPath
          ⟦(reversed.get i).ambientLoop hxU hxV⟧ * acc) 1 := by
    apply congr_arg (fun a : Fin reversed.length → FundamentalGroup X x₀ =>
      Fin.dfoldl reversed.length (fun _ => FundamentalGroup X x₀)
        (fun i acc => a i * acc) 1)
    funext i
    dsimp [connector, F, q]
    exact fundamentalGroup_fromPath_correctedLoop_refl _
  have hright : FundamentalGroup.fromPath
      ⟦Path.correctedLoop (connector 0) (Path.concat q F)
        (connector (Fin.last reversed.length))⟧ =
      FundamentalGroup.fromPath
        ⟦binaryVanKampenLetterConcatLoop hxU hxV letters⟧ := by
    dsimp [connector, q]
    exact (fundamentalGroup_fromPath_correctedLoop_refl (Path.concat (fun _ => x₀) F)).trans
      (by rfl)
  calc
    (letters.map (fun letter => FundamentalGroup.fromPath
        ⟦letter.ambientLoop hxU hxV⟧)).prod =
        Fin.dfoldl reversed.length (fun _ => FundamentalGroup X x₀)
          (fun i acc => FundamentalGroup.fromPath
            ⟦(reversed.get i).ambientLoop hxU hxV⟧ * acc) 1 := hfold.symm
    _ = Fin.dfoldl reversed.length (fun _ => FundamentalGroup X x₀)
          (fun i acc => FundamentalGroup.fromPath
            ⟦Path.correctedLoop (connector i.castSucc) (F i) (connector i.succ)⟧ * acc) 1 :=
      hleft.symm
    _ = FundamentalGroup.fromPath
          ⟦Path.correctedLoop (connector 0) (Path.concat q F)
            (connector (Fin.last reversed.length))⟧ := hconcat
    _ = FundamentalGroup.fromPath
          ⟦binaryVanKampenLetterConcatLoop hxU hxV letters⟧ := hright

/-- 每个 kernel 元素都有精确恢复该元素的非空字母词候选，以及拼接环路到常值道路的
显式同伦。空字母词对应的元素已经是 `1`，后续 VK3 证明可单独立即结束。

> **Entry**: topology.fundamental-group.van-kampen-theorem
@isnad1 id=ex.3h5v.s9.e41e81e38a1e from=translated src=- shape=4a74cf15 vocab=095b0b93
-/
theorem exists_binaryVanKampenKernelConcatLoopHomotopy
    (U V : Set X) {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (a : binaryVanKampenPushout U V hxU hxV)
    (ha : binaryVanKampenCanonicalMap U V hxU hxV a = 1) :
    ∃ letters : List (BinaryVanKampenLetter U V hxU hxV),
      binaryVanKampenLetterWord U V hxU hxV letters = a ∧
        Nonempty ((binaryVanKampenLetterConcatLoop hxU hxV letters).Homotopy
          (Path.refl x₀)) := by
  rcases exists_binaryVanKampenLetterWord U V hxU hxV a with ⟨letters, hletters⟩
  refine ⟨letters, hletters, ?_⟩
  apply pathHomotopic_refl_of_fromPath_eq_one
  rw [← binaryVanKampenCanonicalMap_letterWord_eq_concatLoop hxU hxV letters,
    hletters, ha]

/-- 二元 van Kampen 规范同态 kernel 中的每个元素都是单位元。空字母词直接处理；非空词通过其
零伦的对齐方格细分归约到前序 kernel 字母词定理。

> **Entry**: topology.fundamental-group.van-kampen-theorem
@isnad1 id=eq.9h5v.s9.3ebe380612da from=translated src=- shape=64ec2677 vocab=ccc837d7
-/
theorem binaryVanKampenCanonicalMap_eq_one_imp
    {x₀ : X} (U V : Set X) (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : IsPathConnected (U ∩ V))
    (a : binaryVanKampenPushout U V hxU hxV)
    (ha : binaryVanKampenCanonicalMap U V hxU hxV a = 1) :
    a = 1 := by
  rcases exists_binaryVanKampenKernelConcatLoopHomotopy
    U V hxU hxV a ha with ⟨letters, hletters, ⟨Fhom⟩⟩
  by_cases hempty : letters = []
  · subst letters
    simpa [binaryVanKampenLetterWord] using hletters.symm
  · have hn : 0 < letters.reverse.length := by
      exact List.length_pos_iff.mpr (List.reverse_ne_nil_iff.mpr hempty)
    have hSquare : ∀ z, pathHomotopySquare Fhom z ∈ U ∨
        pathHomotopySquare Fhom z ∈ V := by
      intro z
      have hz : pathHomotopySquare Fhom z ∈ U ∪ V := by
        rw [hcover]
        exact Set.mem_univ _
      exact hz
    obtain ⟨A⟩ := exists_pathConcatAlignedSquareSubdivision
      (pathHomotopySquare Fhom) hUopen hVopen hSquare letters.reverse.length
    exact hletters.symm.trans
      (A.letterWord_eq_one_of_homotopy_of_nonempty
        hxU hxV hUV hU hV letters Fhom hn)

/-- 二元 Seifert--van Kampen 定理的单射部分。

> **Entry**: topology.fundamental-group.van-kampen-theorem
@isnad1 id=injectiv.8h4v.s9.ba582f715fc3 from=translated src=- shape=4e3bd7f6 vocab=a1ab293a
-/
theorem injective_binaryVanKampenCanonicalMap
    {x₀ : X} (U V : Set X) (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : IsPathConnected (U ∩ V)) :
    Function.Injective (binaryVanKampenCanonicalMap U V hxU hxV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext a
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  exact ⟨binaryVanKampenCanonicalMap_eq_one_imp
    U V hxU hxV hUopen hVopen hcover hU hV hUV a,
    fun ha => by simp [ha]⟩

/-- 二元 Seifert--van Kampen 定理：若两个道路连通开集覆盖全空间且交集道路连通，则从合并自由积
到整体基本群的规范映射是群同构。

> **Entry**: topology.fundamental-group.van-kampen-theorem-/
noncomputable def binaryVanKampenCanonicalEquiv
    {x₀ : X} (U V : Set X) (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : IsPathConnected (U ∩ V)) :
    binaryVanKampenPushout U V hxU hxV ≃*
      FundamentalGroup X x₀ :=
  MulEquiv.ofBijective (binaryVanKampenCanonicalMap U V hxU hxV)
    ⟨injective_binaryVanKampenCanonicalMap
      U V hxU hxV hUopen hVopen hcover hU hV hUV,
     Path.surjective_binaryVanKampenCanonicalMap
      U V hxU hxV hUopen hVopen hcover hU hV hUV⟩

/-- 二元 van Kampen 等价的正向同态正是由两个覆盖成员包含到环境空间所诱导的规范映射。

> **Entry**: topology.fundamental-group.van-kampen-theorem
@isnad1 id=eq.8h4v.s9.483ae5941b98 from=translated src=- shape=71e814a8 vocab=0ccf87f2
-/
theorem binaryVanKampenCanonicalEquiv_toMonoidHom
    {x₀ : X} (U V : Set X) (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : IsPathConnected (U ∩ V)) :
    (binaryVanKampenCanonicalEquiv U V hxU hxV hUopen hVopen hcover hU hV hUV).toMonoidHom =
      binaryVanKampenCanonicalMap U V hxU hxV :=
  rfl

/-- 计算二元 van Kampen 等价的正向作用，等同于计算其规范映射。

> **Entry**: topology.fundamental-group.van-kampen-theorem
@isnad1 id=eq.8h5v.s10.23b5f0306590 from=translated src=- shape=e3ee8d8a vocab=702259ce
-/
@[simp] theorem binaryVanKampenCanonicalEquiv_apply
    {x₀ : X} (U V : Set X) (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : IsPathConnected (U ∩ V))
    (a : binaryVanKampenPushout U V hxU hxV) :
    binaryVanKampenCanonicalEquiv U V hxU hxV hUopen hVopen hcover hU hV hUV a =
      binaryVanKampenCanonicalMap U V hxU hxV a :=
  rfl

/-- 对来自任一覆盖成员的生成元，二元 van Kampen 等价等于该包含映射诱导的基本群同态。

> **Entry**: topology.fundamental-group.van-kampen-theorem
@isnad1 id=eq.8h6v.s11.6eaac7088192 from=translated src=- shape=00f079ac vocab=11a1e073
-/
@[simp] theorem binaryVanKampenCanonicalEquiv_of
    {x₀ : X} (U V : Set X) (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : IsPathConnected (U ∩ V)) (b : Bool)
    (g : FundamentalGroup (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b)) :
    binaryVanKampenCanonicalEquiv U V hxU hxV hUopen hVopen hcover hU hV hUV
        (Monoid.PushoutI.of b g) =
      binaryOpenCoverPieceMaps U V hxU hxV b g := by
  rw [binaryVanKampenCanonicalEquiv_apply, binaryVanKampenCanonicalMap,
    Monoid.PushoutI.lift_of]

end SandronesLibrary.Topology
