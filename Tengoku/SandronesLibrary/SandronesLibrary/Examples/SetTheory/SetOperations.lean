/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Set
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 集合论：有限集上的并、交、差、补与 De Morgan 计算

本文件为理论条目 `settheory.set.ext`、`settheory.set.subset.definition`、
`settheory.set.operations.inter-distrib`、`settheory.set.operations.complement-union`、
`settheory.set.operations.complement-inter` 与 `settheory.set.operations.diff-inter-complement`
补齐具体计算例：在有限全集 `Fin 5 = {0,1,2,3,4}` 上取三个命名集合 `A = {1,2,3}`、
`B = {3,4}`、`C = {2,4}`，逐元素算出并、交、差、补、分配律与德摩根律的两侧，
并给出“`A ∪ B = A ∪ C` 推不出 `B = C`”的精确反例（具体见证 + 一般否定命题），
以及“差集不可交换”的辨析。

> **Entry**: examples.settheory.set-operations
-/

noncomputable section

namespace SandronesLibrary.Examples.SetTheory.SetOperations

open Set

/-- **有限全集**：本文件的补集都在 `Fin 5 = {0,1,2,3,4}` 中取，
`U = univ` 把这个全集命名下来，便于把 `Aᶜ` 读作“从 U 中挖掉 A”。-/
abbrev U : Set (Fin 5) := Set.univ

/-- **具体集合 A**：`A = {1,2,3}`。-/
abbrev A : Set (Fin 5) := {1, 2, 3}

/-- **具体集合 B**：`B = {3,4}`。-/
abbrev B : Set (Fin 5) := {3, 4}

/-- **具体集合 C**：`C = {2,4}`。`B` 与 `C` 只差一个元素（`3` 对 `2`），
而两者都落在 `A` 里——这正是并集反例的机关。-/
abbrev C : Set (Fin 5) := {2, 4}

/-- **定义展开（A）**：逐元素读出 `A` 的成员条件。
@isnad1 id=iff.0h1v.s6.690e54eff42b from=translated src=- shape=2006dd71 vocab=5c159595
-/
theorem mem_A_iff (x : Fin 5) : x ∈ A ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  fin_cases x <;> simp [A]

/-- **基本性质**：`0 ∉ A`。这是“定义展开后核对一个具体元素”的最小计算。
@isnad1 id=not.0h0v.s5.9463c60132fa from=translated src=- shape=a3bf8aff vocab=5c159595
-/
theorem zero_notMem_A : (0 : Fin 5) ∉ A := by decide

/-- **基本性质**：`4 ∉ A`。
@isnad1 id=not.0h0v.s5.a06a8d37f3ac from=translated src=- shape=a3bf8aff vocab=5c159595
-/
theorem four_notMem_A : (4 : Fin 5) ∉ A := by decide

/-- **子集的具体核对**：`A ⊆ {1,2,3,4}`。按子集的逐元素刻画
（理论条目 `settheory.set.subset.definition`）对 `Fin 5` 的五个元素逐一验证。
@isnad1 id=le.0h0v.s7.99c62a329b83 from=translated src=- shape=94185e28 vocab=2b5bd6ee
-/
theorem subset_A_1234 : A ⊆ ({1, 2, 3, 4} : Set (Fin 5)) := by
  intro x hx
  fin_cases x <;> simp [A] at hx ⊢

/-- **反例（子集方向）**：`B ⊄ A`。具体见证：`4 ∈ B` 但 `4 ∉ A`
（后者即上面的 `four_notMem_A`）。
@isnad1 id=not.0h0v.s4.f774166d0ec4 from=translated src=- shape=26b21442 vocab=63872dfb
-/
theorem not_subset_B_A : ¬ B ⊆ A := by
  intro h
  exact four_notMem_A (h (by decide : (4 : Fin 5) ∈ B))

/-- **并集逐元素计算**：`A ∪ B = {1,2,3,4}`。
@isnad1 id=eq.0h0v.s7.2e42a378dbbb from=translated src=- shape=a04bc107 vocab=a30c460b
-/
theorem union_A_B : A ∪ B = ({1, 2, 3, 4} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, B]

/-- **并集逐元素计算**：`B ∪ C = {2,3,4}`。
@isnad1 id=eq.0h0v.s7.6923ae395c92 from=translated src=- shape=20a0abf7 vocab=3acccfc1
-/
theorem union_B_C : B ∪ C = ({2, 3, 4} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [B, C]

/-- **交集逐元素计算**：`A ∩ B = {3}`。
@isnad1 id=eq.0h0v.s5.b08aea948e1d from=translated src=- shape=833c2182 vocab=86cb2093
-/
theorem inter_A_B : A ∩ B = ({3} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, B]

/-- **交集逐元素计算**：`A ∩ C = {2}`。
@isnad1 id=eq.0h0v.s5.1cd5a35f9bae from=translated src=- shape=833c2182 vocab=268b2a37
-/
theorem inter_A_C : A ∩ C = ({2} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, C]

/-- **差集逐元素计算**：`A \ B = {1,2}`（从 A 中划掉 B 的元素 `3`）。
@isnad1 id=eq.0h0v.s6.95c69e0d06b3 from=translated src=- shape=feb9dc5a vocab=338746eb
-/
theorem diff_A_B : A \ B = ({1, 2} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, B]

/-- **差集逐元素计算**：`B \ A = {4}`。
@isnad1 id=eq.0h0v.s5.06dbacb213ed from=translated src=- shape=833c2182 vocab=e6587476
-/
theorem diff_B_A : B \ A = ({4} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, B]

/-- **差集逐元素计算**：`C \ A = {4}`。
@isnad1 id=eq.0h0v.s5.ab72cc9ab33c from=translated src=- shape=833c2182 vocab=7e0127dd
-/
theorem diff_C_A : C \ A = ({4} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, C]

/-- **补集逐元素计算**：`Aᶜ = {0,4}`（在有限全集 `Fin 5` 中）。
@isnad1 id=eq.0h0v.s6.4e3089e021b1 from=translated src=- shape=a97c9933 vocab=23a6a07e
-/
theorem compl_A : Aᶜ = ({0, 4} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A]

/-- **补集逐元素计算**：`Bᶜ = {0,1,2}`。
@isnad1 id=eq.0h0v.s7.ea23fbf58453 from=translated src=- shape=d0763aaf vocab=d21401b0
-/
theorem compl_B : Bᶜ = ({0, 1, 2} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [B]

/-- **补集与全集差的关系**：`Aᶜ = U \ A`。把“在有限全集中取补”与“从 U 中作差”
两种读法对上（`U = univ`，两者定义相同；`Aᶜ` 的值已由上面的 `compl_A` 算出）。
@isnad1 id=eq.0h0v.s5.5840f6199d01 from=translated src=- shape=1e5758b5 vocab=722f7e30
-/
theorem compl_A_eq_diff_U : Aᶜ = U \ A := by
  ext x
  fin_cases x <;> simp [U, A]

/-- **分配律左侧计算**：`A ∩ (B ∪ C) = {1,2,3} ∩ {2,3,4} = {2,3}`。
@isnad1 id=eq.0h0v.s6.6d05a91676e5 from=translated src=- shape=a35c919b vocab=6dd4cffd
-/
theorem inter_union_distrib_eval : A ∩ (B ∪ C) = ({2, 3} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, B, C]

/-- **分配律右侧计算**：`(A ∩ B) ∪ (A ∩ C) = {3} ∪ {2} = {2,3}`。
@isnad1 id=eq.0h0v.s7.4eed2dac2579 from=translated src=- shape=03b3fa6a vocab=6dd4cffd
-/
theorem inter_union_distrib_eval' : (A ∩ B) ∪ (A ∩ C) = ({2, 3} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, B, C]

/-- **交对并的分配律（具体验证）**：`A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`，
两侧各自逐元素算成 `{2,3}` 后相接（理论条目 `settheory.set.operations.inter-distrib` 的实例）。
@isnad1 id=eq.0h0v.s6.648682d4b675 from=translated src=- shape=b11ec5c2 vocab=dc6a83d8
-/
theorem inter_distrib_instance : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
  inter_union_distrib_eval.trans inter_union_distrib_eval'.symm

/-- **De Morgan（并）左侧计算**：`(A ∪ B)ᶜ = {0}`。
@isnad1 id=eq.0h0v.s6.2621400ab594 from=translated src=- shape=872c3882 vocab=e94285cb
-/
theorem compl_union_eval : (A ∪ B)ᶜ = ({0} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, B]

/-- **De Morgan（并）右侧计算**：`Aᶜ ∩ Bᶜ = {0,4} ∩ {0,1,2} = {0}`。
@isnad1 id=eq.0h0v.s6.d3a5782c9123 from=translated src=- shape=bc153529 vocab=bd9b2983
-/
theorem compl_inter_compl_eval : Aᶜ ∩ Bᶜ = ({0} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, B]

/-- **De Morgan 律（并）的具体验证**：`(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`。
不是引用一般定理，而是把两侧各自逐元素算成 `{0}` 后相接
（理论条目 `settheory.set.operations.complement-union` 的实例）。
@isnad1 id=eq.0h0v.s6.28ca15adfdc1 from=translated src=- shape=dfd45662 vocab=267c81b1
-/
theorem de_morgan_union : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ :=
  compl_union_eval.trans compl_inter_compl_eval.symm

/-- **De Morgan（交）左侧计算**：`(A ∩ B)ᶜ = {0,1,2,4}`。
@isnad1 id=eq.0h0v.s7.a47dc2a7598e from=translated src=- shape=018ca432 vocab=cc341365
-/
theorem compl_inter_eval : (A ∩ B)ᶜ = ({0, 1, 2, 4} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, B]

/-- **De Morgan（交）右侧计算**：`Aᶜ ∪ Bᶜ = {0,4} ∪ {0,1,2} = {0,1,2,4}`。
@isnad1 id=eq.0h0v.s7.09022d2ae33a from=translated src=- shape=6f9048a5 vocab=a820d882
-/
theorem compl_union_compl_eval : Aᶜ ∪ Bᶜ = ({0, 1, 2, 4} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, B]

/-- **De Morgan 律（交）的具体验证**：`(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`
（理论条目 `settheory.set.operations.complement-inter` 的实例）。
@isnad1 id=eq.0h0v.s6.9bccb55d18dc from=translated src=- shape=dfd45662 vocab=267c81b1
-/
theorem de_morgan_inter : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ :=
  compl_inter_eval.trans compl_union_compl_eval.symm

/-- **差集公式的具体验证**：`A ∩ Bᶜ = {1,2}`，与 `A \ B = {1,2}` 相接得
`A \ B = A ∩ Bᶜ`（理论条目 `settheory.set.operations.diff-inter-complement` 的实例）。
@isnad1 id=eq.0h0v.s6.a452fafbad26 from=translated src=- shape=126c4d7b vocab=cc341365
-/
theorem inter_compl_eval : A ∩ Bᶜ = ({1, 2} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, B]

/-- **差集与补集的关系（具体验证）**：`A \ B = A ∩ Bᶜ`。
@isnad1 id=eq.0h0v.s5.167d669e31ff from=translated src=- shape=d5f1803a vocab=16d81c3c
-/
theorem diff_eq_inter_compl : A \ B = A ∩ Bᶜ :=
  diff_A_B.trans inter_compl_eval.symm

/-- **辨析（差集不可交换）**：`A \ B = {1,2}` 而 `B \ A = {4}`，故两者不相等。
具体见证：`1 ∈ A \ B` 但 `1 ∉ B \ A`。
@isnad1 id=ne.0h0v.s5.8ffffbe90a2f from=translated src=- shape=a0cdb5b9 vocab=769af5b7
-/
theorem diff_not_comm : A \ B ≠ B \ A := by
  intro h
  have h1 : (1 : Fin 5) ∈ B \ A := h ▸ (by decide : (1 : Fin 5) ∈ A \ B)
  exact (by decide : (1 : Fin 5) ∉ B \ A) h1

/-- **并集逐元素计算**：`A ∪ C = {1,2,3,4}`（与 `A ∪ B` 的结果相同）。
@isnad1 id=eq.0h0v.s7.5cd50f9e50e2 from=translated src=- shape=a04bc107 vocab=66abbf1d
-/
theorem union_A_C : A ∪ C = ({1, 2, 3, 4} : Set (Fin 5)) := by
  ext x
  fin_cases x <;> simp [A, C]

/-- **反例的前件**：`A ∪ B = A ∪ C`（两侧都算成 `{1,2,3,4}`）。
@isnad1 id=eq.0h0v.s5.0b9419febe58 from=translated src=- shape=0c313277 vocab=bd5a33b2
-/
theorem union_A_B_eq_union_A_C : A ∪ B = A ∪ C :=
  union_A_B.trans union_A_C.symm

/-- **反例的后件之否定**：`B ≠ C`。具体见证：`3 ∈ B` 但 `3 ∉ C`。
@isnad1 id=ne.0h0v.s3.d64a0a505d95 from=translated src=- shape=2a30f11b vocab=d9472587
-/
theorem B_ne_C : B ≠ C := by
  intro h
  have h3 : (3 : Fin 5) ∈ C := h ▸ (by decide : (3 : Fin 5) ∈ B)
  exact (by decide : (3 : Fin 5) ∉ C) h3

/-- **反例（精确陈述）**：存在 `A B C` 使 `A ∪ B = A ∪ C` 成立而 `B = C` 不成立。
它反驳“并集运算可以从左边消去”的误命题。
@isnad1 id=ex.0h0v.s6.7a9178e725c1 from=translated src=- shape=595c37a8 vocab=e9ce36c6
-/
theorem union_eq_but_ne : ∃ A B C : Set (Fin 5), A ∪ B = A ∪ C ∧ B ≠ C :=
  ⟨A, B, C, union_A_B_eq_union_A_C, B_ne_C⟩

/-- **反例（一般否定命题）**：在 `Fin 5` 上，全称命题
`∀ A B C, A ∪ B = A ∪ C → B = C` 为假。
@isnad1 id=not.0h0v.s6.1de1ef19ec19 from=translated src=- shape=860507d2 vocab=e9ce36c6
-/
theorem union_right_cancel_not_valid :
    ¬ (∀ A B C : Set (Fin 5), A ∪ B = A ∪ C → B = C) := by
  intro h
  exact B_ne_C (h A B C union_A_B_eq_union_A_C)

/-- **反例的“为什么”**：`B \ A = C \ A = {4}`——`B` 与 `C` 的差别（`3` 对 `2`）
全部落在 `A` 内，被 `A` 吸收，所以并集看不出差别。
@isnad1 id=eq.0h0v.s5.a30868d2a0c6 from=translated src=- shape=0e98ad4e vocab=d472ffe5
-/
theorem diff_B_A_eq_diff_C_A : B \ A = C \ A :=
  diff_B_A.trans diff_C_A.symm

/-! ## 理论接口的直接调用

上面的每一条计算都是逐元素做出来的；这一节把 `SetTheory/Set.lean` 的**一般定理**直接作用在
具体集合 `A`、`B`、`C` 上，确认它们给出同一结论。这样本 Entry 与理论条目之间有一条真实的
**声明级依赖**（不只是文档上的对应），上述理论条目也由此获得一个公开的上层使用者。
-/

/-- **外延性原理**（`settheory.set.ext`）作用在具体集合上：`A = B ↔ ∀ x, x ∈ A ↔ x ∈ B`。
@isnad1 id=iff.0h0v.s6.9a3dd3cec5e4 from=translated src=- shape=76a13cfb vocab=861ebb4d
-/
theorem ext_instance : A = B ↔ ∀ x : Fin 5, x ∈ A ↔ x ∈ B :=
  SandronesLibrary.SetTheory.Set.set_ext A B

/-- **子集的逐元素刻画**（`settheory.set.subset.definition`）作用在具体集合上。
@isnad1 id=iff.0h0v.s6.6b6b8bdf9a8b from=translated src=- shape=d4817dee vocab=321fcc95
-/
theorem subset_iff_instance : A ⊆ B ↔ ∀ x : Fin 5, x ∈ A → x ∈ B :=
  SandronesLibrary.SetTheory.Set.subset_iff_forall_mem A B

/-- **交对并的分配律**（`settheory.set.operations.inter-distrib`）作用在具体集合上。
@isnad1 id=eq.0h0v.s6.648682d4b675 from=translated src=- shape=b11ec5c2 vocab=dc6a83d8
-/
theorem inter_distrib_via_theory : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
  SandronesLibrary.SetTheory.Set.inter_distrib_left A B C

/-- **德摩根律（并）**（`settheory.set.operations.complement-union`）作用在具体集合上。
@isnad1 id=eq.0h0v.s6.28ca15adfdc1 from=translated src=- shape=dfd45662 vocab=267c81b1
-/
theorem de_morgan_union_via_theory : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ :=
  SandronesLibrary.SetTheory.Set.complement_union A B

/-- **德摩根律（交）**（`settheory.set.operations.complement-inter`）作用在具体集合上。
@isnad1 id=eq.0h0v.s6.9bccb55d18dc from=translated src=- shape=dfd45662 vocab=267c81b1
-/
theorem de_morgan_inter_via_theory : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ :=
  SandronesLibrary.SetTheory.Set.complement_inter A B

/-- **差集与补集**（`settheory.set.operations.diff-inter-complement`）作用在具体集合上。
@isnad1 id=eq.0h0v.s5.167d669e31ff from=translated src=- shape=d5f1803a vocab=16d81c3c
-/
theorem diff_eq_inter_compl_via_theory : A \ B = A ∩ Bᶜ :=
  SandronesLibrary.SetTheory.Set.diff_inter_complement A B

end SandronesLibrary.Examples.SetTheory.SetOperations
