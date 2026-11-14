import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Relations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 集合论：等价关系与商（模 5 同余类）

本文件为理论条目 `settheory.set.relations.equivalence-class-eq`（等价类相等 ⟺ 元素等价）
与 `settheory.set.relations.quotient-surj`（商映射满射）补齐可检查的例子：模 5 同余作为
`ℤ` 上 `Setoid` 的命名实例、两个代表元同类的显式判定（`7 ≡ 2 [ZMOD 5]`）、商映射满射的
显式见证，以及辨析「不同代表元给出同一个商元素」的精确反例。末尾用 `<` 说明并非任何
二元关系都能充当 `Setoid` 的 `≈`。

> **Entry**: examples.settheory.quotients
-/

noncomputable section

namespace SandronesLibrary.Examples.SetTheory.Quotients

open Set

/-- **模 5 同余关系作为 `ℤ` 上的 `Setoid`**：`a ≈ b` 即 `Int.ModEq 5 a b`
（`a % 5 = b % 5`）。三律由 `Int.ModEq` 的 `refl`/`symm`/`trans` 提供。-/
def modFive : Setoid ℤ where
  r a b := Int.ModEq 5 a b
  iseqv := ⟨Int.ModEq.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **定义展开**：`modFive a b` 就是余数相等 `a % 5 = b % 5`。
@isnad1 id=iff.0h2v.s5.aedbe7179d41 from=translated src=- shape=f5a4d344 vocab=e7139398
-/
theorem modFive_iff_emod (a b : ℤ) : modFive a b ↔ a % 5 = b % 5 := Iff.rfl

/-- **等价刻画**：模 5 同类 ⟺ `5` 整除两数之差。
@isnad1 id=iff.0h2v.s4.0e9b7fe0aad8 from=translated src=- shape=5e7bf502 vocab=56880c48
-/
theorem modFive_iff_dvd (a b : ℤ) : modFive a b ↔ (5 : ℤ) ∣ b - a :=
  Int.modEq_iff_dvd

/-- **真计算**：`(7 : ℤ) % 5 = 2`。
@isnad1 id=eq.0h0v.s4.e6139befe41e from=translated src=- shape=7f6a8e6b vocab=b6f7664a
-/
theorem seven_emod_five : (7 : ℤ) % 5 = 2 := by norm_num

/-- **显式判定同类**：`7` 与 `2` 模 5 同类（余数都是 `2`，真计算）。
@isnad1 id=r.0h0v.s3.87bb13e2e937 from=translated src=- shape=91ed63c4 vocab=25e126b9
-/
theorem seven_modFive_two : modFive 7 2 := by
  rw [modFive_iff_emod]
  norm_num

/-- **显式判定同类（负代表元）**：`-3` 与 `2` 模 5 同类（`-3 % 5 = 2`）。
@isnad1 id=r.0h0v.s4.ad559f24a8c4 from=translated src=- shape=d8786388 vocab=69b6d115
-/
theorem neg_three_modFive_two : modFive (-3) 2 := by
  rw [modFive_iff_emod]
  norm_num

/-- **显式判定不同类**：`7` 与 `1` 模 5 不同类（余数 `2 ≠ 1`）。
@isnad1 id=not.0h0v.s3.1f68f4179473 from=translated src=- shape=3a68cc91 vocab=25e126b9
-/
theorem seven_not_modFive_one : ¬ modFive 7 1 := by
  rw [modFive_iff_emod]
  norm_num

/-- **不同代表元给同一商元素**：`⟦7⟧ = ⟦2⟧`。
@isnad1 id=eq.0h0v.s4.147cad6aa767 from=translated src=- shape=828f1d73 vocab=f67f9df1
-/
theorem quotient_mk_seven_eq_two :
    Quotient.mk modFive (7 : ℤ) = Quotient.mk modFive 2 :=
  Quotient.sound seven_modFive_two

/-- **辨析（核心反例）：商元素相等不决定代表元相等**。商映射把 `7` 与 `2` 送到同一个
商元素，但 `(7 : ℤ) ≠ 2`；这精确否定「商元素唯一决定代表元」——
即否定「`Quotient.mk` 是单射」。
@isnad1 id=and.0h0v.s5.5a3cc0cff7ad from=translated src=- shape=a140992a vocab=f67f9df1
-/
theorem quotient_mk_eq_not_imp_eq :
    Quotient.mk modFive (7 : ℤ) = Quotient.mk modFive 2 ∧ (7 : ℤ) ≠ 2 :=
  ⟨quotient_mk_seven_eq_two, by norm_num⟩

/-- **反例：模 5 的商映射不是单射**。`7 ≠ 2` 却给出同一个商元素，
所以 `Quotient.mk modFive` 不是单射。
@isnad1 id=not.0h0v.s3.00ac7ab634c8 from=translated src=- shape=4fffdac2 vocab=e587c1d2
-/
theorem quotient_mk_not_injective : ¬ Function.Injective (Quotient.mk modFive) := by
  intro h
  exact (by norm_num : (7 : ℤ) ≠ 2) (h quotient_mk_seven_eq_two)

/-- **对照：等号关系的商映射是单射**。非单射的来源是等价关系（把不同元素钉在一起），
不是 `Quotient.mk` 这个构造本身。
@isnad1 id=injectiv.0h0v.s4.5c670d922b66 from=translated src=- shape=adcb81f1 vocab=476b1210
-/
theorem quotient_mk_eq_injective : Function.Injective (Quotient.mk (Setoid.ker (id : ℤ → ℤ))) := by
  intro a b h
  exact Quotient.exact h

/-- **正例：等价类相等 ⟺ 同类**（复用理论条目 `equivalence-class-eq`）。
@isnad1 id=iff.0h2v.s4.4b16691f2b5f from=translated src=- shape=e0a4393b vocab=9663f574
-/
theorem quotient_mk_eq_iff (a b : ℤ) :
    Quotient.mk modFive a = Quotient.mk modFive b ↔ modFive a b :=
  SandronesLibrary.SetTheory.Relations.equivalence_class_eq modFive a b

/-- **正例：商映射满射**（复用理论条目 `quotient-surj`）。
@isnad1 id=surjecti.0h0v.s3.d75e4b8c8be1 from=translated src=- shape=5163d57e vocab=e6d55a3e
-/
theorem quotient_mk_surjective : Function.Surjective (Quotient.mk modFive) :=
  SandronesLibrary.SetTheory.Relations.quotient_surjective modFive

/-- **满射的具体见证**：商元素 `⟦7⟧` 还有一个不同的代表元 `2`。
@isnad1 id=ex.0h0v.s4.312267e9cd85 from=translated src=- shape=98c640b6 vocab=f67f9df1
-/
theorem exists_other_rep :
    ∃ z : ℤ, z ≠ 7 ∧ Quotient.mk modFive z = Quotient.mk modFive 7 :=
  ⟨2, by norm_num, quotient_mk_seven_eq_two.symm⟩

/-- **同一现象的 `ZMod` 形式**：`(7 : ZMod 5) = 2`。
@isnad1 id=eq.0h0v.s6.cde757aa5875 from=translated src=- shape=f9dc6c31 vocab=c87b9854
-/
theorem seven_eq_two_zmod_five : (7 : ZMod 5) = 2 := by decide

/-- **辨析：`<` 不是等价关系**（不满足自反性）。
@isnad1 id=not.0h0v.s3.54eb8dfe1821 from=translated src=- shape=ceb74afe vocab=8c1663d3
-/
theorem lt_not_equivalence : ¬ Equivalence (· < · : ℤ → ℤ → Prop) := by
  intro h
  exact lt_irrefl (0 : ℤ) (h.refl 0)

/-- **辨析：没有以 `<` 为 `≈` 的 `Setoid`**——并非任何二元关系都能充当商构造的等价关系。
@isnad1 id=not.0h0v.s4.155e463af254 from=translated src=- shape=309d4dbd vocab=06acef09
-/
theorem not_exists_setoid_lt : ¬ ∃ s : Setoid ℤ, ∀ a b : ℤ, s a b ↔ a < b := by
  rintro ⟨s, hs⟩
  have h00 : s 0 0 := s.refl 0
  exact lt_irrefl (0 : ℤ) ((hs 0 0).mp h00)

end SandronesLibrary.Examples.SetTheory.Quotients
