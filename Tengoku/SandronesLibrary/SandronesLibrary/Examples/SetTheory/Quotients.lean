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

/-- **定义展开**：`modFive a b` 就是余数相等 `a % 5 = b % 5`。-/
theorem modFive_iff_emod (a b : ℤ) : modFive a b ↔ a % 5 = b % 5 := Iff.rfl

/-- **等价刻画**：模 5 同类 ⟺ `5` 整除两数之差。-/
theorem modFive_iff_dvd (a b : ℤ) : modFive a b ↔ (5 : ℤ) ∣ b - a :=
  Int.modEq_iff_dvd

/-- **真计算**：`(7 : ℤ) % 5 = 2`。-/
theorem seven_emod_five : (7 : ℤ) % 5 = 2 := by norm_num

/-- **显式判定同类**：`7` 与 `2` 模 5 同类（余数都是 `2`，真计算）。-/
theorem seven_modFive_two : modFive 7 2 := by
  rw [modFive_iff_emod]
  norm_num

/-- **显式判定同类（负代表元）**：`-3` 与 `2` 模 5 同类（`-3 % 5 = 2`）。-/
theorem neg_three_modFive_two : modFive (-3) 2 := by
  rw [modFive_iff_emod]
  norm_num

/-- **显式判定不同类**：`7` 与 `1` 模 5 不同类（余数 `2 ≠ 1`）。-/
theorem seven_not_modFive_one : ¬ modFive 7 1 := by
  rw [modFive_iff_emod]
  norm_num

/-- **不同代表元给同一商元素**：`⟦7⟧ = ⟦2⟧`。-/
theorem quotient_mk_seven_eq_two :
    Quotient.mk modFive (7 : ℤ) = Quotient.mk modFive 2 :=
  Quotient.sound seven_modFive_two

/-- **辨析（核心反例）：商元素相等不决定代表元相等**。商映射把 `7` 与 `2` 送到同一个
商元素，但 `(7 : ℤ) ≠ 2`；这精确否定「商元素唯一决定代表元」——
即否定「`Quotient.mk` 是单射」。-/
theorem quotient_mk_eq_not_imp_eq :
    Quotient.mk modFive (7 : ℤ) = Quotient.mk modFive 2 ∧ (7 : ℤ) ≠ 2 :=
  ⟨quotient_mk_seven_eq_two, by norm_num⟩

/-- **反例：模 5 的商映射不是单射**。`7 ≠ 2` 却给出同一个商元素，
所以 `Quotient.mk modFive` 不是单射。-/
theorem quotient_mk_not_injective : ¬ Function.Injective (Quotient.mk modFive) := by
  intro h
  exact (by norm_num : (7 : ℤ) ≠ 2) (h quotient_mk_seven_eq_two)

/-- **对照：等号关系的商映射是单射**。非单射的来源是等价关系（把不同元素钉在一起），
不是 `Quotient.mk` 这个构造本身。-/
theorem quotient_mk_eq_injective : Function.Injective (Quotient.mk (Setoid.ker (id : ℤ → ℤ))) := by
  intro a b h
  exact Quotient.exact h

/-- **正例：等价类相等 ⟺ 同类**（复用理论条目 `equivalence-class-eq`）。-/
theorem quotient_mk_eq_iff (a b : ℤ) :
    Quotient.mk modFive a = Quotient.mk modFive b ↔ modFive a b :=
  SandronesLibrary.SetTheory.Relations.equivalence_class_eq modFive a b

/-- **正例：商映射满射**（复用理论条目 `quotient-surj`）。-/
theorem quotient_mk_surjective : Function.Surjective (Quotient.mk modFive) :=
  SandronesLibrary.SetTheory.Relations.quotient_surjective modFive

/-- **满射的具体见证**：商元素 `⟦7⟧` 还有一个不同的代表元 `2`。-/
theorem exists_other_rep :
    ∃ z : ℤ, z ≠ 7 ∧ Quotient.mk modFive z = Quotient.mk modFive 7 :=
  ⟨2, by norm_num, quotient_mk_seven_eq_two.symm⟩

/-- **同一现象的 `ZMod` 形式**：`(7 : ZMod 5) = 2`。-/
theorem seven_eq_two_zmod_five : (7 : ZMod 5) = 2 := by decide

/-- **辨析：`<` 不是等价关系**（不满足自反性）。-/
theorem lt_not_equivalence : ¬ Equivalence (· < · : ℤ → ℤ → Prop) := by
  intro h
  exact lt_irrefl (0 : ℤ) (h.refl 0)

/-- **辨析：没有以 `<` 为 `≈` 的 `Setoid`**——并非任何二元关系都能充当商构造的等价关系。-/
theorem not_exists_setoid_lt : ¬ ∃ s : Setoid ℤ, ∀ a b : ℤ, s a b ↔ a < b := by
  rintro ⟨s, hs⟩
  have h00 : s 0 0 := s.refl 0
  exact lt_irrefl (0 : ℤ) ((hs 0 0).mp h00)

end SandronesLibrary.Examples.SetTheory.Quotients
