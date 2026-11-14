import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Cardinal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 集合论：可数性（ℕ×ℕ 配对、整数枚举、可数并）

本文件为理论条目 `settheory.cardinal.countable-def`（可数 = 可嵌入 ℕ）、
`settheory.cardinal.countable-union`（可数个可数集之并可数）与
`settheory.cardinal.uncountable-real` 补齐可实际计算的例子：`Nat.pair` 的显式配对值、
`ℤ` 的显式枚举（非负 `↦ 2n`、负 `↦ -2n-1`）及其单射性、两个可数集之并的具体实例
（偶数 ∪ 奇数 = ℕ）与 `ℤ = ⋃ n, {-n, n}`。反例两条：`ℕ` 无限却可数（否定「无限 ⟹ 不可数」），
以及 `Fin 3` 的幂集原型（`2^3 = 8 > 3`，不存在满射）。

> **Entry**: examples.settheory.countability
-/

noncomputable section

namespace SandronesLibrary.Examples.SetTheory.Countability

open Set

/-! ## ℕ × ℕ 的显式配对 -/

/-- **真计算**：`Nat.pair 2 3 = 11`（Cantor 配对把 `(2,3)` 编码成 11）。-/
theorem pair_two_three : Nat.pair 2 3 = 11 := by decide

/-- **真计算**：`Nat.unpair 11 = (2, 3)`，即配对编码可以解回来。-/
theorem unpair_eleven : Nat.unpair 11 = (2, 3) := by
  rw [← pair_two_three, Nat.unpair_pair]

/-- **真计算**：走 mathlib 的双射 `Nat.pairEquiv : ℕ × ℕ ≃ ℕ`，`11` 也解回 `(2,3)`。-/
theorem pairEquiv_symm_eleven : Nat.pairEquiv.symm 11 = (2, 3) := by
  rw [Nat.pairEquiv_symm_apply]
  exact unpair_eleven

/-- **配对是单射**：`(a,b) ↦ Nat.pair a b` 不把两个不同的数对送到同一个自然数。-/
theorem pair_injective : Function.Injective (fun p : ℕ × ℕ => Nat.pair p.1 p.2) := by
  intro p q h
  have h' := Nat.pair_eq_pair.mp h
  exact Prod.ext h'.1 h'.2

/-- **正例：`ℕ × ℕ` 可数**——由配对双射 `Nat.pairEquiv` 把 `ℕ × ℕ` 的可数性归到 `ℕ`。-/
theorem countable_prod_nat : Countable (ℕ × ℕ) :=
  Nat.pairEquiv.countable_iff.mpr inferInstance

/-! ## 整数的显式枚举 -/

/-- **整数枚举**：非负 `z ↦ 2z`（偶数），负 `z ↦ -2z - 1`（奇数）。
这是 `ℤ → ℕ` 的显式单射，即把整数一个不漏地编号。-/
def intToNat (z : ℤ) : ℕ :=
  if 0 ≤ z then z.toNat * 2 else (-z).toNat * 2 - 1

/-- **定义展开（非负支）**：`0 ≤ z` 时 `intToNat z = 2 * z.toNat`。-/
theorem intToNat_of_nonneg {z : ℤ} (hz : 0 ≤ z) : intToNat z = z.toNat * 2 := by
  simp [intToNat, hz]

/-- **定义展开（负支）**：`z < 0` 时 `intToNat z = 2 * (-z).toNat - 1`。-/
theorem intToNat_of_neg {z : ℤ} (hz : ¬ 0 ≤ z) : intToNat z = (-z).toNat * 2 - 1 := by
  simp [intToNat, hz]

/-- **真计算**：`intToNat 0 = 0`。-/
theorem intToNat_zero : intToNat 0 = 0 := by
  rw [intToNat_of_nonneg (by norm_num : (0 : ℤ) ≤ 0)]
  norm_num

/-- **真计算**：`intToNat 3 = 6`（非负 `3 ↦ 2·3`）。-/
theorem intToNat_three : intToNat 3 = 6 := by
  rw [intToNat_of_nonneg (by norm_num : (0 : ℤ) ≤ 3)]
  decide

/-- **真计算**：`intToNat (-1) = 1`（负 `-1 ↦ 2·1 - 1`）。-/
theorem intToNat_neg_one : intToNat (-1) = 1 := by
  rw [intToNat_of_neg (by norm_num : ¬ (0 : ℤ) ≤ -1)]
  norm_num

/-- **真计算**：`intToNat (-4) = 7`（负 `-4 ↦ 2·4 - 1`）。-/
theorem intToNat_neg_four : intToNat (-4) = 7 := by
  rw [intToNat_of_neg (by norm_num : ¬ (0 : ℤ) ≤ -4)]
  decide

/-- **枚举是单射**：不同的整数编号不同（偶数支与奇数支也不相交）。-/
theorem intToNat_injective : Function.Injective intToNat := by
  intro z w h
  rcases le_or_gt 0 z with hz | hz <;> rcases le_or_gt 0 w with hw | hw
  · rw [intToNat_of_nonneg hz, intToNat_of_nonneg hw] at h
    have hzw : z.toNat = w.toNat := by omega
    have hz' : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
    have hw' : (w.toNat : ℤ) = w := Int.toNat_of_nonneg hw
    omega
  · rw [intToNat_of_nonneg hz, intToNat_of_neg (not_le.mpr hw)] at h
    have hb : 1 ≤ (-w).toNat := by
      have hw' : (0 : ℤ) < -w := by omega
      have := Int.toNat_of_nonneg (le_of_lt hw')
      omega
    omega
  · rw [intToNat_of_neg (not_le.mpr hz), intToNat_of_nonneg hw] at h
    have hb : 1 ≤ (-z).toNat := by
      have hz' : (0 : ℤ) < -z := by omega
      have := Int.toNat_of_nonneg (le_of_lt hz')
      omega
    omega
  · rw [intToNat_of_neg (not_le.mpr hz), intToNat_of_neg (not_le.mpr hw)] at h
    have hbz : 1 ≤ (-z).toNat := by
      have hz' : (0 : ℤ) < -z := by omega
      have := Int.toNat_of_nonneg (le_of_lt hz')
      omega
    have hbw : 1 ≤ (-w).toNat := by
      have hw' : (0 : ℤ) < -w := by omega
      have := Int.toNat_of_nonneg (le_of_lt hw')
      omega
    have hzw : (-z).toNat = (-w).toNat := by omega
    have hz' : ((-z).toNat : ℤ) = -z := Int.toNat_of_nonneg (by omega)
    have hw' : ((-w).toNat : ℤ) = -w := Int.toNat_of_nonneg (by omega)
    omega

/-- **显式见证**：`intToNat` 就是理论条目「可数 ⟺ 存在到 ℕ 的单射」里的那个单射。-/
theorem exists_injective_int_nat : ∃ f : ℤ → ℕ, Function.Injective f :=
  ⟨intToNat, intToNat_injective⟩

/-- **正例：`ℤ` 可数**——由显式枚举的单射性经理论条目 `countable-def` 得到。-/
theorem countable_int_of_enumeration : Countable ℤ :=
  (SandronesLibrary.SetTheory.Cardinal.countable_iff_injective_nat ℤ).mpr
    ⟨intToNat, intToNat_injective⟩

/-! ## 两个可数集之并 -/

/-- **偶数集**：`ℕ` 中形如 `2k` 的数。-/
def evens : Set ℕ := Set.range fun k : ℕ => 2 * k

/-- **奇数集**：`ℕ` 中形如 `2k+1` 的数。-/
def odds : Set ℕ := Set.range fun k : ℕ => 2 * k + 1

/-- **真计算**：`4` 是偶数（见证 `k = 2`）。-/
theorem four_mem_evens : 4 ∈ evens := ⟨2, by norm_num⟩

/-- **真计算**：`5` 是奇数（见证 `k = 2`）。-/
theorem five_mem_odds : 5 ∈ odds := ⟨2, by norm_num⟩

/-- **真计算**：`1` 不是偶数（`2k = 1` 无自然数解）。-/
theorem one_not_mem_evens : 1 ∉ evens := by
  rintro ⟨k, hk⟩
  dsimp only at hk
  omega

/-- **并覆盖 `ℕ`**：偶数 ∪ 奇数 = 全集（每个自然数非偶即奇）。-/
theorem evens_union_odds : evens ∪ odds = Set.univ := by
  ext n
  constructor
  · intro _; trivial
  · intro _
    rcases Nat.even_or_odd n with h | h
    · left
      rcases h with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      dsimp only
      omega
    · right
      rcases h with ⟨k, hk⟩
      exact ⟨k, hk.symm⟩

/-- **正例：偶数集可数**（它是 `k ↦ 2k` 的像）。-/
theorem countable_evens : evens.Countable := Set.countable_range _

/-- **正例：奇数集可数**（它是 `k ↦ 2k+1` 的像）。-/
theorem countable_odds : odds.Countable := Set.countable_range _

/-- **正例：两个可数集之并可数**（具体实例：偶数 ∪ 奇数 = `ℕ`）。-/
theorem countable_evens_union_odds : (evens ∪ odds).Countable :=
  countable_evens.union countable_odds

/-- **推论**：`ℕ` 可数（把 `evens ∪ odds` 换回全集）。-/
theorem countable_nat_univ : (Set.univ : Set ℕ).Countable := by
  rw [← evens_union_odds]
  exact countable_evens_union_odds

/-- **`ℤ` 的两半**：`n ↦ {-n, n}`（第 `n` 层同时给出 `-n` 与 `n`）。-/
def intHalves (n : ℕ) : Set ℤ := ({-(n : ℤ), (n : ℤ)} : Set ℤ)

/-- **覆盖**：`ℤ = ⋃ n : ℕ, {-n, n}`（每个整数按绝对值落进某一层）。-/
theorem int_univ_eq_iUnion : (Set.univ : Set ℤ) = ⋃ n : ℕ, intHalves n := by
  ext z
  constructor
  · intro _
    rcases le_or_gt 0 z with hz | hz
    · refine Set.mem_iUnion.mpr ⟨z.toNat, ?_⟩
      change z = -(z.toNat : ℤ) ∨ z = (z.toNat : ℤ)
      exact Or.inr (Int.toNat_of_nonneg hz).symm
    · refine Set.mem_iUnion.mpr ⟨(-z).toNat, ?_⟩
      change z = -(((-z).toNat : ℤ)) ∨ z = ((-z).toNat : ℤ)
      have hm : ((-z).toNat : ℤ) = -z := Int.toNat_of_nonneg (by omega)
      exact Or.inl (by rw [hm]; simp)
  · intro _; trivial

/-- **每层可数**：`{-n, n}` 是二元集，因而可数。-/
theorem countable_intHalves (n : ℕ) : (intHalves n).Countable := by
  rw [intHalves]
  exact ((Set.finite_singleton (n : ℤ)).insert (-(n : ℤ))).countable

/-- **正例：`ℤ` 可数（可数并的具体实例）**——把 `ℤ` 写成可数个可数集
`{-n, n}` 的并，再用理论条目 `countable-union`。-/
theorem countable_int_univ : (Set.univ : Set ℤ).Countable := by
  rw [int_univ_eq_iUnion]
  exact SandronesLibrary.SetTheory.Cardinal.countable_iUnion _ countable_intHalves

/-- **推论**：`Countable ℤ`。-/
theorem countable_int : Countable ℤ := Set.countable_univ_iff.mp countable_int_univ

/-! ## 反例：无限集不必不可数 -/

/-- **`ℕ` 无限**（作为全集）。-/
theorem infinite_nat_univ : (Set.univ : Set ℕ).Infinite := Set.infinite_univ

/-- **反例：无限集不必不可数**。`ℕ`（全集）既无限又可数，精确否定命题
「无限 ⟹ 不可数」（形式化为 `∀ s : Set ℕ, s.Infinite → ¬ s.Countable`）。-/
theorem infinite_not_imp_uncountable :
    ¬ (∀ s : Set ℕ, s.Infinite → ¬ s.Countable) := by
  intro h
  exact h Set.univ Set.infinite_univ Set.countable_univ

/-- **辨析：`ℕ` 与 `ℝ` 都无限，但可数性相反**——「无限」确实弱于「不可数」，
`ℝ` 的不可数由理论条目 `uncountable-real` 提供。-/
theorem nat_real_infinite_contrast :
    (Set.univ : Set ℕ).Infinite ∧ (Set.univ : Set ℕ).Countable ∧
      (Set.univ : Set ℝ).Infinite ∧ ¬ (Set.univ : Set ℝ).Countable :=
  ⟨Set.infinite_univ, Set.countable_univ, Set.infinite_univ,
    fun h => SandronesLibrary.SetTheory.Cardinal.uncountable_real (Set.countable_univ_iff.mp h)⟩

/-! ## 反例：幂集严格更大的有限原型 -/

/-- **真计算**：`Fin 3` 的幂集（用特征函数 `Fin 3 → Bool` 表示）有 `2^3 = 8` 个元素。-/
theorem card_powerset_fin_three : Fintype.card (Fin 3 → Bool) = 8 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_num

/-- **真计算**：`8 > 3`——幂集严格大于原集（有限原型）。-/
theorem card_fin_three_lt_powerset : Fintype.card (Fin 3) < Fintype.card (Fin 3 → Bool) := by
  rw [card_powerset_fin_three, Fintype.card_fin]
  norm_num

/-- **真计算（子集枚举）**：`Fin 3` 的全部子集确实有 8 个。-/
theorem card_finset_powerset_fin_three :
    (Finset.univ.powerset : Finset (Finset (Fin 3))).card = 8 := by
  rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- **真计算**：`{0,2}` 是 `Fin 3` 的一个 2 元子集，并且确实出现在 8 个子集之列。-/
theorem subset_zero_two_mem : ({0, 2} : Finset (Fin 3)) ∈ Finset.univ.powerset := by decide

/-- **反例：不存在从 `Fin 3` 到其幂集的满射**（Cantor 定理的有限原型）：
`8 > 3`，所以没有任何满射。-/
theorem no_surjection_fin_three_powerset :
    ¬ ∃ f : Fin 3 → (Fin 3 → Bool), Function.Surjective f := by
  rintro ⟨f, hf⟩
  have hle := Fintype.card_le_of_surjective f hf
  rw [card_powerset_fin_three, Fintype.card_fin] at hle
  omega

/-- **反例（另一方向）：不存在从幂集到 `Fin 3` 的单射**——幂集严格更大的等价说法。-/
theorem no_injection_powerset_fin_three :
    ¬ ∃ g : (Fin 3 → Bool) → Fin 3, Function.Injective g := by
  rintro ⟨g, hg⟩
  have hle := Fintype.card_le_of_injective g hg
  rw [card_powerset_fin_three, Fintype.card_fin] at hle
  omega

end SandronesLibrary.Examples.SetTheory.Countability
