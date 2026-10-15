/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
module

public import Tengoku
/-!
# LeanPool.OrderPQ.MonoidHom
-/

@[expose] public section

/--
@isnad1 id=eq.1h3v.s4.bfc6d4ddbc4e from=translated src=- shape=225b6c52 vocab=66357236
-/
lemma Set.nat_card_range_of_injective {α β : Type*} (f : α → β) (hf : Function.Injective f) :
    Nat.card (range f) = Nat.card α :=
  Eq.symm <| Nat.card_congr <| Equiv.ofInjective f hf

namespace MonoidHom

end MonoidHom

section OfGenerator

variable {α β : Type*} [Group α] [Group β]

section Lemmas

/--
@isnad1 id=iff.0h3v.s5.f3a0d6eb9cdf from=translated src=- shape=6aef7d5c vocab=03c8be80
-/
@[to_additive]
theorem zpow_eq_self_iff_modEq {x : α} {n : ℤ} : x ^ n = x ↔ n ≡ 1 [ZMOD orderOf x] := by
  convert zpow_eq_zpow_iff_modEq .. using 2
  exact zpow_one x |>.symm

/--
@isnad1 id=modeq.2h4v.s4.7775f39b810f from=translated src=- shape=cca836a0 vocab=bf3fb486
-/
lemma Int.modEq_of_modEq_dvd {n m a b : ℤ} (h : m ∣ n) : a ≡ b [ZMOD n] → a ≡ b [ZMOD m] :=
  Int.modEq_iff_dvd.mpr ∘ Int.dvd_trans h ∘ Int.modEq_iff_dvd.mp

/--
@isnad1 id=eq.0h1v.s5.bed8b1a487fa from=translated src=- shape=55ed9c0f vocab=c3b0c15c
-/
@[to_additive]
lemma Subgroup.nat_card_top : Nat.card (⊤ : Subgroup α) = Nat.card α :=
  Nat.card_congr (Equiv.Set.univ α)

end Lemmas

variable {x : α} (hx : ∀ a : α, a ∈ Subgroup.zpowers x)
include hx

@[to_additive]
lemma MonoidHom.eq_of_apply_eq (f₁ f₂ : α →* β) (h2 : f₁ x = f₂ x) : f₁ = f₂ := by
  ext y
  rw [← (hx y).choose_spec, map_zpow, map_zpow, h2]

@[to_additive]
lemma MulEquiv.eq_of_apply_eq (f₁ f₂ : α ≃* β) (h2 : f₁ x = f₂ x) : f₁ = f₂ :=
  MulEquiv.toMonoidHom_injective <| MonoidHom.eq_of_apply_eq hx _ _ h2

@[to_additive]
private lemma orderOf_eq_nat_card : orderOf x = Nat.card α :=
  Nat.card_zpowers x ▸ (Subgroup.eq_top_iff' _).mpr hx ▸ Subgroup.nat_card_top

variable {y : β} (hy : orderOf y ∣ Nat.card α)
include hy

@[to_additive]
private noncomputable def MonoidHom.ofGeneratorAndImage : α →* β where
  toFun a := y ^ (hx a).choose
  map_one' := by
    have hx' := (hx 1).choose_spec
    simp only [← orderOf_dvd_iff_zpow_eq_one, orderOf_eq_nat_card hx] at hx' ⊢
    exact Int.dvd_trans (Int.ofNat_dvd.mpr hy) hx'
  map_mul' a1 a2 := by
    have h := (hx (a1 * a2)).choose_spec
    nth_rewrite 3 [← (hx a1).choose_spec, ← (hx a2).choose_spec] at h
    rw [← zpow_add, zpow_eq_zpow_iff_modEq] at h ⊢
    exact Int.modEq_of_modEq_dvd (Int.ofNat_dvd.mpr hy) (orderOf_eq_nat_card hx ▸ h)

/--
@isnad1 id=ex.2h4v.s7.67da01536bb5 from=translated src=- shape=65ae95ca vocab=3cddb959
-/
@[to_additive]
lemma MonoidHom.exists_of_generator_and_image : ∃ f : α →* β, f x = y := by
  use MonoidHom.ofGeneratorAndImage hx hy
  change y ^ (hx x).choose = y
  have h := (hx x).choose_spec
  rw [zpow_eq_self_iff_modEq] at h ⊢
  exact Int.modEq_of_modEq_dvd (Int.ofNat_dvd.mpr hy) (orderOf_eq_nat_card hx ▸ h)

end OfGenerator
