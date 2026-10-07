/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.GroupWithZero.ProdHom
public import Tengoku.Seed.Algebra.Order.Group.Equiv
public import Tengoku.Seed.Algebra.Order.Monoid.Lex
public import Tengoku.Seed.Algebra.Order.Hom.MonoidWithZero
public import Tengoku.Seed.Data.Prod.Lex

/-!
# Order homomorphisms for products of linearly ordered groups with zero

This file defines order homomorphisms for products of linearly ordered groups with zero,
which is identified with the `WithZero` of the lexicographic product of the units of the groups.

The product of linearly ordered groups with zero `WithZero (αˣ ×ₗ βˣ)` is a
linearly ordered group with zero itself with natural inclusions but only one projection.
One has to work with the lexicographic product of the units `αˣ ×ₗ βˣ` since otherwise,
the plain product `αˣ × βˣ` would not be linearly ordered.

## TODO

Create the "LinOrdCommGrpWithZero" category.

-/

@[expose] public section

namespace MonoidWithZeroHom

variable {M₀ N₀ : Type*}

/--
@isnad1 id=monotone.0h2v.s8.64ea442ed8e1 from=seed src=0 shape=e73c0a9f vocab=2d6b63dd
-/
lemma inl_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] : Monotone (inl M₀ N₀) := by
  refine (WithZero.map'_mono MonoidHom.inl_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]

/--
@isnad1 id=strictmo.0h2v.s8.6bf6f727aa88 from=seed src=0 shape=e73c0a9f vocab=8a86a06f
-/
lemma inl_strictMono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [PartialOrder N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] : StrictMono (inl M₀ N₀) :=
  inl_mono.strictMono_of_injective inl_injective

/--
@isnad1 id=monotone.0h2v.s8.243c856878a8 from=seed src=0 shape=af15daad vocab=e583364d
-/
lemma inr_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀]
    [DecidablePred fun x : N₀ ↦ x = 0] : Monotone (inr M₀ N₀) := by
  refine (WithZero.map'_mono MonoidHom.inr_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]

/--
@isnad1 id=strictmo.0h2v.s8.642dabe488b7 from=seed src=0 shape=af15daad vocab=8f098a90
-/
lemma inr_strictMono [GroupWithZero M₀] [PartialOrder M₀] [LinearOrderedCommGroupWithZero N₀]
    [DecidablePred fun x : N₀ ↦ x = 0] : StrictMono (inr M₀ N₀) :=
  inr_mono.strictMono_of_injective inr_injective

/--
@isnad1 id=monotone.0h2v.s8.b3c1ceb2991f from=seed src=0 shape=c24f662b vocab=4203d1fe
-/
lemma fst_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀] :
    Monotone (fst M₀ N₀) := by
  refine WithZero.forall.mpr ?_
  simp +contextual [WithZero.forall, Prod.le_def]


/--
@isnad1 id=monotone.0h2v.s8.08862f5214d5 from=seed src=0 shape=c7fe4cd9 vocab=c828bf7a
-/
lemma snd_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀] :
    Monotone (snd M₀ N₀) := by
  refine WithZero.forall.mpr ?_
  simp [WithZero.forall, Prod.le_def]

end MonoidWithZeroHom

namespace LinearOrderedCommGroupWithZero

variable (α β : Type*) [LinearOrderedCommGroupWithZero α] [LinearOrderedCommGroupWithZero β]

open MonoidWithZeroHom

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given linearly ordered groups with zero M, N, the natural inclusion ordered homomorphism from
M to `WithZero (Mˣ ×ₗ Nˣ)`, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def inl : α →*₀o WithZero (αˣ ×ₗ βˣ) where
  __ := (WithZero.map' (toLexMulEquiv ..).toMonoidHom).comp (inl α β)
  monotone' := by simpa using (WithZero.map'_mono (Prod.Lex.toLex_mono)).comp inl_mono

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given linearly ordered groups with zero M, N, the natural inclusion ordered homomorphism from
N to `WithZero (Mˣ ×ₗ Nˣ)`, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def inr : β →*₀o WithZero (αˣ ×ₗ βˣ) where
  __ := (WithZero.map' (toLexMulEquiv ..).toMonoidHom).comp (inr α β)
  monotone' := by simpa using (WithZero.map'_mono (Prod.Lex.toLex_mono)).comp inr_mono

/-- Given linearly ordered groups with zero M, N, the natural projection ordered homomorphism from
`WithZero (Mˣ ×ₗ Nˣ)` to M, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def fst : WithZero (αˣ ×ₗ βˣ) →*₀o α where
  __ := (fst α β).comp (WithZero.map' (toLexMulEquiv (αˣ × βˣ)).symm.toMonoidHom)
  monotone' := by
    -- this can't rely on `Monotone.comp` since `ofLex` is not monotone
    intro x y
    cases x <;>
    cases y
    · simp
    · simp
    · simp
    · simpa using Prod.Lex.monotone_fst _ _

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h2v.s8.cd2d5d933d22 from=seed src=0 shape=c5d5cb6d vocab=7578a76b
-/
@[simp]
theorem fst_comp_inl : (fst _ _).comp (inl α β) = .id α := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp

variable {α β}

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h3v.s10.591608dee8c0 from=seed src=0 shape=435071af vocab=d888df5d
-/
lemma inl_eq_coe_inlₗ {m : α} (hm : m ≠ 0) :
    inl α β m = OrderMonoidHom.inlₗ αˣ βˣ (Units.mk0 _ hm) := by
  lift m to αˣ using isUnit_iff_ne_zero.mpr hm
  simp

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h3v.s10.996ce6a44b79 from=seed src=0 shape=94021765 vocab=d7d67231
-/
lemma inr_eq_coe_inrₗ {n : β} (hn : n ≠ 0) :
    inr α β n = OrderMonoidHom.inrₗ αˣ βˣ (Units.mk0 _ hn) := by
  lift n to βˣ using isUnit_iff_ne_zero.mpr hn
  simp

/--
@isnad1 id=eq.2h4v.s10.65995a7c81ed from=seed src=0 shape=4f2f8e4a vocab=e663b12f
-/
theorem inl_mul_inr_eq_coe_toLex {m : α} {n : β} (hm : m ≠ 0) (hn : n ≠ 0) :
    inl α β m * inr α β n = toLex (Units.mk0 _ hm, Units.mk0 _ hn) := by
  rw [inl_eq_coe_inlₗ hm, inr_eq_coe_inrₗ hn,
      ← WithZero.coe_mul, OrderMonoidHom.inlₗ_mul_inrₗ_eq_toLex]

end LinearOrderedCommGroupWithZero
