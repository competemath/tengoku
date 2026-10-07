/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Prod
public import Tengoku.Seed.Algebra.GroupWithZero.Commute
public import Tengoku.Seed.Algebra.GroupWithZero.Units.Lemmas
public import Tengoku.Seed.Algebra.GroupWithZero.WithZero

/-!
# Homomorphisms for products of groups with zero

This file defines homomorphisms for products of groups with zero,
which is identified with the `WithZero` of the product of the units of the groups.

The product of groups with zero `WithZero (αˣ × βˣ)` is a
group with zero itself with natural inclusions.

TODO: Give `GrpWithZero` instances of `HasBinaryProducts` and `HasBinaryCoproducts`,
as well as a terminal object.

-/

@[expose] public section

namespace MonoidWithZeroHom

/-- The trivial group-with-zero hom is absorbing for composition.
@isnad1 id=eq.0h5v.s7.4b1471c6a935 from=seed src=0 shape=d582ce51 vocab=46dc3559
-/
@[simp]
lemma one_apply_apply_eq {M₀ N₀ G₀ : Type*}
    [GroupWithZero M₀]
    [MulZeroOneClass N₀] [Nontrivial N₀] [NoZeroDivisors N₀]
    [MulZeroOneClass G₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [DecidablePred fun x : N₀ ↦ x = 0]
    (f : M₀ →*₀ N₀) (x : M₀) :
    (1 : N₀ →*₀ G₀) (f x) = (1 : M₀ →*₀ G₀) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero]
    rwa [map_ne_zero f]

/-- The trivial group-with-zero hom is absorbing for composition.
@isnad1 id=eq.0h4v.s7.c647a8b984a1 from=seed src=0 shape=8c23d8ea vocab=8f8f32b3
-/
@[simp]
lemma one_comp {M₀ N₀ G₀ : Type*}
    [GroupWithZero M₀]
    [MulZeroOneClass N₀] [Nontrivial N₀] [NoZeroDivisors N₀]
    [MulZeroOneClass G₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [DecidablePred fun x : N₀ ↦ x = 0]
    (f : M₀ →*₀ N₀) :
    (1 : N₀ →*₀ G₀).comp f = (1 : M₀ →*₀ G₀) :=
  ext <| one_apply_apply_eq _

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

/-- Given groups with zero `G₀`, `H₀`, the natural inclusion ordered homomorphism from
`G₀` to `WithZero (G₀ˣ × H₀ˣ)`, which is the group with zero that can be identified
as their product. -/
def inl [DecidablePred fun x : G₀ ↦ x = 0] : G₀ →*₀ WithZero (G₀ˣ × H₀ˣ) :=
  (WithZero.map' (.inl _ _)).comp
    (.ofClass WithZero.withZeroUnitsEquiv.symm)

/-- Given groups with zero `G₀`, `H₀`, the natural inclusion ordered homomorphism from
`H₀` to `WithZero (G₀ˣ × H₀ˣ)`, which is the group with zero that can be identified
as their product. -/
def inr [DecidablePred fun x : H₀ ↦ x = 0] : H₀ →*₀ WithZero (G₀ˣ × H₀ˣ) :=
  (WithZero.map' (.inr _ _)).comp
    (.ofClass WithZero.withZeroUnitsEquiv.symm)

/-- Given groups with zero `G₀`, `H₀`, the natural projection homomorphism from
`WithZero (G₀ˣ × H₀ˣ)` to `G₀`, which is the group with zero that can be identified
as their product. -/
def fst : WithZero (G₀ˣ × H₀ˣ) →*₀ G₀ :=
  WithZero.lift' ((Units.coeHom _).comp (.fst ..))

/-- Given groups with zero `G₀`, `H₀`, the natural projection homomorphism from
`WithZero (G₀ˣ × H₀ˣ)` to `H₀`, which is the group with zero that can be identified
as their product. -/
def snd : WithZero (G₀ˣ × H₀ˣ) →*₀ H₀ :=
  WithZero.lift' ((Units.coeHom _).comp (.snd ..))

variable {G₀ H₀}

/--
@isnad1 id=eq.0h3v.s8.75ce5e5b6cfa from=seed src=0 shape=0daea79e vocab=0285949a
-/
@[simp]
lemma inl_apply_unit [DecidablePred fun x : G₀ ↦ x = 0] (x : G₀ˣ) :
    inl G₀ H₀ x = ((x, (1 : H₀ˣ)) : WithZero (G₀ˣ × H₀ˣ)) := by
  simp [inl]

/--
@isnad1 id=eq.0h3v.s8.12b5ada40c34 from=seed src=0 shape=4e307e59 vocab=330a6310
-/
@[simp]
lemma inr_apply_unit [DecidablePred fun x : H₀ ↦ x = 0] (x : H₀ˣ) :
    inr G₀ H₀ x = (((1 : G₀ˣ), x) : WithZero (G₀ˣ × H₀ˣ)) := by
  simp [inr]

/--
@isnad1 id=eq.0h3v.s7.2437ab1ac064 from=seed src=0 shape=b067bef0 vocab=4104125e
-/
@[simp] lemma fst_apply_coe (x : G₀ˣ × H₀ˣ) : fst G₀ H₀ x = x.fst := by rfl
/--
@isnad1 id=eq.0h3v.s7.a69a6833f0d3 from=seed src=0 shape=aa3efed6 vocab=433aa412
-/
@[simp] lemma snd_apply_coe (x : G₀ˣ × H₀ˣ) : snd G₀ H₀ x = x.snd := by rfl

/--
@isnad1 id=eq.0h3v.s8.0fa68541c862 from=seed src=0 shape=41c199f7 vocab=be7d6585
-/
@[simp]
theorem fst_inl [DecidablePred fun x : G₀ ↦ x = 0] (x : G₀) :
    fst _ H₀ (inl _ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, fst, inl]

/--
@isnad1 id=eq.0h2v.s7.f56abd55a22c from=seed src=0 shape=15a3e6d0 vocab=d1874a94
-/
@[simp]
theorem fst_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (fst ..).comp (inl G₀ H₀) = .id _ :=
  ext fun _ ↦ fst_inl _

/--
@isnad1 id=eq.0h2v.s7.85f1b64e58ba from=seed src=0 shape=23ba9ca8 vocab=cd22595a
-/
@[simp]
theorem snd_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (snd ..).comp (inl G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, snd, inl]

/--
@isnad1 id=eq.1h3v.s8.c7d16d7c30aa from=seed src=0 shape=ff7a0b76 vocab=07b52c30
-/
theorem snd_inl_apply_of_ne_zero [DecidablePred fun x : G₀ ↦ x = 0] {x : G₀} (hx : x ≠ 0) :
    snd _ _ (inl _ H₀ x) = 1 := by
  rw [← comp_apply, snd_comp_inl, one_apply_of_ne_zero hx]

/--
@isnad1 id=eq.0h2v.s7.0ad998e60dad from=seed src=0 shape=aac50c46 vocab=3af1b7e7
-/
@[simp]
theorem fst_comp_inr [DecidablePred fun x : H₀ ↦ x = 0] :
    (fst ..).comp (inr G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, fst, inr]

/--
@isnad1 id=eq.1h3v.s8.22611b9c239d from=seed src=0 shape=4c4834a0 vocab=0ce11cae
-/
theorem fst_inr_apply_of_ne_zero [DecidablePred fun x : H₀ ↦ x = 0] {x : H₀} (hx : x ≠ 0) :
    fst _ _ (inr G₀ _ x) = 1 := by
  rw [← comp_apply, fst_comp_inr, one_apply_of_ne_zero hx]

/--
@isnad1 id=eq.0h3v.s8.13c2008616fb from=seed src=0 shape=bef2bc22 vocab=9d48f1d2
-/
@[simp]
theorem snd_inr [DecidablePred fun x : H₀ ↦ x = 0] (x : H₀) :
    snd _ _ (inr G₀ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, snd, inr]

/--
@isnad1 id=eq.0h2v.s7.84c90f10fe3a from=seed src=0 shape=8bb4aa4f vocab=43a70571
-/
@[simp]
theorem snd_comp_inr [DecidablePred fun x : H₀ ↦ x = 0] :
    (snd ..).comp (inr G₀ H₀) = .id _ :=
  ext fun _ ↦ snd_inr _

/--
@isnad1 id=injectiv.0h2v.s7.2f50758827bb from=seed src=0 shape=7b6a2fa8 vocab=302aec58
-/
lemma inl_injective [DecidablePred fun x : G₀ ↦ x = 0] :
    Function.Injective (inl G₀ H₀) :=
  Function.HasLeftInverse.injective ⟨fst .., fun _ ↦ by simp⟩

/--
@isnad1 id=injectiv.0h2v.s7.c2ba1be1c0fb from=seed src=0 shape=2ee5b096 vocab=e0152554
-/
lemma inr_injective [DecidablePred fun x : H₀ ↦ x = 0] :
    Function.Injective (inr G₀ H₀) :=
  Function.HasLeftInverse.injective ⟨snd .., fun _ ↦ by simp⟩

/--
@isnad1 id=surjecti.0h2v.s7.a9847253dafc from=seed src=0 shape=68ebc108 vocab=6b9e7561
-/
lemma fst_surjective : Function.Surjective (fst G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨inl .., fun _ ↦ by simp⟩

/--
@isnad1 id=surjecti.0h2v.s7.6d694e475db9 from=seed src=0 shape=aee4a9a8 vocab=32ea8721
-/
lemma snd_surjective : Function.Surjective (snd G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨inr .., fun _ ↦ by simp⟩

variable [DecidablePred fun x : G₀ ↦ x = 0] [DecidablePred fun x : H₀ ↦ x = 0]

/--
@isnad1 id=eq.0h4v.s9.dd1daaed9143 from=seed src=0 shape=66732d78 vocab=19b343b6
-/
theorem inl_mul_inr_eq_mk_of_unit (m : G₀ˣ) (n : H₀ˣ) :
    (inl G₀ H₀ m * inr G₀ H₀ n) = (m, n) := by
  simp [inl, WithZero.withZeroUnitsEquiv, inr, ← WithZero.coe_mul]

/--
@isnad1 id=commute.0h4v.s8.ffe96396a933 from=seed src=0 shape=dc1f13d1 vocab=299ef483
-/
theorem commute_inl_inr (m : G₀) (n : H₀) : Commute (inl G₀ H₀ m) (inr G₀ H₀ n) := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit m <;>
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit n <;>
  simp [inl, inr, WithZero.withZeroUnitsEquiv, commute_iff_eq, ← WithZero.coe_mul]

end MonoidWithZeroHom
