/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.AddGroupWithTop
public import Tengoku.Seed.Algebra.Order.Monoid.Unbundled.MinMax
public import Tengoku.Seed.Algebra.Order.Monoid.Unbundled.Pow
public import Tengoku.Seed.Algebra.Order.Monoid.Unbundled.WithTop
public import Tengoku.Seed.Algebra.Ring.Defs
public import Tengoku.Seed.Order.Hom.Basic
public import Tengoku.Seed.Algebra.NeZero

/-!

# Tropical algebraic structures

This file defines algebraic structures of the (min-)tropical numbers, up to the tropical semiring.
Some basic lemmas about conversion from the base type `R` to `Tropical R` are provided, as
well as the expected implementations of tropical addition and tropical multiplication.

## Main declarations

* `Tropical R`: The type synonym of the tropical interpretation of `R`.
    If `[LinearOrder R]`, then addition on `R` is via `min`.
* `Semiring (Tropical R)`: A `LinearOrderedAddCommMonoidWithTop R`
    induces a `Semiring (Tropical R)`. If one solely has `[LinearOrderedAddCommMonoid R]`,
    then the "tropicalization of `R`" would be `Tropical (WithTop R)`.

## Implementation notes

The tropical structure relies on `Top` and `min`. For the max-tropical numbers, use
`OrderDual R`.

Inspiration was drawn from the implementation of `Additive`/`Multiplicative`/`Opposite`,
where a type synonym is created with some barebones API, and quickly made irreducible.

Algebraic structures are provided with as few typeclass assumptions as possible, even though
most references rely on `Semiring (Tropical R)` for building up the whole theory.

## References followed

* https://arxiv.org/pdf/math/0408099.pdf
* https://www.mathenjeans.fr/sites/default/files/sujets/tropical_geometry_-_casagrande.pdf

-/

@[expose] public section

assert_not_exists Nat.instMulOneClass

universe u v

variable (R : Type u)

/-- The tropicalization of a type `R`. -/
def Tropical : Type u :=
  R

variable {R}

namespace Tropical

/-- Reinterpret `x : R` as an element of `Tropical R`.
See `Tropical.tropEquiv` for the equivalence.
-/
def trop : R → Tropical R :=
  id

/-- Reinterpret `x : Tropical R` as an element of `R`.
See `Tropical.tropEquiv` for the equivalence. -/
@[pp_nodot]
def untrop : Tropical R → R :=
  id

/--
@isnad1 id=injectiv.0h1v.s3.5a1a9cbe7b2d from=seed src=0 shape=58762991 vocab=10b53105
-/
theorem trop_injective : Function.Injective (trop : R → Tropical R) := fun _ _ => id

/--
@isnad1 id=injectiv.0h1v.s3.4b14fcfaf302 from=seed src=0 shape=67ee8dff vocab=42c539da
-/
theorem untrop_injective : Function.Injective (untrop : Tropical R → R) := fun _ _ => id

/--
@isnad1 id=iff.0h3v.s4.10517dec2e61 from=seed src=0 shape=f96d73c0 vocab=7b44a908
-/
@[simp]
theorem trop_inj_iff (x y : R) : trop x = trop y ↔ x = y :=
  Iff.rfl

/--
@isnad1 id=iff.0h3v.s4.4bd5fb6970e8 from=seed src=0 shape=9c6a903f vocab=7ffa70b4
-/
@[simp]
theorem untrop_inj_iff (x y : Tropical R) : untrop x = untrop y ↔ x = y :=
  Iff.rfl

/--
@isnad1 id=eq.0h2v.s3.2a7af109ec49 from=seed src=0 shape=efbf31f7 vocab=23db7ea3
-/
@[simp]
theorem trop_untrop (x : Tropical R) : trop (untrop x) = x :=
  rfl

/--
@isnad1 id=eq.0h2v.s3.c48abfb29a26 from=seed src=0 shape=9290c416 vocab=af4881fd
-/
@[simp]
theorem untrop_trop (x : R) : untrop (trop x) = x :=
  rfl

attribute [irreducible] Tropical

/--
@isnad1 id=leftinve.0h1v.s3.035659a149e9 from=seed src=0 shape=1423a3c4 vocab=4baffbed
-/
theorem leftInverse_trop : Function.LeftInverse (trop : R → Tropical R) untrop :=
  trop_untrop

/--
@isnad1 id=rightinv.0h1v.s3.8ad25a26421c from=seed src=0 shape=1423a3c4 vocab=3bb4d5ce
-/
theorem rightInverse_trop : Function.RightInverse (trop : R → Tropical R) untrop :=
  untrop_trop

/-- Reinterpret `x : R` as an element of `Tropical R`.
See `Tropical.tropOrderIso` for the order-preserving equivalence. -/
def tropEquiv : R ≃ Tropical R where
  toFun := trop
  invFun := untrop
  left_inv := untrop_trop
  right_inv := trop_untrop

/--
@isnad1 id=eq.0h1v.s5.52e13d2cf382 from=seed src=0 shape=7373f03a vocab=5ad6e2c5
-/
@[simp]
theorem tropEquiv_coe_fn : (tropEquiv : R → Tropical R) = trop :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.d765fb6c77e4 from=seed src=0 shape=bdf9f795 vocab=a1c88d62
-/
@[simp]
theorem tropEquiv_symm_coe_fn : (tropEquiv.symm : Tropical R → R) = untrop :=
  rfl

/--
@isnad1 id=iff.0h3v.s4.e334a58ed700 from=seed src=0 shape=e6bbf2e1 vocab=23db7ea3
-/
theorem trop_eq_iff_eq_untrop {x : R} {y} : trop x = y ↔ x = untrop y :=
  tropEquiv.eq_symm_apply.symm

/--
@isnad1 id=iff.0h3v.s4.e1fff7ee5f44 from=seed src=0 shape=f156a160 vocab=23db7ea3
-/
theorem untrop_eq_iff_eq_trop {x} {y : R} : untrop x = y ↔ x = trop y :=
  tropEquiv.symm.eq_symm_apply.symm

/--
@isnad1 id=injectiv.0h1v.s3.5a1a9cbe7b2d from=seed src=0 shape=58762991 vocab=10b53105
-/
theorem injective_trop : Function.Injective (trop : R → Tropical R) :=
  tropEquiv.injective

/--
@isnad1 id=injectiv.0h1v.s3.4b14fcfaf302 from=seed src=0 shape=67ee8dff vocab=42c539da
-/
theorem injective_untrop : Function.Injective (untrop : Tropical R → R) :=
  tropEquiv.symm.injective

/--
@isnad1 id=surjecti.0h1v.s3.dd3c11dfdd80 from=seed src=0 shape=58762991 vocab=312d493a
-/
theorem surjective_trop : Function.Surjective (trop : R → Tropical R) :=
  tropEquiv.surjective

/--
@isnad1 id=surjecti.0h1v.s3.fac0f9917988 from=seed src=0 shape=67ee8dff vocab=57ba3c03
-/
theorem surjective_untrop : Function.Surjective (untrop : Tropical R → R) :=
  tropEquiv.symm.surjective

instance [Inhabited R] : Inhabited (Tropical R) :=
  ⟨trop default⟩

/-- Recursing on an `x' : Tropical R` is the same as recursing on an `x : R` reinterpreted
as a term of `Tropical R` via `trop x`. -/
@[simp]
def tropRec {F : Tropical R → Sort v} (h : ∀ X, F (trop X)) : ∀ X, F X := fun X => h (untrop X)

instance [DecidableEq R] : DecidableEq (Tropical R) := fun _ _ =>
  decidable_of_iff _ injective_untrop.eq_iff

section Order

instance instLETropical [LE R] : LE (Tropical R) where le x y := untrop x ≤ untrop y

/--
@isnad1 id=iff.0h3v.s4.0f39cf2b4b40 from=seed src=0 shape=d886d640 vocab=03a00ff7
-/
@[simp]
theorem untrop_le_iff [LE R] {x y : Tropical R} : untrop x ≤ untrop y ↔ x ≤ y :=
  Iff.rfl

instance decidableLE [LE R] [DecidableLE R] : DecidableLE (Tropical R) := fun x y =>
  ‹DecidableLE R› (untrop x) (untrop y)

instance instLTTropical [LT R] : LT (Tropical R) where lt x y := untrop x < untrop y

/--
@isnad1 id=iff.0h3v.s4.20f8db01430e from=seed src=0 shape=d886d640 vocab=f2847336
-/
@[simp]
theorem untrop_lt_iff [LT R] {x y : Tropical R} : untrop x < untrop y ↔ x < y :=
  Iff.rfl

instance decidableLT [LT R] [DecidableLT R] : DecidableLT (Tropical R) := fun x y =>
  ‹DecidableLT R› (untrop x) (untrop y)

instance instPreorderTropical [Preorder R] : Preorder (Tropical R) :=
  { instLETropical, instLTTropical with
    le_refl := fun x => le_refl (untrop x)
    le_trans := fun _ _ _ h h' => le_trans (α := R) h h'
    lt_iff_le_not_ge := fun _ _ => lt_iff_le_not_ge (α := R) }

/-- Reinterpret `x : R` as an element of `Tropical R`, preserving the order. -/
def tropOrderIso [Preorder R] : R ≃o Tropical R :=
  { tropEquiv with map_rel_iff' := untrop_le_iff }

/--
@isnad1 id=eq.0h1v.s5.4dd5141a14a7 from=seed src=0 shape=97d84648 vocab=19ad8f32
-/
@[simp]
theorem tropOrderIso_coe_fn [Preorder R] : (tropOrderIso : R → Tropical R) = trop :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.1f7f879276eb from=seed src=0 shape=8b47d88f vocab=42fd3a9c
-/
@[simp]
theorem tropOrderIso_symm_coe_fn [Preorder R] : (tropOrderIso.symm : Tropical R → R) = untrop :=
  rfl

/--
@isnad1 id=monotone.0h1v.s3.a78b40288944 from=seed src=0 shape=a638af76 vocab=0c9bb5ae
-/
theorem trop_monotone [Preorder R] : Monotone (trop : R → Tropical R) := fun _ _ => id

/--
@isnad1 id=monotone.0h1v.s3.0435670e3001 from=seed src=0 shape=e7497ca1 vocab=7ce99761
-/
theorem untrop_monotone [Preorder R] : Monotone (untrop : Tropical R → R) := fun _ _ => id

instance instPartialOrderTropical [PartialOrder R] : PartialOrder (Tropical R) :=
  { instPreorderTropical with le_antisymm := fun _ _ h h' => untrop_injective (le_antisymm h h') }

instance instZeroTropical [Top R] : Zero (Tropical R) :=
  ⟨trop ⊤⟩

instance instTopTropical [Top R] : Top (Tropical R) :=
  ⟨0⟩

/--
@isnad1 id=eq.0h1v.s4.d156c46aa428 from=seed src=0 shape=dd677712 vocab=2de6b79b
-/
@[simp]
theorem untrop_zero [Top R] : untrop (0 : Tropical R) = ⊤ :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.1411ac0f2fc7 from=seed src=0 shape=ef198ed6 vocab=99171325
-/
@[simp]
theorem trop_top [Top R] : trop (⊤ : R) = 0 :=
  rfl

/--
@isnad1 id=ne.0h2v.s4.846d91e4aa47 from=seed src=0 shape=d4123819 vocab=4d62062d
-/
@[simp]
theorem trop_coe_ne_zero (x : R) : trop (x : WithTop R) ≠ 0 :=
  nofun

/--
@isnad1 id=ne.0h2v.s4.d494b0963175 from=seed src=0 shape=4539a155 vocab=4d62062d
-/
@[simp]
theorem zero_ne_trop_coe (x : R) : 0 ≠ (trop x : Tropical (WithTop R)) :=
  nofun

/--
@isnad1 id=le.0h2v.s5.c8da433ddd39 from=seed src=0 shape=94b50747 vocab=549b64bb
-/
@[simp]
theorem le_zero [LE R] [OrderTop R] (x : Tropical R) : x ≤ 0 :=
  le_top (α := R)

instance [LE R] [OrderTop R] : OrderTop (Tropical R) :=
  { instTopTropical with le_top := fun _ => le_top (α := R) }

variable [LinearOrder R]

/-- Tropical addition is the minimum of two underlying elements of `R`. -/
instance : Add (Tropical R) :=
  ⟨fun x y => trop (min (untrop x) (untrop y))⟩

instance instAddCommSemigroupTropical : AddCommSemigroup (Tropical R) where
  add_assoc _ _ _ := untrop_injective (min_assoc _ _ _)
  add_comm _ _ := untrop_injective (min_comm _ _)

/--
@isnad1 id=eq.0h3v.s5.a1b346c3bef9 from=seed src=0 shape=155cb897 vocab=5216bac3
-/
@[simp]
theorem untrop_add (x y : Tropical R) : untrop (x + y) = min (untrop x) (untrop y) :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.82feb851bbbc from=seed src=0 shape=6621af23 vocab=b7d05003
-/
@[simp]
theorem trop_min (x y : R) : trop (min x y) = trop x + trop y :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.82feb851bbbc from=seed src=0 shape=6621af23 vocab=b7d05003
-/
@[simp]
theorem trop_inf (x y : R) : trop (x ⊓ y) = trop x + trop y :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.3f3a40fc9faf from=seed src=0 shape=7e99ae6d vocab=8fbcb018
-/
theorem trop_add_def (x y : Tropical R) : x + y = trop (min (untrop x) (untrop y)) :=
  rfl

instance instLinearOrderTropical : LinearOrder (Tropical R) :=
  { instPartialOrderTropical with
    le_total := fun a b => le_total (untrop a) (untrop b)
    toDecidableLE := Tropical.decidableLE
    toDecidableEq := Tropical.instDecidableEq
    toDecidableLT := Tropical.decidableLT
    max := fun a b => trop (max (untrop a) (untrop b))
    max_def := fun a b => untrop_injective (by
      simp only [max_def, untrop_le_iff, untrop_trop]; split_ifs <;> simp)
    min := (· + ·)
    min_def := fun a b => untrop_injective (by
      simp only [untrop_add, min_def, untrop_le_iff]; split_ifs <;> simp) }

/--
@isnad1 id=eq.0h3v.s5.298d5a3c54a0 from=seed src=0 shape=3b88c4ec vocab=3c9f846b
-/
@[simp]
theorem untrop_sup (x y : Tropical R) : untrop (x ⊔ y) = untrop x ⊔ untrop y :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.298d5a3c54a0 from=seed src=0 shape=3b88c4ec vocab=3c9f846b
-/
@[simp]
theorem untrop_max (x y : Tropical R) : untrop (max x y) = max (untrop x) (untrop y) :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.750edbdbe3b2 from=seed src=0 shape=60f60dfe vocab=d5046fdf
-/
@[simp]
theorem min_eq_add : (min : Tropical R → Tropical R → Tropical R) = (· + ·) :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.9354d054748d from=seed src=0 shape=5b23f229 vocab=d5046fdf
-/
@[simp]
theorem inf_eq_add : ((· ⊓ ·) : Tropical R → Tropical R → Tropical R) = (· + ·) :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.d7e86e3ce026 from=seed src=0 shape=34360747 vocab=e0eac50e
-/
theorem trop_max_def (x y : Tropical R) : max x y = trop (max (untrop x) (untrop y)) :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.d7e86e3ce026 from=seed src=0 shape=34360747 vocab=e0eac50e
-/
theorem trop_sup_def (x y : Tropical R) : x ⊔ y = trop (untrop x ⊔ untrop y) :=
  rfl

/--
@isnad1 id=eq.1h3v.s5.a1bee15e326c from=seed src=0 shape=6c356cde vocab=2d3859de
-/
@[simp]
theorem add_eq_left ⦃x y : Tropical R⦄ (h : x ≤ y) : x + y = x :=
  untrop_injective (by simpa using h)

/--
@isnad1 id=eq.1h3v.s5.7dcae37be6af from=seed src=0 shape=5d1fabfe vocab=2d3859de
-/
@[simp]
theorem add_eq_right ⦃x y : Tropical R⦄ (h : y ≤ x) : x + y = y :=
  untrop_injective (by simpa using h)

/--
@isnad1 id=iff.0h3v.s5.9532fb0188bb from=seed src=0 shape=9f771d8b vocab=2d3859de
-/
theorem add_eq_left_iff {x y : Tropical R} : x + y = x ↔ x ≤ y := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_left_iff]

/--
@isnad1 id=iff.0h3v.s5.e1659749c3ac from=seed src=0 shape=6595c8cb vocab=2d3859de
-/
theorem add_eq_right_iff {x y : Tropical R} : x + y = y ↔ y ≤ x := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_right_iff]

/--
@isnad1 id=eq.0h2v.s4.c5deaad9b0c8 from=seed src=0 shape=8668caf2 vocab=6fda8b0c
-/
theorem add_self (x : Tropical R) : x + x = x :=
  untrop_injective (min_eq_right le_rfl)

/--
@isnad1 id=iff.0h4v.s6.b4d37fe60c57 from=seed src=0 shape=9bfa1d1e vocab=2d3859de
-/
theorem add_eq_iff {x y z : Tropical R} : x + y = z ↔ x = z ∧ x ≤ y ∨ y = z ∧ y ≤ x := by
  rw [trop_add_def, trop_eq_iff_eq_untrop]
  simp [min_eq_iff]

/--
@isnad1 id=iff.0h3v.s6.7895dcd699c2 from=seed src=0 shape=c25010f6 vocab=cfabe39c
-/
@[simp]
theorem add_eq_zero_iff {a b : Tropical (WithTop R)} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨rfl, le_antisymm (le_zero _) h⟩
    · exact ⟨le_antisymm (le_zero _) h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp

instance instAddCommMonoidTropical [OrderTop R] : AddCommMonoid (Tropical R) :=
  { instZeroTropical, instAddCommSemigroupTropical with
    zero_add := fun _ => untrop_injective (min_top_left _)
    add_zero := fun _ => untrop_injective (min_top_right _)
    nsmul := nsmulRec }

end Order

section Monoid

/-- Tropical multiplication is the addition in the underlying `R`. -/
instance [Add R] : Mul (Tropical R) :=
  ⟨fun x y => trop (untrop x + untrop y)⟩

/--
@isnad1 id=eq.0h3v.s5.181094567082 from=seed src=0 shape=1c5b7bf3 vocab=92411e8d
-/
@[simp]
theorem trop_add [Add R] (x y : R) : trop (x + y) = trop x * trop y :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.350a69f6d398 from=seed src=0 shape=0090f101 vocab=7caf2cc6
-/
@[simp]
theorem untrop_mul [Add R] (x y : Tropical R) : untrop (x * y) = untrop x + untrop y :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.e18565b26d21 from=seed src=0 shape=2e562dcb vocab=5dcad4f7
-/
theorem trop_mul_def [Add R] (x y : Tropical R) : x * y = trop (untrop x + untrop y) :=
  rfl

instance instOneTropical [Zero R] : One (Tropical R) :=
  ⟨trop 0⟩

/--
@isnad1 id=eq.0h1v.s4.89f9b0e07453 from=seed src=0 shape=be87aaac vocab=07ba5f73
-/
@[simp]
theorem trop_zero [Zero R] : trop (0 : R) = 1 :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.05558b998f11 from=seed src=0 shape=c6b7a0b8 vocab=3990f06c
-/
@[simp]
theorem untrop_one [Zero R] : untrop (1 : Tropical R) = 0 :=
  rfl

instance instAddMonoidWithOneTropical [LinearOrder R] [OrderTop R] [Zero R] :
    AddMonoidWithOne (Tropical R) :=
  { instOneTropical, instAddCommMonoidTropical with
    natCast := fun n => if n = 0 then 0 else 1
    natCast_zero := rfl
    natCast_succ := fun n => (untrop_inj_iff _ _).1 (by cases n <;> simp) }

instance [Zero R] : Nontrivial (Tropical (WithTop R)) :=
  ⟨⟨0, 1, trop_injective.ne WithTop.top_ne_coe⟩⟩

instance [Neg R] : Inv (Tropical R) :=
  ⟨fun x => trop (-untrop x)⟩

/--
@isnad1 id=eq.0h2v.s4.7583d55c02e0 from=seed src=0 shape=58efbbcf vocab=6da618ab
-/
@[simp]
theorem untrop_inv [Neg R] (x : Tropical R) : untrop x⁻¹ = -untrop x :=
  rfl

instance [Sub R] : Div (Tropical R) :=
  ⟨fun x y => trop (untrop x - untrop y)⟩

/--
@isnad1 id=eq.0h3v.s5.bee17117cbd5 from=seed src=0 shape=0090f101 vocab=267a5d29
-/
@[simp]
theorem untrop_div [Sub R] (x y : Tropical R) : untrop (x / y) = untrop x - untrop y :=
  rfl

instance instSemigroupTropical [AddSemigroup R] : Semigroup (Tropical R) where
  mul_assoc _ _ _ := untrop_injective (add_assoc _ _ _)

instance instCommSemigroupTropical [AddCommSemigroup R] : CommSemigroup (Tropical R) :=
  { instSemigroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

instance {α : Type*} [SMul α R] : Pow (Tropical R) α where pow x n := trop <| n • untrop x

/--
@isnad1 id=eq.0h4v.s5.092f4df6d61d from=seed src=0 shape=864fb996 vocab=e55e0a21
-/
@[simp]
theorem untrop_pow {α : Type*} [SMul α R] (x : Tropical R) (n : α) :
    untrop (x ^ n) = n • untrop x :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.e9ffe2504208 from=seed src=0 shape=91180b42 vocab=1eee3fd9
-/
@[simp]
theorem trop_smul {α : Type*} [SMul α R] (x : R) (n : α) : trop (n • x) = trop x ^ n :=
  rfl

instance instMulOneClassTropical [AddZeroClass R] : MulOneClass (Tropical R) where
  one_mul _ := untrop_injective <| zero_add _
  mul_one _ := untrop_injective <| add_zero _

instance instMonoidTropical [AddMonoid R] : Monoid (Tropical R) :=
  { instMulOneClassTropical, instSemigroupTropical with
    npow := fun n x => x ^ n
    npow_zero := fun _ => untrop_injective <| by simp
    npow_succ := fun _ _ => untrop_injective <| succ_nsmul _ _ }

/--
@isnad1 id=eq.0h3v.s5.10867684c83a from=seed src=0 shape=cec6eded vocab=8e9a20ef
-/
@[simp]
theorem trop_nsmul [AddMonoid R] (x : R) (n : ℕ) : trop (n • x) = trop x ^ n :=
  rfl

instance instCommMonoidTropical [AddCommMonoid R] : CommMonoid (Tropical R) :=
  { instMonoidTropical, instCommSemigroupTropical with }

instance instGroupTropical [AddGroup R] : Group (Tropical R) :=
  { instMonoidTropical with
    div_eq_mul_inv := fun _ _ => untrop_injective <| by simp [sub_eq_add_neg]
    inv_mul_cancel := fun _ => untrop_injective <| neg_add_cancel _
    zpow := fun n x => trop <| n • untrop x
    zpow_zero' := fun _ => untrop_injective <| zero_zsmul _
    zpow_succ' := fun _ _ => untrop_injective <| SubNegMonoid.zsmul_succ' _ _
    zpow_neg' := fun _ _ => untrop_injective <| SubNegMonoid.zsmul_neg' _ _ }

instance [AddCommGroup R] : CommGroup (Tropical R) :=
  { instGroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

/--
@isnad1 id=eq.0h3v.s5.d667c977f7a6 from=seed src=0 shape=7867c3f1 vocab=d023c715
-/
@[simp]
theorem untrop_zpow [AddGroup R] (x : Tropical R) (n : ℤ) : untrop (x ^ n) = n • untrop x :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.299cb4c941bc from=seed src=0 shape=cec6eded vocab=2861adeb
-/
@[simp]
theorem trop_zsmul [AddGroup R] (x : R) (n : ℤ) : trop (n • x) = trop x ^ n :=
  rfl

end Monoid

section Distrib

/--
@isnad1 id=mulleftm.0h1v.s4.cf1c309388fc from=seed src=0 shape=46b8a2f7 vocab=4077e882
-/
instance mulLeftMono [LE R] [Add R] [AddLeftMono R] :
    MulLeftMono (Tropical R) :=
  ⟨fun _ y z h => add_le_add_right (show untrop y ≤ untrop z from h) _⟩

/--
@isnad1 id=mulright.0h1v.s4.10deb63caaf2 from=seed src=0 shape=46b8a2f7 vocab=d998915c
-/
instance mulRightMono [LE R] [Add R] [AddRightMono R] :
    MulRightMono (Tropical R) :=
  ⟨fun _ y z h => add_le_add_left (show untrop y ≤ untrop z from h) _⟩

/--
@isnad1 id=addleftm.0h1v.s4.bbf3b301f918 from=seed src=0 shape=1666ae32 vocab=9e3e4986
-/
instance addLeftMono [LinearOrder R] : AddLeftMono (Tropical R) :=
  ⟨fun x y z h => by
    rcases le_total x y with hx | hy
    · rw [add_eq_left hx, add_eq_left (hx.trans h)]
    · rw [add_eq_right hy]
      rcases le_total x z with hx | hx
      · rwa [add_eq_left hx]
      · rwa [add_eq_right hx]⟩

/--
@isnad1 id=mullefts.0h1v.s4.68cfd042e84d from=seed src=0 shape=46b8a2f7 vocab=e8770eab
-/
instance mulLeftStrictMono [LT R] [Add R] [AddLeftStrictMono R] :
    MulLeftStrictMono (Tropical R) :=
  ⟨fun _ _ _ h => add_lt_add_right (untrop_lt_iff.2 h) _⟩

/--
@isnad1 id=mulright.0h1v.s4.d4e6336d5d3c from=seed src=0 shape=46b8a2f7 vocab=ea9e0b14
-/
instance mulRightStrictMono [Preorder R] [Add R] [AddRightStrictMono R] :
    MulRightStrictMono (Tropical R) :=
  ⟨fun _ y z h => add_lt_add_left (show untrop y < untrop z from h) _⟩

instance instDistribTropical [LinearOrder R] [Add R] [AddLeftMono R] [AddRightMono R] :
    Distrib (Tropical R) where
  left_distrib _ _ _ := untrop_injective (min_add_add_left _ _ _).symm
  right_distrib _ _ _ := untrop_injective (min_add_add_right _ _ _).symm

/--
@isnad1 id=eq.0h4v.s7.c59bd43531e5 from=seed src=0 shape=54de1e88 vocab=0fd94e26
-/
@[simp]
theorem add_pow [LinearOrder R] [AddMonoid R] [AddLeftMono R] [AddRightMono R]
    (x y : Tropical R) (n : ℕ) :
    (x + y) ^ n = x ^ n + y ^ n := by
  rcases le_total x y with h | h
  · rw [add_eq_left h, add_eq_left (pow_le_pow_left' h _)]
  · rw [add_eq_right h, add_eq_right (pow_le_pow_left' h _)]

end Distrib

section Semiring

variable [LinearOrderedAddCommMonoidWithTop R]

instance : CommSemiring (Tropical R) :=
  { instAddMonoidWithOneTropical,
    instDistribTropical,
    instAddCommMonoidTropical,
    instCommMonoidTropical with
    zero_mul := fun _ => untrop_injective (by simp [top_add])
    mul_zero := fun _ => untrop_injective (by simp [add_top]) }

/--
@isnad1 id=eq.0h3v.s6.1d2d11f10ac1 from=seed src=0 shape=8b66a5f5 vocab=66af935a
-/
@[simp]
theorem succ_nsmul {R} [LinearOrder R] [OrderTop R] (x : Tropical R) (n : ℕ) : (n + 1) • x = x := by
  induction n with
  | zero => simp [one_nsmul]
  | succ n IH => rw [add_nsmul, IH, one_nsmul, add_self]

-- TODO: find/create the right classes to make this hold (for enat, ennreal, etc)
-- Requires `zero_eq_bot` to be true
-- lemma add_eq_zero_iff {a b : tropical R} :
--   a + b = 1 ↔ a = 1 ∨ b = 1 := sorry
/--
@isnad1 id=iff.0h3v.s6.55524018534b from=seed src=0 shape=c25010f6 vocab=f7bd5f56
-/
theorem mul_eq_zero_iff {R : Type*} [AddCommMonoid R]
    {a b : Tropical (WithTop R)} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  simp [← untrop_inj_iff, WithTop.add_eq_top]

instance {R : Type*} [AddCommMonoid R] :
    NoZeroDivisors (Tropical (WithTop R)) :=
  ⟨mul_eq_zero_iff.mp⟩

end Semiring

end Tropical
