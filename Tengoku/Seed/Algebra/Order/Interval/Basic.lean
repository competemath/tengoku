/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Ring.Prod
public import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
public import Tengoku.Seed.Algebra.Order.Ring.Canonical
public import Tengoku.Seed.Order.Interval.Basic
public import Tengoku.Seed.Tactic.Positivity.Core
public import Tengoku.Seed.Algebra.Group.Pointwise.Set.Basic

/-!
# Interval arithmetic

This file defines arithmetic operations on intervals and prove their correctness. Note that this is
full precision operations. The essentials of float operations can be found
in `Data.FP.Basic`. We have not yet integrated these with the rest of the library.
-/

@[expose] public section


open Function Set

open scoped Pointwise

universe u

variable {ι α : Type*}

/-! ### One/zero -/


section One

section Preorder

variable [Preorder α] [One α]

@[to_additive]
instance : One (NonemptyInterval α) :=
  ⟨NonemptyInterval.pure 1⟩

@[to_additive]
instance : One (Interval α) :=
  ⟨(1 : NonemptyInterval α)⟩

namespace NonemptyInterval

/--
@isnad1 id=eq.0h1v.s5.de369a4f607f from=seed src=0 shape=8a1f9532 vocab=41500a44
-/
@[to_additive (attr := simp) toProd_zero]
theorem toProd_one : (1 : NonemptyInterval α).toProd = 1 :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.72eeb324daec from=seed src=0 shape=db66ae8c vocab=cee29e52
-/
@[to_additive]
theorem fst_one : (1 : NonemptyInterval α).fst = 1 :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.aa09b86395ca from=seed src=0 shape=db66ae8c vocab=06d5567e
-/
@[to_additive]
theorem snd_one : (1 : NonemptyInterval α).snd = 1 :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.d00691372550 from=seed src=0 shape=9168166a vocab=29386253
-/
@[to_additive (attr := push_cast, simp)]
theorem coe_one_interval : ((1 : NonemptyInterval α) : Interval α) = 1 :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.ed4e19e5d94c from=seed src=0 shape=0dd0c4c7 vocab=59659ddd
-/
@[to_additive (attr := simp)]
theorem pure_one : pure (1 : α) = 1 :=
  rfl

end NonemptyInterval

namespace Interval

/--
@isnad1 id=eq.0h1v.s5.1541e0180303 from=seed src=0 shape=0dd0c4c7 vocab=091d22ad
-/
@[to_additive (attr := simp)]
theorem pure_one : pure (1 : α) = 1 :=
  rfl

/--
@isnad1 id=ne.0h1v.s5.57eaf1ca87fd from=seed src=0 shape=e7e04754 vocab=43ddc5c9
-/
@[to_additive (attr := simp)] lemma one_ne_bot : (1 : Interval α) ≠ ⊥ := pure_ne_bot

/--
@isnad1 id=ne.0h1v.s5.2dbadf836e15 from=seed src=0 shape=041122ce vocab=43ddc5c9
-/
@[to_additive (attr := simp)] lemma bot_ne_one : (⊥ : Interval α) ≠ 1 := bot_ne_pure

end Interval

end Preorder

section PartialOrder

variable [PartialOrder α] [One α]

namespace NonemptyInterval

/--
@isnad1 id=eq.0h1v.s5.a23f7e2e4783 from=seed src=0 shape=7c4558f8 vocab=29eca7a3
-/
@[to_additive (attr := simp)]
theorem coe_one : ((1 : NonemptyInterval α) : Set α) = 1 :=
  coe_pure _

/--
@isnad1 id=mem.0h1v.s5.7e504f4c0caf from=seed src=0 shape=68ea3ba8 vocab=4e7faf76
-/
@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : NonemptyInterval α) :=
  ⟨le_rfl, le_rfl⟩

end NonemptyInterval

namespace Interval

/--
@isnad1 id=eq.0h1v.s5.8fd52d72feae from=seed src=0 shape=7c4558f8 vocab=4dc743e4
-/
@[to_additive (attr := simp)]
theorem coe_one : ((1 : Interval α) : Set α) = 1 :=
  Icc_self _

/--
@isnad1 id=mem.0h1v.s5.c3643ded1c43 from=seed src=0 shape=68ea3ba8 vocab=62a8d13c
-/
@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Interval α) :=
  ⟨le_rfl, le_rfl⟩

end Interval

end PartialOrder

end One

/-!
### Addition/multiplication

Note that this multiplication does not apply to `ℚ` or `ℝ`.
-/


section Mul

variable [Preorder α] [Mul α] [MulLeftMono α] [MulRightMono α]

@[to_additive]
instance : Mul (NonemptyInterval α) :=
  ⟨fun s t => ⟨s.toProd * t.toProd, mul_le_mul' s.fst_le_snd t.fst_le_snd⟩⟩

@[to_additive]
instance : Mul (Interval α) :=
  ⟨WithBot.map₂ (· * ·)⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a b : α)

/--
@isnad1 id=eq.0h3v.s6.99be8b760fa8 from=seed src=0 shape=1cdf39fc vocab=62abe6d1
-/
@[to_additive (attr := simp) toProd_add]
theorem toProd_mul : (s * t).toProd = s.toProd * t.toProd :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.6757df5c17c7 from=seed src=0 shape=8dc96502 vocab=6bbb6b78
-/
@[to_additive]
theorem fst_mul : (s * t).fst = s.fst * t.fst :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.003a1afc9600 from=seed src=0 shape=8dc96502 vocab=b5af2d48
-/
@[to_additive]
theorem snd_mul : (s * t).snd = s.snd * t.snd :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.fe4f6d1f8784 from=seed src=0 shape=9976bca4 vocab=2c1d3554
-/
@[to_additive (attr := simp)]
theorem coe_mul_interval : (↑(s * t) : Interval α) = s * t :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.fc4f92831c64 from=seed src=0 shape=882e32ec vocab=db835c07
-/
@[to_additive (attr := simp)]
theorem pure_mul_pure : pure a * pure b = pure (a * b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

/--
@isnad1 id=eq.0h2v.s6.8df1fb71a56a from=seed src=0 shape=bbc9aff1 vocab=a94c48d1
-/
@[to_additive (attr := simp)]
theorem bot_mul : ⊥ * t = ⊥ :=
  WithBot.map₂_bot_left _ _

/--
@isnad1 id=eq.0h2v.s6.54c8df79494a from=seed src=0 shape=b72f0bc6 vocab=a94c48d1
-/
@[to_additive (attr := simp)]
theorem mul_bot : s * ⊥ = ⊥ :=
  WithBot.map₂_bot_right _ _

-- simp can already prove `add_bot`
attribute [simp] mul_bot

end Interval

end Mul

/-! ### Powers -/

section Pow

variable [Monoid α] [Preorder α]

@[to_additive]
instance NonemptyInterval.instPow [MulLeftMono α] [MulRightMono α] :
    Pow (NonemptyInterval α) ℕ :=
  ⟨fun s n => ⟨s.toProd ^ n, pow_le_pow_left' s.fst_le_snd _⟩⟩

namespace NonemptyInterval

variable [MulLeftMono α] [MulRightMono α]
variable (s : NonemptyInterval α) (a : α) (n : ℕ)

/--
@isnad1 id=eq.0h3v.s6.c3a3a2d912bb from=seed src=0 shape=cee036c6 vocab=98130a1a
-/
@[to_additive (attr := simp) toProd_nsmul]
theorem toProd_pow : (s ^ n).toProd = s.toProd ^ n :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.46258a30e12d from=seed src=0 shape=5ec72485 vocab=28d7431a
-/
@[to_additive]
theorem fst_pow : (s ^ n).fst = s.fst ^ n :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.e4f33b70e488 from=seed src=0 shape=5ec72485 vocab=e90b5c8e
-/
@[to_additive]
theorem snd_pow : (s ^ n).snd = s.snd ^ n :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.614a6de364e2 from=seed src=0 shape=42546e2f vocab=dcc33ce7
-/
@[to_additive (attr := simp)]
theorem pure_pow : pure a ^ n = pure (a ^ n) :=
  rfl

end NonemptyInterval

end Pow

namespace NonemptyInterval

@[to_additive]
instance commMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    CommMonoid (NonemptyInterval α) :=
  fast_instance% NonemptyInterval.toProd_injective.commMonoid _ toProd_one toProd_mul toProd_pow

end NonemptyInterval

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
instance Interval.mulOneClass [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    MulOneClass (Interval α) where
  one_mul s :=
    (WithBot.map₂_coe_left _ _ _).trans <| by
      simp_rw [one_mul, ← Function.id_def, WithBot.map_id, id]
  mul_one s :=
    (WithBot.map₂_coe_right _ _ _).trans <| by
      simp_rw [mul_one, ← Function.id_def, WithBot.map_id, id]

@[to_additive]
instance Interval.commMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    CommMonoid (Interval α) where
  mul_comm := fun _ _ => Option.map₂_comm mul_comm
  mul_assoc := fun _ _ _ => Option.map₂_assoc mul_assoc

namespace NonemptyInterval

/--
@isnad1 id=eq.0h3v.s6.f3ce67eedd7f from=seed src=0 shape=5e9cfbf9 vocab=0e6caaa0
-/
@[to_additive]
theorem coe_pow_interval [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
    (s : NonemptyInterval α) (n : ℕ) :
    ↑(s ^ n) = (s : Interval α) ^ n :=
  map_pow (⟨⟨(↑), coe_one_interval⟩, coe_mul_interval⟩ : NonemptyInterval α →* Interval α) _ _

-- simp can already prove `coe_nsmul_interval`
attribute [simp] coe_pow_interval

end NonemptyInterval

namespace Interval

variable [CommMonoid α] [Preorder α] [IsOrderedMonoid α] {n : ℕ}

/--
@isnad1 id=eq.1h2v.s6.165896c9df52 from=seed src=0 shape=a8dd0705 vocab=b474f570
-/
@[to_additive]
theorem bot_pow : ∀ {n : ℕ}, n ≠ 0 → (⊥ : Interval α) ^ n = ⊥
  | 0, h => (h rfl).elim
  | Nat.succ n, _ => mul_bot (⊥ ^ n)

end Interval

/-!
### Semiring structure

When `α` is a canonically `OrderedCommSemiring`, the previous `+` and `*` on `NonemptyInterval α`
form a `CommSemiring`.
-/

section NatCast
variable [Preorder α] [NatCast α]

namespace NonemptyInterval

instance : NatCast (NonemptyInterval α) where
  natCast n := pure <| Nat.cast n

/--
@isnad1 id=eq.0h2v.s5.40fb49b71d44 from=seed src=0 shape=11245f6b vocab=e26b701a
-/
theorem fst_natCast (n : ℕ) : (n : NonemptyInterval α).fst = n := rfl

/--
@isnad1 id=eq.0h2v.s5.c882a28cb32b from=seed src=0 shape=11245f6b vocab=de7d53d2
-/
theorem snd_natCast (n : ℕ) : (n : NonemptyInterval α).snd = n := rfl

/--
@isnad1 id=eq.0h2v.s5.0a5a6705f2bb from=seed src=0 shape=c107bffb vocab=0916e03d
-/
@[simp]
theorem pure_natCast (n : ℕ) : pure (n : α) = n := rfl

end NonemptyInterval

end NatCast

namespace NonemptyInterval

instance [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α] :
    CommSemiring (NonemptyInterval α) :=
  fast_instance% NonemptyInterval.toProd_injective.commSemiring _
    toProd_zero toProd_one toProd_add toProd_mul (swap toProd_nsmul) toProd_pow (fun _ => rfl)

end NonemptyInterval

/-!
### Subtraction

Subtraction is defined more generally than division so that it applies to `ℕ` (and `OrderedDiv`
is not a thing and probably should not become one).

However, this means that we can't use `to_additive` in this section.
-/


section Sub

variable [Preorder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] [AddLeftMono α]

instance : Sub (NonemptyInterval α) :=
  ⟨fun s t => ⟨(s.fst - t.snd, s.snd - t.fst), tsub_le_tsub s.fst_le_snd t.fst_le_snd⟩⟩

instance : Sub (Interval α) :=
  ⟨WithBot.map₂ Sub.sub⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) {a b : α}

/--
@isnad1 id=eq.0h3v.s6.d0582170a1f4 from=seed src=0 shape=2331c0d2 vocab=4d420ab9
-/
@[simp]
theorem fst_sub : (s - t).fst = s.fst - t.snd :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.9619fc8d7d06 from=seed src=0 shape=2331c0d2 vocab=4d420ab9
-/
@[simp]
theorem snd_sub : (s - t).snd = s.snd - t.fst :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.d2ec7ad347d4 from=seed src=0 shape=96b7569e vocab=9908422b
-/
@[simp]
theorem coe_sub_interval : (↑(s - t) : Interval α) = s - t :=
  rfl

/--
@isnad1 id=mem.2h5v.s6.8742f5999a99 from=seed src=0 shape=6c6013d3 vocab=532da0b6
-/
theorem sub_mem_sub (ha : a ∈ s) (hb : b ∈ t) : a - b ∈ s - t :=
  ⟨tsub_le_tsub ha.1 hb.2, tsub_le_tsub ha.2 hb.1⟩

/--
@isnad1 id=eq.0h3v.s6.ae0738cec1b2 from=seed src=0 shape=8834a4dd vocab=594fbd8d
-/
@[simp]
theorem pure_sub_pure (a b : α) : pure a - pure b = pure (a - b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

/--
@isnad1 id=eq.0h2v.s6.a6c05b3c098c from=seed src=0 shape=7dc543e2 vocab=efb769f1
-/
@[simp]
theorem bot_sub : ⊥ - t = ⊥ :=
  WithBot.map₂_bot_left _ _

/--
@isnad1 id=eq.0h2v.s6.11c41fbb6aad from=seed src=0 shape=a0a98e92 vocab=efb769f1
-/
@[simp]
theorem sub_bot : s - ⊥ = ⊥ :=
  WithBot.map₂_bot_right _ _

end Interval

end Sub

/-!
### Division in ordered groups

Note that this division does not apply to `ℚ` or `ℝ`.
-/


section Div

variable [Preorder α] [CommGroup α] [MulLeftMono α]

instance : Div (NonemptyInterval α) :=
  ⟨fun s t => ⟨(s.fst / t.snd, s.snd / t.fst), div_le_div'' s.fst_le_snd t.fst_le_snd⟩⟩

instance : Div (Interval α) :=
  ⟨WithBot.map₂ (· / ·)⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a b : α)

/--
@isnad1 id=eq.0h3v.s6.7cc5e83324b9 from=seed src=0 shape=c7c934a9 vocab=06070e9f
-/
@[simp]
theorem fst_div : (s / t).fst = s.fst / t.snd :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.0b127a2758d1 from=seed src=0 shape=c7c934a9 vocab=06070e9f
-/
@[simp]
theorem snd_div : (s / t).snd = s.snd / t.fst :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.03f03a08cb73 from=seed src=0 shape=194c6998 vocab=2f65360b
-/
@[simp]
theorem coe_div_interval : (↑(s / t) : Interval α) = s / t :=
  rfl

/--
@isnad1 id=mem.2h5v.s6.83303dade87f from=seed src=0 shape=ef31d0c3 vocab=3e59a01b
-/
theorem div_mem_div (ha : a ∈ s) (hb : b ∈ t) : a / b ∈ s / t :=
  ⟨div_le_div'' ha.1 hb.2, div_le_div'' ha.2 hb.1⟩

/--
@isnad1 id=eq.0h3v.s6.d124e23bffbe from=seed src=0 shape=fb3da4d4 vocab=6f837115
-/
@[simp]
theorem pure_div_pure : pure a / pure b = pure (a / b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

/--
@isnad1 id=eq.0h2v.s6.9940ab6e3278 from=seed src=0 shape=5cc772f0 vocab=c12b74f4
-/
@[simp]
theorem bot_div : ⊥ / t = ⊥ :=
  WithBot.map₂_bot_left _ _

/--
@isnad1 id=eq.0h2v.s6.b624bf49c8d0 from=seed src=0 shape=f31d116d vocab=c12b74f4
-/
@[simp]
theorem div_bot : s / ⊥ = ⊥ :=
  WithBot.map₂_bot_right _ _

end Interval

end Div

/-! ### Negation/inversion -/


section Inv

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]

@[to_additive]
instance : Inv (NonemptyInterval α) :=
  ⟨fun s => ⟨(s.snd⁻¹, s.fst⁻¹), inv_le_inv' s.fst_le_snd⟩⟩

@[to_additive]
instance : Inv (Interval α) :=
  ⟨WithBot.map Inv.inv⟩

namespace NonemptyInterval

variable (s : NonemptyInterval α) (a : α)

/--
@isnad1 id=eq.0h2v.s6.adff5c5efcd4 from=seed src=0 shape=f7475f04 vocab=da5128d4
-/
@[to_additive (attr := simp)]
theorem fst_inv : s⁻¹.fst = s.snd⁻¹ :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.1eb5233ec11c from=seed src=0 shape=f7475f04 vocab=da5128d4
-/
@[to_additive (attr := simp)]
theorem snd_inv : s⁻¹.snd = s.fst⁻¹ :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.ee74bc71605f from=seed src=0 shape=a08334ea vocab=1e85c762
-/
@[to_additive (attr := simp)]
theorem coe_inv_interval : (↑(s⁻¹) : Interval α) = (↑s)⁻¹ :=
  rfl

/--
@isnad1 id=mem.1h3v.s6.dd6c44a4e299 from=seed src=0 shape=e9ebc27b vocab=31e7e887
-/
@[to_additive]
theorem inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ :=
  ⟨inv_le_inv' ha.2, inv_le_inv' ha.1⟩

/--
@isnad1 id=eq.0h2v.s6.3468fe2d922a from=seed src=0 shape=4d4986c4 vocab=e2c627c6
-/
@[to_additive (attr := simp)]
theorem inv_pure : (pure a)⁻¹ = pure a⁻¹ :=
  rfl

end NonemptyInterval

/--
@isnad1 id=eq.0h1v.s6.8043f87fe4a4 from=seed src=0 shape=dc714602 vocab=725febda
-/
@[to_additive (attr := simp)]
theorem Interval.inv_bot : (⊥ : Interval α)⁻¹ = ⊥ :=
  rfl

end Inv

namespace NonemptyInterval

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {s t : NonemptyInterval α}

/--
@isnad1 id=iff.0h3v.s7.d71d77cfa1cd from=seed src=0 shape=099f8c10 vocab=3bcf7c75
-/
@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = pure a ∧ t = pure b ∧ a * b = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [NonemptyInterval.ext_iff, Prod.ext_iff] at h
    have := (mul_le_mul_iff_of_ge s.fst_le_snd t.fst_le_snd).1 (h.2.trans h.1.symm).le
    refine ⟨s.fst, t.fst, ?_, ?_, h.1⟩ <;> apply NonemptyInterval.ext <;> dsimp [pure]
    · nth_rw 2 [this.1]
    · nth_rw 2 [this.2]
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [pure_mul_pure, h, pure_one]

instance subtractionCommMonoid {α : Type u}
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] :
    SubtractionCommMonoid (NonemptyInterval α) where
  sub_eq_add_neg := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact sub_eq_add_neg _ _
  neg_neg := fun s => by apply NonemptyInterval.ext; exact neg_neg _
  neg_add_rev := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact neg_add_rev _ _
  neg_eq_of_add := fun s t h => by
    obtain ⟨a, b, rfl, rfl, hab⟩ := NonemptyInterval.add_eq_zero_iff.1 h
    rw [neg_pure, neg_eq_of_add_eq_zero_right hab]
  -- TODO: use a better defeq
  zsmul := zsmulRec

@[to_additive existing NonemptyInterval.subtractionCommMonoid]
instance divisionCommMonoid : DivisionCommMonoid (NonemptyInterval α) where
  div_eq_mul_inv := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact div_eq_mul_inv _ _
  inv_inv := fun s => by apply NonemptyInterval.ext; exact inv_inv _
  mul_inv_rev := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact mul_inv_rev _ _
  inv_eq_of_mul := fun s t h => by
    obtain ⟨a, b, rfl, rfl, hab⟩ := NonemptyInterval.mul_eq_one_iff.1 h
    rw [inv_pure, inv_eq_of_mul_eq_one_right hab]

end NonemptyInterval

namespace Interval

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {s t : Interval α}

/--
@isnad1 id=iff.0h3v.s7.922be610be0f from=seed src=0 shape=099f8c10 vocab=354f06d7
-/
@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = pure a ∧ t = pure b ∧ a * b = 1 := by
  cases s
  · simp
  cases t
  · simp
  · simp_rw [← NonemptyInterval.coe_mul_interval, ← NonemptyInterval.coe_one_interval,
      Interval.coe_inj, NonemptyInterval.coe_eq_pure]
    exact NonemptyInterval.mul_eq_one_iff

instance subtractionCommMonoid {α : Type u}
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] :
    SubtractionCommMonoid (Interval α) where
  sub_eq_add_neg := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (sub_eq_add_neg _ _)
  neg_neg := by rintro (_ | s) <;> first | rfl | exact congr_arg WithBot.some (neg_neg _)
  neg_add_rev := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (neg_add_rev _ _)
  neg_eq_of_add := by
    rintro (_ | s) (_ | t) h <;>
      first
        | cases h
        | exact congr_arg WithBot.some (neg_eq_of_add_eq_zero_right <| WithBot.coe_injective h)
  -- TODO: use a better defeq
  zsmul := zsmulRec

@[to_additive existing Interval.subtractionCommMonoid]
instance divisionCommMonoid : DivisionCommMonoid (Interval α) where
  div_eq_mul_inv := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (div_eq_mul_inv _ _)
  inv_inv := by rintro (_ | s) <;> first | rfl | exact congr_arg WithBot.some (inv_inv _)
  mul_inv_rev := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (mul_inv_rev _ _)
  inv_eq_of_mul := by
    rintro (_ | s) (_ | t) h <;>
      first
        | cases h
        | exact congr_arg WithBot.some (inv_eq_of_mul_eq_one_right <| WithBot.coe_injective h)

end Interval

section Length

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a : α)

/-- The length of an interval is its first component minus its second component. This measures the
accuracy of the approximation by an interval. -/
def length : α :=
  s.snd - s.fst

/--
@isnad1 id=le.0h2v.s5.c6a883838142 from=seed src=0 shape=14c0ec02 vocab=fd36c24b
-/
@[simp]
theorem length_nonneg : 0 ≤ s.length :=
  sub_nonneg_of_le s.fst_le_snd

omit [IsOrderedAddMonoid α] in
/--
@isnad1 id=eq.0h2v.s5.72093be77203 from=seed src=0 shape=e224aef9 vocab=794ead11
-/
@[simp]
theorem length_pure : (pure a).length = 0 :=
  sub_self _

omit [IsOrderedAddMonoid α] in
/--
@isnad1 id=eq.0h1v.s5.85e07d754683 from=seed src=0 shape=d4e3877e vocab=cc21bf81
-/
@[simp]
theorem length_zero : (0 : NonemptyInterval α).length = 0 :=
  length_pure _

/--
@isnad1 id=eq.0h2v.s5.322825d750ff from=seed src=0 shape=0523b701 vocab=5f17a3c4
-/
@[simp]
theorem length_neg : (-s).length = s.length :=
  neg_sub_neg _ _

/--
@isnad1 id=eq.0h3v.s6.b316791bab59 from=seed src=0 shape=0697f3bc vocab=8f7a8040
-/
@[simp]
theorem length_add : (s + t).length = s.length + t.length :=
  add_sub_add_comm _ _ _ _

/--
@isnad1 id=eq.0h3v.s6.a834f0ed7e43 from=seed src=0 shape=0697f3bc vocab=c7e0d457
-/
@[simp]
theorem length_sub : (s - t).length = s.length + t.length := by simp [sub_eq_add_neg]

/--
@isnad1 id=eq.0h4v.s6.080a9a52de8d from=seed src=0 shape=48cbca85 vocab=31ddec38
-/
@[simp]
theorem length_sum (f : ι → NonemptyInterval α) (s : Finset ι) :
    (∑ i ∈ s, f i).length = ∑ i ∈ s, (f i).length :=
  map_sum (⟨⟨length, length_zero⟩, length_add⟩ : NonemptyInterval α →+ α) _ _

end NonemptyInterval

namespace Interval

variable (s t : Interval α) (a : α)

/-- The length of an interval is its first component minus its second component. This measures the
accuracy of the approximation by an interval. -/
def length : Interval α → α
  | ⊥ => 0
  | (s : NonemptyInterval α) => s.length

/--
@isnad1 id=le.0h2v.s5.8adf1c62f00c from=seed src=0 shape=14c0ec02 vocab=f3db4e8d
-/
@[simp]
theorem length_nonneg : ∀ s : Interval α, 0 ≤ s.length
  | ⊥ => le_rfl
  | (s : NonemptyInterval α) => s.length_nonneg

omit [IsOrderedAddMonoid α] in
/--
@isnad1 id=eq.0h2v.s5.716bcfa5a33b from=seed src=0 shape=e224aef9 vocab=4a7b0d82
-/
@[simp]
theorem length_pure : (pure a).length = 0 :=
  NonemptyInterval.length_pure _

omit [IsOrderedAddMonoid α] in
/--
@isnad1 id=eq.0h1v.s5.1d84da3fd766 from=seed src=0 shape=d4e3877e vocab=b637c6dd
-/
@[simp]
theorem length_zero : (0 : Interval α).length = 0 :=
  length_pure _

/--
@isnad1 id=eq.0h2v.s5.cc4a342bda3a from=seed src=0 shape=0523b701 vocab=2b5181f7
-/
@[simp]
theorem length_neg : ∀ s : Interval α, (-s).length = s.length
  | ⊥ => rfl
  | (s : NonemptyInterval α) => s.length_neg

omit [IsOrderedAddMonoid α] in
/--
@isnad1 id=eq.0h1v.s5.b5d91c36b849 from=seed src=0 shape=4e15d180 vocab=d427da15
-/
@[simp]
theorem length_bot : (⊥ : Interval α).length = 0 := rfl

/--
@isnad1 id=le.0h3v.s6.2be2a64485d4 from=seed src=0 shape=0697f3bc vocab=546f0afc
-/
theorem length_add_le : ∀ s t : Interval α, (s + t).length ≤ s.length + t.length
  | ⊥, _ => by simp
  | _, ⊥ => by simp
  | (s : NonemptyInterval α), (t : NonemptyInterval α) => (s.length_add t).le

/--
@isnad1 id=le.0h3v.s6.ec26f4fc591d from=seed src=0 shape=0697f3bc vocab=996e167a
-/
theorem length_sub_le : (s - t).length ≤ s.length + t.length := by
  simpa [sub_eq_add_neg] using length_add_le s (-t)

/--
@isnad1 id=le.0h4v.s6.d0ab7fed856d from=seed src=0 shape=48cbca85 vocab=658f0111
-/
theorem length_sum_le (f : ι → Interval α) (s : Finset ι) :
    (∑ i ∈ s, f i).length ≤ ∑ i ∈ s, (f i).length :=
  Finset.le_sum_of_subadditive _ length_zero.le length_add_le _ _

end Interval

end Length

namespace Mathlib.Meta.Positivity
open Lean Qq

/-- Extension for the `positivity` tactic: The length of an interval is always nonnegative. -/
@[positivity NonemptyInterval.length _]
meta def evalNonemptyIntervalLength : PositivityExt where
  eval {u α} _ pα? e :=
    match pα? with | none => pure .none | some _ => do
    let ~q(@NonemptyInterval.length _ $ig $ipo $a) := e |
      throwError "not NonemptyInterval.length"
    let _i ← synthInstanceQ q(IsOrderedAddMonoid $α)
    assertInstancesCommute
    return .nonnegative q(NonemptyInterval.length_nonneg $a)

/-- Extension for the `positivity` tactic: The length of an interval is always nonnegative. -/
@[positivity Interval.length _]
meta def evalIntervalLength : PositivityExt where
  eval {u α} _ pα? e :=
    match pα? with | none => pure .none | some _ => do
    let ~q(@Interval.length _ $ig $ipo $a) := e | throwError "not Interval.length"
    let _i ← synthInstanceQ q(IsOrderedAddMonoid $α)
    assumeInstancesCommute
    return .nonnegative q(Interval.length_nonneg $a)

end Mathlib.Meta.Positivity
