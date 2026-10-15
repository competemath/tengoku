/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Tengoku
public import Tengoku.MeanFourier.MeanFourier.Mathlib.Topology.Bornology.Basic

/-!
# Translating functions
-/

public section

namespace Function
variable {G α M : Type*} [Group G] {x : G} {f : G → α}

/-- Left-translation of a function: `τ_[x] f y := f (x⁻¹ * y)`. -/
@[expose]
def translate (x : G) (f : G → α) : G → α := fun y ↦ f (x⁻¹ * y)

@[inherit_doc translate] notation3 "τ_[" x "]" => translate x

/--
@isnad1 id=eq.0h5v.s5.bece1c6d916c from=translated src=- shape=cd9d707c vocab=a5f5f71f
-/
@[simp] lemma translate_apply (x : G) (f : G → α) (y : G) : τ_[x] f y = f (x⁻¹ * y) := rfl

/--
@isnad1 id=eq.0h3v.s5.c6a712d5fc69 from=translated src=- shape=0a120fa7 vocab=33ca22a7
-/
@[simp] lemma translate_one (f : G → α) : τ_[1] f = f := by ext; simp
/--
@isnad1 id=eq.0h5v.s5.78f06b279fb8 from=translated src=- shape=dc0d1803 vocab=44531316
-/
@[simp] lemma translate_translate (x y : G) (f : G → α) : τ_[x] (τ_[y] f) = τ_[x * y] f := by
  ext; simp [mul_assoc]

-- TODO: Move the `attribute [local push] Function.const_def` from `Mathlib.Order.ScottContinuity`
-- to an earlier file.
/--
@isnad1 id=eq.0h4v.s4.b67669f30363 from=translated src=- shape=8db62fc3 vocab=31344fe5
-/
@[to_fun (attr := simp) translate_fun_const]
lemma translate_const (x : G) (a : α) : τ_[x] (const G a) = const G a := rfl

/--
@isnad1 id=eq.0h3v.s5.998d681f838a from=translated src=- shape=7c84261d vocab=2f11e2ad
-/
@[to_additive (attr := simp) (dont_translate := G)]
lemma translate_one_fun [One M] (x : G) : τ_[x] (1 : G → M) = 1 := rfl

/--
@isnad1 id=eq.0h5v.s6.8e9d0f2f365d from=translated src=- shape=25f51daa vocab=575dc3ee
-/
@[to_additive (attr := simp) (dont_translate := G)]
lemma translate_mul_fun [Mul M] (x : G) (f g : G → M) : τ_[x] (f * g) = τ_[x] f * τ_[x] g := rfl

/--
@isnad1 id=eq.0h4v.s4.3e86c9d7c987 from=translated src=- shape=8ed668c2 vocab=aa5c4bc5
-/
@[simp] lemma range_translate (x : G) (f : G → α) : Set.range (τ_[x] f) = .range f := by
  ext a; exact (Equiv.mulLeft x⁻¹).exists_congr (by simp)

end Function

namespace Bornology
variable {G X : Type*} [Group G] [Bornology X] {x : G} {f : G → X}

/--
@isnad1 id=iff.0h4v.s5.4e4bdf7e2a2c from=translated src=- shape=9c331490 vocab=abd7d6fd
-/
@[simp] lemma isBddFun_translate : IsBddFun (τ_[x] f) ↔ IsBddFun f := by simp [IsBddFun]

/--
@isnad1 id=isbddfun.1h4v.s5.684732bba725 from=translated src=- shape=18fd31eb vocab=abd7d6fd
-/
protected alias ⟨_, IsBddFun.translate⟩ := isBddFun_translate

end Bornology
