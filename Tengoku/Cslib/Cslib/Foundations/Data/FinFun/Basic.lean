/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Xueying Qin
-/

module

public import Tengoku.Cslib.Cslib.Init
public import Tengoku.Seed.Data.Finset.Filter
public import Tengoku.Seed.Data.Finset.Lattice.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite functions

Given types `α` and `β`, and assuming that `β` has a `Zero` element,
a `FinFun α β` is a function from `α` to `β` where only a finite number of elements
in `α` are mapped to non-zero elements.
-/

@[expose] public section

namespace Cslib

/-- A `FinFun` is a function `fn` with a finite `support`.

This is similar to `Finsupp` in Mathlib, but definitions are computable.-/
structure FinFun (α β : Type*) [Zero β] where
  /-- The underlying function.-/
  fn : α → β
  /-- The finite support of the function.-/
  support : Finset α
  /-- Proof that `support` is the support of the underlying function.-/
  mem_support_fn {a : α} : a ∈ support ↔ fn a ≠ 0

attribute [scoped grind _=_] FinFun.mem_support_fn

namespace FinFun

@[inherit_doc]
scoped infixr:25 " →₀ " => FinFun

/-- Constructs a `FinFun` by restricting a function to a given support, filtering out all elements
not mapped to 0 in the support.-/
@[scoped grind .]
def fromFun {α β : Type*} [Zero β] [DecidableEq α]
  [∀ y : β, Decidable (y = 0)] (fn : α → β) (support : Finset α) : α →₀ β where
  fn := (fun a => if a ∈ support then fn a else 0)
  support := support.filter (fn · ≠ 0)
  mem_support_fn := by grind

@[inherit_doc]
scoped notation f:25 "↾₀" support:51 => FinFun.fromFun f support

instance instFunLike [Zero β] : FunLike (α →₀ β) α β where
  coe f := f.fn
  coe_injective := by
    rintro ⟨_, _⟩ ⟨_, _⟩
    simp_all [Finset.ext_iff]

/--
@isnad1 id=eq.0h3v.s5.5b5c0e73ed3b from=translated src=- shape=7b112b69 vocab=f6890994
-/
@[scoped grind =]
theorem coe_fn [Zero β] {f : α →₀ β} : (f : α → β) = f.fn := by simp [DFunLike.coe]

/--
@isnad1 id=eq.0h4v.s5.0153784b8b24 from=translated src=- shape=06e96719 vocab=f6890994
-/
@[scoped grind =]
theorem coe_eq_fn [Zero β] {f : α →₀ β} : f a = f.fn a := by
  simp [DFunLike.coe]

/-- Extensional equality for `FinFun`.
@isnad1 id=eq.1h4v.s5.e42d8e6a7023 from=translated src=- shape=1ff76785 vocab=812e5c97
-/
@[scoped grind ←=]
theorem ext [Zero β] {f g : α →₀ β} (h : ∀ (a : α), f a = g a) : f = g :=
  DFunLike.ext (f := f) (g := g) h

/--
@isnad1 id=iff.0h4v.s5.66be3efe1932 from=translated src=- shape=6cd49507 vocab=53329c8a
-/
@[scoped grind _=_]
theorem mem_support_not_zero [Zero β] {f : α →₀ β} : a ∈ f.support ↔ f a ≠ 0 := by
  grind

/--
@isnad1 id=iff.0h4v.s5.9b30da38c67f from=translated src=- shape=8fef1e39 vocab=53329c8a
-/
@[scoped grind _=_]
theorem not_mem_support_zero [Zero β] {f : α →₀ β} : a ∉ f.support ↔ f a = 0 := by
  grind

/-- If two `FinFun`s are equal, their underlying functions and supports are equal.-/
@[scoped grind .]
theorem eq_fields_eq [Zero β] {f g : α →₀ β} : f = g → f.fn = g.fn ∧ f.support = g.support :=
  by grind

/-- If two functions are equal, two `FinFun`s respectively using them as underlying functions
are equal.
@isnad1 id=eq.1h4v.s5.6a9ebc839c0f from=translated src=- shape=c5d4fc6b vocab=895dd513
-/
@[scoped grind .]
theorem fn_eq_eq [Zero β] {f g : α →₀ β} (h : f.fn = g.fn) : f = g :=
  ext (congrFun h)

/--
@isnad1 id=eq.1h5v.s5.a4fc2644eaaf from=translated src=- shape=3a253d39 vocab=812e5c97
-/
@[scoped grind =>]
theorem congrFinFun [Zero β] {f g : α →₀ β} (h : f = g) (a : α) : f a = g a := by grind

/--
@isnad1 id=eq.1h4v.s6.80e838e20d0f from=translated src=- shape=b691a877 vocab=d029ecb3
-/
@[scoped grind =]
theorem fromFun_eq [Zero β] [DecidableEq α] [∀ y : β, Decidable (y = 0)]
    (f : α → β) (support : Finset α) (h : ∀ a, a ∉ support → f a = 0) :
    (f ↾₀ support) = f := by grind

/--
@isnad1 id=eq.0h4v.s6.54a8acfba76a from=translated src=- shape=bb1aa3c4 vocab=8ee1b5c0
-/
@[scoped grind =]
theorem fromFun_fn [Zero β] [DecidableEq α] [∀ y : β, Decidable (y = 0)]
    (f : α → β) (support : Finset α) :
    (f ↾₀ support).fn = (fun a => if a ∈ support then f a else 0) := by
  grind

/--
@isnad1 id=eq.0h4v.s6.133a4a599dc6 from=translated src=- shape=d88e102f vocab=2abc61d8
-/
@[scoped grind =]
theorem fromFun_support [Zero β] [DecidableEq α] [∀ y : β, Decidable (y = 0)]
    (f : α → β) (support : Finset α) :
    (f ↾₀ support).support = support.filter (f · ≠ 0) := by
  grind

/-- Restricting a function twice to the same support is idempotent.
@isnad1 id=eq.0h4v.s6.4c11082c0f6e from=translated src=- shape=f12ba04e vocab=18c5ec80
-/
@[scoped grind =]
theorem fromFun_idem [Zero β] [DecidableEq α]
    [∀ y : β, Decidable (y = 0)] {f : α → β} {support : Finset α} :
    (f ↾₀ support) ↾₀ support = f ↾₀ support := by grind

/-- Restricting a `FinFun` to its own support is the identity.
@isnad1 id=eq.0h3v.s5.fd4949fa3418 from=translated src=- shape=07a57521 vocab=8b4fd0fe
-/
@[scoped grind =]
theorem coe_fromFun_id [Zero β] [DecidableEq α] [∀ y : β, Decidable (y = 0)] {f : α →₀ β} :
    (f ↾₀ f.support) = f := by grind

/-- Restricting a function twice to two supports is equal to restricting to their intersection.
@isnad1 id=eq.0h5v.s6.dd22cd123c8c from=translated src=- shape=e89f625d vocab=3ec50ede
-/
@[scoped grind =]
theorem fromFun_inter [Zero β] [DecidableEq α]
    [∀ y : β, Decidable (y = 0)] {f : α → β} {support1 support2 : Finset α} :
    (f ↾₀ support1) ↾₀ support2 = f ↾₀ (support1 ∩ support2) := by grind

/-- Restricting a function is commutative.
@isnad1 id=eq.0h5v.s6.284c2c2c6ee7 from=translated src=- shape=91f99d0a vocab=18c5ec80
-/
@[scoped grind =]
theorem fromFun_comm [Zero β] [DecidableEq α]
    [∀ y : β, Decidable (y = 0)] {f : α → β} {support1 support2 : Finset α} :
    (f ↾₀ support1) ↾₀ support2 = (f ↾₀ support2) ↾₀ support1 := by
  grind only [= coe_eq_fn, = fromFun_fn, ←= ext]

/-- Decidable equality-/
instance instDecidableEq [Zero β] [DecidableEq α] [DecidableEq β] : DecidableEq (α →₀ β) :=
  fun f g =>
    if h : ∀ a ∈ f.support ∪ g.support, f a = g a then
      isTrue <| ext fun a => by grind
    else
      isFalse <| by grind

end FinFun

end Cslib
