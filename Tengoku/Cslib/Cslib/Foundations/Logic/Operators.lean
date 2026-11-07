/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring
-/

module

public import Tengoku.Cslib.Cslib.Init
public import Tengoku.Cslib.Cslib.Foundations.Data.PFunctor.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/leanprover/cslib@e806c8e639ed, `Cslib/Foundations/Logic/Operators.lean`: removed 4 tag(s) of the custom grind set(s) `modal` from declarations. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! # Logical operators

This module contains typeclasses and associated notation for common logical operators: propositional
connectives (like `∧` and `→`), modalities (like `◇`, plain and indexed), linear connectives (like
`⊗`), etc.
-/

@[expose] public section

namespace Cslib.Logic

section Propositional

/-! ## Propositional connectives -/

/-- The type `α` has an and connective (`∧`).-/
class HasAnd (α : Type*) where
  /-- `a ∧ b` is the conjunction of `a` and `b`.-/
  and (a b : α) : α

@[inherit_doc] scoped infixr:36 " ∧ " => HasAnd.and

/-- The type `α` has an or connective (`∨`).-/
class HasOr (α : Type*) where
  /-- `a ∨ b` is the disjunction of `a` and `b`.-/
  or (a b : α) : α

@[inherit_doc] scoped infixr:30 " ∨ " => HasOr.or

/-- Finite conjunction, with empty conjunction equal to truth.-/
def finiteAnd [HasAnd α] [Top α] (as : List α) : α := as.foldr (· ∧ ·) ⊤

@[inherit_doc] scoped prefix:max "⋀" => finiteAnd

/--
@isnad1 id=eq.0h1v.s4.0c673f888e6f from=translated src=- shape=691bf2e9 vocab=4314a33d
-/
@[simp, scoped grind =]
theorem finiteAnd_nil [HasAnd α] [Top α] : ⋀([] : List α) = ⊤ := rfl

/--
@isnad1 id=eq.0h3v.s5.7eca792e0ba4 from=translated src=- shape=96afa169 vocab=0aa325e3
-/
@[simp, scoped grind =]
theorem finiteAnd_cons [HasAnd α] [Top α] (a : α) (as : List α) :
    ⋀(a :: as) = (a ∧ ⋀as) := rfl

/-- Finite disjunction, with empty disjunction equal to falsehood.-/
def finiteOr [HasOr α] [Bot α] (as : List α) : α := as.foldr (· ∨ ·) ⊥

@[inherit_doc] scoped prefix:max "⋁" => finiteOr

/--
@isnad1 id=eq.0h1v.s4.af0fe70d9481 from=translated src=- shape=691bf2e9 vocab=6f9b50e6
-/
@[simp, scoped grind =]
theorem finiteOr_nil [HasOr α] [Bot α] : ⋁([] : List α) = ⊥ := rfl

/--
@isnad1 id=eq.0h3v.s5.4431b31712d4 from=translated src=- shape=96afa169 vocab=ff9f5f5e
-/
@[simp, scoped grind =]
theorem finiteOr_cons [HasOr α] [Bot α] (a : α) (as : List α) :
    ⋁(a :: as) = (a ∨ ⋁as) := rfl

/-- The type `α` has an implication connective (`→`).-/
class HasImp (α : Type*) where
  /-- `a → b` denotes `a` implies `b`.-/
  imp (a b : α) : α

@[inherit_doc] scoped infixr:25 " → " => HasImp.imp

/-- The type `α` has a bi-implication connective (`↔`).-/
class HasIff (α : Type*) where
  /-- `a ↔ b` denotes `a` implies `b` and vice-versa.-/
  iff (a b : α) : α

@[inherit_doc] scoped infixr:20 " ↔ " => HasIff.iff

/-- The type `α` has a negation connective (`¬`).-/
class HasNot (α : Type*) where
  /-- `¬a` is the negation of `a`.-/
  not (a : α) : α

@[inherit_doc] scoped notation:max "¬" p:40 => HasNot.not p

end Propositional

section Modal

/-! ## General modalities from modal similarity types (polynomial functors) -/

/-- The type `α` has a family of triangle operators (`Δ`).-/
class HasTriangle (α : Type*) (τ : outParam PFunctor) where
  /-- `Δ[op](φ₁, ..., φₙ)` means that `φ₁`, ..., `φₙ` are valid at some respective related states.-/
  triangle (op : τ.A) (arg : τ.B op → α) : α

@[inherit_doc] scoped notation:50 "Δ[" op "]" arg:max => HasTriangle.triangle op arg

/-- The type `α` has a family of nabla operators (`∇`).-/
class HasNabla (α : Type*) (τ : outParam PFunctor) where
  /-- `∇[op](φ₁, ..., φₙ)` means that `φ₁`, ..., `φₙ` are valid at all respective related states.-/
  nabla (op : τ.A) (arg : τ.B op → α) : α

@[inherit_doc] scoped notation:50 "∇[" op "]" arg:max => HasNabla.nabla op arg

end Modal

section Dynamic

/-! ## Dynamic modalities

Here we need to use the prefix `d` to distinguish our notation from the normal `[·]` and `⟨·⟩`.
A refactoring that makes this unnecessary would be welcome.
-/

/-- The type `α` has a dynamic diamond modality with action type `β` (`d⟨a⟩φ`).-/
class HasDynamicDiamond (α : Type*) (β : outParam Type*) where
  /-- `b` is possibly valid after `a`.-/
  dynDiamond (a : β) (b : α) : α

@[inherit_doc] scoped notation "d⟨" a "⟩" φ:max => HasDynamicDiamond.dynDiamond a φ

/-- The type `α` has a dynamic box modality with action type `β` (`d[a]φ`).-/
class HasDynamicBox (α : Type*) (β : outParam Type*) where
  /-- `b` is necessarily valid after `a`.-/
  dynBox (a : β) (b : α) : α

@[inherit_doc] scoped notation "d[" a "]" φ:max => HasDynamicBox.dynBox a φ

/-- A family of triangle operators over induces dynamic diamond modalities by applying each operator
to the constant argument family.-/
instance [HasTriangle α τ] : HasDynamicDiamond α τ.A where
  dynDiamond op φ := Δ[op](PFunctor.const op φ)

/--
@isnad1 id=eq.0h4v.s5.e49f4e0cd887 from=translated src=- shape=aa0ad0c7 vocab=65c7bcd1
-/
@[simp, scoped grind =]
theorem dynDiamond_eq_triangle [HasTriangle α τ] (op : τ.A) (φ : α) :
    (d⟨op⟩φ) = (Δ[op](PFunctor.const op φ)) := rfl

/-- A family of nabla operators induces dynamic box modalities by applying each operator to the
constant argument family.-/
instance [HasNabla α τ] : HasDynamicBox α τ.A where
  dynBox op φ := ∇[op](PFunctor.const op φ)

/--
@isnad1 id=eq.0h4v.s5.05f2c0655627 from=translated src=- shape=aa0ad0c7 vocab=a4a55c7c
-/
@[simp, scoped grind =]
theorem dynBox_eq_nabla [HasNabla α τ] (op : τ.A) (φ : α) :
    (d[op]φ) = (∇[op](PFunctor.const op φ)) := rfl

end Dynamic

section Unimodal

/-! ## Basic modalities (Unimodal logic operators) -/

/-- The type `α` has a box modality (`□`).-/
class HasBox (α : Type*) where
  /-- `a` is valid in all immediately reachable states.-/
  box (a : α) : α

@[inherit_doc] scoped prefix:40 "□" => HasBox.box

/-- The type `α` has a diamond modality (`◇`).-/
class HasDiamond (α : Type*) where
  /-- `a` is valid in a reachable state.-/
  diamond (a : α) : α

@[inherit_doc] scoped prefix:40 "◇" => HasDiamond.diamond

/-- A dynamic diamond modality with a unique action induces a basic diamond modality.-/
instance [Unique β] [HasDynamicDiamond α β] : HasDiamond α where
  diamond φ := d⟨default⟩φ

/--
@isnad1 id=eq.0h3v.s5.5d4df33a57ed from=translated src=- shape=beb119be vocab=befdadc7
-/
@[simp, scoped grind =]
theorem diamond_eq_dynDiamond [Unique β] [HasDynamicDiamond α β] {φ : α} :
    (◇φ) = (d⟨default⟩φ) := rfl

/-- A dynamic box modality with a unique action induces a basic box modality.-/
instance [Unique β] [HasDynamicBox α β] : HasBox α where
  box φ := d[default]φ

/--
@isnad1 id=eq.0h3v.s5.59ab2620bf77 from=translated src=- shape=beb119be vocab=53dffb17
-/
@[simp, scoped grind =]
theorem box_eq_dynBox [Unique β] [HasDynamicBox α β] {φ : α} :
    (□φ) = (d[default]φ) := rfl

end Unimodal

section Linear

/-! ## Linear connectives -/

/-- The type `α` has a tensor connective (⊗).-/
class HasTensor (α : Type*) where
  /-- `a ⊗ b` is the multiplicative conjunction of `a` and `b`.-/
  tensor (a b : α) : α

@[inherit_doc] scoped infixr:35 " ⊗ " => HasTensor.tensor

end Linear

end Cslib.Logic
