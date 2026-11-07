/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Cslib.Cslib.Computability.Circuit.Signature

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Homomorphisms of interpretations

A homomorphism between two interpretations of the same signature is a map of
carriers that commutes with every operation. This file defines identity and
composition and proves their laws.

The main use of homomorphisms in this library is that evaluation of lines,
programs, and circuits commutes with them (`Line.map_eval`, `Program.map_eval`,
`Program.map_trace`, and `Circuit.map_eval`).
-/

@[expose] public section

namespace Cslib.Circuits

universe v u u₁ u₂ u₃ u₄

variable {σ : Signature.{v}} {U : Type u}
variable {U₁ : Type u₁} {U₂ : Type u₂} {U₃ : Type u₃} {U₄ : Type u₄}

/-- A map that preserves every operation in a pair of interpretations.-/
structure Homomorphism (i₁ : Interpretation σ U₁) (i₂ : Interpretation σ U₂) where
  /-- The underlying map.-/
  map : U₁ → U₂
  /-- The map commutes with every operation in the signature.-/
  homomorphic :
    ∀ (op : σ.Op) (input : Fin (σ.Arity op) → U₁),
      map (i₁ op input) = i₂ op (map ∘ input)

namespace Homomorphism

/--
@isnad1 id=eq.1h7v.s5.1b16c442c9b1 from=translated src=- shape=c632f5da vocab=602a9269
-/
@[ext] theorem ext
    {source : Interpretation σ U₁}
    {target : Interpretation σ U₂}
    {left right : Homomorphism source target}
    (map_eq : left.map = right.map) : left = right := by
  cases left
  cases right
  cases map_eq
  rfl

/-- The identity map is a homomorphism.-/
def id (interpretation : Interpretation σ U) :
    Homomorphism interpretation interpretation where
  map := _root_.id
  homomorphic := by
    intro op input
    rfl

/-- Compose homomorphisms in the direction of their underlying maps.-/
def comp
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    {i₃ : Interpretation σ U₃}
    (outer : Homomorphism i₂ i₃)
    (inner : Homomorphism i₁ i₂) : Homomorphism i₁ i₃ where
  map := outer.map ∘ inner.map
  homomorphic := by
    intro op input
    rw [Function.comp_apply, inner.homomorphic, outer.homomorphic]
    congr 1

/--
@isnad1 id=eq.0h3v.s4.bf72365901b5 from=translated src=- shape=672c3e69 vocab=85b4846f
-/
@[simp] theorem id_map
    (interpretation : Interpretation σ U) :
    (Homomorphism.id interpretation).map = _root_.id := rfl

/--
@isnad1 id=eq.0h9v.s6.89cd0df9b73e from=translated src=- shape=4bbb83ef vocab=50dc240e
-/
@[simp] theorem comp_map
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    {i₃ : Interpretation σ U₃}
    (outer : Homomorphism i₂ i₃)
    (inner : Homomorphism i₁ i₂) :
    (outer.comp inner).map = outer.map ∘ inner.map := rfl

/--
@isnad1 id=eq.0h6v.s5.3a3330290e90 from=translated src=- shape=10887a7f vocab=9d63ee1c
-/
@[simp] theorem id_comp
    {source : Interpretation σ U₁}
    {target : Interpretation σ U₂}
    (homomorphism : Homomorphism source target) :
    (Homomorphism.id target).comp homomorphism = homomorphism := by
  apply Homomorphism.ext
  rfl

/--
@isnad1 id=eq.0h6v.s5.57734b52e9b6 from=translated src=- shape=b2709e73 vocab=9d63ee1c
-/
@[simp] theorem comp_id
    {source : Interpretation σ U₁}
    {target : Interpretation σ U₂}
    (homomorphism : Homomorphism source target) :
    homomorphism.comp (Homomorphism.id source) = homomorphism := by
  apply Homomorphism.ext
  rfl

/--
@isnad1 id=eq.0h12v.s6.bfd95522c2e9 from=translated src=- shape=06d2bc25 vocab=2ac2374b
-/
theorem comp_assoc
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    {i₃ : Interpretation σ U₃}
    {i₄ : Interpretation σ U₄}
    (outer : Homomorphism i₃ i₄)
    (middle : Homomorphism i₂ i₃)
    (inner : Homomorphism i₁ i₂) :
    (outer.comp middle).comp inner = outer.comp (middle.comp inner) := by
  apply Homomorphism.ext
  rfl

end Homomorphism

end Cslib.Circuits
