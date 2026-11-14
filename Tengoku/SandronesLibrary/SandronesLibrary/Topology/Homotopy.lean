/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathConnected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Textbook homotopies

General homotopies and path homotopies relative to endpoints are defined using Sandrone product
topologies, the Sandrone unit interval, and Sandrone continuity.

Current entry:

* `topology.homotopy.definition-foundation`.
-/

open Function

namespace SandronesLibrary.Topology.TextbookTopology

variable {X Y : Type*}

/-- A homotopy from `f` to `g` is a continuous map on the product with the Sandrone unit interval
whose endpoint slices are `f` and `g`.

> **Entry**: topology.homotopy.definition-foundation-/
structure Homotopy (τX : TextbookTopology X) (τY : TextbookTopology Y)
    (f g : X → Y) where
  toFun : X × UnitInterval → Y
  continuous : Continuous (product τX unitInterval) τY toFun
  at_zero : ∀ x, toFun (x, UnitInterval.zero) = f x
  at_one : ∀ x, toFun (x, UnitInterval.one) = g x

namespace Homotopy

instance {τX : TextbookTopology X} {τY : TextbookTopology Y} {f g : X → Y} :
    CoeFun (Homotopy τX τY f g) (fun _ ↦ X × UnitInterval → Y) :=
  ⟨Homotopy.toFun⟩

@[ext]
theorem ext {τX : TextbookTopology X} {τY : TextbookTopology Y} {f g : X → Y}
    {F G : Homotopy τX τY f g} (h : ∀ p, F p = G p) : F = G := by
  cases F
  cases G
  simp_all only [mk.injEq]
  exact funext h

/-- Every continuous map is homotopic to itself by a homotopy constant in the interval
coordinate.-/
def refl {τX : TextbookTopology X} {τY : TextbookTopology Y} {f : X → Y}
    (hf : Continuous τX τY f) : Homotopy τX τY f f where
  toFun := f ∘ Prod.fst
  continuous := hf.comp (continuous_fst τX unitInterval)
  at_zero := fun _ ↦ rfl
  at_one := fun _ ↦ rfl

@[simp] theorem refl_apply {τX : TextbookTopology X} {τY : TextbookTopology Y}
    {f : X → Y} (hf : Continuous τX τY f) (p : X × UnitInterval) :
    refl hf p = f p.1 := rfl

/-- Reverse a homotopy by reflecting its unit-interval time parameter.-/
def symm {τX : TextbookTopology X} {τY : TextbookTopology Y} {f g : X → Y}
    (F : Homotopy τX τY f g) : Homotopy τX τY g f where
  toFun := fun p ↦ F (p.1, p.2.reflect)
  continuous := F.continuous.comp (continuous_prod_mk
    (continuous_fst τX unitInterval)
    (continuous_unitInterval_reflect.comp (continuous_snd τX unitInterval)))
  at_zero := by intro x; simpa using F.at_one x
  at_one := by intro x; simpa using F.at_zero x

end Homotopy

/-- A path homotopy relative to endpoints is a homotopy between the parametrized maps which fixes
the source and target throughout.

> **Entry**: topology.homotopy.definition-foundation-/
structure PathHomotopy {τX : TextbookTopology X} {a b : X}
    (γ δ : Path τX a b) where
  toHomotopy : Homotopy unitInterval τX γ δ
  source_fixed : ∀ s, toHomotopy (UnitInterval.zero, s) = a
  target_fixed : ∀ s, toHomotopy (UnitInterval.one, s) = b

namespace PathHomotopy

/-- A path is homotopic to itself relative to its endpoints.-/
def refl {τX : TextbookTopology X} {a b : X} (γ : Path τX a b) :
    PathHomotopy γ γ where
  toHomotopy := Homotopy.refl γ.continuous
  source_fixed := fun _ ↦ γ.source
  target_fixed := fun _ ↦ γ.target

/-- Reverse the time direction of a path homotopy while retaining its fixed endpoints.-/
def symm {τX : TextbookTopology X} {a b : X} {γ δ : Path τX a b}
    (F : PathHomotopy γ δ) : PathHomotopy δ γ where
  toHomotopy := F.toHomotopy.symm
  source_fixed := by intro s; exact F.source_fixed s.reflect
  target_fixed := by intro s; exact F.target_fixed s.reflect

end PathHomotopy

end SandronesLibrary.Topology.TextbookTopology
