/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import Tengoku

/-!
# LeanPool.DirectedTopologyLean4.DirectedSpace
-/

@[expose] public section

/-
  # Definition of directed spaces
  This file defines the directed space, an extension of a topological space where
  some of its paths are considered directed paths.
-/

universe u

open scoped unitInterval

/-- Definition of a directed topological space.

Dipaths are closed under:
* Constant paths,
* Concatenation of paths,
* Monotone reparametrization of paths. -/
class DirectedSpace (α : Type u) extends TopologicalSpace α where
  /-- Predicate selecting the directed paths in the space. -/
  IsDipath : ∀ {x y : α}, Path x y → Prop
  /-- Every constant path is directed. -/
  isDipath_constant : ∀ (x : α), IsDipath (Path.refl x)
  /-- The concatenation of two directed paths is directed. -/
  isDipath_concat : ∀ {x y z : α} {γ₁ : Path x y}
      {γ₂ : Path y z}, IsDipath γ₁ → IsDipath γ₂ → IsDipath (Path.trans γ₁ γ₂)
  /-- Monotone reparametrization preserves directedness. -/
  isDipath_reparam : ∀ {x y : α} {γ : Path x y} {t₀ t₁ : I}
      {f : Path t₀ t₁}, Monotone f → IsDipath γ → IsDipath (f.map (γ.continuous_toFun))

section DirectedSpace

variable {α : Type u} {x y z : α} [DirectedSpace α] {γ : Path x y} {γ' : Path y z} {t₀ t₁ : I}
  {f : Path t₀ t₁}

/-- A path in a directed space is a dipath if it satisfies the directed-space predicate. -/
def IsDipath : (Path x y) → Prop :=
  DirectedSpace.IsDipath

/-- The constant path at any point of a directed space is directed.
@isnad1 id=isdipath.0h2v.s4.4c69368010de from=translated src=- shape=b2b04e75 vocab=171312ac
-/
lemma isDipath_constant (x : α) : IsDipath (Path.refl x) :=
  DirectedSpace.isDipath_constant _

/-- The concatenation of two dipaths is again a dipath.
@isnad1 id=isdipath.2h6v.s5.5fadef66963b from=translated src=- shape=bad4713b vocab=e788ba5b
-/
lemma isDipath_concat (hγ : IsDipath γ) (hγ' : IsDipath γ') : IsDipath (γ.trans γ') :=
  DirectedSpace.isDipath_concat hγ hγ'

/-- Reparametrizing a dipath along a monotone path yields another dipath.
@isnad1 id=isdipath.2h7v.s8.0b7cac4c5fca from=translated src=- shape=b99f6136 vocab=87a405c8
-/
lemma isDipath_reparam (hfmono : Monotone f) (hγ : IsDipath γ) :
    IsDipath (f.map γ.continuous_toFun) :=
  DirectedSpace.isDipath_reparam hfmono hγ

/-- Casting a path that is directed into another path gives another directed path
@isnad1 id=isdipath.3h6v.s5.ef3615097a90 from=translated src=- shape=184db84c vocab=d9dc6edd
-/
lemma isDipath_cast {x y x' y' : α} (γ : Path x y) (hx : x' = x) (hy : y' = y) (hγ : IsDipath γ) :
  IsDipath (γ.cast hx hy) := by
    subst_vars
    simp_all

end DirectedSpace
