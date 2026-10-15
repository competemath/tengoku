/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import Tengoku.LeanPool.LeanPool.WhiteheadTheorem.HomotopyGroup.InducedMaps
public import Tengoku

/-!
# LeanPool.WhiteheadTheorem.Defs

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Defs`.
-/

@[expose] public section

open CategoryTheory
open scoped ContinuousMap

universe u

/-- `IsWeakHomotopyEquiv` -/
def IsWeakHomotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Prop :=
  Nonempty X ∧
    ∀ n x, Function.Bijective (HomotopyGroup.inducedMap n x f)

/--
@isnad1 id=isiso.1h5v.s6.99ba3480879b from=translated src=- shape=48ebc23c vocab=f0c107dd
-/
lemma isIso_inducedPointedHom_of_isWeakHomotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (hf : IsWeakHomotopyEquiv f) :
    ∀ n x, IsIso (HomotopyGroup.inducedPointedHom n x f) := by
  intro n x
  apply (Pointed.isIso_iff_bijective _).mpr
  have := hf.right n x
  rwa [HomotopyGroup.inducedMap] at this

/-- `IsHomotopyEquiv` -/
def IsHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Prop :=
  ∃ equiv : X ≃ₕ Y, equiv.toFun = f
