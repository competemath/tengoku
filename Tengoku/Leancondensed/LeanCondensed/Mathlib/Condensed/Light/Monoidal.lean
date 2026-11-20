/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Monoidal.Closed
public import Tengoku.Seed.CategoryTheory.Monoidal.Braided.Reflection
public import Tengoku.Seed.CategoryTheory.Monoidal.Braided.Transport
public import Tengoku.Seed.Condensed.Discrete.Module
public import Tengoku.Seed.CategoryTheory.Monoidal.Closed.Types
public import Tengoku.Seed.CategoryTheory.Sites.CartesianClosed
public import Tengoku.Seed.CategoryTheory.Sites.Equivalence
public import Tengoku.Seed.Condensed.Light.Basic
public import Tengoku.Seed.Condensed.Light.Instances
public import Tengoku.Seed.Condensed.Light.Monoidal
public import Tengoku.Seed.Condensed.Light.Small
public import Tengoku.Leancondensed.LeanCondensed.Projects.MonoidalLinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace LightCondensed

variable (R : Type u) [CommRing R]

instance : MonoidalPreadditive (LightCondMod.{u} R) :=
  CategoryTheory.Sheaf.monoidalPreadditive _ _

end LightCondensed
