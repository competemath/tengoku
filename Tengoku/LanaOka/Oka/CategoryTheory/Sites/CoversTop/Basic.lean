/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Tengoku.Seed.CategoryTheory.Sites.CoversTop.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Covering the terminal object by the arrows of a family of sieves

Material for `Mathlib/CategoryTheory/Sites/CoversTop/Basic.lean`; see `README.md` on the mirror
tree.

`CategoryTheory.GrothendieckTopology.CoversTop` is stated for a family of *objects*, whereas the
statements that produce covers — local surjectivity of an epimorphism, for instance — produce a
covering *sieve* over each object. This file bridges the two: the domains of the arrows of such
a family of sieves cover the terminal object.

## Main results

- `CategoryTheory.GrothendieckTopology.coversTop_of_sieves`
-/

@[expose] public section

universe v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- **A family of covering sieves, one over each object, covers the terminal object** by the
domains of its arrows.

The index type is the arrows of the sieves, so that no choice is involved and the family lives
in the same universes as the site. -/
lemma coversTop_of_sieves (J : GrothendieckTopology C) (S : ∀ Z : C, Sieve Z)
    (hS : ∀ Z, S Z ∈ J Z) :
    J.CoversTop (fun (t : Σ (Z : C), Σ (W : C), {g : W ⟶ Z // (S Z).arrows g}) ↦ t.2.1) := by
  intro Z
  refine J.superset_covering ?_ (hS Z)
  intro V g hg
  exact ⟨⟨Z, V, g, hg⟩, ⟨𝟙 V⟩⟩

end CategoryTheory.GrothendieckTopology
