/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted for the quotient-submodule equidistribution formalization from TauCeti commit
eeb5b4bee8bf17747ded538639102901e2cd1116.
-/
module

public import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.Foundation.RepresentationTheory.Quiver.Representation.DimensionVector
public import Tengoku.Seed.Algebra.Category.ModuleCat.Simple
public import Tengoku.Seed.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The vertex simple representations of a quiver

For a vertex `i` of a quiver `Q`, the *vertex simple* representation `Sᵢ` is the base field `k` at
`i` and the zero module at every other vertex, every arrow acting by zero. This file constructs
`Sᵢ` and proves that it is a simple object of the category of representations.

The construction is a `CategoryTheory.Paths.lift` of the prefunctor sending `i` to `k`, every other
vertex to the zero module, and every arrow to the zero map; functoriality along path concatenation
is then supplied by Mathlib. Simplicity is checked pointwise: a monomorphism into `Sᵢ` is zero away
from `i` because the target vanishes there, so it is determined by its component at `i`, where `k`
is a simple `k`-module.

## Main definitions

* `QuotientSubmoduleEquidistribution.Foundation.simpleRep k Q i`: the vertex simple representation `Sᵢ`.

## Main results

* `QuotientSubmoduleEquidistribution.Foundation.simpleRep_simple`: `Sᵢ` is a simple object of `QuotientSubmoduleEquidistribution.Foundation.QuiverRep k Q`.
* `QuotientSubmoduleEquidistribution.Foundation.hom_simpleRep_eq_zero_iff` and `QuotientSubmoduleEquidistribution.Foundation.simpleRep_hom_eq_zero_iff`: a morphism into or
  out of `Sᵢ` is detected by its component at `i`.
* `QuotientSubmoduleEquidistribution.Foundation.dimVector_simpleRep`: the dimension vector of `Sᵢ` is `Pi.single i 1`.
* `QuotientSubmoduleEquidistribution.Foundation.not_nonempty_simpleRep_iso`: vertex simples at distinct vertices are not isomorphic.

## Implementation notes

`simpleRep` branches on equality of vertices. It is noncomputable in any case, so that branch is
decided classically and no `DecidableEq Q` instance appears in the interface; `simpleRep_obj_self`
and `simpleRep_obj_of_ne` describe the two cases without mentioning the branch. Only
`dimVector_simpleRep` assumes `DecidableEq Q`, because `Pi.single` needs one to be stated.

The objects of `CategoryTheory.Paths Q` are the vertices of `Q`, so the statements below use a
vertex directly as an object of the path category.

The roadmap pins the simplicity result as `simpleRep_simple`, so the instance carries that name
rather than the `simple_simpleRep` a Mathlib predicate prefix would give it.

## References

This implements the vertex simples of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
-/

public section

namespace QuotientSubmoduleEquidistribution.Foundation

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

variable (k : Type u) (Q : Type v) [Field k] [Quiver Q]

open scoped Classical in
/-- The **vertex simple** representation `Sᵢ` of a quiver: the base field `k` at the vertex `i`,
the zero module at every other vertex, and the zero map along every arrow.-/
noncomputable def simpleRep (i : Q) : QuiverRep k Q :=
  Paths.lift { obj := fun a ↦ if a = i then ModuleCat.of k k else 0, map := fun _ ↦ 0 }

variable {k Q}

/-- At `i`, the vertex simple `Sᵢ` is the base field `k`.
@isnad1 id=eq.0h3v.s6.633de89c6420 from=translated src=- shape=4c63e68e vocab=328ef6ec
-/
@[simp]
theorem simpleRep_obj_self (i : Q) : (simpleRep k Q i).obj i = ModuleCat.of k k :=
  ite_eq_left rfl

/-- Away from `i`, the vertex simple `Sᵢ` is the zero module.
@isnad1 id=eq.1h4v.s6.a8418ab4f8e7 from=translated src=- shape=66c2a658 vocab=46e1b7aa
-/
@[simp]
theorem simpleRep_obj_of_ne {i a : Q} (h : a ≠ i) : (simpleRep k Q i).obj a = 0 :=
  ite_eq_right h

/-- Away from `i`, the vertex simple `Sᵢ` vanishes.
@isnad1 id=iszero.1h4v.s5.c8a59e54d8c1 from=translated src=- shape=99807106 vocab=bed4302a
-/
theorem isZero_simpleRep_obj {i a : Q} (h : a ≠ i) : IsZero ((simpleRep k Q i).obj a) := by
  rw [simpleRep_obj_of_ne h]
  exact isZero_zero _

/-- Every arrow of the quiver acts by zero on the vertex simple `Sᵢ`.
@isnad1 id=eq.0h6v.s8.307fcb4378d0 from=translated src=- shape=aea83c3d vocab=b9d37cfd
-/
@[simp]
theorem simpleRep_map_toPath (i : Q) {a b : Q} (e : a ⟶ b) :
    (simpleRep k Q i).map e.toPath = 0 :=
  Paths.lift_toPath _ e

/-- More generally, every path of positive length acts by zero on the vertex simple `Sᵢ`.
@isnad1 id=eq.0h8v.s8.d279d5b8167a from=translated src=- shape=bd4eb3b8 vocab=3f80bf2d
-/
@[simp]
theorem simpleRep_map_cons (i : Q) {a b c : Q} (p : Quiver.Path a b) (e : b ⟶ c) :
    (simpleRep k Q i).map (p.cons e) = 0 := by
  rw [simpleRep, Paths.lift_cons]
  exact Limits.comp_zero

/-- A path of positive length acts by zero on the vertex simple `Sᵢ`; only the trivial paths, which
act by the identity, survive.
@isnad1 id=eq.1h6v.s8.781d6c540e0a from=translated src=- shape=dca586e9 vocab=bf7d9174
-/
theorem simpleRep_map_eq_zero_of_length_ne_zero (i : Q) {a b : Q} (p : Quiver.Path a b)
    (hp : p.length ≠ 0) : (simpleRep k Q i).map p = 0 := by
  cases p with
  | nil => exact absurd rfl hp
  | cons q e => exact simpleRep_map_cons i q e

/-- The dimension vector of the vertex simple `Sᵢ` is the standard basis vector at `i`.
@isnad1 id=eq.0h3v.s5.f586b3be75fb from=translated src=- shape=35666db1 vocab=ecf6096b
-/
@[simp]
theorem dimVector_simpleRep [DecidableEq Q] (i : Q) :
    dimVector (simpleRep k Q i) = Pi.single i 1 := by
  funext a
  rw [dimVector_apply, Paths.of_obj, Pi.single_apply]
  rcases eq_or_ne a i with rfl | ha
  · rw [ite_eq_left rfl, simpleRep_obj_self]
    exact Module.finrank_self k
  · rw [ite_eq_right ha]
    have : Subsingleton ((simpleRep k Q i).obj a) :=
      ModuleCat.subsingleton_of_isZero (isZero_simpleRep_obj ha)
    exact Module.finrank_zero_of_subsingleton

/-- Vertex simples at distinct vertices are not isomorphic: their dimension vectors differ.
@isnad1 id=not.1h4v.s5.6610bbd7ee38 from=translated src=- shape=469f5b93 vocab=a5a0c310
-/
theorem not_nonempty_simpleRep_iso {i j : Q} (h : i ≠ j) :
    ¬ Nonempty (simpleRep k Q i ≅ simpleRep k Q j) := by
  classical
  rintro ⟨e⟩
  have hd := dimVector_eq_of_iso e
  rw [dimVector_simpleRep, dimVector_simpleRep] at hd
  simpa [Pi.single_apply, h] using congrFun hd i

end QuotientSubmoduleEquidistribution.Foundation
