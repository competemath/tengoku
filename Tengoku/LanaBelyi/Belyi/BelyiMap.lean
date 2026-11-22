/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.Ramification
import Tengoku.LanaBelyi.Belyi.P1.Points

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Belyi maps

The central definition of the project (taxis issue #47, used by #51–#55): a **Belyi map**
on a scheme `X` over a field `k` is a finite morphism `X ⟶ ℙ¹_k` whose branch locus is
contained in the three marked points `{0, 1, ∞}` of `ℙ¹` (`Belyi/P1/Points.lean`).

Belyi's theorem (B14) states that a curve over `ℂ` is definable over `ℚ̄` if and only if
it admits a Belyi map.

## Main definitions

* `Belyi.markedPoints k`: the set `{0, 1, ∞} ⊆ ℙ¹_k`.
* `Belyi.IsBelyiMap k f`: `f : X ⟶ ℙ¹_k` is finite with `Branch f ⊆ {0, 1, ∞}`.

## Main results

* `Belyi.IsBelyiMap.of_isIso_comp`: precomposition with an isomorphism preserves the
  property (the branch locus is unchanged).
* `Belyi.isBelyiMap_of_etale`: a finite étale morphism to `ℙ¹` is a Belyi map (vacuously,
  its branch locus is empty).
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory

variable (k : Type u) [Field k]

/-- The three marked points `0 = [0:1]`, `1 = [1:1]`, `∞ = [1:0]` of the projective
line. -/
def markedPoints : Set (P1 k) := {P1.zero k, P1.one k, P1.infty k}

/--
@isnad1 id=mem.0h1v.s5.b7a632ea38e2 from=translated src=- shape=6f135e67 vocab=54f23f46
-/
@[simp] lemma zero_mem_markedPoints : P1.zero k ∈ markedPoints k := by
  simp [markedPoints]

/--
@isnad1 id=mem.0h1v.s5.cc464f4ca906 from=translated src=- shape=6f135e67 vocab=912c608d
-/
@[simp] lemma one_mem_markedPoints : P1.one k ∈ markedPoints k := by
  simp [markedPoints]

/--
@isnad1 id=mem.0h1v.s5.1c27b5135acf from=translated src=- shape=6f135e67 vocab=cba6a9a5
-/
@[simp] lemma infty_mem_markedPoints : P1.infty k ∈ markedPoints k := by
  simp [markedPoints]

/-- The set of marked points has exactly three elements.
@isnad1 id=eq.0h1v.s4.592d8d82dc23 from=translated src=- shape=0bbdd966 vocab=53dc3dce
-/
lemma markedPoints_ncard : (markedPoints k).ncard = 3 := by
  rw [markedPoints, Set.ncard_insert_of_notMem (by
      simp [P1.zero_ne_one k, P1.zero_ne_infty k]),
    Set.ncard_insert_of_notMem (by simp [P1.one_ne_infty k])]
  simp

/--
@isnad1 id=finite.0h1v.s4.2036782d9e03 from=translated src=- shape=8e70c307 vocab=ca78ff06
-/
lemma finite_markedPoints : (markedPoints k).Finite :=
  (Set.finite_singleton _).insert _ |>.insert _

variable {X : Scheme.{u}}

/-- A **Belyi map** on `X` is a finite morphism `X ⟶ ℙ¹_k` branched only over the three
marked points `0`, `1`, `∞`. -/
structure IsBelyiMap (f : X ⟶ P1 k) : Prop where
  isFinite : IsFinite f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  branch_subset : Branch f ⊆ markedPoints k

namespace IsBelyiMap

variable {k} {f : X ⟶ P1 k}

/-- A finite morphism to `ℙ¹` that is étale (hence unbranched) is a Belyi map.
@isnad1 id=isbelyim.0h3v.s5.bdb59c3e99cb from=translated src=- shape=79308620 vocab=6e10a8cc
-/
lemma _root_.Belyi.isBelyiMap_of_etale (f : X ⟶ P1 k) [IsFinite f]
    [LocallyOfFinitePresentation f] [Etale f] : IsBelyiMap k f where
  isFinite := inferInstance
  locallyOfFinitePresentation := inferInstance
  branch_subset := by simp

/-- Precomposition with an isomorphism preserves being a Belyi map: the branch locus of
`e ≫ f` is that of `f`.
@isnad1 id=isbelyim.1h5v.s6.676c5f3239a8 from=translated src=- shape=5e1eb534 vocab=2d4befe1
-/
lemma of_isIso_comp {X' : Scheme.{u}} (e : X' ⟶ X) [IsIso e]
    [LocallyOfFinitePresentation (e ≫ f)] (h : IsBelyiMap k f) : IsBelyiMap k (e ≫ f) where
  isFinite := have := h.isFinite; inferInstance
  locallyOfFinitePresentation := inferInstance
  branch_subset := by
    have := h.isFinite
    have := h.locallyOfFinitePresentation
    refine subset_trans (branch_comp_subset e f) ?_
    simp only [branch_eq_empty_of_isIso, Set.image_empty, Set.empty_union]
    exact h.branch_subset

/-- **B5 → Belyi maps**: if `f : X ⟶ ℙ¹` is finite and `g : ℙ¹ ⟶ ℙ¹` is a finite
self-map carrying the branch locus of `f` and its own branch locus into the marked
points, then `f ≫ g` is a Belyi map.

This is the bookkeeping step of the forward direction (B8): `f` is the map to `ℙ¹`
produced by B1, and `g` is the polynomial map produced by the reductions B6 (issue #49)
and B7 (issue #50).
@isnad1 id=isbelyim.2h4v.s8.97521b2dfb47 from=translated src=- shape=f8261008 vocab=bf6f2fbc
-/
lemma comp {f : X ⟶ P1 k} (g : P1 k ⟶ P1 k) [IsFinite f] [IsFinite g]
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    [LocallyOfFinitePresentation (f ≫ g)]
    (hbf : (g '' Branch f) ⊆ markedPoints k) (hbg : Branch g ⊆ markedPoints k) :
    IsBelyiMap k (f ≫ g) where
  isFinite := inferInstance
  locallyOfFinitePresentation := inferInstance
  branch_subset :=
    (branch_comp_subset f g).trans (Set.union_subset hbf hbg)

end IsBelyiMap

end Belyi
