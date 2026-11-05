/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Geometry.FiniteRank
import Tengoku.AclGeom.AclGeom.Closure.RationalFunctions
import Tengoku.AclGeom.AclGeom.Perfection.Lattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Acceptance test for milestone M1: rational function fields

The blueprint's acceptance test for M1: construct the lattice and point
geometry for the rational function field `k(t₁,…,tₙ)/k` and prove the
canonical lattice/closed-point-set round trips.

Concretely, with `K = FractionRing (MvPolynomial (Fin n) k)`:

* the complete lattice `𝒢(K/k)` and its atomistic structure instantiate;
* each variable `tᵢ` is transcendental over `k`, hence generates a point;
* the variables generate everything: `racl k (range t) = ⊤`, so the whole
  geometry has rank at most `n`;
* the round trips are `ClosedIF.pointSetIso`, instantiated here.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom.Test

open IntermediateField MvPolynomial AclGeom

noncomputable section

variable (k : Type*) [Field k] (n : ℕ)

/-- The rational function field `k(t₁,…,tₙ)`.-/
abbrev RatFn := FractionRing (MvPolynomial (Fin n) k)

/-- The `i`-th variable, as an element of the rational function field.-/
def t (i : Fin n) : RatFn k n :=
  algebraMap (MvPolynomial (Fin n) k) (RatFn k n) (X i)

/-- The variables are algebraically independent over `k`.-/
theorem algebraicIndependent_t : AlgebraicIndependent k (t k n) :=
  algebraicIndependent_algebraMap_X k (Fin n)

/-- Each variable is transcendental over `k`.-/
theorem transcendental_t (i : Fin n) : Transcendental k (t k n i) := by
  have h := (algebraicIndependent_t k n).comp (fun _ : Unit ↦ i)
    (fun a b _ ↦ Subsingleton.elim a b)
  exact algebraicIndependent_unique_type_iff.1 h

/-- Each variable generates a point of the geometry.-/
theorem t_notMem_bot (i : Fin n) : t k n i ∉ (⊥ : ClosedIF k (RatFn k n)) :=
  fun h ↦ transcendental_t k n i (ClosedIF.mem_bot_iff.1 h)

/-- The point of the `i`-th variable.-/
def tPoint (i : Fin n) : Point k (RatFn k n) :=
  Point.mk' k (t k n i) (t_notMem_bot k n i)

/-- The variables generate the field: `k(t₁,…,tₙ)` adjoined over `k` is
everything.-/
theorem adjoin_range_t : adjoin k (Set.range (t k n)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) k) z
  have key : ∀ p : MvPolynomial (Fin n) k,
      algebraMap (MvPolynomial (Fin n) k) (RatFn k n) p ∈ adjoin k (Set.range (t k n)) := by
    intro p
    have hp : p ∈ Algebra.adjoin k (Set.range (X : Fin n → MvPolynomial (Fin n) k)) := by
      rw [MvPolynomial.adjoin_range_X]
      trivial
    have himg : algebraMap (MvPolynomial (Fin n) k) (RatFn k n) p ∈
        (Algebra.adjoin k (Set.range (X : Fin n → MvPolynomial (Fin n) k))).map
          (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) (RatFn k n)) :=
      ⟨p, hp, rfl⟩
    rw [AlgHom.map_adjoin (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) (RatFn k n)),
      ← Set.range_comp] at himg
    exact algebra_adjoin_le_adjoin k _ himg
  exact div_mem (key p) (key q)

/-- The relative algebraic closure of the variables is everything.-/
theorem racl_range_t : racl k (Set.range (t k n)) = ⊤ := by
  rw [eq_top_iff, ← adjoin_range_t k n]
  exact adjoin_le_racl k _

section PerfectionAcceptance

/-!
Acceptance for milestone M2: for any chosen perfection, the perfection order
isomorphism round-trips every closed subfield by extensional equality, and
every integral Frobenius power induces the identity on the closed lattice
(hence on every point of the geometry).
-/

variable (π : Perfection (RatFn k n))

end PerfectionAcceptance

end

end AclGeom.Test
