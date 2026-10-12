/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Geometry.Convex.Cone.Basic
public import Tengoku.Tauceti.TauCeti.Geometry.Convex.Cone.Face.Basic
public import Tengoku.Tauceti.TauCeti.Geometry.Convex.Cone.Face.Finite

/-!
# Rays of toric cones

A ray of a cone is a one-dimensional face. This file defines the ray type on Mathlib's face
lattice and proves the finiteness needed to index the primitive ray generators of a toric cone:
finite generation of the ambient cone alone already bounds the rays. It also records the
geometric content of one-dimensionality: every nonzero point of a salient ray spans it as a
pointed cone.

## Main declarations

* `TauCeti.Toric.ToricRay`: the one-dimensional faces of a pointed cone.
* `TauCeti.Toric.ToricRay.finite_of_fg`: a finitely generated pointed cone, and hence a toric
  cone, has finitely many rays.
* `TauCeti.Toric.ToricRay.exists_mem_ne_zero`: every ray contains a nonzero point.
* `TauCeti.Toric.ToricRay.eq_hull_singleton`: every nonzero point of a salient ray generates
  that ray.
* `TauCeti.Toric.ToricRay.instIsEmptyBot`: the zero cone has no rays.
* `TauCeti.Toric.ToricRay.faceEmbedding` and `TauCeti.Toric.ToricRay.range_faceEmbedding`: the
  rays of a face of a cone are exactly the rays of the cone contained in that face.
* `TauCeti.Toric.ToricRay.hullSingleton` and `TauCeti.Toric.ToricRay.eq_hullSingleton`: the cone
  spanned by a nonzero vector is its own only ray.
* `TauCeti.Toric.ToricRay.map_fst_eq_bot_of_map_snd_ne_bot`,
  `TauCeti.Toric.ToricRay.prodRayFst`, `TauCeti.Toric.ToricRay.prodRaySnd`,
  `TauCeti.Toric.ToricRay.prodInl`, `TauCeti.Toric.ToricRay.prodInr` and
  `TauCeti.Toric.ToricRay.prodSplit`: the rays of a product of salient cones are exactly the rays
  of the two factors.

## References

The ray description is from §1.2 of W. Fulton, *Introduction to Toric Varieties*, and §1.2 of
D. Cox, J. Little and H. Schenck, *Toric Varieties*.
-/

public section

namespace TauCeti.Toric

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {σ τ : PointedCone ℝ V}

/-- A ray of a pointed cone is a face whose linear span has real dimension one. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
abbrev ToricRay (σ : PointedCone ℝ V) :=
  {ρ : σ.Face // Module.finrank ℝ (Submodule.span ℝ ((ρ : PointedCone ℝ V) : Set V)) = 1}

namespace ToricRay

/-- The pointed cone underlying a ray. -/
abbrev toPointedCone (ρ : ToricRay σ) : PointedCone ℝ V := ρ.1.toPointedCone

/-- Rays are viewed as sets of vectors: membership `x ∈ ρ` and the coercion `(ρ : Set V)` both
refer to the pointed cone `ρ.toPointedCone` underlying the ray, and two rays with the same
points are equal. -/
instance : SetLike (ToricRay σ) V where
  coe ρ := ρ.toPointedCone
  coe_injective _ρ _τ h := Subtype.ext (PointedCone.Face.ext fun x ↦ Set.ext_iff.mp h x)

/-- The span of the cone underlying a ray has real dimension one. -/
@[simp]
theorem finrank_span (ρ : ToricRay σ) :
    Module.finrank ℝ (Submodule.span ℝ (ρ : Set V)) = 1 := ρ.2

/-- A ray is not the zero pointed cone. -/
theorem toPointedCone_ne_bot (ρ : ToricRay σ) : ρ.toPointedCone ≠ ⊥ := by
  intro hρ
  have hset : (ρ : Set V) = ({0} : Set V) :=
    congrArg (fun C : PointedCone ℝ V ↦ (C : Set V)) hρ
  have hdim := ρ.finrank_span
  rw [hset, Submodule.span_zero_singleton, finrank_bot] at hdim
  omega

/-! ### The zero cone -/

/-- The zero cone has no rays: its only face is itself, whose span is zero-dimensional. -/
instance instIsEmptyBot : IsEmpty (ToricRay (⊥ : PointedCone ℝ V)) where
  false ρ := ρ.toPointedCone_ne_bot (le_antisymm ρ.1.isFaceOf.le bot_le)

/-! ### Rays of a face -/

/-- A ray of a face `τ` of a cone `σ` is a ray of `σ`: a face of a face is a face, and
one-dimensionality of the span does not mention the ambient cone. -/
def faceEmbedding (hτ : τ.IsFaceOf σ) : ToricRay τ ↪ ToricRay σ where
  toFun ρ := ⟨⟨ρ.toPointedCone, ρ.1.isFaceOf.trans hτ⟩, ρ.2⟩
  inj' ρ ρ' h := by
    have hcone : ρ.toPointedCone = ρ'.toPointedCone :=
      congrArg (fun ν : ToricRay σ ↦ ν.toPointedCone) h
    exact Subtype.ext (SetLike.coe_injective
      (congrArg (fun C : PointedCone ℝ V ↦ (C : Set V)) hcone))

@[simp]
theorem toPointedCone_faceEmbedding (hτ : τ.IsFaceOf σ) (ρ : ToricRay τ) :
    (faceEmbedding hτ ρ).toPointedCone = ρ.toPointedCone := (rfl)

@[simp]
theorem mem_faceEmbedding (hτ : τ.IsFaceOf σ) (ρ : ToricRay τ) {x : V} :
    x ∈ faceEmbedding hτ ρ ↔ x ∈ ρ := (Iff.rfl)

/-- The rays of a face `τ` of `σ` are exactly the rays of `σ` that are contained in `τ`: a face of
`σ` contained in `τ` is a face of `τ`, and one-dimensionality does not mention the ambient cone. -/
@[simp]
theorem range_faceEmbedding (hτ : τ.IsFaceOf σ) :
    Set.range (faceEmbedding hτ) = {ρ : ToricRay σ | ρ.toPointedCone ≤ τ} := by
  ext ρ
  refine ⟨?_, fun hρ ↦ ?_⟩
  · rintro ⟨ν, rfl⟩
    exact ν.1.isFaceOf.le
  · exact ⟨⟨⟨ρ.toPointedCone, (PointedCone.IsFaceOf.isFaceOf_iff_le ρ.1.isFaceOf hτ).2 hρ⟩, ρ.2⟩,
      rfl⟩

/-! ### The ray spanned by a vector -/

/-- A ray of the cone spanned by a vector is the whole cone: a proper face of that cone misses the
spanning vector, hence is the zero cone, which is not a ray. -/
@[simp]
theorem toPointedCone_eq_of_hull_singleton {x : V}
    (ρ : ToricRay (PointedCone.hull ℝ {x})) : ρ.toPointedCone = PointedCone.hull ℝ {x} := by
  have hx : x ∈ ρ.toPointedCone := by
    by_contra hx
    have h := ρ.1.eq_hull_inter_of_eq_hull {x} rfl
    rw [Set.singleton_inter_eq_empty.2 (by simpa using hx)] at h
    exact ρ.toPointedCone_ne_bot (by simpa using h)
  exact le_antisymm ρ.1.isFaceOf.le (Submodule.span_le.2 (Set.singleton_subset_iff.2 hx))

/-- Two rays with the same underlying cone are equal. -/
theorem toPointedCone_injective :
    Function.Injective (toPointedCone : ToricRay σ → PointedCone ℝ V) := fun _ _ h ↦
  SetLike.coe_injective (congrArg (fun C : PointedCone ℝ V ↦ (C : Set V)) h)

/-! ### Rays of a product -/

section Prod

variable {V' : Type*} [AddCommGroup V'] [Module ℝ V'] {τ : PointedCone ℝ V'}

/-- A ray of a product of cones is determined by its two projections. -/
theorem prod_ext {G H : ToricRay (σ.prod τ)}
    (h₁ : PointedCone.map (LinearMap.fst ℝ V V') G.toPointedCone
      = PointedCone.map (LinearMap.fst ℝ V V') H.toPointedCone)
    (h₂ : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone
      = PointedCone.map (LinearMap.snd ℝ V V') H.toPointedCone) : G = H := by
  apply toPointedCone_injective
  have key {A B : ToricRay (σ.prod τ)}
      (hfst : PointedCone.map (LinearMap.fst ℝ V V') A.toPointedCone ≤
        PointedCone.map (LinearMap.fst ℝ V V') B.toPointedCone)
      (hsnd : PointedCone.map (LinearMap.snd ℝ V V') A.toPointedCone ≤
        PointedCone.map (LinearMap.snd ℝ V V') B.toPointedCone) :
      A.toPointedCone ≤ B.toPointedCone := by
    intro x hx
    obtain ⟨a, ha, ha1⟩ := Submodule.mem_map.1
      (hfst (Submodule.mem_map.2 ⟨x, hx, rfl⟩))
    obtain ⟨c, hc, hc2⟩ := Submodule.mem_map.1
      (hsnd (Submodule.mem_map.2 ⟨x, hx, rfl⟩))
    have hxa : (x.1, a.2) = a := Prod.ext ha1.symm rfl
    have hcx : (c.1, x.2) = c := Prod.ext rfl hc2.symm
    have hadd : (x.1, a.2) + (c.1, x.2) = x + (c.1, a.2) := by
      ext <;> simp [add_comm]
    have hsum : x + (c.1, a.2) ∈ B.toPointedCone := by
      rw [← hadd, hxa, hcx]
      exact Submodule.add_mem _ ha hc
    exact B.1.isFaceOf.mem_of_add_mem_left (x := x) (y := (c.1, a.2))
      (Submodule.mem_prod.2 ⟨by
          have h := B.1.isFaceOf.le ha
          rw [← hxa] at h
          exact (Submodule.mem_prod.1 h).1,
        by
          have h := B.1.isFaceOf.le hc
          rw [← hcx] at h
          exact (Submodule.mem_prod.1 h).2⟩)
      (Submodule.mem_prod.2 ⟨(Submodule.mem_prod.1 (B.1.isFaceOf.le hc)).1,
        (Submodule.mem_prod.1 (B.1.isFaceOf.le ha)).2⟩) hsum
  exact le_antisymm (key h₁.le h₂.le) (key h₁.ge h₂.ge)

/-- A ray of the first factor included as a ray of the product by taking its product with the zero
cone in the second factor. -/
def prodInl (hτ : (τ : ConvexCone ℝ V').Salient) (ρ : ToricRay σ) : ToricRay (σ.prod τ) :=
  ⟨⟨ρ.toPointedCone.prod ⊥, ρ.1.isFaceOf.prod hτ.bot_isFaceOf⟩,
    (PointedCone.finrank_span_coe_prod_bot ρ.toPointedCone).trans ρ.2⟩

@[simp]
theorem toPointedCone_prodInl (hτ : (τ : ConvexCone ℝ V').Salient) (ρ : ToricRay σ) :
    (prodInl hτ ρ).toPointedCone = ρ.toPointedCone.prod ⊥ := (rfl)

/-- Membership in a ray included from the first factor is coordinatewise. -/
@[simp]
theorem mem_prodInl (hτ : (τ : ConvexCone ℝ V').Salient) (ρ : ToricRay σ) {x : V × V'} :
    x ∈ prodInl hτ ρ ↔ x.1 ∈ ρ ∧ x.2 = 0 := (Iff.rfl)

/-- A ray of the second factor included as a ray of the product by taking the product of the zero
cone in the first factor with that ray. -/
def prodInr (hσ : (σ : ConvexCone ℝ V).Salient) (ρ : ToricRay τ) : ToricRay (σ.prod τ) :=
  ⟨⟨(⊥ : PointedCone ℝ V).prod ρ.toPointedCone, hσ.bot_isFaceOf.prod ρ.1.isFaceOf⟩,
    (PointedCone.finrank_span_coe_bot_prod ρ.toPointedCone).trans ρ.2⟩

@[simp]
theorem toPointedCone_prodInr (hσ : (σ : ConvexCone ℝ V).Salient) (ρ : ToricRay τ) :
    (prodInr hσ ρ).toPointedCone = (⊥ : PointedCone ℝ V).prod ρ.toPointedCone := (rfl)

/-- Membership in a ray included from the second factor is coordinatewise. -/
@[simp]
theorem mem_prodInr (hσ : (σ : ConvexCone ℝ V).Salient) (ρ : ToricRay τ) {x : V × V'} :
    x ∈ prodInr hσ ρ ↔ x.1 = 0 ∧ x.2 ∈ ρ := (Iff.rfl)

end Prod

end ToricRay

end TauCeti.Toric
