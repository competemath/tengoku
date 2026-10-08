/-
Copyright (c) 2022 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade, Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Convex.Cone.Closure
public import Tengoku.Seed.Geometry.Convex.Cone.Pointed
public import Tengoku.Seed.Topology.Algebra.Module.ClosedSubmodule
public import Tengoku.Seed.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Tengoku.Seed.Topology.Algebra.Order.Module
public import Tengoku.Seed.Topology.Order.DenselyOrdered

/-!
# Proper cones

We define a *proper cone* as a closed, pointed cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once we have the definitions of conic and
linear programs, the results from this file can be used to prove duality theorems.

One can turn `C : PointedCone R E` + `hC : IsClosed C` into `C : ProperCone R E` in a tactic block
by doing `lift C to ProperCone R E using hC`.

One can also turn `C : ConvexCone 𝕜 E` + `hC : Set.Nonempty C ∧ IsClosed C` into
`C : ProperCone 𝕜 E` in a tactic block by doing `lift C to ProperCone 𝕜 E using hC`,
assuming `𝕜` is a dense topological field.

## TODO

The next steps are:
- Add `ConvexConeClass` that extends `SetLike` and replace the below instance
- Define primal and dual cone programs and prove weak duality.
- Prove regular and strong duality for cone programs using Farkas' lemma (see reference).
- Define linear programs and prove LP duality as a special case of cone duality.
- Find a better reference (textbook instead of lecture notes).

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

@[expose] public section

open ContinuousLinearMap Function Set

variable {𝕜 R E F G : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [TopologicalSpace E] [Module R E]
variable [AddCommMonoid F] [TopologicalSpace F] [Module R F]
variable [AddCommMonoid G] [TopologicalSpace G] [Module R G]

local notation "R≥0" => {r : R // 0 ≤ r}

variable (R E) in
/-- A proper cone is a pointed cone `C` that is closed. Proper cones have the nice property that
they are equal to their double dual, see `ProperCone.dual_dual`.
This makes them useful for defining cone programs and proving duality theorems. -/
abbrev ProperCone := ClosedSubmodule R≥0 E

namespace ProperCone
section Module
variable {C C₁ C₂ : ProperCone R E} {r : R} {x : E}

/-- Any proper cone can be seen as a pointed cone.

This is an alias of `ClosedSubmodule.toSubmodule` for convenience and discoverability. -/
@[coe] abbrev toPointedCone (C : ProperCone R E) : PointedCone R E := C.toSubmodule

instance : Coe (ProperCone R E) (PointedCone R E) := ⟨toPointedCone⟩

/--
@isnad1 id=injectiv.0h2v.s5.5ad30b1f86cb from=seed src=0 shape=b1ef29a8 vocab=622c5026
-/
lemma toPointedCone_injective : Injective ((↑) : ProperCone R E → PointedCone R E) :=
  ClosedSubmodule.toSubmodule_injective

-- TODO: add `ConvexConeClass` that extends `SetLike` and replace the below instance
instance : SetLike (ProperCone R E) E where
  coe C := C.carrier
  coe_injective _ _ h := ProperCone.toPointedCone_injective <| SetLike.coe_injective h

instance : PartialOrder (ProperCone R E) := .ofSetLike (ProperCone R E) E

/--
@isnad1 id=eq.1h4v.s7.3990e8d3ad86 from=seed src=0 shape=2e8a3d13 vocab=0cc22a37
-/
@[ext] lemma ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h

/--
@isnad1 id=iff.0h4v.s7.301cef860388 from=seed src=0 shape=08b974ee vocab=8b733a10
-/
lemma mem_toPointedCone : x ∈ C.toPointedCone ↔ x ∈ C := .rfl

/--
@isnad1 id=pointed.0h3v.s6.4cecd12812e9 from=seed src=0 shape=8032c8be vocab=ca28b55d
-/
lemma pointed_toConvexCone (C : ProperCone R E) : (C : ConvexCone R E).Pointed :=
  C.toPointedCone.pointed_toConvexCone

/--
@isnad1 id=nonempty.0h3v.s5.a80c944e8381 from=seed src=0 shape=c2a1c362 vocab=d30744c0
-/
protected lemma nonempty (C : ProperCone R E) : (C : Set E).Nonempty := C.toSubmodule.nonempty
/--
@isnad1 id=isclosed.0h3v.s5.78a3703c5784 from=seed src=0 shape=c2a1c362 vocab=f613e3f4
-/
protected lemma isClosed (C : ProperCone R E) : IsClosed (C : Set E) := C.isClosed'
/--
@isnad1 id=convex.0h3v.s6.68740f6041d8 from=seed src=0 shape=4dad9fe7 vocab=597cbce3
-/
protected lemma convex (C : ProperCone R E) : Convex R (C : Set E) := C.toPointedCone.convex

/--
@isnad1 id=mem.2h5v.s7.ee79f56a3f09 from=seed src=0 shape=54b973c3 vocab=07cdb2aa
-/
protected nonrec lemma smul_mem (C : ProperCone R E) (hx : x ∈ C) (hr : 0 ≤ r) : r • x ∈ C :=
  C.smul_mem ⟨r, hr⟩ hx

section T1Space
variable [T1Space E]

/--
@isnad1 id=iff.0h3v.s8.c2f4617056d0 from=seed src=0 shape=8c524d51 vocab=22a304b8
-/
lemma mem_bot : x ∈ (⊥ : ProperCone R E) ↔ x = 0 := .rfl

/--
@isnad1 id=eq.0h2v.s8.000ff5f3fe24 from=seed src=0 shape=f9a19ddb vocab=0ce60055
-/
@[simp, norm_cast] lemma coe_bot : (⊥ : ProperCone R E) = ({0} : Set E) := rfl
/--
@isnad1 id=eq.0h2v.s8.0bbc317f8ab5 from=seed src=0 shape=034ac196 vocab=4e3c885c
-/
@[simp, norm_cast] lemma toPointedCone_bot : (⊥ : ProperCone R E).toPointedCone = ⊥ := rfl

end T1Space

/-- The closure of image of a proper cone under an `R`-linear map is a proper cone. We
use continuous maps here so that the comap of f is also a map between proper cones. -/
abbrev comap (f : E →L[R] F) (C : ProperCone R F) : ProperCone R E :=
  ClosedSubmodule.comap (f.restrictScalars R≥0) C

/--
@isnad1 id=eq.0h3v.s6.f32afeb135b3 from=seed src=0 shape=bacbfdd9 vocab=c27e30c6
-/
@[simp] lemma comap_id (C : ProperCone R F) : C.comap (.id _ _) = C := rfl

/--
@isnad1 id=eq.0h5v.s7.f116e49f00ea from=seed src=0 shape=fb8fd609 vocab=5f928b26
-/
@[simp] lemma coe_comap (f : E →L[R] F) (C : ProperCone R F) : (C.comap f : Set E) = f ⁻¹' C := rfl

/--
@isnad1 id=eq.0h7v.s7.26b2e1421cf3 from=seed src=0 shape=c5ba3d17 vocab=224e1b52
-/
lemma comap_comap (g : F →L[R] G) (f : E →L[R] F) (C : ProperCone R G) :
    (C.comap g).comap f = C.comap (g.comp f) := rfl

/--
@isnad1 id=iff.0h6v.s7.c0f35a409ae9 from=seed src=0 shape=c4142f4a vocab=189ee22b
-/
lemma mem_comap {C : ProperCone R F} {f : E →L[R] F} : x ∈ C.comap f ↔ f x ∈ C := .rfl

variable [ContinuousAdd F] [ContinuousConstSMul R F]

/-- The closure of image of a proper cone under a linear map is a proper cone.

We use continuous maps here to match `ProperCone.comap`. -/
abbrev map (f : E →L[R] F) (C : ProperCone R E) : ProperCone R F :=
  ClosedSubmodule.map (f.restrictScalars R≥0) C

/--
@isnad1 id=eq.0h3v.s6.95706ad3f118 from=seed src=0 shape=847f83e4 vocab=6a9d0118
-/
@[simp] lemma map_id (C : ProperCone R F) : C.map (.id _ _) = C := ClosedSubmodule.map_id _

/--
@isnad1 id=eq.0h5v.s7.84562336024a from=seed src=0 shape=596983b7 vocab=5ac76153
-/
@[simp, norm_cast]
lemma coe_map (f : E →L[R] F) (C : ProperCone R E) :
    C.map f = (C.toPointedCone.map (f : E →ₗ[R] F)).closure := rfl

/--
@isnad1 id=iff.0h6v.s8.f646fb4fe48c from=seed src=0 shape=53e8b1a0 vocab=4d6d6d32
-/
@[simp]
lemma mem_map {f : E →L[R] F} {C : ProperCone R E} {y : F} :
    y ∈ C.map f ↔ y ∈ (C.toPointedCone.map (f : E →ₗ[R] F)).closure := .rfl

end Module

section PositiveCone
variable [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono R E] [OrderClosedTopology E] {x : E}

variable (R E) in
/-- The positive cone is the proper cone formed by the set of nonnegative elements in an ordered
module. -/
@[simps!]
def positive : ProperCone R E where
  toSubmodule := PointedCone.positive R E
  isClosed' := isClosed_Ici

/--
@isnad1 id=iff.0h3v.s7.9f7ff431d1e0 from=seed src=0 shape=a3dbdd56 vocab=4b881b6c
-/
@[simp] lemma mem_positive : x ∈ positive R E ↔ 0 ≤ x := .rfl
/--
@isnad1 id=eq.0h2v.s7.b4348bf7f078 from=seed src=0 shape=1fa55082 vocab=79f4b747
-/
@[simp] lemma toPointedCone_positive : (positive R E).toPointedCone = .positive R E := rfl

end PositiveCone
end ProperCone

/-!
### Topological properties of convex cones

This section proves topological results about convex cones.
-/

namespace ConvexCone
variable [Semifield 𝕜] [LinearOrder 𝕜] [Module 𝕜 E]

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
  [ContinuousSMul 𝕜 E] {C : ConvexCone 𝕜 E}

/--
@isnad1 id=pointed.2h3v.s8.d104aa5ddd22 from=seed src=0 shape=8717e8b3 vocab=d0272e31
-/
lemma Pointed.of_nonempty_of_isClosed (hC : (C : Set E).Nonempty) (hSclos : IsClosed (C : Set E)) :
    C.Pointed := by
  obtain ⟨x, hx⟩ := hC
  let f : 𝕜 → E := (· • x)
  -- The closure of `f (0, ∞)` is a subset of `C`
  have hfS : closure (f '' Set.Ioi 0) ⊆ C :=
    hSclos.closure_subset_iff.2 <| by rintro _ ⟨_, h, rfl⟩; exact C.smul_mem h hx
  -- `f` is continuous at `0` from the right
  have fc : ContinuousWithinAt f (Set.Ioi (0 : 𝕜)) 0 := by fun_prop
  -- `0 ∈ closure f (0, ∞) ⊆ C, 0 ∈ C`
  simpa [f, Pointed, ← SetLike.mem_coe] using hfS <| fc.mem_closure_image <| by simp

variable [IsOrderedRing 𝕜]

/--
@isnad1 id=canlift.0h2v.s9.0dda5e6187f5 from=seed src=0 shape=c8cf4200 vocab=2723011a
-/
instance canLift : CanLift (ConvexCone 𝕜 E) (ProperCone 𝕜 E) (↑)
    fun C ↦ (C : Set E).Nonempty ∧ IsClosed (C : Set E) where
  prf C hC := ⟨⟨C.toPointedCone <| .of_nonempty_of_isClosed hC.1 hC.2, hC.2⟩, rfl⟩

end ConvexCone
