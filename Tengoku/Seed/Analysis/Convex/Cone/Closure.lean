/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Geometry.Convex.Cone.Pointed
public import Tengoku.Seed.Topology.Algebra.ConstMulAction
public import Tengoku.Seed.Topology.Algebra.Monoid.Defs

/-!
# Closure of cones

We define the closures of convex and pointed cones. This construction is primarily needed for
defining maps between proper cones. The current API is basic and should be extended as necessary.

-/

@[expose] public section

namespace ConvexCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [SMul 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/-- The closure of a convex cone inside a topological space as a convex cone. This
construction is mainly used for defining maps between proper cones. -/
protected def closure (K : ConvexCone 𝕜 E) : ConvexCone 𝕜 E where
  carrier := closure ↑K
  smul_mem' c hc _ h₁ := map_mem_closure (by fun_prop) h₁ fun _ h₂ ↦ K.smul_mem hc h₂
  add_mem' _ h₁ _ h₂ := map_mem_closure₂ continuous_add h₁ h₂ K.add_mem

/--
@isnad1 id=eq.0h3v.s6.419d3a6718db from=seed src=0 shape=38f7d81a vocab=189cf052
-/
@[simp, norm_cast]
theorem coe_closure (K : ConvexCone 𝕜 E) : (K.closure : Set E) = closure K :=
  rfl

/--
@isnad1 id=iff.0h4v.s6.b668fe65fcfd from=seed src=0 shape=ec8e07d3 vocab=2774c2c4
-/
@[simp]
protected theorem mem_closure {K : ConvexCone 𝕜 E} {a : E} :
    a ∈ K.closure ↔ a ∈ closure (K : Set E) :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s6.ba284c7cce31 from=seed src=0 shape=b4597648 vocab=189cf052
-/
@[simp]
theorem closure_eq {K L : ConvexCone 𝕜 E} : K.closure = L ↔ closure (K : Set E) = L :=
  SetLike.ext'_iff

end ConvexCone



namespace PointedCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/--
@isnad1 id=pointed.0h3v.s7.6ceb981fca67 from=seed src=0 shape=432d7a66 vocab=a4cc3616
-/
lemma toConvexCone_closure_pointed (K : PointedCone 𝕜 E) : (K : ConvexCone 𝕜 E).closure.Pointed :=
  subset_closure <| PointedCone.pointed_toConvexCone _

/-- The closure of a pointed cone inside a topological space as a pointed cone. This
construction is mainly used for defining maps between proper cones. -/
protected def closure (K : PointedCone 𝕜 E) : PointedCone 𝕜 E where
  carrier := closure ↑K
  zero_mem' := subset_closure (zero_mem K)
  smul_mem' c _ h₁ := map_mem_closure (continuous_const_smul c.1) h₁ fun _ h₂ ↦ K.smul_mem c.2 h₂
  add_mem' h₁ h₂ := map_mem_closure₂ continuous_add h₁ h₂ (fun _ ha _ hb ↦ K.add_mem ha hb)

/--
@isnad1 id=eq.0h3v.s7.e25fd24d49b2 from=seed src=0 shape=7b5b3b69 vocab=8dabf38c
-/
@[simp, norm_cast]
theorem coe_closure (K : PointedCone 𝕜 E) : (K.closure : Set E) = closure K :=
  rfl

/--
@isnad1 id=iff.0h4v.s7.ce571793362c from=seed src=0 shape=2cb3eef4 vocab=81f1f42b
-/
@[simp]
protected theorem mem_closure {K : PointedCone 𝕜 E} {a : E} :
    a ∈ K.closure ↔ a ∈ closure (K : Set E) :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s7.3866b098697b from=seed src=0 shape=b34642a1 vocab=8dabf38c
-/
@[simp]
theorem closure_eq {K L : PointedCone 𝕜 E} : K.closure = L ↔ closure (K : Set E) = L :=
  SetLike.ext'_iff

end PointedCone
