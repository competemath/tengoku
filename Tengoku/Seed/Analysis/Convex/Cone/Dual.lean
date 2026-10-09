/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Convex.Cone.Basic
public import Tengoku.Seed.Analysis.LocallyConvex.Separation
public import Tengoku.Seed.Geometry.Convex.Cone.Dual
public import Tengoku.Seed.Topology.Algebra.Module.PerfectPairing

/-!
# The topological dual of a cone and Farkas' lemma

Given a continuous bilinear pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`,
we define `ProperCone.dual p C` to be the proper cone in `N` consisting of all points `y` such that
`0 ≤ p x y` for all `x ∈ s`.

When the pairing is perfect, this gives us the algebraic dual of a cone.
See `Mathlib/Geometry/Convex/Cone/Dual.lean` for that case.
When the pairing is continuous and perfect (as a continuous pairing), this gives us the topological
dual instead. This is developed here.

We prove Farkas' lemma, which says that a proper cone `C` in a locally convex topological real
vector space `E` and a point `x₀` not in `C` can be separated by a hyperplane. This is a geometric
interpretation of the Hahn-Banach separation theorem.
As a corollary, we prove that the double dual of a proper cone is itself.

## Main statements

We prove the following theorems:
* `ProperCone.hyperplane_separation`, `ProperCone.hyperplane_separation_point`: Farkas lemma.
* `ProperCone.dual_dual_flip`, `ProperCone.dual_flip_dual`: The double dual of a proper cone.

## References

* https://en.wikipedia.org/wiki/Hyperplane_separation_theorem
* https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation
-/

@[expose] public section

assert_not_exists InnerProductSpace

open Set LinearMap Pointwise

namespace PointedCone
variable {R M N : Type*} [CommRing R] [PartialOrder R] [TopologicalSpace R] [ClosedIciTopology R]
  [IsOrderedRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [TopologicalSpace N]
  {p : M →ₗ[R] N →ₗ[R] R} {s : Set M}

/--
@isnad1 id=isclosed.1h5v.s9.228a13242831 from=seed src=0 shape=86f39f89 vocab=605bd9cc
-/
lemma isClosed_dual (hp : ∀ x, Continuous (p x)) : IsClosed (dual p s : Set N) := by
  rw [← s.biUnion_of_singleton]
  simp_rw [dual_iUnion, Submodule.coe_iInf, dual_singleton]
  exact isClosed_biInter fun x hx ↦ isClosed_Ici.preimage <| hp _

end PointedCone

namespace ProperCone
variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [ClosedIciTopology R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]
  {p : M →ₗ[R] N →ₗ[R] R} [p.IsContPerfPair] {s t : Set M} {y : N}

variable (p s) in
/-- The dual cone of a set `s` with respect to a perfect pairing `p` is the cone consisting of all
points `y` such that for all points `x ∈ s` we have `0 ≤ p x y`. -/
def dual (s : Set M) : ProperCone R N where
  toSubmodule := PointedCone.dual p s
  isClosed' := PointedCone.isClosed_dual fun _ ↦ p.continuous_of_isContPerfPair

/--
@isnad1 id=iff.0h6v.s9.3c3f522f386e from=seed src=0 shape=0edab63c vocab=de457271
-/
@[simp] lemma mem_dual : y ∈ dual p s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ p x y := .rfl

/--
@isnad1 id=eq.0h4v.s9.68f251c80879 from=seed src=0 shape=98300a82 vocab=e41f4214
-/
@[simp] lemma dual_empty : dual p ∅ = ⊤ := by ext; simp
/--
@isnad1 id=eq.0h4v.s9.808df0241410 from=seed src=0 shape=be2521cc vocab=b65ab73e
-/
@[simp] lemma dual_zero : dual p 0 = ⊤ := by ext; simp

/--
@isnad1 id=eq.0h4v.s9.4d1060b3ee0a from=seed src=0 shape=9fd86ed5 vocab=f2eb388f
-/
@[simp] lemma dual_univ [IsTopologicalRing R] [T1Space N] : dual p univ = ⊥ := by
  refine le_antisymm (fun y hy ↦ (_root_.map_eq_zero_iff _ p.flip.toContPerfPair.injective).1 ?_)
    (by simp)
  ext x
  exact (hy <| mem_univ x).antisymm' <| by simpa using hy <| mem_univ (-x)

/--
@isnad1 id=le.1h6v.s8.d039b33ffd69 from=seed src=0 shape=ef603df3 vocab=0fc08d28
-/
@[gcongr] lemma dual_le_dual (h : t ⊆ s) : dual p s ≤ dual p t := fun _y hy _x hx ↦ hy (h hx)

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `p x`.
@isnad1 id=eq.0h5v.s9.12bdf8d3e56a from=seed src=0 shape=7bca19e5 vocab=5b7829bf
-/
lemma dual_singleton [IsTopologicalRing R] [OrderClosedTopology R] (x : M) :
    dual p {x} = (positive R R).comap (p.toContPerfPair x) := by ext; simp

/--
@isnad1 id=eq.0h6v.s8.6f98de4268a3 from=seed src=0 shape=3348eb18 vocab=635dd3a4
-/
lemma dual_union (s t : Set M) : dual p (s ∪ t) = dual p s ⊓ dual p t := by aesop

/--
@isnad1 id=eq.0h6v.s8.da970ad13869 from=seed src=0 shape=85cd0db5 vocab=008c45af
-/
lemma dual_insert (x : M) (s : Set M) : dual p (insert x s) = dual p {x} ⊓ dual p s := by
  rw [insert_eq, dual_union]

/--
@isnad1 id=eq.0h6v.s8.d4930667e077 from=seed src=0 shape=dbfef652 vocab=6aeffa89
-/
lemma dual_iUnion {ι : Sort*} (f : ι → Set M) : dual p (⋃ i, f i) = ⨅ i, dual p (f i) := by
  ext; simp [forall_comm (α := M)]

/--
@isnad1 id=eq.0h5v.s8.e5e17d1d0ae8 from=seed src=0 shape=9ea802d5 vocab=9664f518
-/
lemma dual_sUnion (S : Set (Set M)) : dual p (⋃₀ S) = sInf (dual p '' S) := by
  ext; simp [forall_comm (α := M)]

/-- Any set is a subset of its double dual cone.
@isnad1 id=le.0h5v.s8.dc8bcc8948dd from=seed src=0 shape=d68a936e vocab=ef715398
-/
lemma subset_dual_dual : s ⊆ dual p.flip (dual p s) := fun _x hx _y hy ↦ hy hx

end ProperCone

namespace ProperCone
variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F]
  [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [Module ℝ F]
  {K : Set E} {x₀ : E}

/-- Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones.
@isnad1 id=ex.3h3v.s8.339b2ec515e5 from=seed src=0 shape=d1bdf0fd vocab=419dc1e8
-/
theorem hyperplane_separation (C : ProperCone ℝ E) (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    (hKC : Disjoint K C) : ∃ f : StrongDual ℝ E, (∀ x ∈ C, 0 ≤ f x) ∧ ∀ x ∈ K, f x < 0 := by
  obtain rfl | ⟨x₀, hx₀⟩ := K.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  obtain ⟨f, u, v, hu, huv, hv⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp C.convex C.isClosed hKC
  have hv₀ : v < 0 := by simpa using hv 0 C.zero_mem
  refine ⟨f, fun x hx ↦ ?_, fun x hx ↦ (hu x hx).trans_le <| huv.le.trans hv₀.le⟩
  by_contra! hx₀
  simpa [hx₀.ne] using hv ((v * (f x)⁻¹) • x)
    (C.smul_mem hx <| le_of_lt <| mul_pos_of_neg_of_neg hv₀ <| inv_neg''.2 hx₀)

/-- Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones.
@isnad1 id=ex.1h3v.s8.973604421df9 from=seed src=0 shape=1de3a786 vocab=48b143a5
-/
theorem hyperplane_separation_point (C : ProperCone ℝ E) (hx₀ : x₀ ∉ C) :
    ∃ f : StrongDual ℝ E, (∀ x ∈ C, 0 ≤ f x) ∧ f x₀ < 0 := by
  simpa [*] using C.hyperplane_separation (convex_singleton x₀)

/-- The **double dual of a proper cone** is itself.
@isnad1 id=eq.0h4v.s8.b32ecc2d7a79 from=seed src=0 shape=ce831d76 vocab=47bcc1ce
-/
@[simp] theorem dual_flip_dual (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [p.IsContPerfPair] (C : ProperCone ℝ E) :
    dual p.flip (dual p (C : Set E)) = C := by
  refine le_antisymm (fun x ↦ ?_) subset_dual_dual
  simp only [mem_dual, SetLike.mem_coe]
  contrapose!
  simpa [p.flip.toContPerfPair.surjective.exists] using C.hyperplane_separation_point

/-- The **double dual of a proper cone** is itself.
@isnad1 id=eq.0h4v.s8.5f713073028c from=seed src=0 shape=3a08357e vocab=47bcc1ce
-/
@[simp] theorem dual_dual_flip (p : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) [p.IsContPerfPair] (C : ProperCone ℝ E) :
    dual p (dual p.flip (C : Set E)) = C := C.dual_flip_dual p.flip

end ProperCone
