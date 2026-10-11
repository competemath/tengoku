/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.PO.ID.Partial.SupportFunction.Calculus
public import Tengoku

/-! # Set-Valued Random Variables and Minkowski Means

This file develops the convex-geometric substrate for random closed sets whose
values are nonempty compact convex subsets of an inner-product space. Its main
role in the library is to identify the support function of an empirical
Minkowski average with the ordinary average of scalar support functions.

Main declarations:
* `IsBody` is a local predicate on raw sets asserting nonemptiness, compactness,
  and convexity.
* `isBody_finsetSum` shows that finite Minkowski sums preserve bodies.
* `supportFn_finsetSum` makes support functions commute with finite Minkowski
  sums.
* `minkowskiMean` and `supportFn_minkowskiMean` identify the support function
  of an empirical Minkowski average with the average of support functions.
-/

@[expose] public section

open scoped RealInnerProductSpace Pointwise

namespace Causalean.PartialID.RandomSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The local body predicate requires a raw subset to be [nonempty](hyp:nonempty),
[compact](hyp:isCompact), and [convex](hyp:convex).

This is an unbundled predicate on sets, not Mathlib's bundled `ConvexBody` type. -/
structure IsBody (C : Set E) : Prop where
  nonempty : C.Nonempty
  isCompact : IsCompact C
  convex : Convex ℝ C

/-- On a compact set the linear functional `⟪d, ·⟫` is bounded above.
@isnad1 id=bddabove.1h3v.s5.3abef8468b14 from=translated src=- shape=124556b6 vocab=151168fc
-/
lemma bddAbove_inner_image {C : Set E} (hC : IsCompact C) (d : E) :
    BddAbove ((fun x => ⟪d, x⟫) '' C) := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : E)
  refine ⟨‖d‖ * R, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxR : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
  calc ⟪d, x⟫ ≤ ‖d‖ * ‖x‖ := real_inner_le_norm d x
    _ ≤ ‖d‖ * R := mul_le_mul_of_nonneg_left hxR (norm_nonneg d)

/-- The support function of a body is bounded above, hence meaningful.
@isnad1 id=bddabove.1h3v.s5.28dcb7fddc4d from=translated src=- shape=124556b6 vocab=28205bc4
-/
lemma IsBody.bddAbove {C : Set E} (h : IsBody C) (d : E) :
    BddAbove ((fun x => ⟪d, x⟫) '' C) :=
  bddAbove_inner_image h.isCompact d

/-- A finite Minkowski sum of bodies is a body.
@isnad1 id=isbody.1h4v.s6.974cb4b9e82c from=translated src=- shape=33ee8065 vocab=6e1db286
-/
lemma isBody_finsetSum {ι : Type*} (s : Finset ι) (F : ι → Set E)
    (h : ∀ i ∈ s, IsBody (F i)) : IsBody (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, ← Set.singleton_zero]
      exact ⟨Set.singleton_nonempty 0, isCompact_singleton, convex_singleton 0⟩
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have ha := h a (Finset.mem_insert_self a s)
      have hr := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      exact ⟨ha.nonempty.add hr.nonempty, ha.isCompact.add hr.isCompact,
        ha.convex.add hr.convex⟩

/-- **Support function commutes with finite Minkowski sums**:
`s(∑ᵢ Fᵢ, d) = ∑ᵢ s(Fᵢ, d)`.
@isnad1 id=eq.1h5v.s6.91fb27b3c064 from=translated src=- shape=76c69a26 vocab=06b22eba
-/
theorem supportFn_finsetSum {ι : Type*} (s : Finset ι) (F : ι → Set E) (d : E)
    (h : ∀ i ∈ s, IsBody (F i)) :
    supportFn (∑ i ∈ s, F i) d = ∑ i ∈ s, supportFn (F i) d := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, ← Set.singleton_zero, supportFn,
        Set.image_singleton, inner_zero_right, csSup_singleton]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have ha := h a (Finset.mem_insert_self a s)
      have hr := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hbody := isBody_finsetSum s F hr
      rw [supportFn_minkowski ha.nonempty hbody.nonempty (ha.bddAbove d)
        (hbody.bddAbove d), ih hr]

/-- For [an inner-product outcome space](hyp:E), [an index population](hyp:ι), [a finite index
set](hyp:s), and [a family of subsets of that space](hyp:F), the [empirical Minkowski average](goal)
is the Minkowski sum of the selected sets, scaled by the reciprocal of the
number of selected indices.

The empirical Minkowski average is `(1/|s|) • ∑_{i∈s} Fᵢ`. -/
noncomputable def minkowskiMean {ι : Type*} (s : Finset ι) (F : ι → Set E) : Set E :=
  (s.card : ℝ)⁻¹ • (∑ i ∈ s, F i)

/-- **Keystone — Minkowski-mean support bridge.** Given [a finite index set `s` all of whose
values `F i` are bodies — nonempty, compact, convex subsets](hyp:h), [the support function of the
empirical Minkowski average `(1/|s|) · ∑ᵢ Fᵢ` in a direction `d` equals the arithmetic average of
the individual support functions: `s(d, F̄ₙ) = (1/|s|) · ∑ᵢ s(d, Fᵢ)`](goal). This is the identity
that turns the support process into an ordinary sample mean, so the multivariate CLT applies.
@isnad1 id=eq.1h5v.s6.51fb137d5b33 from=translated src=- shape=cfe3f92d vocab=5ed2d9bd
-/
theorem supportFn_minkowskiMean {ι : Type*} (s : Finset ι) (F : ι → Set E) (d : E)
    (h : ∀ i ∈ s, IsBody (F i)) :
    supportFn (minkowskiMean s F) d
      = (s.card : ℝ)⁻¹ * ∑ i ∈ s, supportFn (F i) d := by
  rw [minkowskiMean,
    supportFn_smul_set (by positivity) (isBody_finsetSum s F h).nonempty
      ((isBody_finsetSum s F h).bddAbove d),
    supportFn_finsetSum s F d h]

end Causalean.PartialID.RandomSet
