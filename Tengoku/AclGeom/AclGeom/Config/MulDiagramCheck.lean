/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.Soundness
import Tengoku.AclGeom.AclGeom.Config.Multiplication

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The coordinate check for the multiplication diagram

The forward half of blueprint Lemma mul-diagram: for algebraically
independent `x, y, a`, the eight points

`X = [x], Y = [y], V = [x/y], E = [xy], A₀ = [a], B₀ = [ax], C₀ = [ay],
D₀ = [axy]`

satisfy `MulDiagram`. Every displayed line follows from one rational
identity (`ax = a·x`, `axy = (ax)·y = x·(ay) = a·(xy)`,
`x/y = (ax)/(ay)`), verified with the rank bridge; this file provides
the entry kit, the line-pair independences, and the rank clauses.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the forward multiplication-diagram table and semantic Q′/J soundness are
proved. The multiplication converse and ACF completeness are proved in
`Config.MultiplicationConverse` and `Config.Completeness`. Original source group/chunk
and scheme/action statements remain separate obligations.
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

section MulTable

variable {x y a : K} (hind : AlgebraicIndependent k ![x, y, a])

include hind

/-! ### Generator projections -/

/--
@isnad1 id=not.1h5v.s6.0ee3f2dce7cf from=translated src=- shape=41b7eb3a vocab=f4889937
-/
theorem mtable_x_notMem_empty : x ∉ racl k (∅ : Set K) := fun h ↦
  AlgebraicIndependent.transcendental hind 0
    (isAlgebraic_of_mem_racl_empty h)

/--
@isnad1 id=not.1h5v.s6.2ec87f80321e from=translated src=- shape=2d97ab55 vocab=f4889937
-/
theorem mtable_y_notMem_empty : y ∉ racl k (∅ : Set K) := fun h ↦
  AlgebraicIndependent.transcendental hind 1
    (isAlgebraic_of_mem_racl_empty h)

/--
@isnad1 id=not.1h5v.s6.a77e67feb55a from=translated src=- shape=26e84643 vocab=f4889937
-/
theorem mtable_a_notMem_empty : a ∉ racl k (∅ : Set K) := fun h ↦
  AlgebraicIndependent.transcendental hind 2
    (isAlgebraic_of_mem_racl_empty h)

/--
@isnad1 id=ne.1h5v.s6.09361b722c23 from=translated src=- shape=cdb9ccaf vocab=dd1bc422
-/
theorem mtable_x_ne_zero : x ≠ 0 := by
  intro h0
  have h := mtable_x_notMem_empty hind
  rw [h0] at h
  exact h (zero_mem _)

/--
@isnad1 id=ne.1h5v.s6.956b0df079bd from=translated src=- shape=13c91934 vocab=dd1bc422
-/
theorem mtable_y_ne_zero : y ≠ 0 := by
  intro h0
  have h := mtable_y_notMem_empty hind
  rw [h0] at h
  exact h (zero_mem _)

/--
@isnad1 id=ne.1h5v.s6.3461fb857aca from=translated src=- shape=72107609 vocab=dd1bc422
-/
theorem mtable_a_ne_zero : a ≠ 0 := by
  intro h0
  have h := mtable_a_notMem_empty hind
  rw [h0] at h
  exact h (zero_mem _)

/--
@isnad1 id=not.1h5v.s6.892cb13c3f0a from=translated src=- shape=0e85dda4 vocab=4789c72c
-/
theorem mtable_y_notMem_x : y ∉ racl k ({x} : Set K) := by
  have h : AlgebraicIndependent k ![x, y] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 0) (j := 1) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair h

/--
@isnad1 id=not.1h5v.s6.8acf0ee90f9e from=translated src=- shape=2c47ae94 vocab=4789c72c
-/
theorem mtable_x_notMem_y : x ∉ racl k ({y} : Set K) := by
  have h : AlgebraicIndependent k ![x, y] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 0) (j := 1) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

/--
@isnad1 id=not.1h5v.s6.7ab89bc32eb6 from=translated src=- shape=bd335f8c vocab=4789c72c
-/
theorem mtable_a_notMem_x : a ∉ racl k ({x} : Set K) := by
  have h : AlgebraicIndependent k ![x, a] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 0) (j := 2) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair h

/--
@isnad1 id=not.1h5v.s6.7d7882b91955 from=translated src=- shape=fd081f50 vocab=4789c72c
-/
theorem mtable_a_notMem_y : a ∉ racl k ({y} : Set K) := by
  have h : AlgebraicIndependent k ![y, a] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 1) (j := 2) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair h

/--
@isnad1 id=not.1h5v.s6.5bfa44d7b699 from=translated src=- shape=bdacca43 vocab=4b0dde1a
-/
theorem mtable_a_notMem_xy : a ∉ racl k ({x, y} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 1}) (i := 2) (by decide)
  simpa [Set.image_insert_eq] using h

/--
@isnad1 id=not.1h5v.s6.c5dc75d46e6b from=translated src=- shape=3bb706b3 vocab=4b0dde1a
-/
theorem mtable_x_notMem_ay : x ∉ racl k ({a, y} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {2, 1}) (i := 0) (by decide)
  simpa [Set.image_insert_eq] using h

/--
@isnad1 id=not.1h5v.s6.9120b4547d71 from=translated src=- shape=964a0773 vocab=4b0dde1a
-/
theorem mtable_y_notMem_ax : y ∉ racl k ({a, x} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {2, 0}) (i := 1) (by decide)
  simpa [Set.image_insert_eq] using h

/-! ### Transcendence of the composite entries -/

/-- `x/y` is a point.
@isnad1 id=not.1h5v.s7.1332794091dc from=translated src=- shape=1f634c5c vocab=fade4ae6
-/
theorem mtable_div_notMem_bot : x / y ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {y} ?_ (mtable_x_notMem_y hind)
  have hq : x / y ∈ racl k (insert (x / y) ({y} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hy : y ∈ racl k (insert (x / y) ({y} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem hq hy
  rwa [div_mul_cancel₀ x (mtable_y_ne_zero hind)] at h

/-- `xy` is a point.
@isnad1 id=not.1h5v.s7.ae8d8f1387c6 from=translated src=- shape=1f634c5c vocab=c99eb412
-/
theorem mtable_mul_notMem_bot : x * y ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {y} ?_ (mtable_x_notMem_y hind)
  have hm : x * y ∈ racl k (insert (x * y) ({y} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hy : y ∈ racl k (insert (x * y) ({y} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem hm (inv_mem hy)
  rwa [mul_inv_cancel_right₀ (mtable_y_ne_zero hind)] at h

/-- `ax` is a point.
@isnad1 id=not.1h5v.s7.d12d89cbe5e9 from=translated src=- shape=2b4628ed vocab=c99eb412
-/
theorem mtable_ax_notMem_bot : a * x ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover (w := x) {a} ?_ ?_
  · have hm : a * x ∈ racl k (insert (a * x) ({a} : Set K)) :=
      subset_racl k _ (Set.mem_insert _ _)
    have ha : a ∈ racl k (insert (a * x) ({a} : Set K)) :=
      subset_racl k _ (Set.mem_insert_of_mem _ rfl)
    have h := MulMemClass.mul_mem (inv_mem ha) hm
    rwa [inv_mul_cancel_left₀ (mtable_a_ne_zero hind)] at h
  · intro h
    have h2 : AlgebraicIndependent k ![a, x] := by
      simpa using AlgebraicIndependent.comp_pair hind
        (i := 2) (j := 0) (by decide)
    exact AlgebraicIndependent.notMem_racl_pair h2 h

/-- `ay` is a point.
@isnad1 id=not.1h5v.s7.794983c89439 from=translated src=- shape=04e16d85 vocab=c99eb412
-/
theorem mtable_ay_notMem_bot : a * y ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover (w := y) {a} ?_ ?_
  · have hm : a * y ∈ racl k (insert (a * y) ({a} : Set K)) :=
      subset_racl k _ (Set.mem_insert _ _)
    have ha : a ∈ racl k (insert (a * y) ({a} : Set K)) :=
      subset_racl k _ (Set.mem_insert_of_mem _ rfl)
    have h := MulMemClass.mul_mem (inv_mem ha) hm
    rwa [inv_mul_cancel_left₀ (mtable_a_ne_zero hind)] at h
  · intro h
    have h2 : AlgebraicIndependent k ![a, y] := by
      simpa using AlgebraicIndependent.comp_pair hind
        (i := 2) (j := 1) (by decide)
    exact AlgebraicIndependent.notMem_racl_pair h2 h

/-- `axy` is a point.
@isnad1 id=not.1h5v.s8.25964f3bb764 from=translated src=- shape=0aa2a6a7 vocab=c99eb412
-/
theorem mtable_axy_notMem_bot : a * x * y ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, y} ?_ (mtable_x_notMem_ay hind)
  set S : Set K := insert (a * x * y) {a, y} with hS
  have hm : a * x * y ∈ racl k S := subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k S :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hy : y ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := MulMemClass.mul_mem
    (inv_mem (MulMemClass.mul_mem ha hy)) hm
  have harith : (a * y)⁻¹ * (a * x * y) = x := by
    have hr : a * x * y = a * y * x := by ring
    rw [hr, inv_mul_cancel_left₀ (mul_ne_zero (mtable_a_ne_zero hind)
      (mtable_y_ne_zero hind))]
  rwa [harith] at h

/-! ### Independence of the line pairs -/

/--
@isnad1 id=algebrai.1h5v.s6.cece53bb6369 from=translated src=- shape=4349ac62 vocab=dd1bc422
-/
theorem mtable_indep_xa : AlgebraicIndependent k ![x, a] := by
  simpa using AlgebraicIndependent.comp_pair hind
    (i := 0) (j := 2) (by decide)

/--
@isnad1 id=algebrai.1h5v.s6.6888deb4f50e from=translated src=- shape=0b607ccb vocab=dd1bc422
-/
theorem mtable_indep_ay : AlgebraicIndependent k ![a, y] := by
  simpa using AlgebraicIndependent.comp_pair hind
    (i := 2) (j := 1) (by decide)

/--
@isnad1 id=algebrai.1h5v.s6.70f4a8241413 from=translated src=- shape=b27c240b vocab=dd1bc422
-/
theorem mtable_indep_xy : AlgebraicIndependent k ![x, y] := by
  simpa using AlgebraicIndependent.comp_pair hind
    (i := 0) (j := 1) (by decide)

/--
@isnad1 id=algebrai.1h5v.s7.c7f8d547f560 from=translated src=- shape=1bcde665 vocab=ef3de844
-/
theorem mtable_indep_a_xy : AlgebraicIndependent k ![a, x * y] := by
  refine algebraicIndependent_pair ?_ ?_
  · intro h
    have hsub : racl k ({x * y} : Set K) ≤ racl k ({x, y} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have hx : x ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
      have hy : y ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem hx hy
    exact mtable_a_notMem_xy hind (hsub h)
  · intro h
    have hm0 : x * y ∉ racl k (∅ : Set K) := by
      intro h2
      exact mtable_mul_notMem_bot hind
        (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h2))
    have h' : x * y ∈ racl k (insert a (∅ : Set K)) := by simpa using h
    have h2 := racl_exchange h' hm0
    have h3 : a ∈ racl k ({x * y} : Set K) := by simpa using h2
    have hsub : racl k ({x * y} : Set K) ≤ racl k ({x, y} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have hx : x ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
      have hy : y ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem hx hy
    exact mtable_a_notMem_xy hind (hsub h3)

/--
@isnad1 id=algebrai.1h5v.s7.5dfac7a684bc from=translated src=- shape=26065043 vocab=ef3de844
-/
theorem mtable_indep_ax_y : AlgebraicIndependent k ![a * x, y] := by
  refine algebraicIndependent_pair ?_ ?_
  · intro h
    have hax0 : a * x ∉ racl k (∅ : Set K) := by
      intro h2
      exact mtable_ax_notMem_bot hind
        (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h2))
    have h' : a * x ∈ racl k (insert y (∅ : Set K)) := by simpa using h
    have h2 := racl_exchange h' hax0
    have h3 : y ∈ racl k ({a * x} : Set K) := by simpa using h2
    have hsub : racl k ({a * x} : Set K) ≤ racl k ({a, x} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      have hx : x ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hx
    exact mtable_y_notMem_ax hind (hsub h3)
  · intro h
    have hsub : racl k ({a * x} : Set K) ≤ racl k ({a, x} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      have hx : x ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hx
    exact mtable_y_notMem_ax hind (hsub h)

/--
@isnad1 id=algebrai.1h5v.s7.22ec7c1c9bb7 from=translated src=- shape=a19c3874 vocab=ef3de844
-/
theorem mtable_indep_x_ay : AlgebraicIndependent k ![x, a * y] := by
  refine algebraicIndependent_pair ?_ ?_
  · intro h
    have hsub : racl k ({a * y} : Set K) ≤ racl k ({a, y} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      have hy : y ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hy
    exact mtable_x_notMem_ay hind (hsub h)
  · intro h
    have hay0 : a * y ∉ racl k (∅ : Set K) := by
      intro h2
      exact mtable_ay_notMem_bot hind
        (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h2))
    have h' : a * y ∈ racl k (insert x (∅ : Set K)) := by simpa using h
    have h2 := racl_exchange h' hay0
    have h3 : x ∈ racl k ({a * y} : Set K) := by simpa using h2
    have hsub : racl k ({a * y} : Set K) ≤ racl k ({a, y} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      have hy : y ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hy
    exact mtable_x_notMem_ay hind (hsub h3)

/--
@isnad1 id=algebrai.1h5v.s7.77ab7eb7a6eb from=translated src=- shape=33c1f3a9 vocab=ef3de844
-/
theorem mtable_indep_ax_ay : AlgebraicIndependent k ![a * x, a * y] := by
  refine algebraicIndependent_pair ?_ ?_
  · intro h
    have hsub : racl k ({a * y} : Set K) ≤ racl k ({a, y} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      have hy : y ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hy
    have h2 := hsub h
    have ha : a ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
    have hx : x ∈ racl k ({a, y} : Set K) := by
      have h3 := MulMemClass.mul_mem (inv_mem ha) h2
      rwa [inv_mul_cancel_left₀ (mtable_a_ne_zero hind)] at h3
    exact mtable_x_notMem_ay hind hx
  · intro h
    have hsub : racl k ({a * x} : Set K) ≤ racl k ({a, x} : Set K) := by
      refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
      have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      have hx : x ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
      exact MulMemClass.mul_mem ha hx
    have h2 := hsub h
    have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
    have hy : y ∈ racl k ({a, x} : Set K) := by
      have h3 := MulMemClass.mul_mem (inv_mem ha) h2
      rwa [inv_mul_cancel_left₀ (mtable_a_ne_zero hind)] at h3
    exact mtable_y_notMem_ax hind hy

/-! ### The seven rank-two lines and the nondegeneracy clause -/

/--
@isnad1 id=rankeq.1h5v.s7.99cfa04f8ce9 from=translated src=- shape=3b3e5aae vocab=61af493d
-/
theorem mtable_line_XAB :
    RankEq 2 (ClosedIF.point k x ⊔
      (ClosedIF.point k a ⊔ ClosedIF.point k (a * x))) := by
  refine rankEq_two_points (mtable_indep_xa hind) ?_
  refine racl_congr_of_subset_racl ?_ ?_
  · rw [Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    have hx : x ∈ racl k ({x, a} : Set K) := subset_racl k _ (by simp)
    have ha : a ∈ racl k ({x, a} : Set K) := subset_racl k _ (by simp)
    exact ⟨hx, ha, MulMemClass.mul_mem ha hx⟩
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨subset_racl k _ (by simp), subset_racl k _ (by simp)⟩

/--
@isnad1 id=rankeq.1h5v.s7.ce08af8ecc1b from=translated src=- shape=5e435e18 vocab=61af493d
-/
theorem mtable_line_AYC :
    RankEq 2 (ClosedIF.point k a ⊔
      (ClosedIF.point k y ⊔ ClosedIF.point k (a * y))) := by
  refine rankEq_two_points (mtable_indep_ay hind) ?_
  refine racl_congr_of_subset_racl ?_ ?_
  · rw [Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    have ha : a ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
    have hy : y ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
    exact ⟨ha, hy, MulMemClass.mul_mem ha hy⟩
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨subset_racl k _ (by simp), subset_racl k _ (by simp)⟩

/--
@isnad1 id=rankeq.1h5v.s7.5c8ee9db55cd from=translated src=- shape=24d3623b vocab=61af493d
-/
theorem mtable_line_AED :
    RankEq 2 (ClosedIF.point k a ⊔
      (ClosedIF.point k (x * y) ⊔ ClosedIF.point k (a * x * y))) := by
  refine rankEq_two_points (mtable_indep_a_xy hind) ?_
  refine racl_congr_of_subset_racl ?_ ?_
  · rw [Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    have ha : a ∈ racl k ({a, x * y} : Set K) := subset_racl k _ (by simp)
    have hm : x * y ∈ racl k ({a, x * y} : Set K) :=
      subset_racl k _ (by simp)
    have hprod := MulMemClass.mul_mem ha hm
    have harith : a * (x * y) = a * x * y := by ring
    rw [harith] at hprod
    exact ⟨ha, hm, hprod⟩
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨subset_racl k _ (by simp), subset_racl k _ (by simp)⟩

/--
@isnad1 id=rankeq.1h5v.s7.f8adcccc50d1 from=translated src=- shape=5c2f0f6a vocab=61af493d
-/
theorem mtable_line_BYD :
    RankEq 2 (ClosedIF.point k (a * x) ⊔
      (ClosedIF.point k y ⊔ ClosedIF.point k (a * x * y))) := by
  refine rankEq_two_points (mtable_indep_ax_y hind) ?_
  refine racl_congr_of_subset_racl ?_ ?_
  · rw [Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    have hax : a * x ∈ racl k ({a * x, y} : Set K) :=
      subset_racl k _ (by simp)
    have hy : y ∈ racl k ({a * x, y} : Set K) := subset_racl k _ (by simp)
    exact ⟨hax, hy, MulMemClass.mul_mem hax hy⟩
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨subset_racl k _ (by simp), subset_racl k _ (by simp)⟩

/--
@isnad1 id=rankeq.1h5v.s7.524e55c7ce6d from=translated src=- shape=2375c878 vocab=61af493d
-/
theorem mtable_line_XCD :
    RankEq 2 (ClosedIF.point k x ⊔
      (ClosedIF.point k (a * y) ⊔ ClosedIF.point k (a * x * y))) := by
  refine rankEq_two_points (mtable_indep_x_ay hind) ?_
  refine racl_congr_of_subset_racl ?_ ?_
  · rw [Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    have hx : x ∈ racl k ({x, a * y} : Set K) := subset_racl k _ (by simp)
    have hay : a * y ∈ racl k ({x, a * y} : Set K) :=
      subset_racl k _ (by simp)
    have hprod := MulMemClass.mul_mem hx hay
    have harith : x * (a * y) = a * x * y := by ring
    rw [harith] at hprod
    exact ⟨hx, hay, hprod⟩
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨subset_racl k _ (by simp), subset_racl k _ (by simp)⟩

/--
@isnad1 id=rankeq.1h5v.s7.10937f356764 from=translated src=- shape=e45c5c87 vocab=a3b48abd
-/
theorem mtable_line_BCV :
    RankEq 2 (ClosedIF.point k (a * x) ⊔
      (ClosedIF.point k (a * y) ⊔ ClosedIF.point k (x / y))) := by
  refine rankEq_two_points (mtable_indep_ax_ay hind) ?_
  refine racl_congr_of_subset_racl ?_ ?_
  · rw [Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    have hax : a * x ∈ racl k ({a * x, a * y} : Set K) :=
      subset_racl k _ (by simp)
    have hay : a * y ∈ racl k ({a * x, a * y} : Set K) :=
      subset_racl k _ (by simp)
    have hq := MulMemClass.mul_mem hax (inv_mem hay)
    have ha0 : a ≠ 0 := mtable_a_ne_zero hind
    have harith : a * x * (a * y)⁻¹ = x / y := by
      rw [mul_inv, div_eq_mul_inv,
        show a * x * (a⁻¹ * y⁻¹) = a * a⁻¹ * (x * y⁻¹) from by ring,
        mul_inv_cancel₀ ha0, one_mul]
    rw [harith] at hq
    exact ⟨hax, hay, hq⟩
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨subset_racl k _ (by simp), subset_racl k _ (by simp)⟩

/--
@isnad1 id=rankeq.1h5v.s8.e8b37521ec4b from=translated src=- shape=6eac4dd3 vocab=a3b48abd
-/
theorem mtable_line_XYEV :
    RankEq 2 (ClosedIF.point k x ⊔ (ClosedIF.point k y ⊔
      (ClosedIF.point k (x * y) ⊔ ClosedIF.point k (x / y)))) := by
  refine rankEq_of_coe_eq_racl (mtable_indep_xy hind) ?_
  rw [range_pair]
  have hx : x ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
  have hy : y ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
  have hm : x * y ∈ racl k ({x, y} : Set K) := MulMemClass.mul_mem hx hy
  have hq : x / y ∈ racl k ({x, y} : Set K) := by
    rw [div_eq_mul_inv]
    exact MulMemClass.mul_mem hx (inv_mem hy)
  refine ClosedIF.coe_eq_racl_of_le ?_ ?_
  · refine sup_le (ClosedIF.point_le_iff.2 hx) ?_
    refine sup_le (ClosedIF.point_le_iff.2 hy) ?_
    exact sup_le (ClosedIF.point_le_iff.2 hm) (ClosedIF.point_le_iff.2 hq)
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · exact (ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self x)
    · exact (ClosedIF.le_iff.1 (le_sup_left.trans le_sup_right))
        (ClosedIF.mem_point_self y)

/--
@isnad1 id=rankeq.1h5v.s7.70b4ed1501c8 from=translated src=- shape=d8e75bd6 vocab=0ef8016a
-/
theorem mtable_rank_XYA :
    RankEq 3 (ClosedIF.point k x ⊔
      (ClosedIF.point k y ⊔ ClosedIF.point k a)) := by
  exact rankEq_three_points hind rfl

/-! ### Distinctness kit -/

/--
@isnad1 id=not.1h5v.s7.ad33ae42e203 from=translated src=- shape=12d13c14 vocab=eb91f72f
-/
theorem mtable_x_notMem_bot : x ∉ (⊥ : ClosedIF k K) := fun h ↦
  AlgebraicIndependent.transcendental hind 0 (ClosedIF.mem_bot_iff.1 h)

/--
@isnad1 id=not.1h5v.s7.224f0aa90227 from=translated src=- shape=b0694137 vocab=eb91f72f
-/
theorem mtable_y_notMem_bot : y ∉ (⊥ : ClosedIF k K) := fun h ↦
  AlgebraicIndependent.transcendental hind 1 (ClosedIF.mem_bot_iff.1 h)

/--
@isnad1 id=not.1h5v.s7.40d178599dcf from=translated src=- shape=22563497 vocab=eb91f72f
-/
theorem mtable_a_notMem_bot : a ∉ (⊥ : ClosedIF k K) := fun h ↦
  AlgebraicIndependent.transcendental hind 2 (ClosedIF.mem_bot_iff.1 h)

/--
@isnad1 id=not.1h5v.s7.34d3c25b683e from=translated src=- shape=641b2a4e vocab=e2c4dba1
-/
theorem mtable_mul_notMem_empty : x * y ∉ racl k (∅ : Set K) := fun h ↦
  mtable_mul_notMem_bot hind
    (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h))

/--
@isnad1 id=not.1h5v.s7.4fd695f1d5cb from=translated src=- shape=e6bb97f1 vocab=e2c4dba1
-/
theorem mtable_ax_notMem_empty : a * x ∉ racl k (∅ : Set K) := fun h ↦
  mtable_ax_notMem_bot hind
    (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h))

/--
@isnad1 id=not.1h5v.s7.5902bc78f82c from=translated src=- shape=84af6b29 vocab=e2c4dba1
-/
theorem mtable_ay_notMem_empty : a * y ∉ racl k (∅ : Set K) := fun h ↦
  mtable_ay_notMem_bot hind
    (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h))

omit hind in
/--
@isnad1 id=le.0h4v.s6.57a3cf39cb82 from=translated src=- shape=e7c1a91d vocab=3afd211c
-/
theorem mtable_racl_div_le :
    racl k ({x / y} : Set K) ≤ racl k ({x, y} : Set K) := by
  refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
  have hx : x ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
  have hy : y ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
  rw [div_eq_mul_inv]
  exact MulMemClass.mul_mem hx (inv_mem hy)

omit hind in
/--
@isnad1 id=le.0h4v.s6.faf028cdc02a from=translated src=- shape=e7c1a91d vocab=0568c848
-/
theorem mtable_racl_mul_le :
    racl k ({x * y} : Set K) ≤ racl k ({x, y} : Set K) := by
  refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
  have hx : x ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
  have hy : y ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
  exact MulMemClass.mul_mem hx hy

omit hind in
/--
@isnad1 id=le.0h4v.s6.39c2ba003bcb from=translated src=- shape=01ce91c6 vocab=0568c848
-/
theorem mtable_racl_ax_le :
    racl k ({a * x} : Set K) ≤ racl k ({a, x} : Set K) := by
  refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
  have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
  have hx : x ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
  exact MulMemClass.mul_mem ha hx

omit hind in
/--
@isnad1 id=le.0h4v.s6.39c2ba003bcb from=translated src=- shape=01ce91c6 vocab=0568c848
-/
theorem mtable_racl_ay_le :
    racl k ({a * y} : Set K) ≤ racl k ({a, y} : Set K) := by
  refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
  have ha : a ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
  have hy : y ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
  exact MulMemClass.mul_mem ha hy

/--
@isnad1 id=not.1h5v.s6.8c05bbe6c5bc from=translated src=- shape=94eb8e7a vocab=4789c72c
-/
theorem mtable_x_notMem_a : x ∉ racl k ({a} : Set K) :=
  AlgebraicIndependent.notMem_racl_pair' (mtable_indep_xa hind)

/--
@isnad1 id=not.1h5v.s6.11804bf3d101 from=translated src=- shape=9dc08a4b vocab=4789c72c
-/
theorem mtable_y_notMem_a : y ∉ racl k ({a} : Set K) :=
  AlgebraicIndependent.notMem_racl_pair (mtable_indep_ay hind)

/-! ### Pairwise non-membership of the eight entries -/

/--
@isnad1 id=not.1h5v.s7.4e8e2d96ccaa from=translated src=- shape=f6600226 vocab=e6c9d6d3
-/
theorem mtable_ne02 : x / y ∉ racl k ({x} : Set K) := by
  intro h
  have hx : x ∈ racl k ({x} : Set K) := subset_racl k _ rfl
  have hq0 : x / y ≠ 0 :=
    div_ne_zero (mtable_x_ne_zero hind) (mtable_y_ne_zero hind)
  have hprod : (x / y) * y ∈ racl k ({x} : Set K) := by
    rw [div_mul_cancel₀ x (mtable_y_ne_zero hind)]
    exact hx
  exact mtable_y_notMem_x hind (mem_of_mul_mem_left h hq0 hprod)

/--
@isnad1 id=not.1h5v.s7.6f06893281b9 from=translated src=- shape=f6600226 vocab=a4570295
-/
theorem mtable_ne03 : x * y ∉ racl k ({x} : Set K) := by
  intro h
  have hx : x ∈ racl k ({x} : Set K) := subset_racl k _ rfl
  exact mtable_y_notMem_x hind
    (mem_of_mul_mem_left hx (mtable_x_ne_zero hind) h)

/--
@isnad1 id=not.1h5v.s7.30d3755b04e3 from=translated src=- shape=b5646e2d vocab=a4570295
-/
theorem mtable_ne05 : a * x ∉ racl k ({x} : Set K) := by
  intro h
  have hx : x ∈ racl k ({x} : Set K) := subset_racl k _ rfl
  exact mtable_a_notMem_x hind
    (mem_of_mul_mem_right hx (mtable_x_ne_zero hind) h)

/--
@isnad1 id=not.1h5v.s7.b9be8214e43f from=translated src=- shape=50da1804 vocab=a4570295
-/
theorem mtable_ne06 : a * y ∉ racl k ({x} : Set K) := by
  intro h
  have h' : a * y ∈ racl k (insert x (∅ : Set K)) := by simpa using h
  have h2 := racl_exchange h' (mtable_ay_notMem_empty hind)
  have h3 : x ∈ racl k ({a * y} : Set K) := by simpa using h2
  exact mtable_x_notMem_ay hind (mtable_racl_ay_le h3)

/--
@isnad1 id=not.1h5v.s7.ad337f4072a5 from=translated src=- shape=23199931 vocab=a4570295
-/
theorem mtable_ne07 : a * x * y ∉ racl k ({x} : Set K) := by
  intro h
  have hx : x ∈ racl k ({x} : Set K) := subset_racl k _ rfl
  have h' : a * y * x ∈ racl k ({x} : Set K) := by
    have harith : a * y * x = a * x * y := by ring
    rwa [harith]
  exact mtable_ne06 hind
    (mem_of_mul_mem_right hx (mtable_x_ne_zero hind) h')

/--
@isnad1 id=not.1h5v.s7.226eedbc585c from=translated src=- shape=bbcfed34 vocab=e6c9d6d3
-/
theorem mtable_ne12 : x / y ∉ racl k ({y} : Set K) := by
  intro h
  have hy : y ∈ racl k ({y} : Set K) := subset_racl k _ rfl
  have hx := MulMemClass.mul_mem h hy
  rw [div_mul_cancel₀ x (mtable_y_ne_zero hind)] at hx
  exact mtable_x_notMem_y hind hx

/--
@isnad1 id=not.1h5v.s7.fecf2be187e2 from=translated src=- shape=bbcfed34 vocab=a4570295
-/
theorem mtable_ne13 : x * y ∉ racl k ({y} : Set K) := by
  intro h
  have hy : y ∈ racl k ({y} : Set K) := subset_racl k _ rfl
  exact mtable_x_notMem_y hind
    (mem_of_mul_mem_right hy (mtable_y_ne_zero hind) h)

/--
@isnad1 id=not.1h5v.s7.f6e08abd737e from=translated src=- shape=c34a965e vocab=a4570295
-/
theorem mtable_ne15 : a * x ∉ racl k ({y} : Set K) := by
  intro h
  have h' : a * x ∈ racl k (insert y (∅ : Set K)) := by simpa using h
  have h2 := racl_exchange h' (mtable_ax_notMem_empty hind)
  have h3 : y ∈ racl k ({a * x} : Set K) := by simpa using h2
  exact mtable_y_notMem_ax hind (mtable_racl_ax_le h3)

/--
@isnad1 id=not.1h5v.s7.2f5231ca70b4 from=translated src=- shape=cf23e19d vocab=a4570295
-/
theorem mtable_ne16 : a * y ∉ racl k ({y} : Set K) := by
  intro h
  have hy : y ∈ racl k ({y} : Set K) := subset_racl k _ rfl
  exact mtable_a_notMem_y hind
    (mem_of_mul_mem_right hy (mtable_y_ne_zero hind) h)

/--
@isnad1 id=not.1h5v.s7.1f35fcc423bc from=translated src=- shape=198c87e2 vocab=a4570295
-/
theorem mtable_ne17 : a * x * y ∉ racl k ({y} : Set K) := by
  intro h
  have hy : y ∈ racl k ({y} : Set K) := subset_racl k _ rfl
  exact mtable_ne15 hind
    (mem_of_mul_mem_right hy (mtable_y_ne_zero hind) h)

/--
@isnad1 id=not.1h5v.s7.bd8de512c623 from=translated src=- shape=b66eceec vocab=5f155f7c
-/
theorem mtable_ne23 : x * y ∉ racl k ({x / y} : Set K) := by
  intro h
  have hq : x / y ∈ racl k ({x / y} : Set K) := subset_racl k _ rfl
  have hy0 : y ≠ 0 := mtable_y_ne_zero hind
  have hsq := MulMemClass.mul_mem h hq
  have harith : x * y * (x / y) = x ^ 2 := by
    field_simp
  rw [harith] at hsq
  have hx : x ∈ racl k ({x / y} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 hsq)
      (mem_racl_singleton_pow two_ne_zero)
  have hq0 : x / y ≠ 0 :=
    div_ne_zero (mtable_x_ne_zero hind) hy0
  have hprod : (x / y) * y ∈ racl k ({x / y} : Set K) := by
    rw [div_mul_cancel₀ x hy0]
    exact hx
  have hx' : x ∈ racl k (insert (x / y) (∅ : Set K)) := by simpa using hx
  have h2 := racl_exchange hx' (mtable_x_notMem_empty hind)
  have h3 : x / y ∈ racl k ({x} : Set K) := by simpa using h2
  have hprod2 : (x / y) * y ∈ racl k ({x} : Set K) := by
    rw [div_mul_cancel₀ x hy0]
    exact subset_racl k _ rfl
  exact mtable_y_notMem_x hind (mem_of_mul_mem_left h3 hq0 hprod2)

/--
@isnad1 id=not.1h5v.s7.02344e1b3652 from=translated src=- shape=e9fc07a9 vocab=e6c9d6d3
-/
theorem mtable_ne24 : a ∉ racl k ({x / y} : Set K) := fun h ↦
  mtable_a_notMem_xy hind (mtable_racl_div_le h)

/--
@isnad1 id=not.1h5v.s7.1539f53e9ab0 from=translated src=- shape=3667a110 vocab=5f155f7c
-/
theorem mtable_ne25 : a * x ∉ racl k ({x / y} : Set K) := by
  intro h
  have h' : a * x ∈ racl k (insert (x / y) (∅ : Set K)) := by simpa using h
  have h2 := racl_exchange h' (mtable_ax_notMem_empty hind)
  have h3 : x / y ∈ racl k ({a * x} : Set K) := by simpa using h2
  have h4 : x / y ∈ racl k ({a, x} : Set K) := mtable_racl_ax_le h3
  have hq0 : x / y ≠ 0 :=
    div_ne_zero (mtable_x_ne_zero hind) (mtable_y_ne_zero hind)
  have hprod : (x / y) * y ∈ racl k ({a, x} : Set K) := by
    rw [div_mul_cancel₀ x (mtable_y_ne_zero hind)]
    exact subset_racl k _ (by simp)
  exact mtable_y_notMem_ax hind (mem_of_mul_mem_left h4 hq0 hprod)

/--
@isnad1 id=not.1h5v.s7.6d61f132e193 from=translated src=- shape=0e445af7 vocab=5f155f7c
-/
theorem mtable_ne26 : a * y ∉ racl k ({x / y} : Set K) := by
  intro h
  have h' : a * y ∈ racl k (insert (x / y) (∅ : Set K)) := by simpa using h
  have h2 := racl_exchange h' (mtable_ay_notMem_empty hind)
  have h3 : x / y ∈ racl k ({a * y} : Set K) := by simpa using h2
  have h4 : x / y ∈ racl k ({a, y} : Set K) := mtable_racl_ay_le h3
  have hy : y ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
  have hx := MulMemClass.mul_mem h4 hy
  rw [div_mul_cancel₀ x (mtable_y_ne_zero hind)] at hx
  exact mtable_x_notMem_ay hind hx

/--
@isnad1 id=not.1h5v.s7.d904cf6b9875 from=translated src=- shape=7e79868e vocab=5f155f7c
-/
theorem mtable_ne27 : a * x * y ∉ racl k ({x / y} : Set K) := by
  intro h
  have h2 : a * x * y ∈ racl k ({x, y} : Set K) := mtable_racl_div_le h
  have hxy : x * y ∈ racl k ({x, y} : Set K) := by
    have hx : x ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
    have hy : y ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem hx hy
  have hxy0 : x * y ≠ 0 :=
    mul_ne_zero (mtable_x_ne_zero hind) (mtable_y_ne_zero hind)
  have h' : a * (x * y) ∈ racl k ({x, y} : Set K) := by
    have harith : a * (x * y) = a * x * y := by ring
    rwa [harith]
  exact mtable_a_notMem_xy hind
    (mem_of_mul_mem_right hxy hxy0 h')

/--
@isnad1 id=not.1h5v.s7.7f41a46f9f49 from=translated src=- shape=e9fc07a9 vocab=a4570295
-/
theorem mtable_ne34 : a ∉ racl k ({x * y} : Set K) := fun h ↦
  mtable_a_notMem_xy hind (mtable_racl_mul_le h)

/--
@isnad1 id=not.1h5v.s7.3c0e3c568150 from=translated src=- shape=3667a110 vocab=a4570295
-/
theorem mtable_ne35 : a * x ∉ racl k ({x * y} : Set K) := by
  intro h
  have h2 : a * x ∈ racl k ({x, y} : Set K) := mtable_racl_mul_le h
  have hx : x ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
  exact mtable_a_notMem_xy hind
    (mem_of_mul_mem_right hx (mtable_x_ne_zero hind) h2)

/--
@isnad1 id=not.1h5v.s7.dd5cde6d1555 from=translated src=- shape=0e445af7 vocab=a4570295
-/
theorem mtable_ne36 : a * y ∉ racl k ({x * y} : Set K) := by
  intro h
  have h2 : a * y ∈ racl k ({x, y} : Set K) := mtable_racl_mul_le h
  have hy : y ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
  exact mtable_a_notMem_xy hind
    (mem_of_mul_mem_right hy (mtable_y_ne_zero hind) h2)

/--
@isnad1 id=not.1h5v.s7.d15ce59985ad from=translated src=- shape=a4e63dfe vocab=a4570295
-/
theorem mtable_ne37 : a * x * y ∉ racl k ({x * y} : Set K) := by
  intro h
  have h2 : a * x * y ∈ racl k ({x, y} : Set K) := mtable_racl_mul_le h
  have hxy : x * y ∈ racl k ({x, y} : Set K) := by
    have hx : x ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
    have hy : y ∈ racl k ({x, y} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem hx hy
  have hxy0 : x * y ≠ 0 :=
    mul_ne_zero (mtable_x_ne_zero hind) (mtable_y_ne_zero hind)
  have h' : a * (x * y) ∈ racl k ({x, y} : Set K) := by
    have harith : a * (x * y) = a * x * y := by ring
    rwa [harith]
  exact mtable_a_notMem_xy hind
    (mem_of_mul_mem_right hxy hxy0 h')

/--
@isnad1 id=not.1h5v.s7.fec510b8fca7 from=translated src=- shape=7edf2dfc vocab=a4570295
-/
theorem mtable_ne45 : a * x ∉ racl k ({a} : Set K) := by
  intro h
  have ha : a ∈ racl k ({a} : Set K) := subset_racl k _ rfl
  exact mtable_x_notMem_a hind
    (mem_of_mul_mem_left ha (mtable_a_ne_zero hind) h)

/--
@isnad1 id=not.1h5v.s7.dcd1981bcba5 from=translated src=- shape=05c6127a vocab=a4570295
-/
theorem mtable_ne46 : a * y ∉ racl k ({a} : Set K) := by
  intro h
  have ha : a ∈ racl k ({a} : Set K) := subset_racl k _ rfl
  exact mtable_y_notMem_a hind
    (mem_of_mul_mem_left ha (mtable_a_ne_zero hind) h)

/--
@isnad1 id=not.1h5v.s7.58f69946436b from=translated src=- shape=d5c93cea vocab=a4570295
-/
theorem mtable_ne47 : a * x * y ∉ racl k ({a} : Set K) := by
  intro h
  have ha : a ∈ racl k ({a} : Set K) := subset_racl k _ rfl
  have h' : a * (x * y) ∈ racl k ({a} : Set K) := by
    have harith : a * (x * y) = a * x * y := by ring
    rwa [harith]
  have hxy : x * y ∈ racl k ({a} : Set K) :=
    mem_of_mul_mem_left ha (mtable_a_ne_zero hind) h'
  have hxy' : x * y ∈ racl k (insert a (∅ : Set K)) := by simpa using hxy
  have h2 := racl_exchange hxy' (mtable_mul_notMem_empty hind)
  have h3 : a ∈ racl k ({x * y} : Set K) := by simpa using h2
  exact mtable_a_notMem_xy hind (mtable_racl_mul_le h3)

/--
@isnad1 id=not.1h5v.s7.26b7a6f69ac0 from=translated src=- shape=31d12b5a vocab=a4570295
-/
theorem mtable_ne56 : a * y ∉ racl k ({a * x} : Set K) := by
  intro h
  have h2 : a * y ∈ racl k ({a, x} : Set K) := mtable_racl_ax_le h
  have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
  exact mtable_y_notMem_ax hind
    (mem_of_mul_mem_left ha (mtable_a_ne_zero hind) h2)

/--
@isnad1 id=not.1h5v.s7.897371cfe475 from=translated src=- shape=325fc348 vocab=a4570295
-/
theorem mtable_ne57 : a * x * y ∉ racl k ({a * x} : Set K) := by
  intro h
  have h2 : a * x * y ∈ racl k ({a, x} : Set K) := mtable_racl_ax_le h
  have hax : a * x ∈ racl k ({a, x} : Set K) := by
    have ha : a ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
    have hx : x ∈ racl k ({a, x} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem ha hx
  have hax0 : a * x ≠ 0 :=
    mul_ne_zero (mtable_a_ne_zero hind) (mtable_x_ne_zero hind)
  exact mtable_y_notMem_ax hind
    (mem_of_mul_mem_left hax hax0 h2)

/--
@isnad1 id=not.1h5v.s7.50631fd334dc from=translated src=- shape=311f50c9 vocab=a4570295
-/
theorem mtable_ne67 : a * x * y ∉ racl k ({a * y} : Set K) := by
  intro h
  have h2 : a * x * y ∈ racl k ({a, y} : Set K) := mtable_racl_ay_le h
  have hay : a * y ∈ racl k ({a, y} : Set K) := by
    have ha : a ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
    have hy : y ∈ racl k ({a, y} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem ha hy
  have hay0 : a * y ≠ 0 :=
    mul_ne_zero (mtable_a_ne_zero hind) (mtable_y_ne_zero hind)
  have h' : a * y * x ∈ racl k ({a, y} : Set K) := by
    have harith : a * y * x = a * x * y := by ring
    rwa [harith]
  exact mtable_x_notMem_ay hind
    (mem_of_mul_mem_left hay hay0 h')

/-! ### The assembly -/

/-- **The coordinate check for the multiplication diagram** (blueprint
Lemma mul-diagram, forward half): the eight monomial points at an
independent triple satisfy `MulDiagram`.
@isnad1 id=muldiagr.1h5v.s7.8da9cc9dcda0 from=translated src=- shape=78dbe6b7 vocab=d32cf58b
-/
theorem mulDiagram_of_indep :
    MulDiagram (Point.mk' k x (mtable_x_notMem_bot hind))
      (Point.mk' k y (mtable_y_notMem_bot hind))
      (Point.mk' k (x / y) (mtable_div_notMem_bot hind))
      (Point.mk' k (x * y) (mtable_mul_notMem_bot hind))
      (Point.mk' k a (mtable_a_notMem_bot hind))
      (Point.mk' k (a * x) (mtable_ax_notMem_bot hind))
      (Point.mk' k (a * y) (mtable_ay_notMem_bot hind))
      (Point.mk' k (a * x * y) (mtable_axy_notMem_bot hind)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- distinctness
    have hne : ∀ i j : Fin 8, i < j →
        (![Point.mk' k x (mtable_x_notMem_bot hind),
          Point.mk' k y (mtable_y_notMem_bot hind),
          Point.mk' k (x / y) (mtable_div_notMem_bot hind),
          Point.mk' k (x * y) (mtable_mul_notMem_bot hind),
          Point.mk' k a (mtable_a_notMem_bot hind),
          Point.mk' k (a * x) (mtable_ax_notMem_bot hind),
          Point.mk' k (a * y) (mtable_ay_notMem_bot hind),
          Point.mk' k (a * x * y) (mtable_axy_notMem_bot hind)] :
          Fin 8 → Point k K) i ≠
        (![Point.mk' k x (mtable_x_notMem_bot hind),
          Point.mk' k y (mtable_y_notMem_bot hind),
          Point.mk' k (x / y) (mtable_div_notMem_bot hind),
          Point.mk' k (x * y) (mtable_mul_notMem_bot hind),
          Point.mk' k a (mtable_a_notMem_bot hind),
          Point.mk' k (a * x) (mtable_ax_notMem_bot hind),
          Point.mk' k (a * y) (mtable_ay_notMem_bot hind),
          Point.mk' k (a * x * y) (mtable_axy_notMem_bot hind)] :
          Fin 8 → Point k K) j := by
      intro i j hlt
      fin_cases i <;> fin_cases j
      · exact absurd hlt (by decide)
      · change Point.mk' k (x) (mtable_x_notMem_bot hind) ≠
          Point.mk' k (y) (mtable_y_notMem_bot hind)
        exact Point.mk'_ne (mtable_y_notMem_x hind)
      · change Point.mk' k (x) (mtable_x_notMem_bot hind) ≠
          Point.mk' k (x / y) (mtable_div_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne02 hind)
      · change Point.mk' k (x) (mtable_x_notMem_bot hind) ≠
          Point.mk' k (x * y) (mtable_mul_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne03 hind)
      · change Point.mk' k (x) (mtable_x_notMem_bot hind) ≠
          Point.mk' k (a) (mtable_a_notMem_bot hind)
        exact Point.mk'_ne (mtable_a_notMem_x hind)
      · change Point.mk' k (x) (mtable_x_notMem_bot hind) ≠
          Point.mk' k (a * x) (mtable_ax_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne05 hind)
      · change Point.mk' k (x) (mtable_x_notMem_bot hind) ≠
          Point.mk' k (a * y) (mtable_ay_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne06 hind)
      · change Point.mk' k (x) (mtable_x_notMem_bot hind) ≠
          Point.mk' k (a * x * y) (mtable_axy_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne07 hind)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · change Point.mk' k (y) (mtable_y_notMem_bot hind) ≠
          Point.mk' k (x / y) (mtable_div_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne12 hind)
      · change Point.mk' k (y) (mtable_y_notMem_bot hind) ≠
          Point.mk' k (x * y) (mtable_mul_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne13 hind)
      · change Point.mk' k (y) (mtable_y_notMem_bot hind) ≠
          Point.mk' k (a) (mtable_a_notMem_bot hind)
        exact Point.mk'_ne (mtable_a_notMem_y hind)
      · change Point.mk' k (y) (mtable_y_notMem_bot hind) ≠
          Point.mk' k (a * x) (mtable_ax_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne15 hind)
      · change Point.mk' k (y) (mtable_y_notMem_bot hind) ≠
          Point.mk' k (a * y) (mtable_ay_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne16 hind)
      · change Point.mk' k (y) (mtable_y_notMem_bot hind) ≠
          Point.mk' k (a * x * y) (mtable_axy_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne17 hind)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · change Point.mk' k (x / y) (mtable_div_notMem_bot hind) ≠
          Point.mk' k (x * y) (mtable_mul_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne23 hind)
      · change Point.mk' k (x / y) (mtable_div_notMem_bot hind) ≠
          Point.mk' k (a) (mtable_a_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne24 hind)
      · change Point.mk' k (x / y) (mtable_div_notMem_bot hind) ≠
          Point.mk' k (a * x) (mtable_ax_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne25 hind)
      · change Point.mk' k (x / y) (mtable_div_notMem_bot hind) ≠
          Point.mk' k (a * y) (mtable_ay_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne26 hind)
      · change Point.mk' k (x / y) (mtable_div_notMem_bot hind) ≠
          Point.mk' k (a * x * y) (mtable_axy_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne27 hind)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · change Point.mk' k (x * y) (mtable_mul_notMem_bot hind) ≠
          Point.mk' k (a) (mtable_a_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne34 hind)
      · change Point.mk' k (x * y) (mtable_mul_notMem_bot hind) ≠
          Point.mk' k (a * x) (mtable_ax_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne35 hind)
      · change Point.mk' k (x * y) (mtable_mul_notMem_bot hind) ≠
          Point.mk' k (a * y) (mtable_ay_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne36 hind)
      · change Point.mk' k (x * y) (mtable_mul_notMem_bot hind) ≠
          Point.mk' k (a * x * y) (mtable_axy_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne37 hind)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · change Point.mk' k (a) (mtable_a_notMem_bot hind) ≠
          Point.mk' k (a * x) (mtable_ax_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne45 hind)
      · change Point.mk' k (a) (mtable_a_notMem_bot hind) ≠
          Point.mk' k (a * y) (mtable_ay_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne46 hind)
      · change Point.mk' k (a) (mtable_a_notMem_bot hind) ≠
          Point.mk' k (a * x * y) (mtable_axy_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne47 hind)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · change Point.mk' k (a * x) (mtable_ax_notMem_bot hind) ≠
          Point.mk' k (a * y) (mtable_ay_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne56 hind)
      · change Point.mk' k (a * x) (mtable_ax_notMem_bot hind) ≠
          Point.mk' k (a * x * y) (mtable_axy_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne57 hind)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · change Point.mk' k (a * y) (mtable_ay_notMem_bot hind) ≠
          Point.mk' k (a * x * y) (mtable_axy_notMem_bot hind)
        exact Point.mk'_ne (mtable_ne67 hind)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
    intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (hne i j h)
    · exact h
    · exact absurd hij.symm (hne j i h)
  · change RankEq 2 (ClosedIF.point k x ⊔
      (ClosedIF.point k a ⊔ ClosedIF.point k (a * x)))
    exact mtable_line_XAB hind
  · change RankEq 2 (ClosedIF.point k a ⊔
      (ClosedIF.point k y ⊔ ClosedIF.point k (a * y)))
    exact mtable_line_AYC hind
  · change RankEq 2 (ClosedIF.point k a ⊔
      (ClosedIF.point k (x * y) ⊔ ClosedIF.point k (a * x * y)))
    exact mtable_line_AED hind
  · change RankEq 2 (ClosedIF.point k (a * x) ⊔
      (ClosedIF.point k y ⊔ ClosedIF.point k (a * x * y)))
    exact mtable_line_BYD hind
  · change RankEq 2 (ClosedIF.point k x ⊔
      (ClosedIF.point k (a * y) ⊔ ClosedIF.point k (a * x * y)))
    exact mtable_line_XCD hind
  · change RankEq 2 (ClosedIF.point k (a * x) ⊔
      (ClosedIF.point k (a * y) ⊔ ClosedIF.point k (x / y)))
    exact mtable_line_BCV hind
  · change RankEq 2 (ClosedIF.point k x ⊔ (ClosedIF.point k y ⊔
      (ClosedIF.point k (x * y) ⊔ ClosedIF.point k (x / y))))
    exact mtable_line_XYEV hind
  · change RankEq 3 (ClosedIF.point k x ⊔
      (ClosedIF.point k y ⊔ ClosedIF.point k a))
    exact mtable_rank_XYA hind

end MulTable

section QPrimeSoundness

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Soundness of the geometric `Q′`** (blueprint Thm qp-correct, one
direction): every semantic quadruple is geometric — the ratio point
supplies the `Q`-witness, and a fresh parameter builds the
multiplication diagram converting it into the product point.
@isnad1 id=qgeom.2h6v.s7.efe53105c843 from=translated src=- shape=c356f3ba vocab=b119ed73
-/
theorem q'Geom_of_q'Sem {X Y Z W : Point k K}
    (hfresh : ∀ S : Finset K, S.card ≤ 4 → ∃ z, z ∉ racl k (S : Set K))
    (h : Q'Sem X Y Z W) : Q'Geom X Y Z W := by
  classical
  obtain ⟨u, v, hpair, hX, hY, hZ, hW⟩ := h
  obtain ⟨a, ha⟩ := hfresh {u, v} (by
    have h1 := Finset.card_insert_le u ({v} : Finset K)
    have h2 : ({v} : Finset K).card = 1 := Finset.card_singleton v
    omega)
  have ha' : a ∉ racl k ({u, v} : Set K) := by simpa using ha
  have htriple : AlgebraicIndependent k ![u, v, a] := by
    have hra : a ∉ racl k (Set.range ![u, v]) := by
      rwa [range_pair]
    have hsnoc := algebraicIndependent_snoc hpair hra
    have heq : Fin.snoc ![u, v] a = ![u, v, a] := by
      funext i
      fin_cases i <;> simp [Fin.snoc]
    rwa [heq] at hsnoc
  set V : Point k K := Point.mk' k (u / v) (mtable_div_notMem_bot htriple)
    with hV
  have hQ : QGeom X Y Z V :=
    qGeom_of_qSem hfresh ⟨u, v, hpair, hX, hY, hZ, rfl⟩
  have hM := mulDiagram_of_indep htriple
  have e1 : Point.mk' k u (mtable_x_notMem_bot htriple) = X :=
    Subtype.ext (by rw [hX]; rfl)
  have e2 : Point.mk' k v (mtable_y_notMem_bot htriple) = Y :=
    Subtype.ext (by rw [hY]; rfl)
  have e4 : Point.mk' k (u * v) (mtable_mul_notMem_bot htriple) = W :=
    Subtype.ext (by rw [hW]; rfl)
  rw [e1, e2, e4] at hM
  exact ⟨V, _, _, _, _, hQ, hM⟩

end QPrimeSoundness

section JSoundness

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Soundness of the geometric `J`** (blueprint Thm j-acf-correct, one
direction): the value of the `j`-map at an independent pair satisfies the
three-conjunct geometric identity — using the normalizations
`[x/(xa)] = [1/a] = [a]`, `[a+1] = [a]`, and `x(a+1) = x + xa`.
@isnad1 id=jgeom.2h3v.s7.6f16f83dce39 from=translated src=- shape=46f16105 vocab=16c8fe28
-/
theorem jGeom_of_jSem {X : Fin 5 → Point k K}
    (hfresh : ∀ S : Finset K, S.card ≤ 4 → ∃ z, z ∉ racl k (S : Set K))
    (h : JSem X) : JGeom (X 0) (X 1) (X 2) (X 3) (X 4) := by
  classical
  obtain ⟨x, a, hpair, h0, h1, h2, h3, h4⟩ := h
  have hx0 : x ∉ racl k (∅ : Set K) := fun hm ↦
    AlgebraicIndependent.notMem_racl_pair' hpair
      (racl_mono (Set.empty_subset _) hm)
  have ha0 : a ∉ racl k (∅ : Set K) := fun hm ↦
    AlgebraicIndependent.notMem_racl_pair hpair
      (racl_mono (Set.empty_subset _) hm)
  have hxne : x ≠ 0 := by
    intro he
    rw [he] at hx0
    exact hx0 (zero_mem _)
  have hane : a ≠ 0 := by
    intro he
    rw [he] at ha0
    exact ha0 (zero_mem _)
  have hax : a ∉ racl k ({x} : Set K) :=
    AlgebraicIndependent.notMem_racl_pair hpair
  have hxa : x ∉ racl k ({a} : Set K) :=
    AlgebraicIndependent.notMem_racl_pair' hpair
  -- `xa ∉ racl{x}` and `x ∉ racl{xa}`.
  have hprod_x : x * a ∉ racl k ({x} : Set K) := by
    intro hm
    have hxx : x ∈ racl k ({x} : Set K) := subset_racl k _ rfl
    exact hax (mem_of_mul_mem_left hxx hxne hm)
  have hx_prod : x ∉ racl k ({x * a} : Set K) := by
    intro hm
    have hm' : x ∈ racl k (insert (x * a) (∅ : Set K)) := by simpa using hm
    have h5 := racl_exchange hm' hx0
    have h6 : x * a ∈ racl k ({x} : Set K) := by simpa using h5
    exact hprod_x h6
  -- Conjunct 1: `QGeom ([x], [xa], [x+xa], [a])` via the ratio witness.
  have hc1 : QGeom (X 0) (X 2) (X 3) (X 4) := by
    refine qGeom_of_qSem hfresh ⟨x, x * a,
      algebraicIndependent_pair hx_prod hprod_x, h0, h2, h3, ?_⟩
    rw [h4]
    have harith : x / (x * a) = a⁻¹ := by
      field_simp
    rw [harith, ClosedIF.point_inv]
  -- Conjunct 2: `Q'Geom ([x], [a], [x+a], [xa])` literally.
  have hc2 : Q'Geom (X 0) (X 4) (X 1) (X 2) :=
    q'Geom_of_q'Sem hfresh ⟨x, a, hpair, h0, h4, h1, h2⟩
  -- Conjunct 3: `Q'Geom ([x], [a], [x+a], [x+xa])` at the shifted
  -- representative `a + 1`.
  have hshift : ClosedIF.point k (a + 1) = ClosedIF.point k a := by
    have hone : a + (1 : K) = a + algebraMap k K 1 := by rw [map_one]
    rw [hone, ClosedIF.point_add_algebraMap]
  have hc3 : Q'Geom (X 0) (X 4) (X 1) (X 3) := by
    have hpair' : AlgebraicIndependent k ![x, a + 1] := by
      refine algebraicIndependent_pair ?_ ?_
      · intro hm
        refine hxa ?_
        have heq : racl k ({a + 1} : Set K) = racl k ({a} : Set K) := by
          have hone : a + (1 : K) = a + algebraMap k K 1 := by rw [map_one]
          rw [hone, racl_add_algebraMap]
        rwa [heq] at hm
      · intro hm
        have ha' : a ∈ racl k ({x} : Set K) := by
          have h5 := sub_mem hm (one_mem (racl k ({x} : Set K)))
          rwa [add_sub_cancel_right] at h5
        exact hax ha'
    refine q'Geom_of_q'Sem hfresh ⟨x, a + 1, hpair', h0, ?_, ?_, ?_⟩
    · rw [h4, hshift]
    · rw [h1]
      have harith : x + (a + 1) = x + a + 1 := by ring
      rw [harith]
      have hone : x + a + (1 : K) = x + a + algebraMap k K 1 := by
        rw [map_one]
      rw [hone, ClosedIF.point_add_algebraMap]
    · rw [h3]
      have harith : x * (a + 1) = x + x * a := by ring
      rw [harith]
  exact ⟨hc1, hc2, hc3⟩

end JSoundness

end

end AclGeom
