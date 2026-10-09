/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.TangentCone.Basic
import Tengoku.Seed.Topology.Algebra.Module.Basic

/-!
# Indexed product of sets with unique differentiability property

In this file we prove that the indexed product
of a family sets with unique differentiability property
has the same property, see `UniqueDiffOn.pi` and  `UniqueDiffOn.univ_pi`.
-/

public section

open Filter Set
open scoped Topology

section Semiring

variable {𝕜 : Type*} [Semiring 𝕜]
  {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousAdd (E i)] [∀ i, ContinuousConstSMul 𝕜 (E i)]
  {s : ∀ i, Set (E i)} {x : ∀ i, E i}

/-- The tangent cone of a product contains the tangent cone of each factor.
@isnad1 id=mapsto.1h6v.s8.7dc4fd337997 from=seed src=0 shape=29502d34 vocab=004d1f05
-/
theorem mapsTo_tangentConeAt_pi [DecidableEq ι] {i : ι} (hi : ∀ j ≠ i, x j ∈ closure (s j)) :
    MapsTo (Pi.single i) (tangentConeAt 𝕜 (s i) (x i)) (tangentConeAt 𝕜 (Set.pi univ s) x) := by
  rw [← tangentConeAt_closure (s := .pi _ _)]
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  apply mem_tangentConeAt_of_seq l c (fun n ↦ Pi.single i (d n))
  · rw [tendsto_pi_nhds]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, tendsto_const_nhds]
  · refine hds.mono fun n hn ↦ ?_
    rw [closure_pi_set, mem_univ_pi]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, subset_closure hn]
  · rw [tendsto_pi_nhds]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, tendsto_const_nhds]

/--
@isnad1 id=uniquedi.1h5v.s7.74f3e1a8d289 from=seed src=0 shape=cea9e14a vocab=471de2af
-/
theorem UniqueDiffWithinAt.univ_pi {s : ∀ i, Set (E i)} {x : ∀ i, E i}
    (h : ∀ i, UniqueDiffWithinAt 𝕜 (s i) (x i)) : UniqueDiffWithinAt 𝕜 (Set.pi univ s) x := by
  classical
  simp only [uniqueDiffWithinAt_iff, closure_pi_set] at h ⊢
  refine ⟨.of_closure <| (dense_pi univ fun i _ ↦ (h i).1).closure.mono ?_, fun i _ => (h i).2⟩
  simp only [closure_pi_set, ← Submodule.closure_coe_iSup_map_single, Submodule.map_span]
  gcongr
  refine iSup_le fun i ↦ ?_
  gcongr
  exact mapsTo_tangentConeAt_pi (fun j _ ↦ (h j).2) |>.image_subset

/-- The product of a family of sets of unique differentiability is a set of unique
differentiability.
@isnad1 id=uniquedi.1h4v.s7.17e7264de0ac from=seed src=0 shape=2b1d7883 vocab=26e45c01
-/
theorem UniqueDiffOn.univ_pi {s : ∀ i, Set (E i)} (h : ∀ i, UniqueDiffOn 𝕜 (s i)) :
    UniqueDiffOn 𝕜 (Set.pi univ s) :=
  fun _x hx ↦ .univ_pi fun i ↦ h i _ <| hx i (mem_univ i)

end Semiring

variable {𝕜 : Type*} [DivisionSemiring 𝕜]
  {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [TopologicalSpace 𝕜] [(𝓝[≠] (0 : 𝕜)).NeBot]
  [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousAdd (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
  {s : ∀ i, Set (E i)} {x : ∀ i, E i} {I : Set ι}

/--
@isnad1 id=uniquedi.1h6v.s8.36a068b34044 from=seed src=0 shape=7302fd2f vocab=be548823
-/
theorem UniqueDiffWithinAt.pi (h : ∀ i ∈ I, UniqueDiffWithinAt 𝕜 (s i) (x i)) :
    UniqueDiffWithinAt 𝕜 (Set.pi I s) x := by
  classical
  rw [← Set.univ_pi_piecewise_univ]
  refine UniqueDiffWithinAt.univ_pi fun i => ?_
  by_cases hi : i ∈ I <;> simp [*, uniqueDiffWithinAt_univ]

/-- The product of a family of sets of unique differentiability is a set of unique
differentiability.
@isnad1 id=uniquedi.1h5v.s8.d71a381377b8 from=seed src=0 shape=58d7d46a vocab=7b8b2d33
-/
theorem UniqueDiffOn.pi (h : ∀ i ∈ I, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.pi I s) :=
  fun x hx => UniqueDiffWithinAt.pi fun i hi => h i hi (x i) (hx i hi)
