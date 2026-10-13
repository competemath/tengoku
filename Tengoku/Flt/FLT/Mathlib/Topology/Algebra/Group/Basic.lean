/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Tengoku

/-! # Lemmas about topological groups -/

public section

/--
@isnad1 id=iff.0h4v.s6.5bf6a17d2c01 from=translated src=- shape=269e508b vocab=3c75f0d3
-/
@[to_additive]
lemma continuous_iff_continuousAt_one
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M : Type*} {hom : Type*} [MulOneClass M]
    [TopologicalSpace M] [ContinuousMul M] [FunLike hom G M]
    [MonoidHomClass hom G M] {f : hom} : Continuous ⇑f ↔ ContinuousAt (⇑f) 1 :=
  ⟨Continuous.continuousAt, continuous_of_continuousAt_one _⟩

/--
@isnad1 id=continuo.1h3v.s6.1d4f72437b13 from=translated src=- shape=681f613e vocab=f80fc3bc
-/
@[to_additive]
lemma MonoidHom.continuous_of_isOpen_ker {G H : Type*} [Group G] [MulOneClass H] {φ : G →* H}
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [ContinuousMul H]
    (hφ : IsOpen (φ.ker : Set G)) : Continuous φ := by
  refine continuous_of_continuousAt_one _ ?_
  intro U hU
  simp only [Filter.mem_map]
  exact Filter.mem_of_superset (hφ.mem_nhds (by simp)) (Set.preimage_mono
    (Set.singleton_subset_iff.mpr (mem_of_mem_nhds (by simpa using hU))))

/--
@isnad1 id=iff.0h3v.s6.014f4514243a from=translated src=- shape=441086fc vocab=e21847df
-/
@[to_additive]
lemma MonoidHom.continuous_iff_isOpen_ker {G H : Type*} [Group G] [MulOneClass H] {φ : G →* H}
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [DiscreteTopology H] :
    Continuous φ ↔ IsOpen (φ.ker : Set G) :=
  ⟨fun h ↦ (isOpen_discrete {1}).preimage h, MonoidHom.continuous_of_isOpen_ker⟩
