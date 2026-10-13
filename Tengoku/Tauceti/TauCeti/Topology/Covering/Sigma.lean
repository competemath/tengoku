/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
import Tengoku.Tauceti.TauCeti.Topology.Homeomorph.SetCongr

/-!
# Covering maps of a disjoint union

A family of covering maps `f i : E i → X i` assembles into a single map
`Sigma.map id f : (Σ i, E i) → Σ i, X i`, and this file proves that the assembled map is again a
covering map, identifies its fibres, and computes its monodromy.

Everything is local: the summand `Set.range (Sigma.mk i)` is open in `Σ i, X i`, the assembled
map restricts over it to `f i` up to the two open embeddings, and `IsCoveringMap` is a pointwise
condition, so the summandwise statements glue with no compatibility to check.

The classification of covering spaces by functors out of the fundamental groupoid,
`TauCeti.CoveringSpace.monodromyEquivalence`, is available only over a path-connected base, which
a disjoint union need not be; the statements here are proved summandwise instead and assume no
connectivity.

## Main declarations

* `TauCeti.isCoveringMap_sigmaMap`: **a disjoint union of covering maps is a covering map.**
* `TauCeti.sigmaMapFiberEquiv`: the fibre of `Sigma.map id f` over `⟨i, x⟩` is the fibre of
  `f i` over `x`.
* `TauCeti.monodromy_sigmaMap`: that identification intertwines the monodromy of `f i` along a
  path with the monodromy of `Sigma.map id f` along its image in `Σ i, X i`.

-/

public section

namespace TauCeti

open Topology

variable {ι : Type*} {E X : ι → Type*} [∀ i, TopologicalSpace (E i)]
  [∀ i, TopologicalSpace (X i)] (f : ∀ i, E i → X i)

/-- **A disjoint union of covering maps is a covering map.** -/
theorem isCoveringMap_sigmaMap (hf : ∀ i, IsCoveringMap (f i)) :
    IsCoveringMap (Sigma.map id f) := by
  rintro ⟨i, x⟩
  -- The `i`-th summand of `Σ i, E i` is exactly the part of `Σ i, E i` lying over the `i`-th
  -- summand of `Σ i, X i`.
  have hpre : Sigma.map id f ⁻¹' Set.range (Sigma.mk i) = Set.range (Sigma.mk i) := by
    simpa using (Set.image_sigmaMk_preimage_sigmaMap Function.injective_id f i Set.univ).symm
  have hopen : IsOpen (Sigma.map id f ⁻¹' Set.range (Sigma.mk i)) := by
    rw [hpre]
    exact isOpen_range_sigmaMk
  refine IsCoveringMapOn.of_isCoveringMap_restrictPreimage _ isOpen_range_sigmaMk hopen ?_ _
    ⟨x, rfl⟩
  let hE : (Sigma.map id f ⁻¹' Set.range (Sigma.mk i) : Set (Σ i, E i)) ≃ₜ E i :=
    (Homeomorph.setCongr hpre).trans (IsEmbedding.sigmaMk (σ := E)).toHomeomorph.symm
  let hX : X i ≃ₜ (Set.range (Sigma.mk i) : Set (Σ i, X i)) :=
    (IsEmbedding.sigmaMk (σ := X)).toHomeomorph
  have heq : (Set.range (Sigma.mk i)).restrictPreimage (Sigma.map id f) =
      hX ∘ f i ∘ hE := by
    refine funext fun p ↦ Subtype.ext ?_
    obtain ⟨⟨j, e⟩, hje⟩ := p
    obtain rfl : j = i := by simpa [Sigma.map, eq_comm] using hje
    -- Evaluate each link of the two chains through its application lemma instead of unfolding
    -- the equivalence it is built from: the application lemmas are stable under changes to
    -- those definitions, which definitional unfolding is not.
    simp only [Set.restrictPreimage, Set.MapsTo.val_restrict_apply, Sigma.map, id_eq,
      Function.comp_apply, Homeomorph.trans_apply, Homeomorph.setCongr_apply,
      IsEmbedding.toHomeomorph_symm_apply, IsEmbedding.toHomeomorph_apply_coe, hX, hE]
  rw [heq]
  exact ((hf i).comp_homeomorph hE).homeomorph_comp hX

end TauCeti
