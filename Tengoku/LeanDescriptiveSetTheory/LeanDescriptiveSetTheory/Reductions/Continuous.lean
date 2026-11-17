/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Relations.Sections
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Open

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuous many-one reducibility

`ContinuouslyReduces s t` means that membership in `s` is the pullback of membership in `t` along
one continuous map. The source set is the first argument and the target set is the second. The API
keeps the exact preimage equality visible and supplies composition, complement, product,
homeomorphism, and fixed-parameter section transports without introducing notation or an order
instance.
-/

open Set

universe u v w u' v'

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- `s` continuously reduces to `t` when `s` is the exact preimage of `t` under a continuous
map. The source set is the first argument.-/
def ContinuouslyReduces (s : Set X) (t : Set Y) : Prop :=
  ∃ f : X → Y, Continuous f ∧ f ⁻¹' t = s

/-- Build a reduction from the pointwise membership equation used by applications.-/
theorem continuouslyReduces_of_continuous {s : Set X} {t : Set Y} (f : X → Y)
    (hf : Continuous f) (hmem : ∀ x, x ∈ s ↔ f x ∈ t) :
    ContinuouslyReduces s t := by
  refine ⟨f, hf, ?_⟩
  ext x
  exact (hmem x).symm

/-- Pointwise form of continuous reducibility.-/
theorem continuouslyReduces_iff {s : Set X} {t : Set Y} :
    ContinuouslyReduces s t ↔
      ∃ f : X → Y, Continuous f ∧ ∀ x, x ∈ s ↔ f x ∈ t := by
  constructor
  · rintro ⟨f, hf, hpre⟩
    refine ⟨f, hf, fun x => ?_⟩
    exact (Set.ext_iff.mp hpre x).symm
  · rintro ⟨f, hf, hmem⟩
    exact continuouslyReduces_of_continuous f hf hmem

/-- Extract a continuous reduction map with its pointwise application law.-/
theorem ContinuouslyReduces.exists_map {s : Set X} {t : Set Y}
    (h : ContinuouslyReduces s t) :
    ∃ f : X → Y, Continuous f ∧ ∀ x, x ∈ s ↔ f x ∈ t :=
  continuouslyReduces_iff.1 h

/-- Continuous reducibility is reflexive.-/
theorem ContinuouslyReduces.refl (s : Set X) : ContinuouslyReduces s s :=
  ⟨id, continuous_id, rfl⟩

/-- Continuous reducibility is transitive, with witnesses composed in source-to-target order.-/
theorem ContinuouslyReduces.trans {s : Set X} {t : Set Y} {r : Set Z}
    (hst : ContinuouslyReduces s t) (htr : ContinuouslyReduces t r) :
    ContinuouslyReduces s r := by
  rcases hst with ⟨f, hf, hft⟩
  rcases htr with ⟨g, hg, hgr⟩
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  change f ⁻¹' (g ⁻¹' r) = s
  rw [hgr, hft]

/-- The same map reduces the complements of the source and target sets.-/
theorem ContinuouslyReduces.compl {s : Set X} {t : Set Y}
    (h : ContinuouslyReduces s t) : ContinuouslyReduces sᶜ tᶜ := by
  rcases h with ⟨f, hf, hpre⟩
  refine ⟨f, hf, ?_⟩
  rw [preimage_compl, hpre]

/-- A continuous preimage always reduces to its target.-/
theorem continuouslyReduces_preimage {t : Set Y} (f : X → Y) (hf : Continuous f) :
    ContinuouslyReduces (f ⁻¹' t) t :=
  ⟨f, hf, rfl⟩

/-- Precompose a reduction by a continuous map on its source.-/
theorem ContinuouslyReduces.preimage_source {s : Set X} {t : Set Y}
    (h : ContinuouslyReduces s t) (f : Z → X) (hf : Continuous f) :
    ContinuouslyReduces (f ⁻¹' s) t :=
  (continuouslyReduces_preimage f hf).trans h

/-- Product reductions are witnessed coordinatewise.-/
theorem ContinuouslyReduces.prod {s : Set X} {t : Set Y}
    {X' : Type u'} {Y' : Type v'} [TopologicalSpace X'] [TopologicalSpace Y']
    {s' : Set X'} {t' : Set Y'} (h : ContinuouslyReduces s t)
    (h' : ContinuouslyReduces s' t') :
    ContinuouslyReduces (s ×ˢ s') (t ×ˢ t') := by
  rcases h with ⟨f, hf, hpre⟩
  rcases h' with ⟨g, hg, hpre'⟩
  refine ⟨fun z => (f z.1, g z.2),
    (hf.comp continuous_fst).prodMk (hg.comp continuous_snd), ?_⟩
  ext z
  exact and_congr (Set.ext_iff.mp hpre z.1) (Set.ext_iff.mp hpre' z.2)

/-- A homeomorphism reduces a set to its image.-/
theorem Homeomorph.continuouslyReduces_image (e : X ≃ₜ Y) (s : Set X) :
    ContinuouslyReduces s (e '' s) := by
  refine ⟨e, e.continuous, ?_⟩
  ext x
  simp

/-- The inverse homeomorphism reduces the image of a set back to the set.-/
theorem Homeomorph.image_continuouslyReduces (e : X ≃ₜ Y) (s : Set X) :
    ContinuouslyReduces (e '' s) s := by
  refine ⟨e.symm, e.symm.continuous, ?_⟩
  exact (e.image_eq_preimage_symm s).symm

/-- Transport both sides of a reduction through homeomorphisms.-/
theorem ContinuouslyReduces.homeomorph {s : Set X} {t : Set Y}
    {X' : Type u'} {Y' : Type v'} [TopologicalSpace X'] [TopologicalSpace Y']
    (h : ContinuouslyReduces s t) (e : X ≃ₜ X') (d : Y ≃ₜ Y') :
    ContinuouslyReduces (e '' s) (d '' t) :=
  (DescriptiveSetTheory.Homeomorph.image_continuouslyReduces e s).trans
    (h.trans (DescriptiveSetTheory.Homeomorph.continuouslyReduces_image d t))

/-- Continuous reducibility is invariant when both sets are transported by homeomorphisms.-/
theorem continuouslyReduces_image_iff {s : Set X} {t : Set Y}
    {X' : Type u'} {Y' : Type v'} [TopologicalSpace X'] [TopologicalSpace Y']
    (e : X ≃ₜ X') (d : Y ≃ₜ Y') :
    ContinuouslyReduces (e '' s) (d '' t) ↔ ContinuouslyReduces s t := by
  constructor
  · intro h
    exact (DescriptiveSetTheory.Homeomorph.continuouslyReduces_image e s).trans
      (h.trans (DescriptiveSetTheory.Homeomorph.image_continuouslyReduces d t))
  · intro h
    exact h.homeomorph e d

/-- Fixing the first coordinate continuously reduces a vertical section to the total relation.-/
theorem continuouslyReduces_verticalSection (U : Set (X × Y)) (p : X) :
    ContinuouslyReduces (verticalSection U p) U :=
  ⟨fun x => (p, x), continuous_const.prodMk continuous_id, rfl⟩

/-- Fixing the second coordinate continuously reduces a horizontal section to the total relation.-/
theorem continuouslyReduces_horizontalSection (U : Set (X × Y)) (p : Y) :
    ContinuouslyReduces (horizontalSection U p) U :=
  ⟨fun x => (x, p), continuous_id.prodMk continuous_const, rfl⟩

/-- Every set in the pointclass of a universal relation continuously reduces to that relation.-/
theorem IsUniversalFor.continuouslyReduces {C : Set Y → Prop} {U : Set (X × Y)}
    (hU : IsUniversalFor C U) {s : Set Y} (hs : C s) :
    ContinuouslyReduces s U := by
  obtain ⟨p, hp⟩ := (hU s).1 hs
  rw [← hp]
  exact continuouslyReduces_verticalSection U p

end DescriptiveSetTheory
