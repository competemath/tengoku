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

/-- Build a reduction from the pointwise membership equation used by applications.
@isnad1 id=continuo.2h5v.s5.d46b2d541a2e from=translated src=- shape=ea54536b vocab=f80bded1
-/
theorem continuouslyReduces_of_continuous {s : Set X} {t : Set Y} (f : X → Y)
    (hf : Continuous f) (hmem : ∀ x, x ∈ s ↔ f x ∈ t) :
    ContinuouslyReduces s t := by
  refine ⟨f, hf, ?_⟩
  ext x
  exact (hmem x).symm

/-- Pointwise form of continuous reducibility.
@isnad1 id=iff.0h4v.s5.137501457f6e from=translated src=- shape=764cd623 vocab=f80bded1
-/
theorem continuouslyReduces_iff {s : Set X} {t : Set Y} :
    ContinuouslyReduces s t ↔
      ∃ f : X → Y, Continuous f ∧ ∀ x, x ∈ s ↔ f x ∈ t := by
  constructor
  · rintro ⟨f, hf, hpre⟩
    refine ⟨f, hf, fun x => ?_⟩
    exact (Set.ext_iff.mp hpre x).symm
  · rintro ⟨f, hf, hmem⟩
    exact continuouslyReduces_of_continuous f hf hmem

/-- Extract a continuous reduction map with its pointwise application law.
@isnad1 id=ex.1h4v.s5.7a1eea54b32b from=translated src=- shape=ae054151 vocab=f80bded1
-/
theorem ContinuouslyReduces.exists_map {s : Set X} {t : Set Y}
    (h : ContinuouslyReduces s t) :
    ∃ f : X → Y, Continuous f ∧ ∀ x, x ∈ s ↔ f x ∈ t :=
  continuouslyReduces_iff.1 h

/-- Continuous reducibility is reflexive.
@isnad1 id=continuo.0h2v.s3.9d7b21b778c1 from=translated src=- shape=ef8aadb5 vocab=9fe74fc0
-/
theorem ContinuouslyReduces.refl (s : Set X) : ContinuouslyReduces s s :=
  ⟨id, continuous_id, rfl⟩

/-- Continuous reducibility is transitive, with witnesses composed in source-to-target order.
@isnad1 id=continuo.2h6v.s5.9db3f7b83150 from=translated src=- shape=3ab927f1 vocab=9fe74fc0
-/
theorem ContinuouslyReduces.trans {s : Set X} {t : Set Y} {r : Set Z}
    (hst : ContinuouslyReduces s t) (htr : ContinuouslyReduces t r) :
    ContinuouslyReduces s r := by
  rcases hst with ⟨f, hf, hft⟩
  rcases htr with ⟨g, hg, hgr⟩
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  change f ⁻¹' (g ⁻¹' r) = s
  rw [hgr, hft]

/-- The same map reduces the complements of the source and target sets.
@isnad1 id=continuo.1h4v.s5.f095f021f526 from=translated src=- shape=bf84506b vocab=85e2d626
-/
theorem ContinuouslyReduces.compl {s : Set X} {t : Set Y}
    (h : ContinuouslyReduces s t) : ContinuouslyReduces sᶜ tᶜ := by
  rcases h with ⟨f, hf, hpre⟩
  refine ⟨f, hf, ?_⟩
  rw [preimage_compl, hpre]

/-- A continuous preimage always reduces to its target.
@isnad1 id=continuo.1h4v.s5.a5320a91e5fe from=translated src=- shape=3ae6c155 vocab=033fbde0
-/
theorem continuouslyReduces_preimage {t : Set Y} (f : X → Y) (hf : Continuous f) :
    ContinuouslyReduces (f ⁻¹' t) t :=
  ⟨f, hf, rfl⟩

/-- Precompose a reduction by a continuous map on its source.
@isnad1 id=continuo.2h6v.s5.44d7a676feff from=translated src=- shape=120f724c vocab=033fbde0
-/
theorem ContinuouslyReduces.preimage_source {s : Set X} {t : Set Y}
    (h : ContinuouslyReduces s t) (f : Z → X) (hf : Continuous f) :
    ContinuouslyReduces (f ⁻¹' s) t :=
  (continuouslyReduces_preimage f hf).trans h

/-- Product reductions are witnessed coordinatewise.
@isnad1 id=continuo.2h8v.s6.7a4859b967ac from=translated src=- shape=579a3dcf vocab=24673571
-/
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

/-- A homeomorphism reduces a set to its image.
@isnad1 id=continuo.0h4v.s5.0f4143987f98 from=translated src=- shape=06597046 vocab=303681d6
-/
theorem Homeomorph.continuouslyReduces_image (e : X ≃ₜ Y) (s : Set X) :
    ContinuouslyReduces s (e '' s) := by
  refine ⟨e, e.continuous, ?_⟩
  ext x
  simp

/-- The inverse homeomorphism reduces the image of a set back to the set.
@isnad1 id=continuo.0h4v.s5.f2678fb14fdb from=translated src=- shape=4418cd8a vocab=303681d6
-/
theorem Homeomorph.image_continuouslyReduces (e : X ≃ₜ Y) (s : Set X) :
    ContinuouslyReduces (e '' s) s := by
  refine ⟨e.symm, e.symm.continuous, ?_⟩
  exact (e.image_eq_preimage_symm s).symm

/-- Transport both sides of a reduction through homeomorphisms.
@isnad1 id=continuo.1h8v.s6.f036b55556b7 from=translated src=- shape=69fac5ea vocab=303681d6
-/
theorem ContinuouslyReduces.homeomorph {s : Set X} {t : Set Y}
    {X' : Type u'} {Y' : Type v'} [TopologicalSpace X'] [TopologicalSpace Y']
    (h : ContinuouslyReduces s t) (e : X ≃ₜ X') (d : Y ≃ₜ Y') :
    ContinuouslyReduces (e '' s) (d '' t) :=
  (DescriptiveSetTheory.Homeomorph.image_continuouslyReduces e s).trans
    (h.trans (DescriptiveSetTheory.Homeomorph.continuouslyReduces_image d t))

/-- Continuous reducibility is invariant when both sets are transported by homeomorphisms.
@isnad1 id=iff.0h8v.s6.35414be1ef9c from=translated src=- shape=2c6c6699 vocab=303681d6
-/
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

/-- Fixing the first coordinate continuously reduces a vertical section to the total relation.
@isnad1 id=continuo.0h4v.s5.87aa0c0cd869 from=translated src=- shape=8b8467cf vocab=f05402a0
-/
theorem continuouslyReduces_verticalSection (U : Set (X × Y)) (p : X) :
    ContinuouslyReduces (verticalSection U p) U :=
  ⟨fun x => (p, x), continuous_const.prodMk continuous_id, rfl⟩

/-- Fixing the second coordinate continuously reduces a horizontal section to the total relation.
@isnad1 id=continuo.0h4v.s5.36594cb07aca from=translated src=- shape=8ff00dfe vocab=21ed771c
-/
theorem continuouslyReduces_horizontalSection (U : Set (X × Y)) (p : Y) :
    ContinuouslyReduces (horizontalSection U p) U :=
  ⟨fun x => (x, p), continuous_id.prodMk continuous_const, rfl⟩

/-- Every set in the pointclass of a universal relation continuously reduces to that relation.
@isnad1 id=continuo.1h6v.s5.bde8d0a9a810 from=translated src=- shape=47e3907d vocab=f078d93d
-/
theorem IsUniversalFor.continuouslyReduces {C : Set Y → Prop} {U : Set (X × Y)}
    (hU : IsUniversalFor C U) {s : Set Y} (hs : C s) :
    ContinuouslyReduces s U := by
  obtain ⟨p, hp⟩ := (hU s).1 hs
  rw [← hp]
  exact continuouslyReduces_verticalSection U p

end DescriptiveSetTheory
