/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Tengoku.Seed.AlgebraicGeometry.AffineScheme
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Flat
import Tengoku.Seed.AlgebraicGeometry.OpenImmersion
import Tengoku.Seed.RingTheory.Flat.EquationalCriterion
import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Algebra
import Tengoku.Seed.RingTheory.Flat.TorsionFree
import Tengoku.Seed.RingTheory.RingHom.FaithfullyFlat
import Tengoku.Seed.RingTheory.RingHom.Flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Flatness of the actual geometric étale stalk

A finite family of germs and a relation among them descend to one pointed
étale neighborhood. The filtered-colimit equality criterion makes that relation
zero on a further neighborhood. Choose an actual affine open neighborhood of
the geometric point there. Its structure map is étale, hence flat, so the
relation is trivial by the equational criterion for flatness. Its witnesses
map to witnesses in the geometric stalk.

This proves flatness of the structure map constructed in
`GeometricStalkStructure`. It does not assume an affine-colimit presentation
or flatness as a field of a strict-henselization package.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Every actual pointed étale neighborhood has an affine pointed étale
refinement, constructed by lifting the geometric point to an affine open.
@isnad1 id=ex.0h5v.s10.cc2bce87c979 from=translated src=- shape=089a76fa vocab=29ea4f99
-/
theorem geometricStalk_exists_affine_refinement
    {S : Scheme.{u}} {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ S) (W : S.Etale)
    (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W) :
    ∃ (V : S.Etale) (v : (Scheme.pointEtaleNeighborhoods s).fiber.obj V) (f : V ⟶ W),
      IsAffine V.left ∧ (Scheme.pointEtaleNeighborhoods s).fiber.map f v = t := by
  let tHom : Spec (CommRingCat.of Ω) ⟶ W.left := t.left
  let p : W.left ⟶ S := W.hom
  obtain ⟨A, j, hj, hmem, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := tHom default) (U := ⊤) (by trivial)
  let : IsOpenImmersion j := hj
  have hrange : Set.range tHom ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x default]
    exact hmem
  let l : Spec (CommRingCat.of Ω) ⟶ Spec A := IsOpenImmersion.lift j tHom hrange
  have hl : l ≫ j = tHom := IsOpenImmersion.lift_fac j tHom hrange
  have hjp : Etale (j ≫ p) := by
    let : Etale p := W.prop
    exact Etale.etale_comp j p
  let V : S.Etale := MorphismProperty.Over.mk ⊤ (j ≫ p) hjp
  have hlp : l ≫ (j ≫ p) = s := by
    rw [← Category.assoc, hl]
    exact Over.w t
  let v : (Scheme.pointEtaleNeighborhoods s).fiber.obj V := by
    change Over.mk s ⟶ Over.mk (j ≫ p)
    exact Over.homMk l hlp
  let f : V ⟶ W := MorphismProperty.Over.homMk (show V.left ⟶ W.left from j) rfl
  have hV : IsAffine V.left := by
    change IsAffine (Spec A)
    infer_instance
  refine ⟨V, v, f, hV, ?_⟩
  apply Over.OverMorphism.ext
  exact hl

variable {R Ω : Type u} [CommRing R] [Field Ω]
  (φ : R →+* Ω)

end EtaleFundamentalGroups.StrictHenselian
