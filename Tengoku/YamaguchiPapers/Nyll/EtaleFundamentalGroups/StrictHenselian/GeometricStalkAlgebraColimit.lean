/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Tengoku.Seed.CategoryTheory.Comma.Over.Basic
import Tengoku.Seed.CategoryTheory.Filtered.FinallySmall
import Tengoku.Seed.CategoryTheory.Limits.Final

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual geometric stalk as a filtered colimit of base algebras

The structure maps of the pointed étale neighborhoods commute with the actual
geometric-stalk germ maps. Thus the defining ring colimit lifts to the category
of algebras under the original ring. Restricting along the small filtered final
model supplies a small filtered diagram whose colimit is the same actual stalk,
with its actual structure homomorphism. This is the input for finite-data
algebra descent, rather than an assumed presentation of strict henselization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω)

/-- A small filtered index category for the actual algebra presentation.-/
abbrev GeometricStalkAlgebraIndex :=
  FinallySmall.FilteredFinalModel.{u}
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ

end EtaleFundamentalGroups.StrictHenselian
