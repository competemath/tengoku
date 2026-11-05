/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import Tengoku.Seed.Algebra.Polynomial.Lifts
import Tengoku.Seed.FieldTheory.IsSepClosed
import Tengoku.Seed.FieldTheory.Separable
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Basic
import Tengoku.Seed.RingTheory.LocalRing.RingHom.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The separably closed residue field of the geometric étale stalk

Evaluation of the constructed stalk in the geometric field is a local
homomorphism, so it induces an embedding of its actual residue field into that
field. For a monic separable irreducible residue polynomial, lift its coefficients
to the stalk. Its simple root in the geometric field lifts to a root in the
stalk by the concrete standard étale neighborhood from
`GeometricStalkHenselian`. Reduction of this root proves that the residue field
is separably closed.

Thus the constructed ring is strictly local: it is Henselian with separably
closed residue field. This does not yet identify it with a separately chosen
strict henselization, or establish the manuscript's inertia comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- Evaluation is local because its nonzero values are precisely the units
of the constructed geometric stalk.-/
instance geometricStalkEvaluation_isLocalHom :
    IsLocalHom (geometricStalkEvaluation s).hom where
  map_nonunit a ha := geometricStalk_isUnit_of_evaluation_ne_zero s a ha.ne_zero

/-- The embedding of the actual residue field of the geometric étale stalk
into the chosen geometric field.-/
def geometricStalkResidueEmbedding :
    IsLocalRing.ResidueField (geometricStalk s) →+* Ω :=
  IsLocalRing.ResidueField.lift (geometricStalkEvaluation s).hom

end EtaleFundamentalGroups.StrictHenselian
