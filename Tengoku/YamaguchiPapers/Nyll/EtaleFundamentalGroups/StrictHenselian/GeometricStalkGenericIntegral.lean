/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Etale
import Tengoku.Seed.AlgebraicGeometry.Morphisms.RingHomProperties
import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace
import Tengoku.Seed.RingTheory.Etale.Basic
import Tengoku.Seed.RingTheory.IntegralClosure.Algebra.Basic
import Tengoku.Seed.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.RingTheory.RingHom.Etale
import Tengoku.Seed.RingTheory.TensorProduct.Maps
import Tengoku.Seed.RingTheory.Unramified.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Field base changes of the actual geometric stalk are integral

Represent a germ on an actual affine étale neighborhood. After base change
to a field, that neighborhood's algebra is formally unramified and of finite
type, hence finite as a vector space. Its elements are therefore integral.
The actual germ map induces a map of the field-base-changed algebras, carrying
this integral equation to the geometric stalk. Tensor induction supplies
integrality for every element of the base change.

This argument needs no finite presentation of a fraction field over the
original ring. No domain or normality assumption on the base is needed for
this integrality result.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω]
  (φ : R →+* Ω)

end EtaleFundamentalGroups.StrictHenselian
