/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Galois cohomology for Kummer theory

Hilbert 90 and multiplicative cocycle statements used by the concrete Kummer correspondence.
-/

namespace KummerTheory

open groupCohomology

section NoetherHilbert90

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {f : Gal(L/K) → Lˣ}

end NoetherHilbert90

section CyclicHilbert90

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable [IsGalois K L]

end CyclicHilbert90

section IntegralHilbert90

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable [IsGalois K L]
variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra A B] [Algebra A L] [Algebra A K] [Algebra B L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
variable [IsDomain A] [IsIntegralClosure B A L]

end IntegralHilbert90

end KummerTheory
