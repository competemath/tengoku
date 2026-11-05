/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.Kummer.Concrete.ContinuousHilbert90
import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.Topology.AlgebraicGaloisOrbits
import Tengoku.Seed.FieldTheory.IsSepClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifting continuous cocycles through power maps

Over a separably closed Galois extension, Hilbert 90 writes a continuous
multiplicative cocycle as a coboundary. Taking a root of that actual coboundary
parameter lifts the cocycle, preserving local constancy and the root-of-unity
coefficient bound.
-/

namespace KummerTheory
open groupCohomology
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

/-- A root quotient is locally constant in the Krull topology.
@isnad1 id=islocall.0h3v.s6.35e9ff285e7b from=translated src=- shape=0f7d9e07 vocab=2c557471
-/
theorem isLocallyConstant_rootQuotient (γ : Ωˣ) :
    IsLocallyConstant (rootQuotient (K := K) γ) := by
  exact (GaloisCohomology.isLocallyConstant_galois_units (K := K) γ).comp
    (fun z : Ωˣ => z / γ)

variable [IsSepClosed Ω]

end KummerTheory
