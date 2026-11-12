/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.RingTheory.Ideal.UFD
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.RegularLocalHeightOnePrincipal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Factoriality of a two-dimensional regular local ring

P2.3 proves that every height-one prime of a two-dimensional regular local ring is principal
(`IsRegularLocalRing.isPrincipal_of_height_one`).  Combined with P2.2 (regular local rings are
domains) and the Noetherian criterion
`UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one`, this makes the ring factorial.

This is the local input recorded by `docs/CONSTRUCTION_R4_HRR.md` §4 as G4c's
"factoriality/Cartier geometry" half: at a closed point of a regular surface, an ambient rational
function factors as a unit times a Laurent product of local equations of the prime divisors
through that point.  The surface consumer interface is
`Chow/SurfaceRestrictionLocalFactorization.lean`.

No claim about the geometric assembly is made here; this file is pure commutative algebra.
-/

noncomputable section
namespace Tengoku.GrothendieckRiemannRoch end Tengoku.GrothendieckRiemannRoch open Tengoku.GrothendieckRiemannRoch 
universe u

namespace IsRegularLocalRing

/-- **Local factoriality.**  A two-dimensional regular local ring is a unique factorization
domain.  Every height-one prime is principal by P2.3, and a Noetherian domain with that property
is factorial.
@isnad1 id=uniquefa.1h1v.s5.0c20a3134c67 from=translated src=- shape=50208249 vocab=9f84884e
-/
theorem uniqueFactorizationMonoid_of_ringKrullDim_eq_two (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 2) :
    letI := isDomain_of_isRegularLocalRing R
    UniqueFactorizationMonoid R := by
  letI : IsDomain R := isDomain_of_isRegularLocalRing R
  exact UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
    fun p _ hph ↦ isPrincipal_of_height_one hdim p hph

end IsRegularLocalRing
-- Tengoku: root names of this library moved to Tengoku.GrothendieckRiemannRoch so they do not collide with other libraries (generated)
