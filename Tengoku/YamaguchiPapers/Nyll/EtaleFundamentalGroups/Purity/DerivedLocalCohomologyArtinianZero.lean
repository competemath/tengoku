/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroModule
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.FinitePowerTorsionLength
import Tengoku.Seed.RingTheory.FiniteLength
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Defs
import Tengoku.Seed.RingTheory.Noetherian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite length in degree zero

Degree-zero local cohomology embeds in its finite coefficient module.
Noetherianity makes it finite, and its maximal-ideal-power torsion then
gives finite length.  This is the base of the Artinianness induction.
-/

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Degree-zero local cohomology of a finite module over a Noetherian
local ring has finite length.
@isnad1 id=isfinite.0h2v.s6.b48990c8a2b7 from=translated src=- shape=4f897a49 vocab=b069d905
-/
theorem isFiniteLength_derivedLocalCohomologyModule_maximalIdeal_zero
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsFiniteLength R
      (derivedLocalCohomologyModule (IsLocalRing.maximalIdeal R) M 0) := by
  let : IsNoetherian R
      (derivedLocalCohomologyModule (IsLocalRing.maximalIdeal R) M 0) :=
    isNoetherian_of_injective
      (derivedLocalCohomologyZeroToModule (IsLocalRing.maximalIdeal R) M)
      (derivedLocalCohomologyZeroToModule_injective (IsLocalRing.maximalIdeal R) M)
  exact Purity.isFiniteLength_of_finite_of_maximalIdealPower_torsion
    (derivedLocalCohomologyModule_exists_idealPower_smul_eq_zero
      (IsLocalRing.maximalIdeal R) M 0)

/-- In particular degree-zero maximal-support local cohomology of a
finite module is Artinian.
@isnad1 id=isartini.0h2v.s7.fb5160f2757e from=translated src=- shape=4f897a49 vocab=5da79005
-/
theorem isArtinian_derivedLocalCohomologyModule_maximalIdeal_zero
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsArtinian R
      (derivedLocalCohomologyModule (IsLocalRing.maximalIdeal R) M 0) :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp
    (isFiniteLength_derivedLocalCohomologyModule_maximalIdeal_zero M)).2

end EtaleFundamentalGroups
