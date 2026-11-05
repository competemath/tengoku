/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.IdealCyclotomicBaseResidue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cyclotomic inversion from a divisorial residue field

For a discrete valuation base, the residue field is the function field of the
corresponding prime divisor.  This file identifies that field with the
intrinsic decomposition residue field of a prime in a finite Galois
normalization, and feeds geometric integrality of the divisorial residue
field into finite-level cyclotomic inversion.
-/

noncomputable section

universe uB uK uL

namespace TameAbhyankar.SGA1

open CategoryTheory
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

attribute [local instance] Ideal.Quotient.field

/-- A prime above the maximal ideal of a discrete valuation base is nonzero.
The torsion-free algebra instance is constructed from the specified integral
closure rather than exposed as an additional hypothesis.
@isnad1 id=ne.0h5v.s8.1d250c42e1dc from=translated src=- shape=356dd769 vocab=b6a36a47
-/
theorem dvrNormalizationPrime_ne_bot
    {A : Type uL} {B : Type uB} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [Algebra K L] [Algebra A B] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (P : Ideal B) [P.LiesOver (IsLocalRing.maximalIdeal A)] : P ≠ ⊥ := by
  let : Module.IsTorsionFree A L :=
    Module.IsTorsionFree.trans_faithfulSMul A K L
  have hAL : Function.Injective (algebraMap A L) := by
    intro x y hxy
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa only [IsScalarTower.algebraMap_apply A K L] using hxy
  have hAB : Function.Injective (algebraMap A B) := by
    intro x y hxy
    apply hAL
    rw [IsScalarTower.algebraMap_apply A B L,
      IsScalarTower.algebraMap_apply A B L, hxy]
  let : Nontrivial B :=
    hAB.nontrivial
  let : Module.IsTorsionFree A B :=
    IsIntegralClosure.isTorsionFree A L
  exact Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field A) P

end TameAbhyankar.SGA1

end
