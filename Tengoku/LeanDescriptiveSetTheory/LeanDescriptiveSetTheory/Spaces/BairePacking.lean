/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.Seed.Logic.Equiv.Nat
import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinate packing for Baire space

This module fixes the coordinate order used by universal analytic relations. A single Baire point
is homeomorphic to a pair, and hence to a left-associated triple `((parameter, object), witness)`.
It also gives a continuous surjection from Baire space onto Cantor space, with an explicit right
inverse, so the existing Cantor parameters for universal closed sets can be reused.
-/

namespace DescriptiveSetTheory

/-- Baire space is homeomorphic to two copies of itself.-/
def bairePairHomeomorph : (ℕ → ℕ) ≃ₜ (ℕ → ℕ) × (ℕ → ℕ) :=
  (Homeomorph.piCongrLeft (Y := fun _ : ℕ => ℕ) Equiv.natSumNatEquivNat).symm.trans
    (Homeomorph.sumPiEquivProdPi ℕ ℕ fun _ => ℕ)

/-- Pack two Baire points into one.-/
def packBairePair (p : (ℕ → ℕ) × (ℕ → ℕ)) : ℕ → ℕ :=
  bairePairHomeomorph.symm p

/-- Unpack one Baire point into two.-/
def unpackBairePair (p : ℕ → ℕ) : (ℕ → ℕ) × (ℕ → ℕ) :=
  bairePairHomeomorph p

/--
@isnad1 id=eq.0h1v.s4.bc25ea4251c9 from=translated src=- shape=0c340fec vocab=baafdf38
-/
@[simp]
theorem unpackBairePair_packBairePair (p : (ℕ → ℕ) × (ℕ → ℕ)) :
    unpackBairePair (packBairePair p) = p :=
  bairePairHomeomorph.apply_symm_apply p

/--
@isnad1 id=eq.0h1v.s3.dcb42d6cfab8 from=translated src=- shape=4c35d954 vocab=19f28a8e
-/
@[simp]
theorem packBairePair_unpackBairePair (p : ℕ → ℕ) :
    packBairePair (unpackBairePair p) = p :=
  bairePairHomeomorph.symm_apply_apply p

/-- Pair packing is continuous.
@isnad1 id=continuo.0h0v.s5.0c24cefd5fa9 from=translated src=- shape=08501989 vocab=89ee127b
-/
theorem continuous_packBairePair : Continuous packBairePair :=
  bairePairHomeomorph.symm.continuous

/-- Pair unpacking is continuous.
@isnad1 id=continuo.0h0v.s5.411a55a8e694 from=translated src=- shape=9472c28e vocab=7750aa88
-/
theorem continuous_unpackBairePair : Continuous unpackBairePair :=
  bairePairHomeomorph.continuous

/-- A single Baire point packs a left-associated parameter/object/witness triple.-/
def baireTripleHomeomorph :
    (ℕ → ℕ) ≃ₜ (((ℕ → ℕ) × (ℕ → ℕ)) × (ℕ → ℕ)) :=
  bairePairHomeomorph.trans
    (bairePairHomeomorph.prodCongr (Homeomorph.refl (ℕ → ℕ)))

/-- Pack a left-associated Baire triple into one Baire point.-/
def packBaireTriple (p : ((ℕ → ℕ) × (ℕ → ℕ)) × (ℕ → ℕ)) : ℕ → ℕ :=
  baireTripleHomeomorph.symm p

/-- Unpack a Baire point as `((parameter, object), witness)`.-/
def unpackBaireTriple (p : ℕ → ℕ) : ((ℕ → ℕ) × (ℕ → ℕ)) × (ℕ → ℕ) :=
  baireTripleHomeomorph p

/--
@isnad1 id=eq.0h1v.s4.b31bf196d7aa from=translated src=- shape=82d0b42d vocab=15813458
-/
@[simp]
theorem unpackBaireTriple_packBaireTriple
    (p : ((ℕ → ℕ) × (ℕ → ℕ)) × (ℕ → ℕ)) :
    unpackBaireTriple (packBaireTriple p) = p :=
  baireTripleHomeomorph.apply_symm_apply p

/--
@isnad1 id=eq.0h1v.s3.78719baa3d47 from=translated src=- shape=4c35d954 vocab=5bc29307
-/
@[simp]
theorem packBaireTriple_unpackBaireTriple (p : ℕ → ℕ) :
    packBaireTriple (unpackBaireTriple p) = p :=
  baireTripleHomeomorph.symm_apply_apply p

/-- Read a Baire point as a Cantor point by testing each coordinate for zero.-/
def baireToCantor (p : ℕ → ℕ) (n : ℕ) : Bool :=
  if p n = 0 then false else true

/-- Embed a Cantor point into Baire space using only zero and one.-/
def cantorToBaire (q : ℕ → Bool) (n : ℕ) : ℕ :=
  if q n = false then 0 else 1

/-- The explicit Cantor-to-Baire embedding is a right inverse of `baireToCantor`.
@isnad1 id=eq.0h1v.s3.f2ceba667cff from=translated src=- shape=ca40310a vocab=01ea87df
-/
@[simp]
theorem baireToCantor_cantorToBaire (q : ℕ → Bool) :
    baireToCantor (cantorToBaire q) = q := by
  ext n
  cases h : q n <;> simp [baireToCantor, cantorToBaire, h]

/-- The coordinatewise map from Baire space onto Cantor space is continuous.
@isnad1 id=continuo.0h0v.s4.a87fb6214514 from=translated src=- shape=9b4c26d4 vocab=5c4dfcc5
-/
theorem continuous_baireToCantor : Continuous baireToCantor :=
  continuous_pi fun n =>
    (show Continuous (fun k : ℕ => if k = 0 then false else true) from
      continuous_of_discreteTopology).comp (continuous_apply n)

/-- The zero-one embedding of Cantor space into Baire space is continuous.
@isnad1 id=continuo.0h0v.s4.816dc9454b75 from=translated src=- shape=9b4c26d4 vocab=eda4bf31
-/
theorem continuous_cantorToBaire : Continuous cantorToBaire :=
  continuous_pi fun n =>
    (show Continuous (fun b : Bool => if b = false then 0 else 1) from
      continuous_of_discreteTopology).comp (continuous_apply n)

end DescriptiveSetTheory
