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

@[simp]
theorem unpackBairePair_packBairePair (p : (ℕ → ℕ) × (ℕ → ℕ)) :
    unpackBairePair (packBairePair p) = p :=
  bairePairHomeomorph.apply_symm_apply p

@[simp]
theorem packBairePair_unpackBairePair (p : ℕ → ℕ) :
    packBairePair (unpackBairePair p) = p :=
  bairePairHomeomorph.symm_apply_apply p

/-- Pair packing is continuous.-/
theorem continuous_packBairePair : Continuous packBairePair :=
  bairePairHomeomorph.symm.continuous

/-- Pair unpacking is continuous.-/
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

@[simp]
theorem unpackBaireTriple_packBaireTriple
    (p : ((ℕ → ℕ) × (ℕ → ℕ)) × (ℕ → ℕ)) :
    unpackBaireTriple (packBaireTriple p) = p :=
  baireTripleHomeomorph.apply_symm_apply p

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

/-- The explicit Cantor-to-Baire embedding is a right inverse of `baireToCantor`.-/
@[simp]
theorem baireToCantor_cantorToBaire (q : ℕ → Bool) :
    baireToCantor (cantorToBaire q) = q := by
  ext n
  cases h : q n <;> simp [baireToCantor, cantorToBaire, h]

/-- The coordinatewise map from Baire space onto Cantor space is continuous.-/
theorem continuous_baireToCantor : Continuous baireToCantor :=
  continuous_pi fun n =>
    (show Continuous (fun k : ℕ => if k = 0 then false else true) from
      continuous_of_discreteTopology).comp (continuous_apply n)

/-- The zero-one embedding of Cantor space into Baire space is continuous.-/
theorem continuous_cantorToBaire : Continuous cantorToBaire :=
  continuous_pi fun n =>
    (show Continuous (fun b : Bool => if b = false then 0 else 1) from
      continuous_of_discreteTopology).comp (continuous_apply n)

end DescriptiveSetTheory
