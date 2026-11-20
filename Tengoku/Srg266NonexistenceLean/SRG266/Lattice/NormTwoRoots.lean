/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PDUnimodular

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

def NormTwoRoot {n : ℕ} (L : PDUnimodularLattice n) :=
  {x : L.carrier // L.pairing x x = 2}

instance {n : ℕ} (L : PDUnimodularLattice n) : InvolutiveNeg (NormTwoRoot L) where
  neg := fun r => ⟨-r.1, by simpa using r.2⟩
  neg_neg r := Subtype.ext (neg_neg r.1)

/--
@isnad1 id=eq.0h3v.s9.dc3027c681a7 from=translated src=- shape=b0caab32 vocab=d410adf2
-/
@[simp]
theorem NormTwoRoot.coe_neg {n : ℕ} {L : PDUnimodularLattice n}
    (r : NormTwoRoot L) : (-r).1 = -(r.1) :=
  rfl

def normTwoRootVal {n : ℕ} {L : PDUnimodularLattice n} :
    NormTwoRoot L → L.carrier := Subtype.val

/--
@isnad1 id=eq.0h3v.s6.e98a48fcc0e0 from=translated src=- shape=b9d2ee17 vocab=40b6f86d
-/
@[simp]
theorem normTwoRootVal_neg {n : ℕ} {L : PDUnimodularLattice n}
    (r : NormTwoRoot L) : normTwoRootVal (-r) = -normTwoRootVal r :=
  rfl

/--
@isnad1 id=ne.0h3v.s6.94f7b3a95cb7 from=translated src=- shape=67a9d111 vocab=d5dd78d7
-/
theorem normTwoRootVal_ne_zero {n : ℕ} {L : PDUnimodularLattice n}
    (r : NormTwoRoot L) : normTwoRootVal r ≠ 0 := by
  intro hr
  have hnorm := r.2
  change r.1 = 0 at hr
  simp [hr] at hnorm

end SRG266.Lattice
