import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Compact.Definitions
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Challenge
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Bounded coordinate proof for the inverse trace Gram permutation -/

noncomputable section
namespace CompactOneBit

open scoped BigOperators

def oldDual (f : Coord) : Coord := fun k => ∑ j : Fin 27,
  f j * AlbertLean.traceDualCoeff j k

private theorem oldDual_coord_0 (f : Coord) : oldDual f 0 = f 0 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_1 (f : Coord) : oldDual f 1 = f 1 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_2 (f : Coord) : oldDual f 2 = f 2 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]

-- The remaining coordinates are generated as separate declarations below so
-- each finite delta-sum reduction receives an independent heartbeat budget.
private theorem oldDual_coord_3 (f : Coord) : oldDual f 3 = f 4 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_4 (f : Coord) : oldDual f 4 = f 3 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_5 (f : Coord) : oldDual f 5 = f 10 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_6 (f : Coord) : oldDual f 6 = -f 9 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_7 (f : Coord) : oldDual f 7 = f 8 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_8 (f : Coord) : oldDual f 8 = f 7 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_9 (f : Coord) : oldDual f 9 = -f 6 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_10 (f : Coord) : oldDual f 10 = f 5 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_11 (f : Coord) : oldDual f 11 = f 15 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_12 (f : Coord) : oldDual f 12 = f 16 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_13 (f : Coord) : oldDual f 13 = f 17 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_14 (f : Coord) : oldDual f 14 = f 18 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_15 (f : Coord) : oldDual f 15 = f 11 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_16 (f : Coord) : oldDual f 16 = f 12 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_17 (f : Coord) : oldDual f 17 = f 13 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_18 (f : Coord) : oldDual f 18 = f 14 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_19 (f : Coord) : oldDual f 19 = f 23 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_20 (f : Coord) : oldDual f 20 = f 24 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_21 (f : Coord) : oldDual f 21 = f 25 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_22 (f : Coord) : oldDual f 22 = f 26 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_23 (f : Coord) : oldDual f 23 = f 19 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_24 (f : Coord) : oldDual f 24 = f 20 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_25 (f : Coord) : oldDual f 25 = f 21 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]
private theorem oldDual_coord_26 (f : Coord) : oldDual f 26 = f 22 := by
  simp [oldDual, AlbertLean.traceDualCoeff, AlbertLean.traceDualCoeffNat,
    Fin.sum_univ_succ, AlbertLean.q]

theorem dual_eq_oldDual (f : Coord) : dual f = oldDual f := by
  funext k
  fin_cases k <;> simp [dual, oldDual_coord_0, oldDual_coord_1,
    oldDual_coord_2, oldDual_coord_3, oldDual_coord_4, oldDual_coord_5,
    oldDual_coord_6, oldDual_coord_7, oldDual_coord_8, oldDual_coord_9,
    oldDual_coord_10, oldDual_coord_11, oldDual_coord_12, oldDual_coord_13,
    oldDual_coord_14, oldDual_coord_15, oldDual_coord_16, oldDual_coord_17,
    oldDual_coord_18, oldDual_coord_19, oldDual_coord_20, oldDual_coord_21,
    oldDual_coord_22, oldDual_coord_23, oldDual_coord_24, oldDual_coord_25,
    oldDual_coord_26]

end CompactOneBit
