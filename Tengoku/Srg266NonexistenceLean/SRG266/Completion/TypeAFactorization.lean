/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.D7Glue
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.RankSixComplements
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11TypeAFactorization
import Tengoku.Srg266NonexistenceLean.SRG266.NotOneIntegrable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

open SRG266.Lattice
open scoped BigOperators _root_.Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
@isnad1 id=eq.2h6v.s13.407c1db76b70 from=translated src=- shape=123a0e89 vocab=1d8215c3
-/
theorem lorentzD7FrameVector_pair_localGram
    (hG : IsHypothetical G) (x : V) (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (D E : SecondSubconstituent G x) :
    lorentzD7Form G x c (lorentzD7FrameVector G hG x c hc D)
      (lorentzD7FrameVector G hG x c hc E) = (localGramMatrix G x D E : ℚ)+1 := by
  change lorentzPerpForm G x c (lorentzPerpGenerator G hG x c hc D)
    (lorentzPerpGenerator G hG x c hc E) +
      standardRatForm 7 (coordinateSpinor 7) (coordinateSpinor 7) = _
  rw [coordinateSpinor_norm]
  have h := lorentzHeightZeroPart_generator_generator G hG x c hc D E
  change lorentzPerpForm G x c (lorentzPerpGenerator G hG x c hc D)
    (lorentzPerpGenerator G hG x c hc E) = (localKMatrix G x D E : ℚ)+1/4 at h
  rw [h]
  simp [localKMatrix]
  ring

end SRG266
