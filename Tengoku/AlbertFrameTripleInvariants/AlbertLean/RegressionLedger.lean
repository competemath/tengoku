import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.Regressions
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.TraceFormLaws
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

theorem traceForm_basis_0_scratch (y : Coord) :
    traceForm (basisVec 0) y = y 0 := by
  norm_num [traceForm_eq_gram, traceFormGram, basisVec, v, q, Fin.ext_iff]

theorem traceForm_basis_1_scratch (y : Coord) :
    traceForm (basisVec 1) y = y 1 := by
  norm_num [traceForm_eq_gram, traceFormGram, basisVec, v, q, Fin.ext_iff]

theorem regressionM09 :
    m09LedgerTheta1.P 0 1 = q 1 36 ∧
    (ledger witnessThetaM).P 0 1 = q 4 3 ∧
    m09LedgerTheta1 ≠ ledger witnessThetaM := by
  have he1 : projector theta1E 1 = basisVec 1 := by
    rw [show projector theta1E 1 =
      one - structuredProduct theta1E theta1E by rfl, theta1E_square]
    funext k
    fin_cases k <;>
      norm_num [Theta1ESquare, one, basisVec, v, q, Fin.ext_iff]
  have hem0 : projector thetaME 0 = basisVec 0 := by
    rw [thetaME_eq_theta1E_fast]
    rw [show projector theta1E 0 =
      (2 : ℚ)⁻¹ • (structuredProduct theta1E theta1E - theta1E) by rfl,
      theta1E_square]
    funext k
    fin_cases k <;>
      norm_num [Theta1ESquare, theta1E, one, basisVec, v, q, Fin.ext_iff]
  have hf0coord : projector theta1F 0 1 = q 1 36 := by
    rw [show projector theta1F 0 =
      (2 : ℚ)⁻¹ • (structuredProduct theta1F theta1F - theta1F) by rfl,
      theta1F_square]
    norm_num [Theta1FSquare, theta1F, v, q]
  have hfm1coord : projector thetaMF 1 0 = q 4 3 := by
    rw [show projector thetaMF 1 =
      one - structuredProduct thetaMF thetaMF by rfl, thetaMF_square]
    norm_num [ThetaMFSquare, thetaMF, one, v, q]
  have hmut : m09LedgerTheta1.P 0 1 = q 1 36 := by
    simp [m09LedgerTheta1, ledger, witnessTheta1]
    rw [he1, traceForm_basis_1_scratch, hf0coord]
  have hbase : (ledger witnessThetaM).P 0 1 = q 4 3 := by
    simp [ledger, witnessThetaM]
    rw [hem0, traceForm_basis_0_scratch, hfm1coord]
  refine ⟨hmut, hbase, ?_⟩
  intro h
  have hp := congrArg (fun L : Ledger => L.P 0 1) h
  rw [hmut, hbase] at hp
  norm_num [q] at hp

end AlbertLean
