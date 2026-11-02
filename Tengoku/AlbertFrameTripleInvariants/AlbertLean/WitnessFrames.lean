import Tengoku.AlbertFrameTripleInvariants.AlbertLean.FrameLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

private theorem theta1E_lawfulEncoder : LawfulEncoder theta1E := by
  norm_num [LawfulEncoder, traceN_eq_coords, spurN_eq_spurPairForm,
    spurPairForm, cubicNorm,
    theta1E, one, v, q]

private theorem theta1F_lawfulEncoder : LawfulEncoder theta1F := by
  norm_num [LawfulEncoder, traceN_eq_coords, spurN_eq_spurPairForm,
    spurPairForm, cubicNorm,
    theta1F, one, v, q]

private theorem theta1K_lawfulEncoder : LawfulEncoder theta1K := by
  norm_num [LawfulEncoder, traceN_eq_coords, spurN_eq_spurPairForm,
    spurPairForm, cubicNorm,
    theta1K, one, v, q]

private theorem thetaME_lawfulEncoder : LawfulEncoder thetaME := by
  norm_num [LawfulEncoder, traceN_eq_coords, spurN_eq_spurPairForm,
    spurPairForm, cubicNorm,
    thetaME, one, v, q]

private theorem thetaMF_lawfulEncoder : LawfulEncoder thetaMF := by
  norm_num [LawfulEncoder, traceN_eq_coords, spurN_eq_spurPairForm,
    spurPairForm, cubicNorm,
    thetaMF, one, v, q]

private theorem thetaMK_lawfulEncoder : LawfulEncoder thetaMK := by
  norm_num [LawfulEncoder, traceN_eq_coords, spurN_eq_spurPairForm,
    spurPairForm, cubicNorm,
    thetaMK, one, v, q]

theorem witnessTheta1Lawful : LawfulFrameTriple witnessTheta1 := by
  intro r
  fin_cases r
  · exact lawfulFrame_of_lawfulEncoder theta1E theta1E_lawfulEncoder
  · exact lawfulFrame_of_lawfulEncoder theta1F theta1F_lawfulEncoder
  · exact lawfulFrame_of_lawfulEncoder theta1K theta1K_lawfulEncoder

theorem witnessThetaMLawful : LawfulFrameTriple witnessThetaM := by
  intro r
  fin_cases r
  · exact lawfulFrame_of_lawfulEncoder thetaME thetaME_lawfulEncoder
  · exact lawfulFrame_of_lawfulEncoder thetaMF thetaMF_lawfulEncoder
  · exact lawfulFrame_of_lawfulEncoder thetaMK thetaMK_lawfulEncoder

end AlbertLean
