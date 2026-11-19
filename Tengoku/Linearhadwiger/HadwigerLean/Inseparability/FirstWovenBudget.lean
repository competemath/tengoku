import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.ScaleCeilEstimates
import Tengoku.Linearhadwiger.HadwigerLean.Woven.Uniform
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The first CI stage needs a rooted clique model and no linkage paths. -/

namespace HadwigerLean.Inseparability

/--
@isnad1 id=le.2h2v.s5.451606c485e7 from=translated src=- shape=2c9eb290 vocab=60006f9a
-/
theorem first_stage_uniformCliqueK_le
    (t C : ℕ) (ht : 3 ≤ t) (hC : 9000000 ≤ C) :
    HadwigerLean.Woven.uniformCliqueK (stageBlockSize t) 0 ≤ C * t := by
  let x := stageBlockSize t
  let d : ℝ :=
    30 * (((2 * x : ℕ) : ℝ)) *
      Real.sqrt (Real.log (((2 * x : ℕ) : ℝ)))
  let q := Nat.ceil d
  have hx : x ≤ t := stageBlockSize_le t ht
  have hr := stageBlockSize_root_log_bound t ht
  change (((2 * x : ℕ) : ℝ) *
    Real.sqrt (Real.log (((2 * x : ℕ) : ℝ)))) ≤ 4 * (t : ℝ) at hr
  have hd : d ≤ (120 * t : ℕ) := by
    dsimp [d]
    push_cast at hr ⊢
    nlinarith
  have hq : q ≤ 120 * t := Nat.ceil_le.mpr hd
  have hK : HadwigerLean.Woven.uniformCliqueK x 0 = x + 2 * (x + q) := by
    simp [HadwigerLean.Woven.uniformCliqueK,
      HadwigerLean.Woven.uniformCliqueQ, q, d]
  rw [hK]
  nlinarith

end HadwigerLean.Inseparability
