import Tengoku.Seed.Analysis.SpecificLimits.Normed
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

def markedFactor (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ((R * (1 - qInv) - K * V ^ a) / (1 - V) + J) / (1 - R)

def markedTableSeries (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ∑' r : ℕ, R ^ r *
    ((∑' m : ℕ, (R * (1 - qInv) * V ^ m - K * V ^ (m + a))) + J)

/--
@isnad1 id=eq.2h6v.s5.5f71350d5100 from=translated src=- shape=ae758b73 vocab=58b802c4
-/
theorem marked_table_resummation (R V qInv K J : ℂ) (a : ℕ)
    (hR : ‖R‖ < 1) (hV : ‖V‖ < 1) :
    markedTableSeries R V qInv K J a = markedFactor R V qInv K J a := by
  have hgeo := hasSum_geometric_of_norm_lt_one hV
  have hfirst := hgeo.mul_left (R * (1 - qInv))
  have hsecond : HasSum (fun m : ℕ => K * V ^ (m + a))
      (K * V ^ a * (1 - V)⁻¹) := by
    convert hgeo.mul_left (K * V ^ a) using 1
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)
  have hin := (hfirst.sub hsecond).tsum_eq
  unfold markedTableSeries
  rw [hin, tsum_mul_right, tsum_geometric_of_norm_lt_one hR]
  unfold markedFactor
  simp only [div_eq_mul_inv]
  ring

/--
@isnad1 id=eq.2h6v.s7.f94d11ccfd49 from=translated src=- shape=89e0884a vocab=0961d568
-/
theorem unramified_marked_error (R V qInv K W D : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv K (-D + W * R) 1 + D =
      (R * ((1 - qInv) + (1 - V) * (W - D)) - K * V) /
        ((1 - R) * (1 - V)) := by
  unfold markedFactor
  field_simp
  ring

end SevenEighths.ProbeEuler
end

end OAI
