import Tengoku.Piirrationalitymeasure.Formalization.SavingEndpointGerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Endpoint germs depend only on the relative order of endpoint velocities. -/

namespace PiIrrationality

def SavingVelocityOrderEq (a b c : ℝ) (v w : ℝ × ℝ) : Prop :=
  ∀ T S : SavingEndpointType,
    savingEndpointVelocity a b c v T < savingEndpointVelocity a b c v S ↔
      savingEndpointVelocity a b c w T < savingEndpointVelocity a b c w S

theorem SavingVelocityOrderEq.eq_iff {a b c : ℝ} {v w : ℝ × ℝ}
    (h : SavingVelocityOrderEq a b c v w) (T S : SavingEndpointType) :
    savingEndpointVelocity a b c v T = savingEndpointVelocity a b c v S ↔
      savingEndpointVelocity a b c w T = savingEndpointVelocity a b c w S := by
  simp only [le_antisymm_iff, ← not_lt, h T S, h S T]

theorem savingEndpoint_linear_coefficient {a b c : ℝ} (v : ℝ × ℝ)
    (T S : SavingEndpointType) (hS : savingEndpointSlope a b c S ≠ 0) :
    savingEndpointSlope a b c S * savingEndpointVelocity a b c v T +
        savingEndpointGradient v S =
      savingEndpointSlope a b c S *
        (savingEndpointVelocity a b c v T - savingEndpointVelocity a b c v S) := by
  unfold savingEndpointVelocity
  field_simp
  <;> ring

theorem quadraticFloorGerm_eq_of_sign {x l l' q : ℝ}
    (hneg : l < 0 ↔ l' < 0) (hzero : l = 0 ↔ l' = 0) :
    quadraticFloorGerm x l q = quadraticFloorGerm x l' q := by
  have hp : quadraticPerturbationNegative l q ↔ quadraticPerturbationNegative l' q := by
    simp only [quadraticPerturbationNegative, hneg, hzero]
  by_cases h : x = (⌊x⌋ : ℝ) ∧ quadraticPerturbationNegative l q
  · rw [quadraticFloorGerm, ite_eq_left h, quadraticFloorGerm, ite_eq_left ⟨h.1, hp.mp h.2⟩]
  · rw [quadraticFloorGerm, ite_eq_right h, quadraticFloorGerm,
      ite_eq_right (fun h' => h ⟨h'.1, hp.mpr h'.2⟩)]

theorem savingEndpointFloorGerm_eq_of_order {a b c : ℝ} {v w : ℝ × ℝ}
    (hpos : ∀ S, 0 < savingEndpointSlope a b c S)
    (horder : SavingVelocityOrderEq a b c v w)
    (T : SavingEndpointType) (j : ℤ) (side : ℝ) (S : SavingEndpointType) :
    savingEndpointFloorGerm a b c v T j side S =
      savingEndpointFloorGerm a b c w T j side S := by
  unfold savingEndpointFloorGerm
  rw [savingEndpoint_linear_coefficient v T S (ne_of_gt (hpos S)),
    savingEndpoint_linear_coefficient w T S (ne_of_gt (hpos S))]
  apply quadraticFloorGerm_eq_of_sign
  · have hmul (d : ℝ) : savingEndpointSlope a b c S * d < 0 ↔ d < 0 := by
      constructor
      · intro h
        nlinarith [hpos S]
      · exact mul_neg_of_pos_of_neg (hpos S)
    simpa only [hmul, sub_neg] using horder T S
  · simpa only [mul_eq_zero, (ne_of_gt (hpos S)), false_or, sub_eq_zero] using
      horder.eq_iff T S

theorem savingEndpointChiGerm_eq_of_order {a b c : ℝ} {v w : ℝ × ℝ}
    (hpos : ∀ S, 0 < savingEndpointSlope a b c S)
    (horder : SavingVelocityOrderEq a b c v w)
    (T : SavingEndpointType) (j : ℤ) (side : ℝ) :
    savingEndpointChiGerm a b c v T j side =
      savingEndpointChiGerm a b c w T j side := by
  unfold savingEndpointChiGerm
  simp_rw [savingEndpointFloorGerm_eq_of_order hpos horder]

theorem savingEndpointVelocity_add_smul (a b c : ℝ) (v w : ℝ × ℝ)
    (u t : ℝ) (T : SavingEndpointType) :
    savingEndpointVelocity a b c (u • v + t • w) T =
      u * savingEndpointVelocity a b c v T + t * savingEndpointVelocity a b c w T := by
  cases T <;> dsimp [savingEndpointVelocity, savingEndpointGradient,
    savingEndpointShift, savingEndpointSlope] <;> ring

end PiIrrationality
