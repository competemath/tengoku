import Tengoku.Piirrationalitymeasure.Formalization.EndpointSectorData
import Tengoku.Piirrationalitymeasure.Formalization.EndpointCountRealization
import Tengoku.Piirrationalitymeasure.Formalization.SavingGermOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Velocity order and actual endpoint germs are constant throughout each open sector. -/

namespace PiIrrationality

theorem candidateEndpointSlope_pos (T : SavingEndpointType) :
    0 < savingEndpointSlope 1857 3714 5570 T := by
  cases T <;> norm_num [savingEndpointSlope]

private theorem candidateSector_velocity_lt {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateOpenSector i v) (T S : SavingEndpointType)
    (hlt : (candidateEndpointVelocityRat (candidateSectorDirection i) T : ℝ) <
      (candidateEndpointVelocityRat (candidateSectorDirection i) S : ℝ)) :
    savingEndpointVelocity 1857 3714 5570 v T <
      savingEndpointVelocity 1857 3714 5570 v S := by
  have hc := candidateSectorRay_velocity_order i T S (by exact_mod_cast hlt)
  have hL : (candidateEndpointVelocityRat (candidateSectorRay i) T : ℝ) ≤
      (candidateEndpointVelocityRat (candidateSectorRay i) S : ℝ) := by
    exact_mod_cast hc.1
  have hR : (candidateEndpointVelocityRat (candidateSectorRay (candidateSectorNext i)) T : ℝ) ≤
      (candidateEndpointVelocityRat (candidateSectorRay (candidateSectorNext i)) S : ℝ) := by
    exact_mod_cast hc.2.1
  have hstrict : (candidateEndpointVelocityRat (candidateSectorRay i) T : ℝ) <
        (candidateEndpointVelocityRat (candidateSectorRay i) S : ℝ) ∨
      (candidateEndpointVelocityRat (candidateSectorRay (candidateSectorNext i)) T : ℝ) <
        (candidateEndpointVelocityRat (candidateSectorRay (candidateSectorNext i)) S : ℝ) := by
    exact_mod_cast hc.2.2
  rcases hv with ⟨u, t, hu, ht, rfl⟩
  simp only [savingEndpointVelocity_add_smul, candidateSectorRayReal,
    ← candidateEndpointVelocity_ratCast]
  rcases hstrict with h | h
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h hu)
      (mul_le_mul_of_nonneg_left hR ht.le)
  · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hL hu.le)
      (mul_lt_mul_of_pos_left h ht)

theorem candidateOpenSector_velocity_order {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateOpenSector i v) :
    SavingVelocityOrderEq 1857 3714 5570 v
      ((candidateSectorDirection i).1, (candidateSectorDirection i).2) := by
  intro T S
  rw [← candidateEndpointVelocity_ratCast, ← candidateEndpointVelocity_ratCast]
  constructor
  · intro h
    rcases lt_trichotomy
        (candidateEndpointVelocityRat (candidateSectorDirection i) T : ℝ)
        (candidateEndpointVelocityRat (candidateSectorDirection i) S : ℝ) with hlt | heq | hgt
    · exact hlt
    · have hTS := (candidateSectorDirection_velocities_distinct i T S).mp
        (by exact_mod_cast heq)
      subst S
      exact (lt_irrefl _ h).elim
    · exact (lt_asymm h (candidateSector_velocity_lt hv S T hgt)).elim
  · exact candidateSector_velocity_lt hv T S

theorem candidateOpenSector_chiGerm {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateOpenSector i v) (T : SavingEndpointType) (j : ℤ) (side : ℚ) :
    savingEndpointChiGerm 1857 3714 5570 v T j side =
      (candidateEndpointChiGermRat (candidateSectorDirection i) T j side : ℝ) := by
  rw [savingEndpointChiGerm_eq_of_order candidateEndpointSlope_pos
    (candidateOpenSector_velocity_order hv), candidateEndpointChiGerm_ratCast]

end PiIrrationality
