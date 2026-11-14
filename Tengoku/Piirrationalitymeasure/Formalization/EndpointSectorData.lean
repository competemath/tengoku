import Tengoku.Piirrationalitymeasure.Formalization.EndpointCountData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The twelve rays and exact velocity-order checks from Section 6.6. -/

namespace PiIrrationality

def candidateSectorRay (i : Fin 12) : ℚ × ℚ :=
  ![(1, 0), (1857, 929), (1, 2), (0, 1), (-3713, 3714), (-2, 1),
    (-1, 0), (-1857, -929), (-1, -2), (0, -1), (3713, -3714), (2, -1)] i

def candidateSectorNext (i : Fin 12) : Fin 12 := i + 1

noncomputable def candidateSectorRayReal (i : Fin 12) : ℝ × ℝ :=
  ((candidateSectorRay i).1, (candidateSectorRay i).2)

def CandidateOpenSector (i : Fin 12) (v : ℝ × ℝ) : Prop :=
  ∃ u t : ℝ, 0 < u ∧ 0 < t ∧
    v = u • candidateSectorRayReal i + t • candidateSectorRayReal (candidateSectorNext i)

def CandidateClosedSector (i : Fin 12) (v : ℝ × ℝ) : Prop :=
  ∃ u t : ℝ, 0 ≤ u ∧ 0 ≤ t ∧
    v = u • candidateSectorRayReal i + t • candidateSectorRayReal (candidateSectorNext i)

theorem candidateSectorRay_det_pos : ∀ i : Fin 12,
    0 < (candidateSectorRay i).1 * (candidateSectorRay (candidateSectorNext i)).2 -
      (candidateSectorRay i).2 * (candidateSectorRay (candidateSectorNext i)).1 := by
  decide +kernel

theorem candidateSectorDirection_velocities_distinct : ∀ (i : Fin 12)
    (T S : SavingEndpointType),
    candidateEndpointVelocityRat (candidateSectorDirection i) T =
      candidateEndpointVelocityRat (candidateSectorDirection i) S ↔ T = S := by
  decide +kernel

theorem candidateSectorRay_velocity_order : ∀ (i : Fin 12) (T S : SavingEndpointType),
    candidateEndpointVelocityRat (candidateSectorDirection i) T <
        candidateEndpointVelocityRat (candidateSectorDirection i) S →
      candidateEndpointVelocityRat (candidateSectorRay i) T ≤
        candidateEndpointVelocityRat (candidateSectorRay i) S ∧
      candidateEndpointVelocityRat (candidateSectorRay (candidateSectorNext i)) T ≤
        candidateEndpointVelocityRat (candidateSectorRay (candidateSectorNext i)) S ∧
      (candidateEndpointVelocityRat (candidateSectorRay i) T <
        candidateEndpointVelocityRat (candidateSectorRay i) S ∨
      candidateEndpointVelocityRat (candidateSectorRay (candidateSectorNext i)) T <
        candidateEndpointVelocityRat (candidateSectorRay (candidateSectorNext i)) S) := by
  decide +kernel

end PiIrrationality
