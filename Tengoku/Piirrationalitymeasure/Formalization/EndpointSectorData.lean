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

/--
@isnad1 id=lt.0h1v.s5.831cc8b53356 from=translated src=- shape=566a610d vocab=dff20156
-/
theorem candidateSectorRay_det_pos : ∀ i : Fin 12,
    0 < (candidateSectorRay i).1 * (candidateSectorRay (candidateSectorNext i)).2 -
      (candidateSectorRay i).2 * (candidateSectorRay (candidateSectorNext i)).1 := by
  decide +kernel

/--
@isnad1 id=iff.0h3v.s4.c757dca667d8 from=translated src=- shape=f88bc008 vocab=dbff1d3a
-/
theorem candidateSectorDirection_velocities_distinct : ∀ (i : Fin 12)
    (T S : SavingEndpointType),
    candidateEndpointVelocityRat (candidateSectorDirection i) T =
      candidateEndpointVelocityRat (candidateSectorDirection i) S ↔ T = S := by
  decide +kernel

/--
@isnad1 id=and.1h3v.s6.75b5ad56cd02 from=translated src=- shape=790fd0c4 vocab=1ab29191
-/
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
