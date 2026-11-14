import Tengoku.Piirrationalitymeasure.Formalization.EndpointSectorData
import Tengoku.Piirrationalitymeasure.Formalization.EndpointCountRealization
import Tengoku.Piirrationalitymeasure.Formalization.SavingTranslationBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The printed linear forms, their wall values, and the uniform cone bound. -/

namespace PiIrrationality

def candidateSectorLinearFormRat (i : Fin 12) (v : ℚ × ℚ) : ℚ :=
  (candidateSectorRow i).px * v.1 + (candidateSectorRow i).py * v.2

noncomputable def candidateSectorLinearForm (i : Fin 12) (v : ℝ × ℝ) : ℝ :=
  ((candidateSectorRow i).px : ℝ) * v.1 + ((candidateSectorRow i).py : ℝ) * v.2

theorem candidateSectorLinearForm_ratCast (i : Fin 12) (v : ℚ × ℚ) :
    (candidateSectorLinearFormRat i v : ℝ) = candidateSectorLinearForm i (v.1, v.2) := by
  simp only [candidateSectorLinearFormRat, candidateSectorLinearForm, Rat.cast_add, Rat.cast_mul]

theorem candidateSectorLinearForm_add_smul (i : Fin 12) (v w : ℝ × ℝ) (u t : ℝ) :
    candidateSectorLinearForm i (u • v + t • w) =
      u * candidateSectorLinearForm i v + t * candidateSectorLinearForm i w := by
  dsimp [candidateSectorLinearForm]
  ring

theorem candidateSectorLinearForm_counts (i : Fin 12) (v : ℝ × ℝ) :
    (candidateExpectedCount i .A : ℝ) * savingEndpointVelocity 1857 3714 5570 v .A +
      (candidateExpectedCount i .B : ℝ) * savingEndpointVelocity 1857 3714 5570 v .B +
      (candidateExpectedCount i .C : ℝ) * savingEndpointVelocity 1857 3714 5570 v .C +
      (candidateExpectedCount i .Q : ℝ) * savingEndpointVelocity 1857 3714 5570 v .Q =
        candidateSectorLinearForm i v := by
  have hm : candidateSectorRow i ∈ sectorRows := List.getElem_mem _
  obtain ⟨hx, hy⟩ := sectorRows_forms _ hm
  dsimp [candidateSectorLinearForm, candidateExpectedCount, savingEndpointVelocity,
    savingEndpointGradient, savingEndpointShift, savingEndpointSlope]
  rw [hx, hy]
  push_cast
  ring

theorem candidateSectorLinearForm_wall_rat : ∀ i : Fin 12,
    candidateSectorLinearFormRat i (candidateSectorRay (candidateSectorNext i)) =
      candidateSectorLinearFormRat (candidateSectorNext i)
        (candidateSectorRay (candidateSectorNext i)) := by
  decide +kernel

theorem candidateSectorLinearForm_rays_bound_rat : ∀ i : Fin 12,
    candidateSectorLinearFormRat i (candidateSectorRay i) ≤
      -(557 : ℚ) / 4139253 * (|(candidateSectorRay i).1| + |(candidateSectorRay i).2|) ∧
    candidateSectorLinearFormRat i (candidateSectorRay (candidateSectorNext i)) ≤
      -(557 : ℚ) / 4139253 *
        (|(candidateSectorRay (candidateSectorNext i)).1| +
          |(candidateSectorRay (candidateSectorNext i)).2|) := by
  decide +kernel

theorem candidateSectorLinearForm_wall (i : Fin 12) :
    candidateSectorLinearForm i (candidateSectorRayReal (candidateSectorNext i)) =
      candidateSectorLinearForm (candidateSectorNext i)
        (candidateSectorRayReal (candidateSectorNext i)) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (candidateSectorLinearForm_wall_rat i)
  simpa only [candidateSectorLinearForm_ratCast, candidateSectorRayReal] using h

theorem candidateSectorLinearForm_rays_bound (i : Fin 12) :
    candidateSectorLinearForm i (candidateSectorRayReal i) ≤
      -(557 : ℝ) / 4139253 * parameterNormOne (candidateSectorRayReal i) ∧
    candidateSectorLinearForm i (candidateSectorRayReal (candidateSectorNext i)) ≤
      -(557 : ℝ) / 4139253 *
        parameterNormOne (candidateSectorRayReal (candidateSectorNext i)) := by
  have h := candidateSectorLinearForm_rays_bound_rat i
  unfold candidateSectorRayReal parameterNormOne
  dsimp only [Prod.fst, Prod.snd]
  rw [← candidateSectorLinearForm_ratCast, ← candidateSectorLinearForm_ratCast]
  exact_mod_cast h

theorem candidateSectorLinearForm_bound {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateClosedSector i v) :
    candidateSectorLinearForm i v ≤ -(557 : ℝ) / 4139253 * parameterNormOne v := by
  rcases hv with ⟨u, t, hu, ht, rfl⟩
  obtain ⟨hL, hR⟩ := candidateSectorLinearForm_rays_bound i
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hL hu)
    (mul_le_mul_of_nonneg_left hR ht)
  have hn : parameterNormOne
      (u • candidateSectorRayReal i + t • candidateSectorRayReal (candidateSectorNext i)) ≤
      u * parameterNormOne (candidateSectorRayReal i) +
        t * parameterNormOne (candidateSectorRayReal (candidateSectorNext i)) := by
    have h : ∀ z w : ℝ × ℝ, parameterNormOne (z + w) ≤
        parameterNormOne z + parameterNormOne w := by
      intro z w
      dsimp [parameterNormOne]
      linarith [abs_add_le z.1 w.1, abs_add_le z.2 w.2]
    simpa only [parameterNormOne_smul, abs_of_nonneg hu, abs_of_nonneg ht] using
      h (u • candidateSectorRayReal i) (t • candidateSectorRayReal (candidateSectorNext i))
  rw [candidateSectorLinearForm_add_smul]
  nlinarith only [hsum, hn]

end PiIrrationality
