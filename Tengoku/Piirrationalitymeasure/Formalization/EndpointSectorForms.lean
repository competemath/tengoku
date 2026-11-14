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

/--
@isnad1 id=eq.0h2v.s5.9d761747a56d from=translated src=- shape=634a2f90 vocab=ce90287f
-/
theorem candidateSectorLinearForm_ratCast (i : Fin 12) (v : ℚ × ℚ) :
    (candidateSectorLinearFormRat i v : ℝ) = candidateSectorLinearForm i (v.1, v.2) := by
  simp only [candidateSectorLinearFormRat, candidateSectorLinearForm, Rat.cast_add, Rat.cast_mul]

/--
@isnad1 id=eq.0h5v.s6.c25830542a1d from=translated src=- shape=5017d2d9 vocab=6d3b94a3
-/
theorem candidateSectorLinearForm_add_smul (i : Fin 12) (v w : ℝ × ℝ) (u t : ℝ) :
    candidateSectorLinearForm i (u • v + t • w) =
      u * candidateSectorLinearForm i v + t * candidateSectorLinearForm i w := by
  dsimp [candidateSectorLinearForm]
  ring

/--
@isnad1 id=eq.0h2v.s7.7f8a9e40e063 from=translated src=- shape=74f1727d vocab=f3e50191
-/
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

/--
@isnad1 id=eq.0h1v.s4.d4de901f2393 from=translated src=- shape=4fa3492b vocab=fe43bea6
-/
theorem candidateSectorLinearForm_wall_rat : ∀ i : Fin 12,
    candidateSectorLinearFormRat i (candidateSectorRay (candidateSectorNext i)) =
      candidateSectorLinearFormRat (candidateSectorNext i)
        (candidateSectorRay (candidateSectorNext i)) := by
  decide +kernel

/--
@isnad1 id=and.0h1v.s7.3fc0b8418874 from=translated src=- shape=4a5f6d43 vocab=9c759a24
-/
theorem candidateSectorLinearForm_rays_bound_rat : ∀ i : Fin 12,
    candidateSectorLinearFormRat i (candidateSectorRay i) ≤
      -(557 : ℚ) / 4139253 * (|(candidateSectorRay i).1| + |(candidateSectorRay i).2|) ∧
    candidateSectorLinearFormRat i (candidateSectorRay (candidateSectorNext i)) ≤
      -(557 : ℚ) / 4139253 *
        (|(candidateSectorRay (candidateSectorNext i)).1| +
          |(candidateSectorRay (candidateSectorNext i)).2|) := by
  decide +kernel

/--
@isnad1 id=eq.0h1v.s4.c5a7bae47b2a from=translated src=- shape=4fa3492b vocab=68d0fae9
-/
theorem candidateSectorLinearForm_wall (i : Fin 12) :
    candidateSectorLinearForm i (candidateSectorRayReal (candidateSectorNext i)) =
      candidateSectorLinearForm (candidateSectorNext i)
        (candidateSectorRayReal (candidateSectorNext i)) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (candidateSectorLinearForm_wall_rat i)
  simpa only [candidateSectorLinearForm_ratCast, candidateSectorRayReal] using h

/--
@isnad1 id=and.0h1v.s6.0782836c4bc9 from=translated src=- shape=f8669e1a vocab=a32e5130
-/
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

/--
@isnad1 id=le.1h2v.s5.1a8338d1ee59 from=translated src=- shape=c9b8bae3 vocab=582abe64
-/
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
