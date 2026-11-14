import Tengoku.Piirrationalitymeasure.Formalization.EndpointSectorData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The twelve closed cones cover all real directions. -/

namespace PiIrrationality

private theorem cone_of_nonneg_determinants (a b v : ℝ × ℝ)
    (hd : 0 < a.1 * b.2 - a.2 * b.1)
    (hL : 0 ≤ a.1 * v.2 - a.2 * v.1)
    (hR : 0 ≤ v.1 * b.2 - v.2 * b.1) :
    ∃ u t : ℝ, 0 ≤ u ∧ 0 ≤ t ∧ v = u • a + t • b := by
  refine ⟨(v.1 * b.2 - v.2 * b.1) / (a.1 * b.2 - a.2 * b.1),
    (a.1 * v.2 - a.2 * v.1) / (a.1 * b.2 - a.2 * b.1),
    div_nonneg hR hd.le, div_nonneg hL hd.le, ?_⟩
  apply Prod.ext
  · change v.1 = (v.1 * b.2 - v.2 * b.1) / (a.1 * b.2 - a.2 * b.1) * a.1 +
      (a.1 * v.2 - a.2 * v.1) / (a.1 * b.2 - a.2 * b.1) * b.1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff (ne_of_gt hd)).mpr
    ring
  · change v.2 = (v.1 * b.2 - v.2 * b.1) / (a.1 * b.2 - a.2 * b.1) * a.2 +
      (a.1 * v.2 - a.2 * v.1) / (a.1 * b.2 - a.2 * b.1) * b.2
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff (ne_of_gt hd)).mpr
    ring

/--
@isnad1 id=candidat.2h2v.s6.72c3d59691f6 from=translated src=- shape=3e3ea747 vocab=b253acf2
-/
theorem candidateClosedSector_of_det (i : Fin 12) (v : ℝ × ℝ)
    (hL : 0 ≤ (candidateSectorRayReal i).1 * v.2 - (candidateSectorRayReal i).2 * v.1)
    (hR : 0 ≤ v.1 * (candidateSectorRayReal (candidateSectorNext i)).2 -
      v.2 * (candidateSectorRayReal (candidateSectorNext i)).1) :
    CandidateClosedSector i v := by
  have hd : 0 < (candidateSectorRayReal i).1 *
        (candidateSectorRayReal (candidateSectorNext i)).2 -
      (candidateSectorRayReal i).2 * (candidateSectorRayReal (candidateSectorNext i)).1 := by
    dsimp only [candidateSectorRayReal]
    exact_mod_cast candidateSectorRay_det_pos i
  exact cone_of_nonneg_determinants _ _ _ hd hL hR

private theorem candidateSectorRay_opposite_rat : ∀ i : Fin 12,
    candidateSectorRay (i + 6) = -candidateSectorRay i := by
  decide +kernel

/--
@isnad1 id=eq.0h1v.s6.5631b878ba42 from=translated src=- shape=eae0735e vocab=24bcd7f6
-/
theorem candidateSectorRayReal_opposite (i : Fin 12) :
    candidateSectorRayReal (i + 6) = -candidateSectorRayReal i := by
  have h := congrArg (fun w : ℚ × ℚ => ((w.1 : ℝ), (w.2 : ℝ)))
    (candidateSectorRay_opposite_rat i)
  simpa [candidateSectorRayReal] using h

/--
@isnad1 id=candidat.1h2v.s6.9d1128514e79 from=translated src=- shape=90a31b6b vocab=db48d977
-/
theorem CandidateClosedSector.neg {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateClosedSector i v) : CandidateClosedSector (i + 6) (-v) := by
  rcases hv with ⟨u, t, hu, ht, rfl⟩
  refine ⟨u, t, hu, ht, ?_⟩
  have hnext : candidateSectorNext (i + 6) = candidateSectorNext i + 6 := by
    unfold candidateSectorNext
    ac_rfl
  rw [hnext, candidateSectorRayReal_opposite, candidateSectorRayReal_opposite]
  simp only [smul_neg, neg_add]

private theorem candidateClosedSector_cover_upper (v : ℝ × ℝ) (hy : 0 ≤ v.2) :
    ∃ i : Fin 12, CandidateClosedSector i v := by
  by_cases hx : 0 ≤ v.1
  · by_cases h0 : 1857 * v.2 ≤ 929 * v.1
    · refine ⟨0, candidateClosedSector_of_det 0 v ?_ ?_⟩ <;>
        dsimp [candidateSectorRayReal, candidateSectorRay, candidateSectorNext] <;>
        norm_num <;> linarith
    · by_cases h1 : v.2 ≤ 2 * v.1
      · refine ⟨1, candidateClosedSector_of_det 1 v ?_ ?_⟩ <;>
          dsimp [candidateSectorRayReal, candidateSectorRay, candidateSectorNext] <;>
          norm_num <;> linarith
      · refine ⟨2, candidateClosedSector_of_det 2 v ?_ ?_⟩ <;>
          dsimp [candidateSectorRayReal, candidateSectorRay, candidateSectorNext] <;>
          norm_num <;> linarith
  · by_cases h3 : 0 ≤ 3714 * v.1 + 3713 * v.2
    · refine ⟨3, candidateClosedSector_of_det 3 v ?_ ?_⟩ <;>
        dsimp [candidateSectorRayReal, candidateSectorRay, candidateSectorNext] <;>
        norm_num <;> linarith
    · by_cases h4 : 0 ≤ v.1 + 2 * v.2
      · refine ⟨4, candidateClosedSector_of_det 4 v ?_ ?_⟩ <;>
          dsimp [candidateSectorRayReal, candidateSectorRay, candidateSectorNext] <;>
          norm_num <;> linarith
      · refine ⟨5, candidateClosedSector_of_det 5 v ?_ ?_⟩ <;>
          dsimp [candidateSectorRayReal, candidateSectorRay, candidateSectorNext] <;>
          norm_num <;> linarith

/--
@isnad1 id=ex.0h1v.s4.240181dec354 from=translated src=- shape=58764068 vocab=a7b48499
-/
theorem candidateClosedSector_cover (v : ℝ × ℝ) :
    ∃ i : Fin 12, CandidateClosedSector i v := by
  by_cases hy : 0 ≤ v.2
  · exact candidateClosedSector_cover_upper v hy
  · obtain ⟨i, hi⟩ := candidateClosedSector_cover_upper (-v)
      (by dsimp only [Prod.snd_neg]; linarith)
    exact ⟨i + 6, by simpa only [neg_neg] using hi.neg⟩

end PiIrrationality
