import Tengoku.Piirrationalitymeasure.Formalization.EndpointSectorGeometry
import Tengoku.Piirrationalitymeasure.Formalization.EndpointSectorForms
import Tengoku.Piirrationalitymeasure.Formalization.EndpointUniformOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The sector table defines a continuous homogeneous function with a uniform negative bound. -/

namespace PiIrrationality

open Set

theorem candidateClosedSector_iff_det (i : Fin 12) (v : ℝ × ℝ) :
    CandidateClosedSector i v ↔
      0 ≤ (candidateSectorRayReal i).1 * v.2 - (candidateSectorRayReal i).2 * v.1 ∧
      0 ≤ v.1 * (candidateSectorRayReal (candidateSectorNext i)).2 -
        v.2 * (candidateSectorRayReal (candidateSectorNext i)).1 := by
  constructor
  · rintro ⟨u, t, hu, ht, rfl⟩
    have hd : 0 ≤ (candidateSectorRayReal i).1 *
          (candidateSectorRayReal (candidateSectorNext i)).2 -
        (candidateSectorRayReal i).2 * (candidateSectorRayReal (candidateSectorNext i)).1 := by
      dsimp only [candidateSectorRayReal]
      exact_mod_cast (candidateSectorRay_det_pos i).le
    have hL := mul_nonneg ht hd
    have hR := mul_nonneg hu hd
    dsimp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    constructor <;> nlinarith only [hL, hR]
  · rintro ⟨hL, hR⟩
    exact candidateClosedSector_of_det i v hL hR

theorem isClosed_candidateClosedSector (i : Fin 12) :
    IsClosed {v : ℝ × ℝ | CandidateClosedSector i v} := by
  have heq : {v : ℝ × ℝ | CandidateClosedSector i v} =
      {v : ℝ × ℝ | 0 ≤ (candidateSectorRayReal i).1 * v.2 -
        (candidateSectorRayReal i).2 * v.1} ∩
      {v : ℝ × ℝ | 0 ≤ v.1 * (candidateSectorRayReal (candidateSectorNext i)).2 -
        v.2 * (candidateSectorRayReal (candidateSectorNext i)).1} := by
    ext v
    exact candidateClosedSector_iff_det i v
  rw [heq]
  exact (isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_le continuous_const (by fun_prop))

set_option maxHeartbeats 0 in
theorem candidateSectorLinearForm_eq_on_overlap (i j : Fin 12) (v : ℝ × ℝ)
    (hi : CandidateClosedSector i v) (hj : CandidateClosedSector j v) :
    candidateSectorLinearForm i v = candidateSectorLinearForm j v := by
  obtain ⟨hiL, hiR⟩ := (candidateClosedSector_iff_det i v).mp hi
  obtain ⟨hjL, hjR⟩ := (candidateClosedSector_iff_det j v).mp hj
  fin_cases i <;> fin_cases j <;>
    dsimp [candidateSectorRayReal, candidateSectorRay, candidateSectorNext,
      candidateSectorLinearForm, candidateSectorRow, sectorRows] at * <;>
    norm_num at * <;> linarith

noncomputable def candidateSectorVariation (v : ℝ × ℝ) : ℝ :=
  candidateSectorLinearForm (Classical.choose (candidateClosedSector_cover v)) v

theorem candidateSectorVariation_eq_form {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateClosedSector i v) :
    candidateSectorVariation v = candidateSectorLinearForm i v :=
  candidateSectorLinearForm_eq_on_overlap _ i v
    (Classical.choose_spec (candidateClosedSector_cover v)) hv

theorem continuous_candidateSectorVariation : Continuous candidateSectorVariation := by
  apply (locallyFinite_of_finite (fun i : Fin 12 =>
    {v : ℝ × ℝ | CandidateClosedSector i v})).continuous
  · ext v
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    exact candidateClosedSector_cover v
  · exact isClosed_candidateClosedSector
  · intro i
    have hc : Continuous (candidateSectorLinearForm i) := by
      unfold candidateSectorLinearForm
      fun_prop
    exact hc.continuousOn.congr (fun _ hv => candidateSectorVariation_eq_form hv)

theorem CandidateClosedSector.smul {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateClosedSector i v) {s : ℝ} (hs : 0 ≤ s) :
    CandidateClosedSector i (s • v) := by
  rcases hv with ⟨u, t, hu, ht, rfl⟩
  exact ⟨s * u, s * t, mul_nonneg hs hu, mul_nonneg hs ht,
    by rw [smul_add, smul_smul, smul_smul]⟩

theorem candidateSectorVariation_smul (v : ℝ × ℝ) {s : ℝ} (hs : 0 ≤ s) :
    candidateSectorVariation (s • v) = s * candidateSectorVariation v := by
  obtain ⟨i, hi⟩ := candidateClosedSector_cover v
  rw [candidateSectorVariation_eq_form (hi.smul hs), candidateSectorVariation_eq_form hi]
  dsimp [candidateSectorLinearForm]
  ring

theorem candidateSectorVariation_bound (v : ℝ × ℝ) :
    candidateSectorVariation v ≤ -(557 : ℝ) / 4139253 * parameterNormOne v := by
  obtain ⟨i, hi⟩ := candidateClosedSector_cover v
  rw [candidateSectorVariation_eq_form hi]
  exact candidateSectorLinearForm_bound hi

theorem candidateSectorVariation_neg {v : ℝ × ℝ} (hv : v ≠ 0) :
    candidateSectorVariation v < 0 := by
  have hn : 0 < parameterNormOne v :=
    lt_of_lt_of_le (norm_pos_iff.mpr hv) (norm_le_parameterNormOne v)
  exact (candidateSectorVariation_bound v).trans_lt
    (mul_neg_of_neg_of_pos (by norm_num) hn)

end PiIrrationality
