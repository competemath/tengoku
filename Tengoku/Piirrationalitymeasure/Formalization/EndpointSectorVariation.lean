import Tengoku.Piirrationalitymeasure.Formalization.EndpointSectorGeometry
import Tengoku.Piirrationalitymeasure.Formalization.EndpointSectorForms
import Tengoku.Piirrationalitymeasure.Formalization.EndpointUniformOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The sector table defines a continuous homogeneous function with a uniform negative bound. -/

namespace PiIrrationality

open Set

/--
@isnad1 id=iff.0h2v.s6.369a7d442898 from=translated src=- shape=0717e00a vocab=b253acf2
-/
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

/--
@isnad1 id=isclosed.0h1v.s5.dd81356c4422 from=translated src=- shape=c925d561 vocab=a5c55f45
-/
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
/--
@isnad1 id=eq.2h3v.s5.9f2d0c3eac50 from=translated src=- shape=47a165e8 vocab=9f43526f
-/
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

/--
@isnad1 id=eq.1h2v.s4.63b2c723cf35 from=translated src=- shape=a02e4309 vocab=7c38a052
-/
theorem candidateSectorVariation_eq_form {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateClosedSector i v) :
    candidateSectorVariation v = candidateSectorLinearForm i v :=
  candidateSectorLinearForm_eq_on_overlap _ i v
    (Classical.choose_spec (candidateClosedSector_cover v)) hv

/--
@isnad1 id=continuo.0h0v.s4.55bbf936c388 from=translated src=- shape=8e22ceaf vocab=fb11a04a
-/
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

/--
@isnad1 id=candidat.2h3v.s5.3a60c494e56e from=translated src=- shape=d864e747 vocab=217d89c7
-/
theorem CandidateClosedSector.smul {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateClosedSector i v) {s : ℝ} (hs : 0 ≤ s) :
    CandidateClosedSector i (s • v) := by
  rcases hv with ⟨u, t, hu, ht, rfl⟩
  exact ⟨s * u, s * t, mul_nonneg hs hu, mul_nonneg hs ht,
    by rw [smul_add, smul_smul, smul_smul]⟩

/--
@isnad1 id=eq.1h2v.s5.064c47fd23f7 from=translated src=- shape=f4c7e766 vocab=cb796787
-/
theorem candidateSectorVariation_smul (v : ℝ × ℝ) {s : ℝ} (hs : 0 ≤ s) :
    candidateSectorVariation (s • v) = s * candidateSectorVariation v := by
  obtain ⟨i, hi⟩ := candidateClosedSector_cover v
  rw [candidateSectorVariation_eq_form (hi.smul hs), candidateSectorVariation_eq_form hi]
  dsimp [candidateSectorLinearForm]
  ring

/--
@isnad1 id=le.0h1v.s5.1e6739c81357 from=translated src=- shape=39af9f31 vocab=8c46aaaf
-/
theorem candidateSectorVariation_bound (v : ℝ × ℝ) :
    candidateSectorVariation v ≤ -(557 : ℝ) / 4139253 * parameterNormOne v := by
  obtain ⟨i, hi⟩ := candidateClosedSector_cover v
  rw [candidateSectorVariation_eq_form hi]
  exact candidateSectorLinearForm_bound hi

/--
@isnad1 id=lt.1h1v.s5.d67bc988e28a from=translated src=- shape=4d8808da vocab=1b03b57f
-/
theorem candidateSectorVariation_neg {v : ℝ × ℝ} (hv : v ≠ 0) :
    candidateSectorVariation v < 0 := by
  have hn : 0 < parameterNormOne v :=
    lt_of_lt_of_le (norm_pos_iff.mpr hv) (norm_le_parameterNormOne v)
  exact (candidateSectorVariation_bound v).trans_lt
    (mul_neg_of_neg_of_pos (by norm_num) hn)

end PiIrrationality
