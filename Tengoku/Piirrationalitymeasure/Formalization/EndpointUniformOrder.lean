import Tengoku.Piirrationalitymeasure.Formalization.SavingCircle
import Tengoku.Piirrationalitymeasure.Formalization.EndpointSectorOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! One common neighborhood preserves base separation and the order on each open cone. -/

namespace PiIrrationality

open Filter Set
open scoped Topology

abbrev CandidateEndpointLabel := Σ T : SavingEndpointType, Fin (candidateEndpointSize T)

def candidateEndpointLabelIndex (p : CandidateEndpointLabel) : ℤ :=
  (p.2.val : ℤ) + candidateEndpointStart p.1

noncomputable def candidateEndpointPosition (z : ℝ × ℝ) (p : CandidateEndpointLabel) : ℝ :=
  savingEndpoint 1857 3714 5570 z p.1 (candidateEndpointLabelIndex p)

theorem candidateEndpointLabelIndex_mem (p : CandidateEndpointLabel) :
    candidateEndpointLabelIndex p ∈ candidateEndpointIndices p.1 := by
  rw [mem_candidateEndpointIndices]
  dsimp [candidateEndpointLabelIndex]
  have h := p.2.isLt
  omega

theorem continuous_candidateEndpointPosition (p : CandidateEndpointLabel) :
    Continuous (fun z : ℝ × ℝ => candidateEndpointPosition z p) := by
  rcases p with ⟨T, n⟩
  cases T <;> dsimp [candidateEndpointPosition, savingEndpoint, savingEndpointShift,
    savingEndpointSlope] <;> fun_prop

theorem candidateEndpointPosition_eq_base_add (z : ℝ × ℝ) (p : CandidateEndpointLabel) :
    candidateEndpointPosition z p = candidateEndpointPosition 0 p +
      savingEndpointVelocity 1857 3714 5570 z p.1 := by
  simpa only [one_smul, one_mul, candidateEndpointPosition] using
    savingEndpoint_eq_base_add_velocity 1857 3714 5570 z p.1 (candidateEndpointLabelIndex p) 1

theorem candidateEndpointPosition_injective_type (T : SavingEndpointType) (z : ℝ × ℝ) :
    Function.Injective (fun n : Fin (candidateEndpointSize T) =>
      candidateEndpointPosition z ⟨T, n⟩) := by
  intro n m h
  dsimp only [candidateEndpointPosition, savingEndpoint, candidateEndpointLabelIndex] at h
  have hd : savingEndpointSlope 1857 3714 5570 T ≠ 0 :=
    (candidateEndpointSlope_pos T).ne'
  have he := sub_left_inj.mp ((div_left_inj' hd).mp h)
  have he' : (n.val : ℤ) + candidateEndpointStart T =
      (m.val : ℤ) + candidateEndpointStart T := by exact_mod_cast he
  apply Fin.ext
  exact_mod_cast add_right_cancel he'

theorem candidateEndpointLabel_eq_of_type_base {p q : CandidateEndpointLabel}
    (hT : p.1 = q.1) (hbase : candidateEndpointPosition 0 p = candidateEndpointPosition 0 q) :
    p = q := by
  rcases p with ⟨T, n⟩
  rcases q with ⟨S, m⟩
  dsimp only at hT
  subst S
  have hn := candidateEndpointPosition_injective_type T 0 hbase
  subst m
  rfl

theorem norm_le_parameterNormOne (z : ℝ × ℝ) : ‖z‖ ≤ parameterNormOne z := by
  rw [Prod.norm_def]
  simp only [Real.norm_eq_abs, parameterNormOne]
  exact max_le (le_add_of_nonneg_right (abs_nonneg _))
    (le_add_of_nonneg_left (abs_nonneg _))

theorem candidateEndpoint_base_order_eventually :
    ∀ᶠ z : ℝ × ℝ in 𝓝 0, ∀ p q : CandidateEndpointLabel,
      candidateEndpointPosition 0 p < candidateEndpointPosition 0 q →
        candidateEndpointPosition z p < candidateEndpointPosition z q := by
  apply eventually_all.mpr
  intro p
  apply eventually_all.mpr
  intro q
  by_cases hpq : candidateEndpointPosition 0 p < candidateEndpointPosition 0 q
  · filter_upwards [(continuous_candidateEndpointPosition p).continuousAt.eventually_lt
      (continuous_candidateEndpointPosition q).continuousAt hpq] with z hz
    exact fun _ => hz
  · exact Eventually.of_forall fun _ h => (hpq h).elim

theorem candidateEndpoint_uniform_separation :
    ∃ rho : ℝ, 0 < rho ∧ ∀ z : ℝ × ℝ, parameterNormOne z < rho →
      (∀ (T : SavingEndpointType) (j : ℤ),
        savingEndpoint 1857 3714 5570 z T j ∈
          Ioo (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1) ↔
            j ∈ candidateEndpointIndices T) ∧
      (∀ p q : CandidateEndpointLabel,
        candidateEndpointPosition 0 p < candidateEndpointPosition 0 q →
          candidateEndpointPosition z p < candidateEndpointPosition z q) := by
  obtain ⟨delta, hdelta, horder⟩ := Metric.eventually_nhds_iff.mp
    candidateEndpoint_base_order_eventually
  refine ⟨min (1 / 100) delta, lt_min (by norm_num) hdelta, ?_⟩
  intro z hz
  have hzcut : parameterNormOne z ≤ 1 / 100 :=
    (lt_of_lt_of_le hz (min_le_left _ _)).le
  have hzdelta : dist z 0 < delta := by
    rw [dist_zero_right]
    exact lt_of_le_of_lt (norm_le_parameterNormOne z)
      (lt_of_lt_of_le hz (min_le_right _ _))
  exact ⟨fun T j => savingEndpoint_candidate_period_enumeration T j hzcut, horder hzdelta⟩

def CandidateEndpointSectorOrder (i : Fin 12) (p q : CandidateEndpointLabel) : Prop :=
  candidateEndpointPosition 0 p < candidateEndpointPosition 0 q ∨
    (candidateEndpointPosition 0 p = candidateEndpointPosition 0 q ∧
      savingEndpointVelocity 1857 3714 5570
          ((candidateSectorDirection i).1, (candidateSectorDirection i).2) p.1 <
        savingEndpointVelocity 1857 3714 5570
          ((candidateSectorDirection i).1, (candidateSectorDirection i).2) q.1)

theorem candidateEndpointSectorOrder_trichotomy (i : Fin 12) (p q : CandidateEndpointLabel) :
    CandidateEndpointSectorOrder i p q ∨ p = q ∨ CandidateEndpointSectorOrder i q p := by
  rcases lt_trichotomy (candidateEndpointPosition 0 p) (candidateEndpointPosition 0 q)
    with hlo | heq | hgt
  · exact Or.inl (Or.inl hlo)
  · rcases lt_trichotomy
        (savingEndpointVelocity 1857 3714 5570
          ((candidateSectorDirection i).1, (candidateSectorDirection i).2) p.1)
        (savingEndpointVelocity 1857 3714 5570
          ((candidateSectorDirection i).1, (candidateSectorDirection i).2) q.1)
        with hvlo | hveq | hvgt
    · exact Or.inl (Or.inr ⟨heq, hvlo⟩)
    · rw [← candidateEndpointVelocity_ratCast, ← candidateEndpointVelocity_ratCast] at hveq
      have hT := (candidateSectorDirection_velocities_distinct i p.1 q.1).mp
        (by exact_mod_cast hveq)
      exact Or.inr (Or.inl (candidateEndpointLabel_eq_of_type_base hT heq))
    · exact Or.inr (Or.inr (Or.inr ⟨heq.symm, hvgt⟩))
  · exact Or.inr (Or.inr (Or.inl hgt))

theorem candidateEndpoint_uniform_sector_order :
    ∃ rho : ℝ, 0 < rho ∧ ∀ (i : Fin 12) (z : ℝ × ℝ),
      CandidateOpenSector i z → parameterNormOne z < rho →
      (∀ (T : SavingEndpointType) (j : ℤ),
        savingEndpoint 1857 3714 5570 z T j ∈
          Ioo (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1) ↔
            j ∈ candidateEndpointIndices T) ∧
      (∀ p q : CandidateEndpointLabel,
        candidateEndpointPosition z p < candidateEndpointPosition z q ↔
          CandidateEndpointSectorOrder i p q) := by
  obtain ⟨rho, hrho, hsep⟩ := candidateEndpoint_uniform_separation
  refine ⟨rho, hrho, ?_⟩
  intro i z hsector hz
  obtain ⟨hcut, hbase⟩ := hsep z hz
  refine ⟨hcut, ?_⟩
  have hv := candidateOpenSector_velocity_order hsector
  intro p q
  constructor
  · intro h
    rcases lt_trichotomy (candidateEndpointPosition 0 p) (candidateEndpointPosition 0 q)
      with hlo | heq | hgt
    · exact Or.inl hlo
    · refine Or.inr ⟨heq, (hv p.1 q.1).mp ?_⟩
      rw [candidateEndpointPosition_eq_base_add z p,
        candidateEndpointPosition_eq_base_add z q] at h
      linarith
    · exact (lt_asymm h (hbase q p hgt)).elim
  · rintro (hlo | ⟨heq, hvel⟩)
    · exact hbase p q hlo
    · have hvel' := (hv p.1 q.1).mpr hvel
      rw [candidateEndpointPosition_eq_base_add z p, candidateEndpointPosition_eq_base_add z q]
      linarith

theorem candidateEndpoint_uniform_fan :
    ∃ rho : ℝ, 0 < rho ∧ ∀ (i : Fin 12) (z : ℝ × ℝ),
      CandidateOpenSector i z → parameterNormOne z < rho →
      (∀ (T : SavingEndpointType) (j : ℤ),
        savingEndpoint 1857 3714 5570 z T j ∈
          Ioo (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1) ↔
            j ∈ candidateEndpointIndices T) ∧
      (∀ p q : CandidateEndpointLabel,
        candidateEndpointPosition z p < candidateEndpointPosition z q ↔
          CandidateEndpointSectorOrder i p q) ∧
      Function.Injective (candidateEndpointPosition z) := by
  obtain ⟨rho, hrho, hfan⟩ := candidateEndpoint_uniform_sector_order
  refine ⟨rho, hrho, ?_⟩
  intro i z hsector hz
  obtain ⟨hcut, horder⟩ := hfan i z hsector hz
  refine ⟨hcut, horder, ?_⟩
  intro p q hpq
  rcases candidateEndpointSectorOrder_trichotomy i p q with hlo | heq | hgt
  · have h := (horder p q).mpr hlo
    rw [hpq] at h
    exact (lt_irrefl _ h).elim
  · exact heq
  · have h := (horder q p).mpr hgt
    rw [hpq] at h
    exact (lt_irrefl _ h).elim

end PiIrrationality
