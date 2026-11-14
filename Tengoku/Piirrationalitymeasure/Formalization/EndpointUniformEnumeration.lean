import Tengoku.Piirrationalitymeasure.Formalization.SavingOrderedPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! One endpoint enumeration per sector works throughout a common neighborhood. -/

set_option maxRecDepth 100000

namespace PiIrrationality

theorem candidateOpenSector_small_point (i : Fin 12) {rho : ℝ} (hrho : 0 < rho) :
    ∃ z : ℝ × ℝ, CandidateOpenSector i z ∧ parameterNormOne z < rho := by
  let d := candidateSectorRayReal i + candidateSectorRayReal (candidateSectorNext i)
  let t := rho / (2 * (parameterNormOne d + 1))
  have hden : 0 < 2 * (parameterNormOne d + 1) := by
    have hn := parameterNormOne_nonneg d
    positivity
  have ht : 0 < t := div_pos hrho hden
  have htprod : t * (2 * (parameterNormOne d + 1)) = rho :=
    div_mul_cancel₀ rho hden.ne'
  refine ⟨t • d, ⟨t, t, ht, ht, by dsimp [d]; rw [smul_add]⟩, ?_⟩
  rw [parameterNormOne_smul, abs_of_pos ht]
  nlinarith only [htprod, ht, hrho]

theorem candidateEndpoint_uniform_enumeration :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 / 100 ∧ ∀ i : Fin 12,
      ∃ (e : CandidateEndpointEnumeration) (w : ℝ × ℝ),
        CandidateOpenSector i w ∧ parameterNormOne w < rho ∧ CandidateOrderedEndpoints e w ∧
        ∀ z : ℝ × ℝ, CandidateOpenSector i z → parameterNormOne z < rho →
          CandidateOrderedEndpoints e z := by
  obtain ⟨r, hr, hfan⟩ := candidateEndpoint_uniform_fan
  let rho : ℝ := min r (1 / 100)
  have hrho : 0 < rho := lt_min hr (by norm_num)
  refine ⟨rho, hrho, min_le_right _ _, ?_⟩
  intro i
  obtain ⟨w, hwi, hwn⟩ := candidateOpenSector_small_point i hrho
  have hwr : parameterNormOne w < r := lt_of_lt_of_le hwn (min_le_left _ _)
  obtain ⟨_, hworder, hwinj⟩ := hfan i w hwi hwr
  obtain ⟨e, he⟩ := exists_strictMono_enumeration (candidateEndpointPosition w) hwinj
  have hall : ∀ z : ℝ × ℝ, CandidateOpenSector i z → parameterNormOne z < rho →
      CandidateOrderedEndpoints e z := by
    intro z hzi hzn
    obtain ⟨hzcut, hzorder, _⟩ := hfan i z hzi (lt_of_lt_of_le hzn (min_le_left _ _))
    constructor
    · intro j k hjk
      exact (hzorder (e j) (e k)).mpr ((hworder (e j) (e k)).mp (he hjk))
    · intro k
      exact (hzcut (e k).1 (candidateEndpointLabelIndex (e k))).mpr
        (candidateEndpointLabelIndex_mem (e k))
  exact ⟨e, w, hwi, hwn, hall w hwi hwn, hall⟩

end PiIrrationality
