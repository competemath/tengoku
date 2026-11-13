import Tengoku.Rankamplificationtotient.RankAmplification.Scales

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Saddle-point algebra Elementary identities for the fixed-rank cutoff and the moving-rank optimization in Proposition 10.27. -/

namespace RankAmplification

noncomputable section

/-- The fixed-rank cutoff `T_J = G / √J`.-/
def fixedRankT (J : ℕ) (x : ℝ) : ℝ := scaleG x / Real.sqrt J

theorem fixedRankT_pos {J : ℕ} {x : ℝ} (hJ : 0 < J) (hG : 0 < scaleG x) :
    0 < fixedRankT J x :=
  div_pos hG (Real.sqrt_pos.2 (by exact_mod_cast hJ))

theorem sqrt_mul_fixedRankT {J : ℕ} {x : ℝ} (hJ : 0 < J) :
    Real.sqrt J * fixedRankT J x = scaleG x := by
  rw [fixedRankT]
  exact mul_div_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hJ)))

/-- The exact algebra behind `J T_J = √J G`.-/
theorem nat_mul_fixedRankT {J : ℕ} {x : ℝ} (hJ : 0 < J) :
    J * fixedRankT J x = Real.sqrt J * scaleG x := by
  have hsqrt : Real.sqrt (J : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hJ))
  have hsq : (Real.sqrt (J : ℝ)) ^ 2 = J := Real.sq_sqrt (by positivity)
  calc
    J * fixedRankT J x = (Real.sqrt (J : ℝ)) ^ 2 * fixedRankT J x :=
      congrArg (fun z : ℝ ↦ z * fixedRankT J x) hsq.symm
    _ = Real.sqrt J * scaleG x := by
      rw [fixedRankT]
      field_simp [hsqrt]

/-- The exponent supplied by the two competing branches in Proposition 10.27.-/
def movingSaddleExponent (c : ℝ) : ℝ := min c (1 / (4 * c))

/-- The transfer architecture cannot beat `1/2`.-/
theorem movingSaddleExponent_le_half {c : ℝ} (hc : 0 < c) :
    movingSaddleExponent c ≤ 1 / 2 := by
  unfold movingSaddleExponent
  by_cases h : c ≤ 1 / 2
  · exact (min_le_left _ _).trans h
  · have hhalf : 1 / 2 < c := lt_of_not_ge h
    have hinv : 1 / (4 * c) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * c) (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    exact (min_le_right _ _).trans hinv.le

/-- Equality in the moving saddle occurs only at `c=1/2`.-/
theorem movingSaddleExponent_eq_half_iff {c : ℝ} (hc : 0 < c) :
    movingSaddleExponent c = 1 / 2 ↔ c = 1 / 2 := by
  constructor
  · intro heq
    have hle : (1 / 2 : ℝ) ≤ movingSaddleExponent c := heq.ge
    have hcLower : (1 / 2 : ℝ) ≤ c := hle.trans (min_le_left _ _)
    have hinvLower : (1 / 2 : ℝ) ≤ 1 / (4 * c) := hle.trans (min_le_right _ _)
    have hcUpper : c ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * c)] at hinvLower
      nlinarith
    exact le_antisymm hcUpper hcLower
  · intro hcEq
    subst c
    norm_num [movingSaddleExponent]

theorem movingSaddleExponent_lt_half {c : ℝ} (hc : 0 < c) (hne : c ≠ 1 / 2) :
    movingSaddleExponent c < 1 / 2 :=
  lt_of_le_of_ne (movingSaddleExponent_le_half hc)
    (Ne.symm (fun h ↦ hne ((movingSaddleExponent_eq_half_iff hc).mp h.symm)))

end

end RankAmplification
