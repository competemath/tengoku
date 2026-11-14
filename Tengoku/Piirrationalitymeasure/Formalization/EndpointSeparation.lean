import Tengoku.Piirrationalitymeasure.Formalization.EndpointCardinality
import Tengoku.Piirrationalitymeasure.Formalization.SavingTranslationBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The exact minimum circular gap and explicit separation radius in (6.19). -/

namespace PiIrrationality

private theorem endpoint_difference_denominator (T S : SavingEndpointType) (j k : ℤ) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 13797510 ∧ ∃ z : ℤ,
      (candidateEndpointBaseRat T j - candidateEndpointBaseRat S k) * D = z := by
  cases T <;> cases S
  · refine ⟨1857, by norm_num, by norm_num, j - k, ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨3714, by norm_num, by norm_num, 2 * j - 1 - k, ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨10343490, by norm_num, by norm_num, 2785 * (2 * j - 1) - 1857 * k, ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨13797510, by norm_num, by norm_num,
      3715 * (2 * j - 1) - 1857 * (2 * k - 1), ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨3714, by norm_num, by norm_num, j - (2 * k - 1), ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨3714, by norm_num, by norm_num, j - k, ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨10343490, by norm_num, by norm_num, 2785 * j - 1857 * k, ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨13797510, by norm_num, by norm_num, 3715 * j - 1857 * (2 * k - 1), ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨10343490, by norm_num, by norm_num, 1857 * j - 2785 * (2 * k - 1), ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨10343490, by norm_num, by norm_num, 1857 * j - 2785 * k, ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨5570, by norm_num, by norm_num, j - k, ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨4138510, by norm_num, by norm_num, 743 * j - 557 * (2 * k - 1), ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨13797510, by norm_num, by norm_num,
      1857 * (2 * j - 1) - 3715 * (2 * k - 1), ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨13797510, by norm_num, by norm_num, 1857 * (2 * j - 1) - 3715 * k, ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨4138510, by norm_num, by norm_num, 557 * (2 * j - 1) - 743 * k, ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring
  · refine ⟨3715, by norm_num, by norm_num, j - k, ?_⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
    <;> ring

private theorem rational_gap_of_denominator {x : ℚ} {D : ℕ} (hD : 0 < D)
    (hDle : D ≤ 13797510) (hx : x ≠ 0) (hz : ∃ z : ℤ, x * D = z) :
    (1 : ℚ) / 13797510 ≤ |x| := by
  obtain ⟨z, hz⟩ := hz
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  have hDle' : (D : ℚ) ≤ 13797510 := by exact_mod_cast hDle
  have hzne : z ≠ 0 := by
    intro he
    rw [he, Int.cast_zero] at hz
    exact hx ((mul_eq_zero.mp hz).resolve_right hD'.ne')
  have hzabs : (1 : ℚ) ≤ |(z : ℚ)| := by
    have hzpos : (0 : ℤ) < |z| := abs_pos.mpr hzne
    exact_mod_cast (show (1 : ℤ) ≤ |z| by omega)
  rw [← hz, abs_mul, abs_of_pos hD'] at hzabs
  have hm := mul_le_mul_of_nonneg_left hDle' (abs_nonneg x)
  linarith

/--
@isnad1 id=le.1h5v.s6.b8c72844731d from=translated src=- shape=c5f8a240 vocab=d446a5ff
-/
theorem candidateEndpoint_integer_offset_gap (T S : SavingEndpointType) (j k m : ℤ)
    (hne : candidateEndpointBaseRat T j - candidateEndpointBaseRat S k ≠ (m : ℚ)) :
    (1 : ℚ) / 13797510 ≤
      |candidateEndpointBaseRat T j - candidateEndpointBaseRat S k - m| := by
  obtain ⟨D, hD, hDle, z, hz⟩ := endpoint_difference_denominator T S j k
  apply rational_gap_of_denominator hD hDle (sub_ne_zero.mpr hne)
  refine ⟨z - m * (D : ℤ), ?_⟩
  push_cast
  rw [sub_mul, hz]

def endpointCircularGap (x y : ℚ) : ℚ := min |x - y| (1 - |x - y|)

/--
@isnad1 id=le.3h2v.s5.f6e8731a0ed1 from=translated src=- shape=298dad32 vocab=7b315f86
-/
theorem candidateEndpoint_circular_gap_lower {x y : ℚ}
    (hx : x ∈ candidateDistinctEndpointBases) (hy : y ∈ candidateDistinctEndpointBases)
    (hne : x ≠ y) : (1 : ℚ) / 13797510 ≤ endpointCircularGap x y := by
  obtain ⟨T, j, hj, rfl⟩ := (mem_candidateDistinctEndpointBases x).mp hx
  obtain ⟨S, k, hk, rfl⟩ := (mem_candidateDistinctEndpointBases y).mp hy
  obtain ⟨hx0, hx1⟩ := (candidateEndpointBase_mem_Ico T j).mpr hj
  obtain ⟨hy0, hy1⟩ := (candidateEndpointBase_mem_Ico S k).mpr hk
  unfold endpointCircularGap
  apply le_min
  · simpa only [Int.cast_zero, sub_zero] using
      candidateEndpoint_integer_offset_gap T S j k 0 (sub_ne_zero.mpr hne)
  · have hd : |candidateEndpointBaseRat T j - candidateEndpointBaseRat S k| < 1 :=
      abs_lt.mpr ⟨by linarith, by linarith⟩
    by_cases hxy : candidateEndpointBaseRat S k ≤ candidateEndpointBaseRat T j
    · have h := candidateEndpoint_integer_offset_gap T S j k 1 (by norm_num; linarith)
      rw [Int.cast_one, abs_of_nonneg (sub_nonneg.mpr hxy),
        abs_of_neg (by linarith : candidateEndpointBaseRat T j -
          candidateEndpointBaseRat S k - 1 < 0)] at *
      linarith
    · have h := candidateEndpoint_integer_offset_gap T S j k (-1) (by norm_num; linarith)
      rw [Int.cast_neg, Int.cast_one] at h
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hxy))] at hd ⊢
      rw [abs_of_pos (by linarith : 0 < candidateEndpointBaseRat T j -
        candidateEndpointBaseRat S k - (-1))] at h
      linarith

/--
@isnad1 id=and.0h0v.s6.a02799bbfb6a from=translated src=- shape=e954162c vocab=0c6acc4e
-/
theorem candidateEndpoint_circular_gap_attained :
    candidateEndpointBaseRat .B 1856 ∈ candidateDistinctEndpointBases ∧
    candidateEndpointBaseRat .Q 1857 ∈ candidateDistinctEndpointBases ∧
    candidateEndpointBaseRat .B 1856 ≠ candidateEndpointBaseRat .Q 1857 ∧
    endpointCircularGap (candidateEndpointBaseRat .B 1856)
      (candidateEndpointBaseRat .Q 1857) = 1 / 13797510 := by
  refine ⟨(mem_candidateDistinctEndpointBases _).mpr ⟨.B, 1856, ?_, rfl⟩,
    (mem_candidateDistinctEndpointBases _).mpr ⟨.Q, 1857, ?_, rfl⟩, ?_, ?_⟩ <;>
    norm_num [mem_candidateEndpointIndices, candidateEndpointStart, candidateEndpointSize,
      candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat,
      endpointCircularGap]

/--
@isnad1 id=and.0h0v.s7.6a6f422655f9 from=translated src=- shape=1026a8e4 vocab=40c9b925
-/
theorem candidateEndpoint_separation_constants :
    max (1 / 1857 : ℚ) (max (1 / 3714) (2 / 3715)) = 1 / 1857 ∧
      2 * (1 / 1857 : ℚ) * (1 / 60000) < (1 / 13797510) / 4 := by
  norm_num

/--
@isnad1 id=le.0h3v.s6.0f43ae22003a from=translated src=- shape=0c41c222 vocab=6f34c821
-/
theorem candidateEndpoint_displacement_bound (T : SavingEndpointType) (j : ℤ)
    (z : ℝ × ℝ) :
    |savingEndpoint 1857 3714 5570 z T j - savingEndpoint 1857 3714 5570 0 T j| ≤
      parameterNormOne z / 1857 := by
  have h1 := abs_nonneg z.1
  have h2 := abs_nonneg z.2
  have hsum := abs_add_le z.1 (2 * z.2)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsum
  have he : savingEndpoint 1857 3714 5570 z T j -
      savingEndpoint 1857 3714 5570 0 T j =
      match T with
      | .A => -z.1 / 1857
      | .B => -z.2 / 3714
      | .C => 0
      | .Q => -(z.1 + 2 * z.2) / 3715 := by
    cases T <;> dsimp [savingEndpoint, savingEndpointSlope, savingEndpointShift] <;> ring
  rw [he]
  cases T <;> dsimp only
  · rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1857)]
    dsimp [parameterNormOne]
    linarith
  · rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3714)]
    dsimp [parameterNormOne]
    linarith
  · simp only [abs_zero, parameterNormOne]
    positivity
  · rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3715)]
    dsimp [parameterNormOne]
    linarith

/--
@isnad1 id=lt.2h6v.s8.832253aa4c33 from=translated src=- shape=63b5f2c6 vocab=e9c8d007
-/
theorem candidateEndpoint_explicit_separation (T S : SavingEndpointType) (j k m : ℤ)
    {z : ℝ × ℝ} (hz : parameterNormOne z < 1 / 60000)
    (hne : savingEndpoint 1857 3714 5570 0 T j -
      savingEndpoint 1857 3714 5570 0 S k ≠ (m : ℝ)) :
    (3 : ℝ) / (4 * 13797510) <
      |savingEndpoint 1857 3714 5570 z T j -
        savingEndpoint 1857 3714 5570 z S k - m| := by
  have hneRat : candidateEndpointBaseRat T j - candidateEndpointBaseRat S k ≠ (m : ℚ) := by
    intro he
    apply hne
    rw [← candidateEndpointBase_ratCast, ← candidateEndpointBase_ratCast]
    exact_mod_cast he
  have hgapRat := candidateEndpoint_integer_offset_gap T S j k m hneRat
  have hgap : (1 : ℝ) / 13797510 ≤
      |savingEndpoint 1857 3714 5570 0 T j -
        savingEndpoint 1857 3714 5570 0 S k - m| := by
    rw [← candidateEndpointBase_ratCast, ← candidateEndpointBase_ratCast]
    have hh : (((1 : ℚ) / 13797510 : ℚ) : ℝ) ≤
        ((|candidateEndpointBaseRat T j - candidateEndpointBaseRat S k - m| : ℚ) : ℝ) :=
      Rat.cast_le.mpr hgapRat
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_abs,
      Rat.cast_sub, Rat.cast_intCast] at hh
    exact hh
  have hT := candidateEndpoint_displacement_bound T j z
  have hS := candidateEndpoint_displacement_bound S k z
  have habs := abs_sub
    (savingEndpoint 1857 3714 5570 z T j - savingEndpoint 1857 3714 5570 0 T j)
    (savingEndpoint 1857 3714 5570 z S k - savingEndpoint 1857 3714 5570 0 S k)
  have htri := abs_sub
    (savingEndpoint 1857 3714 5570 z T j - savingEndpoint 1857 3714 5570 z S k - m)
    ((savingEndpoint 1857 3714 5570 z T j - savingEndpoint 1857 3714 5570 0 T j) -
      (savingEndpoint 1857 3714 5570 z S k - savingEndpoint 1857 3714 5570 0 S k))
  have he : (savingEndpoint 1857 3714 5570 z T j -
      savingEndpoint 1857 3714 5570 z S k - m) -
      ((savingEndpoint 1857 3714 5570 z T j - savingEndpoint 1857 3714 5570 0 T j) -
        (savingEndpoint 1857 3714 5570 z S k - savingEndpoint 1857 3714 5570 0 S k)) =
      savingEndpoint 1857 3714 5570 0 T j - savingEndpoint 1857 3714 5570 0 S k - m := by
    ring
  rw [he] at htri
  linarith

end PiIrrationality
