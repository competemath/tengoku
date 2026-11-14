import Tengoku.Piirrationalitymeasure.Formalization.EndpointSectorVariation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A direction-independent bound for the variation in Section 6.3. -/

namespace PiIrrationality

/--
@isnad1 id=and.0h1v.s5.a19623ef4aec from=translated src=- shape=133e3c97 vocab=ea40a4ca
-/
theorem candidateSectorRow_abs_coefficients : ∀ i : Fin 12,
    |(candidateSectorRow i).px| ≤ 1 ∧ |(candidateSectorRow i).py| ≤ 1 := by
  decide +kernel

/--
@isnad1 id=le.0h2v.s4.9a22a411e606 from=translated src=- shape=3d81211f vocab=62a50414
-/
theorem candidateSectorLinearForm_abs_le (i : Fin 12) (v : ℝ × ℝ) :
    |candidateSectorLinearForm i v| ≤ parameterNormOne v := by
  obtain ⟨hx, hy⟩ := candidateSectorRow_abs_coefficients i
  have hx' : |((candidateSectorRow i).px : ℝ)| ≤ 1 := by exact_mod_cast hx
  have hy' : |((candidateSectorRow i).py : ℝ)| ≤ 1 := by exact_mod_cast hy
  unfold candidateSectorLinearForm parameterNormOne
  calc
    _ ≤ |((candidateSectorRow i).px : ℝ) * v.1| +
        |((candidateSectorRow i).py : ℝ) * v.2| := abs_add_le _ _
    _ ≤ |v.1| + |v.2| := by
      simp only [abs_mul]
      exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) hx')
        (mul_le_of_le_one_left (abs_nonneg _) hy')

/--
@isnad1 id=le.0h1v.s3.3bd772cbc925 from=translated src=- shape=2c3b3e84 vocab=b3504e02
-/
theorem candidateSectorVariation_abs_le (v : ℝ × ℝ) :
    |candidateSectorVariation v| ≤ parameterNormOne v := by
  obtain ⟨i, hi⟩ := candidateClosedSector_cover v
  rw [candidateSectorVariation_eq_form hi]
  exact candidateSectorLinearForm_abs_le i v

end PiIrrationality
