import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.ContinuationPolynomialContour

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

noncomputable section
open MeasureTheory Set Filter Complex
namespace SevenEighths.Continuation

lemma shifted_height_two (t q : ℝ) :
    (3+|t|)^2≤2*(3+|q|)^2*(1+|t+q|^2) := by
  have ht : |t|≤|t+q|+|q| := by
    calc
      |t|=|(t+q)+(-q)| := by ring_nf
      _ ≤ |t+q|+|-q| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hq : 0≤|q| := abs_nonneg _
  have hu : 0≤|t+q| := abs_nonneg _
  have hb : (3+|t|)^2≤(3+|q|+|t+q|)^2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hs := sq_nonneg ((3+|q|)-|t+q|)
  have hm : 0≤((3+|q|)^2-1)*|t+q|^2 := mul_nonneg (by nlinarith) (sq_nonneg _)
  nlinarith

end SevenEighths.Continuation

end

end OAI
