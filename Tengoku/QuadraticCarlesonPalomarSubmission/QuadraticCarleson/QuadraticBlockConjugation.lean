import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceySparseDilation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conjugation of finite quadratic blocks

Changing the sign of a nonzero modulation leaves its selected spatial scales
unchanged. Since the dyadic cutoff is real, conjugating the input therefore
turns the negative-modulation block exactly into the conjugate of the
positive-modulation block.
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace QuadraticCarleson.QuadraticBlockConjugation

set_option autoImplicit false

noncomputable section

/-- The paper's selected spatial scales depend only on absolute modulation.
@isnad1 id=eq.1h2v.s4.f03e020ae3ee from=translated src=- shape=5d55e21d vocab=a1ba862c
-/
theorem oscillatoryScaleIndex_neg (lam : ℝ) (hlam : lam ≠ 0) (r : ℕ) :
    oscillatoryScaleIndex (-lam) r (neg_ne_zero.mpr hlam) =
      oscillatoryScaleIndex lam r hlam := by
  apply oscillatoryScaleIndex_unique lam r hlam
  simpa only [OscillatoryScaleSpec, abs_neg] using
    oscillatoryScaleIndex_spec (-lam) r (neg_ne_zero.mpr hlam)

/--
@isnad1 id=eq.0h4v.s5.2fd7bf530221 from=translated src=- shape=d055286c vocab=2f447564
-/
theorem lowOscillatoryKernel_neg_eq_conj
    (lam : ℝ) (B : ℕ) (J : ℕ → ℤ) (t : ℝ) :
    lowOscillatoryKernel (-lam) B J t = conj (lowOscillatoryKernel lam B J t) := by
  simp only [lowOscillatoryKernel, map_sum, map_mul, Complex.conj_ofReal,
    ← phase_neg_eq_conj, neg_mul]

/-- Exact conjugation for a finite block, under the total integral convention.
@isnad1 id=eq.0h5v.s6.c9f06b39e7c4 from=translated src=- shape=57085d47 vocab=48415044
-/
theorem finiteQuadraticDyadicBlock_neg_eq_conj
    (lam : ℝ) (j : ℤ) (B : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    finiteQuadraticDyadicBlock (-lam) j B f x =
      conj (finiteQuadraticDyadicBlock lam j B (fun y ↦ conj (f y)) x) := by
  unfold finiteQuadraticDyadicBlock
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  simp [lowOscillatoryKernel_neg_eq_conj]

/-- The actual paper block changes modulation sign by conjugating the input.
@isnad1 id=eq.1h4v.s6.bc9d8302e81b from=translated src=- shape=489c9639 vocab=50c100f5
-/
theorem paperLowDyadicOperator_neg_eq_conj
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    paperLowDyadicOperator (-lam) (neg_ne_zero.mpr hlam) B f x =
      conj (paperLowDyadicOperator lam hlam B (L0Infinity.conjugate f) x) := by
  rw [paperLowDyadicOperator_eq_finiteQuadraticDyadicBlock,
    paperLowDyadicOperator_eq_finiteQuadraticDyadicBlock,
    oscillatoryScaleIndex_neg, finiteQuadraticDyadicBlock_neg_eq_conj]
  rfl

/--
@isnad1 id=eq.1h4v.s5.c1780684398d from=translated src=- shape=4d96ca90 vocab=474a9215
-/
theorem norm_paperLowDyadicOperator_neg
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖paperLowDyadicOperator (-lam) (neg_ne_zero.mpr hlam) B f x‖ =
      ‖paperLowDyadicOperator lam hlam B (L0Infinity.conjugate f) x‖ := by
  rw [paperLowDyadicOperator_neg_eq_conj, Complex.norm_conj]

/--
@isnad1 id=eq.1h4v.s6.c5f75f7a190d from=translated src=- shape=bea8703e vocab=9b8786a5
-/
theorem enorm_paperLowDyadicOperator_neg
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖paperLowDyadicOperator (-lam) (neg_ne_zero.mpr hlam) B f x‖ₑ =
      ‖paperLowDyadicOperator lam hlam B (L0Infinity.conjugate f) x‖ₑ := by
  simpa only [ofReal_norm] using
    congrArg ENNReal.ofReal (norm_paperLowDyadicOperator_neg lam hlam B f x)

end
end QuadraticCarleson.QuadraticBlockConjugation
