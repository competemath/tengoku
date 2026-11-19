import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyQuadraticDirectPStopping
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyNativePositiveSuffixResolved
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyLowFullOddReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unconditional sparse bound for the high full-odd quadratic suffixes

The direct quadratic one-node theorem gives the positive-half suffix bound
with a factor three for the shifted grids. Reflection restores the full odd
kernel with a further factor two. All constants are independent of the lower
and upper high-scale cutoffs.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson.KrauseLaceyHighFullSuffixResolved

open KrauseLaceyFullDyadicSparseTransfer
open KrauseLaceyNativePositiveSuffixResolved
open KrauseLaceyQuadraticDirectPStopping
open KrauseLaceyCompactPairingStabilization KrauseLaceySharpSmoothAdapter
open KrauseLaceyFullDyadicReflection KrauseLaceyLowFullOddReduction

set_option autoImplicit false

noncomputable section

/-- Six times the checked one-node constant: three shifted grids and the two
spatial halves of the full odd kernel.-/
def highFullSuffixSparseConstant : ℝ := 6 * directQuadraticOneNodeConstant

/--
@isnad1 id=le.0h0v.s3.677d719e85bd from=translated src=- shape=ff3a10fc vocab=c97635a6
-/
theorem highFullSuffixSparseConstant_nonneg :
    0 ≤ highFullSuffixSparseConstant :=
  mul_nonneg (by norm_num) directQuadraticOneNodeConstant_nonneg

/-- The high positive suffix estimate has no remaining analytic premise.
@isnad1 id=hasnativ.0h0v.s4.4557b8aa0c59 from=translated src=- shape=998bb51b vocab=54c537d2
-/
theorem hasNativeUnitHighPositiveSuffixSparseBound_directQuadratic :
    HasNativeUnitHighPositiveSuffixSparseBound
      (3 * directQuadraticOneNodeConstant) :=
  hasNativeUnitHighPositiveSuffixSparseBound_of_oneNodePStoppingGoodPart
    hasOneNodePStoppingGoodPartPairingBound_directQuadratic

/-- Unconditional sparse domination of every finite unit-phase full-odd
suffix maximum whose initial dyadic scale is at least one.
@isnad1 id=hasspars.3h3v.s5.eec4663f7390 from=translated src=- shape=e50ad8ec vocab=e6ff8c2a
-/
theorem hasSparseOnePBound_highFullDyadicSuffixMax
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (j : ℤ) (hj : 1 ≤ j) (N : ℕ) :
    HasSparseOnePBound (highFullSuffixSparseConstant * holderConjugate p) p
      (finiteFullDyadicSuffixMaxOperator 1 j N) := by
  have hpositive :=
    hasNativeUnitHighPositiveSuffixSparseBound_directQuadratic.2 p hp hp2 j hj N
  have hC : 0 ≤ 3 * directQuadraticOneNodeConstant * holderConjugate p :=
    mul_nonneg (mul_nonneg (by norm_num) directQuadraticOneNodeConstant_nonneg)
      (holderConjugate_spec hp).symm.pos.le
  have hfull := hasSparseOnePBound_fullDyadicSuffixMax 1 j N hC hpositive
  convert hfull using 1 <;> unfold highFullSuffixSparseConstant <;> ring

/-- The sparse norm has the same uniform high-scale bound.
@isnad1 id=le.3h3v.s6.9489dc722488 from=translated src=- shape=bb6c5076 vocab=f59db0a6
-/
theorem sparseOnePNorm_highFullDyadicSuffixMax_le
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (j : ℤ) (hj : 1 ≤ j) (N : ℕ) :
    sparseOnePNorm p (finiteFullDyadicSuffixMaxOperator 1 j N) ≤
      highFullSuffixSparseConstant * holderConjugate p :=
  sparseOnePNorm_le_of_bound
    (mul_nonneg highFullSuffixSparseConstant_nonneg (holderConjugate_spec hp).symm.pos.le)
    (hasSparseOnePBound_highFullDyadicSuffixMax hp hp2 j hj N)

/--
@isnad1 id=eq.0h3v.s4.0269590b0c45 from=translated src=- shape=84d6861c vocab=de8dd729
-/
@[simp] theorem absoluteValue_finiteFullDyadicSuffixMaxOperator
    (lam : ℝ) (j : ℤ) (N : ℕ) :
    absoluteValueOperator (finiteFullDyadicSuffixMaxOperator lam j N) =
      finiteFullDyadicSuffixMaxOperator lam j N := by
  funext f x
  simp [absoluteValueOperator, finiteFullDyadicSuffixMaxOperator]

/-- Compact-support stabilization passes the uniform high-suffix estimate
to every moving lower cutoff, with no further constant loss.
@isnad1 id=hasspars.3h2v.s5.fb85672c05ac from=translated src=- shape=301a1287 vocab=f8b7ade4
-/
theorem hasSparseOnePBound_highDyadicSmoothHighPassMax
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (j : ℤ) (hj : 1 ≤ j) :
    HasSparseOnePBound (highFullSuffixSparseConstant * holderConjugate p) p
      (dyadicSmoothHighPassMaxOperator 1 j) :=
  hasSparseOnePBound_dyadicSmoothHighPassMax_of_uniform_finiteSuffixMax 1 j
    (fun N ↦ hasSparseOnePBound_highFullDyadicSuffixMax hp hp2 j hj N)

/-- The countable high-pass maximum retains subadditivity in extended norm.
@isnad1 id=le.0h5v.s5.717df1afb36d from=translated src=- shape=f3923914 vocab=02fe6a72
-/
theorem dyadicSmoothHighPassMaxEnorm_add_le
    (lam : ℝ) (j : ℤ) (f g : L0Infinity) (x : ℝ) :
    dyadicSmoothHighPassMaxEnorm lam j (L0Infinity.add f g) x ≤
      dyadicSmoothHighPassMaxEnorm lam j f x +
        dyadicSmoothHighPassMaxEnorm lam j g x := by
  unfold dyadicSmoothHighPassMaxEnorm
  apply iSup_le
  intro m
  rw [smoothQuadraticHighPass_add lam (zpow_pos (by norm_num) _)]
  exact (enorm_add_le _ _).trans (add_le_add
    (le_iSup (fun n : ℕ ↦
      ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (n : ℤ) - 3)) f x‖ₑ) m)
    (le_iSup (fun n : ℕ ↦
      ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (n : ℤ) - 3)) g x‖ₑ) m))

/-- Scalar homogeneity passes exactly through the countable supremum.
@isnad1 id=eq.0h5v.s6.b96a7b9b9ce5 from=translated src=- shape=e9c145a4 vocab=57d558cb
-/
theorem dyadicSmoothHighPassMaxEnorm_smul
    (lam : ℝ) (j : ℤ) (c : ℂ) (f : L0Infinity) (x : ℝ) :
    dyadicSmoothHighPassMaxEnorm lam j (L0Infinity.smul c f) x =
      ‖c‖ₑ * dyadicSmoothHighPassMaxEnorm lam j f x := by
  unfold dyadicSmoothHighPassMaxEnorm
  have hterm (m : ℕ) :
      ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (m : ℤ) - 3))
        (L0Infinity.smul c f) x‖ₑ =
      ‖c‖ₑ * ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (m : ℤ) - 3)) f x‖ₑ := by
    rw [smoothQuadraticHighPass_smul lam (zpow_pos (by norm_num) _) c f x, enorm_mul]
  simp_rw [hterm]
  exact (ENNReal.mul_iSup _ _).symm

/-- The genuine dyadic smooth high-pass maximum satisfies the sublinearity
interface of the finite-family sparse maximal theorem.
@isnad1 id=issublin.0h2v.s3.f6c74452f484 from=translated src=- shape=c57da3d9 vocab=904d8b73
-/
theorem isSublinear_dyadicSmoothHighPassMaxOperator (lam : ℝ) (j : ℤ) :
    IsSublinear (dyadicSmoothHighPassMaxOperator lam j) := by
  constructor
  · intro f g x
    apply (ENNReal.ofReal_le_ofReal_iff (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    simp only [ofReal_norm, enorm_dyadicSmoothHighPassMaxOperator]
    exact dyadicSmoothHighPassMaxEnorm_add_le lam j f g x
  · intro c f x
    apply (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [ENNReal.ofReal_mul (norm_nonneg _)]
    simp only [ofReal_norm, enorm_dyadicSmoothHighPassMaxOperator]
    exact dyadicSmoothHighPassMaxEnorm_smul lam j c f x

/-- Full dyadic convolution is additive on the paper's test space.
@isnad1 id=eq.0h5v.s5.962cb2b63674 from=translated src=- shape=d3338419 vocab=4eb7b676
-/
theorem fullDyadicConvolution_add
    (lam : ℝ) (j : ℤ) (f g : L0Infinity) (x : ℝ) :
    fullDyadicConvolution lam j (L0Infinity.add f g) x =
      fullDyadicConvolution lam j f x + fullDyadicConvolution lam j g x := by
  have hi (h : L0Infinity) : Integrable (fun y ↦
      annularQuadraticKernel (fun t ↦ (dyadicPsi j t : ℂ)) lam (x - y) * h y) :=
    integrable_convolution_row_of_memLp
      (continuous_fullDyadicQuadraticKernel lam j)
      (hasCompactSupport_fullDyadicQuadraticKernel lam j) (memLp_two_L0Infinity h) x
  unfold fullDyadicConvolution
  rw [← integral_add (hi f) (hi g)]
  apply integral_congr_ae
  filter_upwards with y
  change _ * (f y + g y) = _
  ring

/-- Scalar multiplication commutes with a full dyadic convolution.
@isnad1 id=eq.0h5v.s5.9422860666d9 from=translated src=- shape=73d4049d vocab=6ed3fbbd
-/
theorem fullDyadicConvolution_smul
    (lam : ℝ) (j : ℤ) (c : ℂ) (f : L0Infinity) (x : ℝ) :
    fullDyadicConvolution lam j (L0Infinity.smul c f) x =
      c * fullDyadicConvolution lam j f x := by
  unfold fullDyadicConvolution
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  change _ * (c * f y) = _
  ring

/--
@isnad1 id=eq.0h7v.s5.a64ef421c149 from=translated src=- shape=1c7c75bd vocab=d6ea232e
-/
theorem finiteFullDyadicSuffix_add
    (lam : ℝ) (j : ℤ) (N m : ℕ) (f g : L0Infinity) (x : ℝ) :
    finiteFullDyadicSuffix lam j N m (L0Infinity.add f g) x =
      finiteFullDyadicSuffix lam j N m f x + finiteFullDyadicSuffix lam j N m g x := by
  simp only [finiteFullDyadicSuffix, finiteFullDyadicTail,
    fullDyadicConvolution_add, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h7v.s5.e4c1d59773c4 from=translated src=- shape=ec5c8821 vocab=6c36b12c
-/
theorem finiteFullDyadicSuffix_smul
    (lam : ℝ) (j : ℤ) (N m : ℕ) (c : ℂ) (f : L0Infinity) (x : ℝ) :
    finiteFullDyadicSuffix lam j N m (L0Infinity.smul c f) x =
      c * finiteFullDyadicSuffix lam j N m f x := by
  simp only [finiteFullDyadicSuffix, finiteFullDyadicTail,
    fullDyadicConvolution_smul, Finset.mul_sum]

/-- Taking the finite maximum preserves subadditivity of full suffixes.
@isnad1 id=le.0h6v.s5.176e23c3a473 from=translated src=- shape=b3149bb0 vocab=afbe8006
-/
theorem finiteFullDyadicSuffixMaxNNNorm_add_le
    (lam : ℝ) (j : ℤ) (N : ℕ) (f g : L0Infinity) (x : ℝ) :
    finiteFullDyadicSuffixMaxNNNorm lam j N (L0Infinity.add f g) x ≤
      finiteFullDyadicSuffixMaxNNNorm lam j N f x +
        finiteFullDyadicSuffixMaxNNNorm lam j N g x := by
  unfold finiteFullDyadicSuffixMaxNNNorm
  apply Finset.sup_le
  intro m hm
  rw [finiteFullDyadicSuffix_add]
  exact (nnnorm_add_le _ _).trans (add_le_add
    (Finset.le_sup (f := fun r ↦ ‖finiteFullDyadicSuffix lam j N r f x‖₊) hm)
    (Finset.le_sup (f := fun r ↦ ‖finiteFullDyadicSuffix lam j N r g x‖₊) hm))

/-- The finite full-suffix maximum is exactly homogeneous.
@isnad1 id=eq.0h6v.s5.01091d580a2f from=translated src=- shape=c80f4adb vocab=5013dcdb
-/
theorem finiteFullDyadicSuffixMaxNNNorm_smul
    (lam : ℝ) (j : ℤ) (N : ℕ) (c : ℂ) (f : L0Infinity) (x : ℝ) :
    finiteFullDyadicSuffixMaxNNNorm lam j N (L0Infinity.smul c f) x =
      ‖c‖₊ * finiteFullDyadicSuffixMaxNNNorm lam j N f x := by
  unfold finiteFullDyadicSuffixMaxNNNorm
  simp_rw [finiteFullDyadicSuffix_smul, nnnorm_mul]
  exact (NNReal.mul_finset_sup ‖c‖₊ _ _).symm

/--
@isnad1 id=eq.0h5v.s4.8e0d1db42ebc from=translated src=- shape=a11bc5ec vocab=81641c1c
-/
theorem norm_finiteFullDyadicSuffixMaxOperator
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖finiteFullDyadicSuffixMaxOperator lam j N f x‖ =
      (finiteFullDyadicSuffixMaxNNNorm lam j N f x : ℝ) := by
  simp [finiteFullDyadicSuffixMaxOperator]

/-- Sublinearity of the finite full-odd maximum needed for finite sparse
families; no restriction on scales or modulation is required.
@isnad1 id=issublin.0h3v.s3.1f473c4f40c8 from=translated src=- shape=27322421 vocab=acd18df2
-/
theorem isSublinear_finiteFullDyadicSuffixMaxOperator
    (lam : ℝ) (j : ℤ) (N : ℕ) :
    IsSublinear (finiteFullDyadicSuffixMaxOperator lam j N) := by
  constructor
  · intro f g x
    simp only [norm_finiteFullDyadicSuffixMaxOperator]
    exact_mod_cast finiteFullDyadicSuffixMaxNNNorm_add_le lam j N f g x
  · intro c f x
    simp only [norm_finiteFullDyadicSuffixMaxOperator]
    rw [finiteFullDyadicSuffixMaxNNNorm_smul]
    rfl

end
end QuadraticCarleson.KrauseLaceyHighFullSuffixResolved
