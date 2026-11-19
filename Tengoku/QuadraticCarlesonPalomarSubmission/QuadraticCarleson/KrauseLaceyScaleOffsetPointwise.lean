import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceySparseDilation
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyFiniteRadiusSmoothSparse
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.HardyLittlewoodBoundaryControl

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arbitrary smooth radii versus adjacent dyadic radii

Rounding an arbitrary positive smooth radius upward to the next dyadic radius
costs at most `24` times the centered Hardy--Littlewood maximal function.  This
is a bound for the actual difference of the two smooth operators, obtained
from the two cutoff-boundary terms and the sharp annular rounding term.

The same single error bounds every finite maximum, with no cardinality loss.
The lower index of the comparison dyadic maximum is taken from the actual
radii, so a common real scale offset is not incorrectly treated as preserving
the original integer-dyadic lower index.  Pairing comparisons use `normInput`
on their right sides, avoiding cancellation of complex test functions.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal Topology ComplexConjugate

namespace QuadraticCarleson.KrauseLaceyScaleOffsetPointwise

open QuadraticHilbertMaximalMeasurable KrauseLaceySharpSmoothAdapter
open KrauseLaceySparseDilation KrauseLaceyFiniteRadiusSmoothSparse
open KrauseLaceyCompactPairingStabilization KrauseLaceySparseReflection
open HardyLittlewoodBoundaryControl

set_option autoImplicit false

noncomputable section

/-- The actual difference between adjacent smooth cutoffs is one annular
error, uniformly dominated by the same maximal function.
@isnad1 id=le.5h5v.s7.8ef389bfdd6d from=translated src=- shape=3c58f5a4 vocab=28309c35
-/
theorem enorm_smoothHighPass_sub_le_maximal
    (lam : ℝ) {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ) (hρε : ρ ≤ 2 * ε)
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    ‖smoothQuadraticHighPass lam ε f x - smoothQuadraticHighPass lam ρ f x‖ₑ ≤
      24 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  have hρ : 0 < ρ := hε.trans_le hερ
  have hεeq := quadraticHilbertTrunc_eq_smoothHighPass_add_boundary lam hε hfi x
  have hρeq := quadraticHilbertTrunc_eq_smoothHighPass_add_boundary lam hρ hfi x
  have hround := quadraticHilbertTrunc_sub_rounded_eq_boundary lam hε hρ hfi x
  have heq : smoothQuadraticHighPass lam ε f x - smoothQuadraticHighPass lam ρ f x =
      ((∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y) -
        ∫ y, cutoffBoundaryKernel lam ε (x - y) * f y) +
          ∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y := by
    rw [← hround, hεeq, hρeq]
    ring
  rw [heq]
  calc
    _ ≤ (‖∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y‖ₑ +
        ‖∫ y, cutoffBoundaryKernel lam ε (x - y) * f y‖ₑ) +
          ‖∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y‖ₑ :=
      (enorm_add_le _ _).trans (add_le_add enorm_sub_le le_rfl)
    _ ≤ (8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x +
        8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
          8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x :=
      add_le_add (add_le_add
        (radiusRoundingBoundaryOperator_enorm_le_maximal lam hε hερ hρε f hf x)
        (cutoffBoundaryOperator_enorm_le_maximal lam hε f hf x))
        (cutoffBoundaryOperator_enorm_le_maximal lam hρ f hf x)
    _ = _ := by ring

/--
@isnad1 id=le.3h4v.s7.1c8cf25106be from=translated src=- shape=0b3dd19b vocab=bea11d81
-/
theorem enorm_smoothHighPass_sub_dyadicRounded_le_maximal
    (lam : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    ‖smoothQuadraticHighPass lam ρ f x -
        smoothQuadraticHighPass lam (dyadicCeilRadius ρ hρ) f x‖ₑ ≤
      24 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x :=
  enorm_smoothHighPass_sub_le_maximal lam hρ (lt_dyadicCeilRadius ρ hρ).le
    (dyadicCeilRadius_le_two_mul ρ hρ) hf hfi x

/--
@isnad1 id=le.3h4v.s7.b457e06a16b0 from=translated src=- shape=16cf6715 vocab=5736c85d
-/
theorem enorm_smoothHighPass_le_dyadicRounded_add_maximal
    (lam : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    ‖smoothQuadraticHighPass lam ρ f x‖ₑ ≤
      ‖smoothQuadraticHighPass lam (dyadicCeilRadius ρ hρ) f x‖ₑ +
        24 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  calc
    _ = ‖smoothQuadraticHighPass lam (dyadicCeilRadius ρ hρ) f x +
        (smoothQuadraticHighPass lam ρ f x -
          smoothQuadraticHighPass lam (dyadicCeilRadius ρ hρ) f x)‖ₑ := by
      congr 1
      ring
    _ ≤ _ := (enorm_add_le _ _).trans (add_le_add le_rfl
      (enorm_smoothHighPass_sub_dyadicRounded_le_maximal lam hρ hf hfi x))

/-- The minimum of the rounded scales of the actual positive radii.-/
def adjacentDyadicLowerIndex (s : Finset PositiveSmoothRadius) : ℤ :=
  if hs : s.Nonempty then s.inf' hs (fun ρ ↦ dyadicFloorScale ρ.1 ρ.2 + 4) else 0

/--
@isnad1 id=le.1h2v.s5.3e84f5ba9f2e from=translated src=- shape=c83f570b vocab=3ad3276b
-/
theorem adjacentDyadicLowerIndex_le (s : Finset PositiveSmoothRadius)
    (ρ : PositiveSmoothRadius) (hρ : ρ ∈ s) :
    adjacentDyadicLowerIndex s ≤ dyadicFloorScale ρ.1 ρ.2 + 4 := by
  rw [adjacentDyadicLowerIndex, dite_eq_left ⟨ρ, hρ⟩]
  exact Finset.inf'_le _ hρ

/--
@isnad1 id=le.1h5v.s7.5ba49487ff39 from=translated src=- shape=20ad6d79 vocab=57137d75
-/
theorem enorm_adjacentRounded_le_dyadicMax
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (ρ : PositiveSmoothRadius) (hρ : ρ ∈ s)
    (f : L0Infinity) (x : ℝ) :
    ‖smoothQuadraticHighPass lam (dyadicCeilRadius ρ.1 ρ.2) f x‖ₑ ≤
      ‖dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s) f x‖ₑ := by
  have hj := adjacentDyadicLowerIndex_le s ρ hρ
  let m : ℕ := (dyadicFloorScale ρ.1 ρ.2 + 4 - adjacentDyadicLowerIndex s).toNat
  have hm : adjacentDyadicLowerIndex s + (m : ℤ) = dyadicFloorScale ρ.1 ρ.2 + 4 := by
    dsimp [m]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hj)]
    omega
  rw [enorm_dyadicSmoothHighPassMaxOperator, dyadicCeilRadius_eq_two_pow_scale_sub_three,
    ← hm]
  exact le_iSup (fun r : ℕ ↦
    ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (adjacentDyadicLowerIndex s + (r : ℤ) - 3))
      f x‖ₑ) m

/--
@isnad1 id=eq.0h4v.s6.e806d222cacb from=translated src=- shape=96b8a645 vocab=14b345fd
-/
@[simp] theorem enorm_finiteSmoothMaxOperator (lam : ℝ)
    (s : Finset PositiveSmoothRadius) (f : L0Infinity) (x : ℝ) :
    ‖finiteSmoothMaxOperator lam s f x‖ₑ =
      s.sup (fun ρ ↦ ‖smoothQuadraticHighPass lam ρ.1 f x‖ₑ) := by
  rw [← ofReal_norm]
  simp only [finiteSmoothMaxOperator, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
    finiteSmoothMaxNNNorm, ENNReal.coe_finset_sup]
  rfl

/-- The cardinality-free annular comparison for every finite positive-radius
family, including every common real scale offset of the rounded radii.
@isnad1 id=le.0h4v.s7.78cda8eff8a1 from=translated src=- shape=b96a7e88 vocab=77534451
-/
theorem enorm_finiteSmoothMax_le_dyadicMax_add_maximal
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f : L0Infinity) (x : ℝ) :
    ‖finiteSmoothMaxOperator lam s f x‖ₑ ≤
      ‖dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s) f x‖ₑ +
        24 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  rw [enorm_finiteSmoothMaxOperator]
  apply Finset.sup_le
  intro ρ hρ
  exact (enorm_smoothHighPass_le_dyadicRounded_add_maximal lam ρ.2
    f.measurable_toFun f.integrable x).trans
      (add_le_add (enorm_adjacentRounded_le_dyadicMax lam s ρ hρ f x) le_rfl)

/--
@isnad1 id=le.0h4v.s5.f85031d2ecfa from=translated src=- shape=c11b862e vocab=3c1eadc9
-/
theorem norm_finiteSmoothMax_le_dyadicMax_add_boundary
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f : L0Infinity) (x : ℝ) :
    ‖finiteSmoothMaxOperator lam s f x‖ ≤
      ‖dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s) f x‖ +
        24 * ‖centeredHardyLittlewoodBoundaryOperator f x‖ := by
  have h := enorm_finiteSmoothMax_le_dyadicMax_add_maximal lam s f x
  rw [← enorm_centeredHardyLittlewoodBoundaryOperator] at h
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤
      ‖dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s) f x‖ +
        24 * ‖centeredHardyLittlewoodBoundaryOperator f x‖)).mp
  simpa only [ENNReal.ofReal_add (norm_nonneg _)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (norm_nonneg _)),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 24), ENNReal.ofReal_ofNat,
    ofReal_norm] using h

/--
@isnad1 id=eq.0h0v.s2.f9a88ba02087 from=translated src=- shape=4b736592 vocab=1a9f9e13
-/
@[simp] theorem absoluteValue_centeredHardyLittlewoodBoundaryOperator :
    absoluteValueOperator centeredHardyLittlewoodBoundaryOperator =
      centeredHardyLittlewoodBoundaryOperator := by
  funext f x
  simp [absoluteValueOperator, centeredHardyLittlewoodBoundaryOperator]

/-- Pairing form of the actual annular comparison.  The right-hand test
function is its norm, so this statement remains valid for complex inputs.
@isnad1 id=le.0h4v.s5.3138e4e5a94f from=translated src=- shape=239cdff9 vocab=f2d56e8c
-/
theorem norm_pairing_finiteSmoothMax_le_dyadicMax_add_boundary
    (lam : ℝ) (s : Finset PositiveSmoothRadius) (f g : L0Infinity) :
    ‖operatorPairing (finiteSmoothMaxOperator lam s) f g‖ ≤
      ‖operatorPairing (dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s))
          f (normInput g)‖ +
        24 * ‖operatorPairing centeredHardyLittlewoodBoundaryOperator f (normInput g)‖ := by
  have hdy : ‖operatorPairing
        (dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s)) f (normInput g)‖ =
      ∫ x, ‖dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s) f x‖ * ‖g x‖ := by
    simpa only [absoluteValue_dyadicSmoothHighPassMaxOperator] using
      norm_operatorPairing_absolute_normInput
        (dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s)) f g
  have hbd : ‖operatorPairing centeredHardyLittlewoodBoundaryOperator f (normInput g)‖ =
      ∫ x, ‖centeredHardyLittlewoodBoundaryOperator f x‖ * ‖g x‖ := by
    simpa only [absoluteValue_centeredHardyLittlewoodBoundaryOperator] using
      norm_operatorPairing_absolute_normInput centeredHardyLittlewoodBoundaryOperator f g
  have hid : Integrable (fun x ↦
      ‖dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s) f x‖ * ‖g x‖) := by
    simpa only [norm_mul, norm_star] using
      (integrable_pairing_dyadicSmoothHighPassMax lam (adjacentDyadicLowerIndex s) f g).norm
  have hib : Integrable (fun x ↦ ‖centeredHardyLittlewoodBoundaryOperator f x‖ * ‖g x‖) := by
    simpa only [norm_mul, norm_star] using
      (integrable_pairing_of_locallyIntegrable
        (centeredHardyLittlewoodBoundaryOperator_locallyIntegrable f) g).norm
  rw [hdy, hbd, ← integral_const_mul, ← integral_add hid (hib.const_mul 24)]
  apply norm_integral_le_of_norm_le (hid.add (hib.const_mul 24))
  filter_upwards with x
  rw [norm_mul, norm_star, Pi.add_apply]
  calc
    _ ≤ (‖dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s) f x‖ +
        24 * ‖centeredHardyLittlewoodBoundaryOperator f x‖) * ‖g x‖ :=
      mul_le_mul_of_nonneg_right
        (norm_finiteSmoothMax_le_dyadicMax_add_boundary lam s f x) (norm_nonneg _)
    _ = _ := by ring

end
end QuadraticCarleson.KrauseLaceyScaleOffsetPointwise
