import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyCompactPairingStabilization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson.KrauseLaceyFiniteRadiusSmoothSparse

open QuadraticHilbertMaximalMeasurable KrauseLaceySharpSmoothAdapter
open KrauseLaceyFullDyadicSparseTransfer KrauseLaceyCompactPairingStabilization
open KrauseLaceySparseReflection

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The lowest rounded dyadic scale; the empty family uses the harmless index zero.-/
noncomputable def finiteRadiusLowerIndex (s : Finset densePositiveRadii) : ℤ :=
  if hs : s.Nonempty then s.inf' hs (fun ε ↦ dyadicFloorScale ε.1.1 ε.1.2 + 4) else 0

/--
@isnad1 id=le.1h2v.s7.daff13c10b16 from=translated src=- shape=ab2a838d vocab=323acfff
-/
theorem finiteRadiusLowerIndex_le (s : Finset densePositiveRadii)
    (ε : densePositiveRadii) (hε : ε ∈ s) :
    finiteRadiusLowerIndex s ≤ dyadicFloorScale ε.1.1 ε.1.2 + 4 := by
  rw [finiteRadiusLowerIndex, dite_eq_left ⟨ε, hε⟩]
  exact Finset.inf'_le _ hε

/-- Every selected rounded radius is one of the moving lower cutoffs of
the genuine dyadic suffix maximum.
@isnad1 id=le.1h5v.s8.5c06e1219c57 from=translated src=- shape=0dd03b7d vocab=de23c2c4
-/
theorem enorm_roundedSmoothHighPass_le_dyadicMax
    (lam : ℝ) (s : Finset densePositiveRadii) (ε : densePositiveRadii) (hε : ε ∈ s)
    (f : L0Infinity) (x : ℝ) :
    ‖smoothQuadraticHighPass lam (dyadicCeilRadius ε.1.1 ε.1.2) f x‖ₑ ≤
      ‖dyadicSmoothHighPassMaxOperator lam (finiteRadiusLowerIndex s) f x‖ₑ := by
  have hj := finiteRadiusLowerIndex_le s ε hε
  let m : ℕ := (dyadicFloorScale ε.1.1 ε.1.2 + 4 - finiteRadiusLowerIndex s).toNat
  have hm : finiteRadiusLowerIndex s + (m : ℤ) = dyadicFloorScale ε.1.1 ε.1.2 + 4 := by
    dsimp [m]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hj)]
    omega
  rw [enorm_dyadicSmoothHighPassMaxOperator, dyadicCeilRadius_eq_two_pow_scale_sub_three,
    ← hm]
  exact le_iSup (fun r : ℕ ↦
    ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (finiteRadiusLowerIndex s + (r : ℤ) - 3)) f x‖ₑ) m

/--
@isnad1 id=le.0h4v.s6.f1673e9e1281 from=translated src=- shape=f6f235c3 vocab=d130eda7
-/
theorem enorm_finiteRadiusSmoothHighPassMax_le_dyadicMax
    (lam : ℝ) (s : Finset densePositiveRadii) (f : L0Infinity) (x : ℝ) :
    ‖finiteRadiusSmoothHighPassMaxTestOperator lam s f x‖ₑ ≤
      ‖dyadicSmoothHighPassMaxOperator lam (finiteRadiusLowerIndex s) f x‖ₑ := by
  rw [← ofReal_norm, norm_finiteRadiusSmoothHighPassMaxTestOperator, ENNReal.ofReal_coe_nnreal]
  unfold finiteRadiusSmoothHighPassMaxNNNorm
  rw [ENNReal.coe_finset_sup]
  exact Finset.sup_le fun ε hε ↦ enorm_roundedSmoothHighPass_le_dyadicMax lam s ε hε f x

/--
@isnad1 id=le.0h4v.s5.b44a32eae4c7 from=translated src=- shape=c31263eb vocab=0739b07e
-/
theorem norm_finiteRadiusSmoothHighPassMax_le_dyadicMax
    (lam : ℝ) (s : Finset densePositiveRadii) (f : L0Infinity) (x : ℝ) :
    ‖finiteRadiusSmoothHighPassMaxTestOperator lam s f x‖ ≤
      ‖dyadicSmoothHighPassMaxOperator lam (finiteRadiusLowerIndex s) f x‖ := by
  have h := enorm_finiteRadiusSmoothHighPassMax_le_dyadicMax lam s f x
  simpa only [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] using h

/-- Compact stabilization supplies honest integrability of all testing pairings
of the genuine infinite suffix maximum.
@isnad1 id=integrab.0h4v.s6.e75fef79f853 from=translated src=- shape=082e6928 vocab=48ccd1cb
-/
theorem integrable_pairing_dyadicSmoothHighPassMax
    (lam : ℝ) (j : ℤ) (f g : L0Infinity) :
    Integrable (fun x ↦ dyadicSmoothHighPassMaxOperator lam j f x * star (g x)) := by
  obtain ⟨N, hN⟩ := exists_dyadicSmoothHighPassMax_eq_finiteSuffixMax j f g
  apply (integrable_pairing_of_locallyIntegrable
    (locallyIntegrable_finiteFullDyadicSuffixMaxOperator lam j N f) g).congr
  filter_upwards with x
  by_cases hx : x ∈ tsupport g
  · rw [hN lam x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/--
@isnad1 id=eq.0h2v.s3.6f207e52c596 from=translated src=- shape=33e5716c vocab=39428710
-/
theorem absoluteValue_dyadicSmoothHighPassMaxOperator (lam : ℝ) (j : ℤ) :
    absoluteValueOperator (dyadicSmoothHighPassMaxOperator lam j) =
      dyadicSmoothHighPassMaxOperator lam j := by
  funext f x
  simp [absoluteValueOperator, dyadicSmoothHighPassMaxOperator]

/-- Pointwise domination by the nonnegative genuine dyadic maximum transfers
sparse pairings, with exactly the same constant.
@isnad1 id=hasspars.2h5v.s5.48e930142819 from=translated src=- shape=f5779c27 vocab=dc7793d9
-/
theorem hasSparseOnePBound_of_norm_le_dyadicSmoothHighPassMax
    (lam : ℝ) (j : ℤ) {C p : ℝ} {U : TestOperator}
    (hdyadic : HasSparseOnePBound C p (dyadicSmoothHighPassMaxOperator lam j))
    (hdom : ∀ (f : L0Infinity) (x : ℝ),
      ‖U f x‖ ≤ ‖dyadicSmoothHighPassMaxOperator lam j f x‖) :
    HasSparseOnePBound C p U := by
  intro f g
  obtain ⟨S, hS, hb⟩ := hdyadic f (normInput g)
  have hp : ‖operatorPairing (dyadicSmoothHighPassMaxOperator lam j) f (normInput g)‖ =
      ∫ x, ‖dyadicSmoothHighPassMaxOperator lam j f x‖ * ‖g x‖ := by
    simpa only [absoluteValue_dyadicSmoothHighPassMaxOperator] using
      norm_operatorPairing_absolute_normInput (dyadicSmoothHighPassMaxOperator lam j) f g
  rw [hp, sparseForm_normInput] at hb
  have hi : Integrable (fun x ↦ ‖dyadicSmoothHighPassMaxOperator lam j f x‖ * ‖g x‖) := by
    simpa only [norm_mul, norm_star] using (integrable_pairing_dyadicSmoothHighPassMax lam j f g).norm
  have hnorm : ‖operatorPairing U f g‖ ≤
      ∫ x, ‖dyadicSmoothHighPassMaxOperator lam j f x‖ * ‖g x‖ := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards with x
    simpa only [norm_mul, norm_star] using
      mul_le_mul_of_nonneg_right (hdom f x) (norm_nonneg (g x))
  exact ⟨S, hS, (ENNReal.ofReal_le_ofReal hnorm).trans hb⟩

/-- The finite set of rounded radii costs no constant beyond the dyadic maximum.
@isnad1 id=hasspars.1h4v.s5.cc56a5ae72b4 from=translated src=- shape=6bcc898c vocab=fc36c5ee
-/
theorem hasSparseOnePBound_finiteRadiusSmoothHighPassMax_of_dyadicMax
    (lam : ℝ) (s : Finset densePositiveRadii) {C p : ℝ}
    (hdyadic : HasSparseOnePBound C p
      (dyadicSmoothHighPassMaxOperator lam (finiteRadiusLowerIndex s))) :
    HasSparseOnePBound C p (finiteRadiusSmoothHighPassMaxTestOperator lam s) :=
  hasSparseOnePBound_of_norm_le_dyadicSmoothHighPassMax lam (finiteRadiusLowerIndex s)
    hdyadic (norm_finiteRadiusSmoothHighPassMax_le_dyadicMax lam s)

/-- Uniform positive-half finite suffix bounds give every finite-radius smooth
sparse bound. Reflection is the only loss, namely the explicit factor two.
@isnad1 id=hasspars.2h4v.s6.e3a9a98b925e from=translated src=- shape=2e98b613 vocab=78c414a2
-/
theorem hasSparseOnePBound_finiteRadiusSmoothHighPassMax_of_uniform_positive_finiteSuffixMax
    (lam : ℝ) (s : Finset densePositiveRadii) {C p : ℝ} (hC : 0 ≤ C)
    (hpositive : ∀ (j : ℤ) (N : ℕ),
      HasSparseOnePBound C p (finitePositiveDyadicSuffixMaxOperator lam j N)) :
    HasSparseOnePBound (2 * C) p (finiteRadiusSmoothHighPassMaxTestOperator lam s) :=
  hasSparseOnePBound_finiteRadiusSmoothHighPassMax_of_dyadicMax lam s
    (hasSparseOnePBound_dyadicSmoothHighPassMax_of_uniform_positive_finiteSuffixMax
      lam (finiteRadiusLowerIndex s) hC (hpositive (finiteRadiusLowerIndex s)))

end QuadraticCarleson.KrauseLaceyFiniteRadiusSmoothSparse
