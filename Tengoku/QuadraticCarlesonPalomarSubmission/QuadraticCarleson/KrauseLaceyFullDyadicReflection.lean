/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceySharpSmoothAdapter
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.QuadraticFixedHeightAveragingSigned

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Restoring the negative spatial half of the Krause--Lacey kernel

Krause--Lacey carry out the local argument for the positive half of their odd
dyadic kernel and state that the negative half is symmetric.  This file makes
that symmetry exact.  A finite full dyadic tail is the positive-half tail on
`f` minus the same positive-half tail on the reflected input, evaluated at the
reflected point.  Thus no analytic estimate is duplicated for the negative
half.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyFullDyadicReflection

set_option autoImplicit false

noncomputable section

/-- A single positive-half dyadic convolution at scale `j`.-/
def positiveDyadicConvolution
    (lam : ℝ) (j : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, annularQuadraticKernel (positiveDyadicAmplitude j) lam (x - y) * f y

/-- The corresponding convolution with the paper's full odd dyadic kernel.-/
def fullDyadicConvolution
    (lam : ℝ) (j : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, annularQuadraticKernel (fun t ↦ (dyadicPsi j t : ℂ)) lam (x - y) * f y

/-- A finite consecutive positive-half dyadic tail.-/
def finitePositiveDyadicTail
    (lam : ℝ) (j : ℤ) (n : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ r ∈ Finset.range n, positiveDyadicConvolution lam (j + (r : ℤ)) f x

/-- A finite consecutive tail for the genuine full odd dyadic kernel.-/
def finiteFullDyadicTail
    (lam : ℝ) (j : ℤ) (n : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ r ∈ Finset.range n, fullDyadicConvolution lam (j + (r : ℤ)) f x

/-- Maximum over all initial finite tails of length at most `N`.  The value is
kept in `NNReal`, matching the finite-maximal interfaces elsewhere in the
project.-/
def finitePositiveDyadicTailMaxNNNorm
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : NNReal :=
  (Finset.range (N + 1)).sup fun n ↦ ‖finitePositiveDyadicTail lam j n f x‖₊

/-- The same finite maximum for the genuine full odd dyadic kernel.-/
def finiteFullDyadicTailMaxNNNorm
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : NNReal :=
  (Finset.range (N + 1)).sup fun n ↦ ‖finiteFullDyadicTail lam j n f x‖₊

/-- A suffix ending at the common upper scale `j + N`.  Varying `m` is the
finite version of the paper's physical lower-truncation parameter.-/
def finitePositiveDyadicSuffix
    (lam : ℝ) (j : ℤ) (N m : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  finitePositiveDyadicTail lam (j + (m : ℤ)) (N - m) f x

/-- The corresponding finite suffix for the full odd kernel.-/
def finiteFullDyadicSuffix
    (lam : ℝ) (j : ℤ) (N m : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  finiteFullDyadicTail lam (j + (m : ℤ)) (N - m) f x

/-- Maximum over the moving lower cutoffs `m ≤ N` for the positive half.-/
def finitePositiveDyadicSuffixMaxNNNorm
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : NNReal :=
  (Finset.range (N + 1)).sup fun m ↦ ‖finitePositiveDyadicSuffix lam j N m f x‖₊

/-- Maximum over moving lower cutoffs for the full odd kernel.-/
def finiteFullDyadicSuffixMaxNNNorm
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : NNReal :=
  (Finset.range (N + 1)).sup fun m ↦ ‖finiteFullDyadicSuffix lam j N m f x‖₊

/-- Supremum of all finite full-tail approximants.-/
def fullDyadicTailSupEnorm
    (lam : ℝ) (j : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ‖finiteFullDyadicTail lam j n f x‖ₑ

/--
@isnad1 id=continuo.0h2v.s4.4649b8904441 from=translated src=- shape=81a8c335 vocab=b83e9f96
-/
theorem continuous_positiveDyadicQuadraticKernel (lam : ℝ) (j : ℤ) :
    Continuous (annularQuadraticKernel (positiveDyadicAmplitude j) lam) := by
  have ha : Continuous (positiveDyadicAmplitude j) :=
    continuous_iff_continuousAt.mpr
      (fun t ↦ (hasDerivAt_positiveDyadicAmplitude j t).continuousAt)
  unfold annularQuadraticKernel phase
  fun_prop

/--
@isnad1 id=hascompa.0h2v.s4.e890e6917285 from=translated src=- shape=81a8c335 vocab=8c7f7286
-/
theorem hasCompactSupport_positiveDyadicQuadraticKernel (lam : ℝ) (j : ℤ) :
    HasCompactSupport (annularQuadraticKernel (positiveDyadicAmplitude j) lam) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact
      (Icc ((2 : ℝ) ^ (j - 1) / 4) ((2 : ℝ) ^ (j - 1))))
  intro t ht
  apply positiveDyadicAmplitude_support_subset j
  intro hz
  exact ht (by simp [annularQuadraticKernel, hz])

/-- The phase is even, so the odd dyadic amplitude is literally the positive
kernel minus its spatial reflection.
@isnad1 id=eq.0h3v.s5.18511eee2660 from=translated src=- shape=509fccfa vocab=66604005
-/
theorem fullDyadicKernel_eq_positive_sub_reflect (lam : ℝ) (j : ℤ) (t : ℝ) :
    annularQuadraticKernel (fun u ↦ (dyadicPsi j u : ℂ)) lam t =
      annularQuadraticKernel (positiveDyadicAmplitude j) lam t -
        annularQuadraticKernel (positiveDyadicAmplitude j) lam (-t) := by
  unfold annularQuadraticKernel
  change (dyadicPsi j t : ℂ) * phase (lam * t ^ 2) =
    positiveDyadicAmplitude j t * phase (lam * t ^ 2) -
      positiveDyadicAmplitude j (-t) * phase (lam * (-t) ^ 2)
  rw [dyadicPsi_eq_positive_sub_reflect]
  simp only [neg_sq]
  ring

/-- Reflection of the positive kernel is the positive operator on the
reflected input at the reflected observation point.
@isnad1 id=eq.0h4v.s6.4dfd2da89ae2 from=translated src=- shape=8506103e vocab=88859174
-/
theorem reflectedPositiveDyadicConvolution
    (lam : ℝ) (j : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    (∫ y, annularQuadraticKernel (positiveDyadicAmplitude j) lam (-(x - y)) * f y) =
      positiveDyadicConvolution lam j (fun y ↦ f (-y)) (-x) := by
  unfold positiveDyadicConvolution
  calc
    (∫ y, annularQuadraticKernel (positiveDyadicAmplitude j) lam (-(x - y)) * f y) =
        ∫ y, annularQuadraticKernel (positiveDyadicAmplitude j) lam
          (-(x - -y)) * f (-y) :=
      (integral_neg_eq_self
        (fun y ↦ annularQuadraticKernel (positiveDyadicAmplitude j) lam (-(x - y)) * f y)
        volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      congr 2
      ring

/-- Exact one-scale identity restoring the negative spatial half.
@isnad1 id=eq.1h4v.s6.1a9753499b77 from=translated src=- shape=436c076c vocab=09b32fa2
-/
theorem fullDyadicConvolution_eq_positive_sub_reflect
    (lam : ℝ) (j : ℤ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    fullDyadicConvolution lam j f x =
      positiveDyadicConvolution lam j f x -
        positiveDyadicConvolution lam j (fun y ↦ f (-y)) (-x) := by
  have hp : Integrable
      (fun y ↦ annularQuadraticKernel (positiveDyadicAmplitude j) lam (x - y) * f y) :=
    integrable_convolution_row_of_memLp
      (continuous_positiveDyadicQuadraticKernel lam j)
      (hasCompactSupport_positiveDyadicQuadraticKernel lam j) hf x
  have hr : Integrable
      (fun y ↦ annularQuadraticKernel (positiveDyadicAmplitude j) lam (-(x - y)) * f y) := by
    have hc := (continuous_positiveDyadicQuadraticKernel lam j).comp continuous_neg
    have hs := (hasCompactSupport_positiveDyadicQuadraticKernel lam j).comp_homeomorph
      (Homeomorph.neg ℝ)
    exact integrable_convolution_row_of_memLp hc hs hf x
  rw [fullDyadicConvolution, positiveDyadicConvolution, ← reflectedPositiveDyadicConvolution]
  rw [← integral_sub hp hr]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← sub_mul, ← fullDyadicKernel_eq_positive_sub_reflect]

/-- Exact finite-tail identity.  This is the deterministic justification for
using only the positive spatial half in the local KL argument.
@isnad1 id=eq.1h5v.s6.57937b536976 from=translated src=- shape=1dd2c8e1 vocab=04b40686
-/
theorem finiteFullDyadicTail_eq_positive_sub_reflect
    (lam : ℝ) (j : ℤ) (n : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteFullDyadicTail lam j n f x =
      finitePositiveDyadicTail lam j n f x -
        finitePositiveDyadicTail lam j n (fun y ↦ f (-y)) (-x) := by
  unfold finiteFullDyadicTail finitePositiveDyadicTail
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact fullDyadicConvolution_eq_positive_sub_reflect lam (j + (r : ℤ)) hf x

/--
@isnad1 id=le.1h5v.s7.0de726167b86 from=translated src=- shape=115c85f3 vocab=43868048
-/
theorem norm_finiteFullDyadicTail_le_positive_add_reflect
    (lam : ℝ) (j : ℤ) (n : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    ‖finiteFullDyadicTail lam j n f x‖ ≤
      ‖finitePositiveDyadicTail lam j n f x‖ +
        ‖finitePositiveDyadicTail lam j n (fun y ↦ f (-y)) (-x)‖ := by
  rw [finiteFullDyadicTail_eq_positive_sub_reflect lam j n hf x]
  exact norm_sub_le _ _

/-- The maximum of the full odd-kernel tails is pointwise controlled by the
positive-half maximum and its reflected-input copy.  The estimate is uniform
in the number of scales.
@isnad1 id=le.1h5v.s7.aaf3fbd75c20 from=translated src=- shape=0cbf1903 vocab=151872c7
-/
theorem finiteFullDyadicTailMaxNNNorm_le_positive_add_reflect
    (lam : ℝ) (j : ℤ) (N : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteFullDyadicTailMaxNNNorm lam j N f x ≤
      finitePositiveDyadicTailMaxNNNorm lam j N f x +
        finitePositiveDyadicTailMaxNNNorm lam j N (fun y ↦ f (-y)) (-x) := by
  unfold finiteFullDyadicTailMaxNNNorm finitePositiveDyadicTailMaxNNNorm
  apply Finset.sup_le
  intro n hn
  calc
    ‖finiteFullDyadicTail lam j n f x‖₊ ≤
        ‖finitePositiveDyadicTail lam j n f x‖₊ +
          ‖finitePositiveDyadicTail lam j n (fun y ↦ f (-y)) (-x)‖₊ := by
      exact_mod_cast norm_finiteFullDyadicTail_le_positive_add_reflect lam j n hf x
    _ ≤ ((Finset.range (N + 1)).sup fun m ↦
          ‖finitePositiveDyadicTail lam j m f x‖₊) +
        (Finset.range (N + 1)).sup fun m ↦
          ‖finitePositiveDyadicTail lam j m (fun y ↦ f (-y)) (-x)‖₊ :=
      add_le_add (Finset.le_sup (f := fun m ↦
        ‖finitePositiveDyadicTail lam j m f x‖₊) hn)
        (Finset.le_sup (f := fun m ↦
          ‖finitePositiveDyadicTail lam j m (fun y ↦ f (-y)) (-x)‖₊) hn)

/--
@isnad1 id=eq.1h6v.s6.55b4987569dc from=translated src=- shape=426f0e24 vocab=605586e6
-/
theorem finiteFullDyadicSuffix_eq_positive_sub_reflect
    (lam : ℝ) (j : ℤ) (N m : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteFullDyadicSuffix lam j N m f x =
      finitePositiveDyadicSuffix lam j N m f x -
        finitePositiveDyadicSuffix lam j N m (fun y ↦ f (-y)) (-x) := by
  exact finiteFullDyadicTail_eq_positive_sub_reflect
    lam (j + (m : ℤ)) (N - m) hf x

/-- Reflection control in the exact suffix orientation of the KL maximal
physical-truncation operator.
@isnad1 id=le.1h5v.s7.2600a1561e62 from=translated src=- shape=0cbf1903 vocab=b86042d9
-/
theorem finiteFullDyadicSuffixMaxNNNorm_le_positive_add_reflect
    (lam : ℝ) (j : ℤ) (N : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteFullDyadicSuffixMaxNNNorm lam j N f x ≤
      finitePositiveDyadicSuffixMaxNNNorm lam j N f x +
        finitePositiveDyadicSuffixMaxNNNorm lam j N (fun y ↦ f (-y)) (-x) := by
  unfold finiteFullDyadicSuffixMaxNNNorm finitePositiveDyadicSuffixMaxNNNorm
  apply Finset.sup_le
  intro m hm
  calc
    ‖finiteFullDyadicSuffix lam j N m f x‖₊ ≤
        ‖finitePositiveDyadicSuffix lam j N m f x‖₊ +
          ‖finitePositiveDyadicSuffix lam j N m (fun y ↦ f (-y)) (-x)‖₊ := by
      rw [finiteFullDyadicSuffix_eq_positive_sub_reflect lam j N m hf x]
      exact_mod_cast norm_sub_le
        (finitePositiveDyadicSuffix lam j N m f x)
        (finitePositiveDyadicSuffix lam j N m (fun y ↦ f (-y)) (-x))
    _ ≤ ((Finset.range (N + 1)).sup fun q ↦
          ‖finitePositiveDyadicSuffix lam j N q f x‖₊) +
        (Finset.range (N + 1)).sup fun q ↦
          ‖finitePositiveDyadicSuffix lam j N q (fun y ↦ f (-y)) (-x)‖₊ :=
      add_le_add (Finset.le_sup (f := fun q ↦
        ‖finitePositiveDyadicSuffix lam j N q f x‖₊) hm)
        (Finset.le_sup (f := fun q ↦
          ‖finitePositiveDyadicSuffix lam j N q (fun y ↦ f (-y)) (-x)‖₊) hm)

/-- The finite full tails exhaust the actual smooth high-pass convolution.
Compact support of the test input is used in the underlying operator-level
sum/integral theorem, so this is not a merely formal kernel identity.
@isnad1 id=hassum.0h4v.s6.695d6484bd8a from=translated src=- shape=63606bc8 vocab=fc9b0fb5
-/
theorem hasSum_fullDyadicConvolution_add_nat
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    HasSum (fun r : ℕ ↦ fullDyadicConvolution lam (j + (r : ℤ)) f x)
      (KrauseLaceySharpSmoothAdapter.smoothQuadraticHighPass
        lam ((2 : ℝ) ^ (j - 3)) f x) := by
  simpa only [fullDyadicConvolution, annularQuadraticKernel] using
    KrauseLaceySharpSmoothAdapter.hasSum_dyadicQuadraticConvolutions_add_nat
      lam j f x

/--
@isnad1 id=tendsto.0h4v.s6.ade50a4252db from=translated src=- shape=44593988 vocab=e7057c30
-/
theorem tendsto_finiteFullDyadicTail_atTop
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    Tendsto (fun n : ℕ ↦ finiteFullDyadicTail lam j n f x) atTop
      (nhds (KrauseLaceySharpSmoothAdapter.smoothQuadraticHighPass
        lam ((2 : ℝ) ^ (j - 3)) f x)) := by
  simpa only [finiteFullDyadicTail] using
    (hasSum_fullDyadicConvolution_add_nat lam j f x).tendsto_sum_nat

/-- The genuine smooth high-pass value is controlled by the supremum of its
finite odd-kernel approximants.  This is the pointwise limit bridge used when
passing a uniform finite sparse estimate to the actual operator.
@isnad1 id=le.0h4v.s6.a2af20e6b54c from=translated src=- shape=bf279acc vocab=4d764787
-/
theorem smoothQuadraticHighPass_enorm_le_fullDyadicTailSupEnorm
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    ‖KrauseLaceySharpSmoothAdapter.smoothQuadraticHighPass
        lam ((2 : ℝ) ^ (j - 3)) f x‖ₑ ≤
      fullDyadicTailSupEnorm lam j f x := by
  unfold fullDyadicTailSupEnorm
  have hnorm : Tendsto
      (fun n : ℕ ↦ ‖finiteFullDyadicTail lam j n f x‖)
      atTop
      (nhds ‖KrauseLaceySharpSmoothAdapter.smoothQuadraticHighPass
        lam ((2 : ℝ) ^ (j - 3)) f x‖) :=
    (continuous_norm.tendsto _).comp
      (tendsto_finiteFullDyadicTail_atTop lam j f x)
  have henorm : Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal ‖finiteFullDyadicTail lam j n f x‖)
      atTop
      (nhds (ENNReal.ofReal
        ‖KrauseLaceySharpSmoothAdapter.smoothQuadraticHighPass
          lam ((2 : ℝ) ^ (j - 3)) f x‖)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm
  rw [← ofReal_norm]
  apply le_of_tendsto henorm
  exact Filter.Eventually.of_forall fun n ↦ by
    simpa only [ofReal_norm] using
      (le_iSup (fun m : ℕ ↦ ‖finiteFullDyadicTail lam j m f x‖ₑ) n)

end
end KrauseLaceyFullDyadicReflection
end QuadraticCarleson
