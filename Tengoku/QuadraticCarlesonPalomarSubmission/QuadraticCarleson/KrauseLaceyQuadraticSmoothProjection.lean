import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyQuadraticAnnularTail
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PositiveDyadicKernel
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.HilbertMaximalWeakOneOne
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.HilbertRepresentativeBridge
import Tengoku.Seed.Analysis.Fourier.Convolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Concrete smooth frequency cutoffs for the direct quadratic proof

The positive quadratic kernel at physical scale `2^j` has stationary
frequency in the normalized interval `[1/4, 1]`.  We choose a smooth cutoff
which is identically one on the larger interval `[1/8, 2]` and is supported
in `(1/16, 33/16)`.  Its dyadic dilates are exactly disjoint after separating
the scales into seven residue classes.
-/

open Function MeasureTheory Set FourierTransform Metric
open scoped ENNReal NNReal ContDiff SchwartzMap ComplexConjugate Convolution

namespace QuadraticCarleson.KrauseLaceyQuadraticSmoothProjection

open HilbertMaximalWeakOneOne

set_option autoImplicit false

noncomputable section

/-- A one-sided smooth frequency bump.  The inner ball is `[1/8,2]` and
the outer ball is `(1/16,33/16)`.-/
def annularFrequencyCutoffData : ContDiffBump (17 / 16 : ℝ) :=
  ⟨15 / 16, 1, by norm_num, by norm_num⟩

def annularFrequencyCutoffReal : ℝ → ℝ := annularFrequencyCutoffData

def annularFrequencyCutoff (ξ : ℝ) : ℂ :=
  (annularFrequencyCutoffReal ξ : ℂ)

/--
@isnad1 id=contdiff.0h0v.s5.dcd37571165c from=translated src=- shape=352d7a74 vocab=17eb62fb
-/
theorem contDiff_annularFrequencyCutoff :
    ContDiff ℝ ∞ annularFrequencyCutoff := by
  exact Complex.ofRealCLM.contDiff.comp annularFrequencyCutoffData.contDiff

/--
@isnad1 id=eq.1h1v.s5.339b4f3e29da from=translated src=- shape=df0b7202 vocab=e3a7a1af
-/
theorem annularFrequencyCutoff_eq_one {ξ : ℝ}
    (hξ : ξ ∈ Icc (1 / 8 : ℝ) 2) :
    annularFrequencyCutoff ξ = 1 := by
  have hmem : ξ ∈ closedBall (17 / 16 : ℝ) (15 / 16) := by
    rw [mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hξ.1, hξ.2]
  have hbump : annularFrequencyCutoffData ξ = 1 :=
    annularFrequencyCutoffData.one_of_mem_closedBall hmem
  change (annularFrequencyCutoffData ξ : ℂ) = 1
  rw [hbump]
  norm_num

/--
@isnad1 id=eq.1h1v.s6.c42c4aa5b4b8 from=translated src=- shape=61d9e9a3 vocab=8c4f8340
-/
theorem annularFrequencyCutoff_eq_zero {ξ : ℝ}
    (hξ : ξ ≤ 1 / 16 ∨ 33 / 16 ≤ ξ) :
    annularFrequencyCutoff ξ = 0 := by
  have hdist : (1 : ℝ) ≤ dist ξ (17 / 16 : ℝ) := by
    rw [Real.dist_eq]
    rcases hξ with hlow | hhigh
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  have hbump : annularFrequencyCutoffData ξ = 0 :=
    annularFrequencyCutoffData.zero_of_le_dist hdist
  change (annularFrequencyCutoffData ξ : ℂ) = 0
  rw [hbump]
  norm_num

/--
@isnad1 id=le.0h0v.s5.c7fe0288cafd from=translated src=- shape=6758b511 vocab=0dd4ba47
-/
theorem annularFrequencyCutoff_support_subset :
    Function.support annularFrequencyCutoff ⊆ Ioo (1 / 16 : ℝ) (33 / 16) := by
  intro ξ hξ
  constructor
  · by_contra h
    exact hξ (annularFrequencyCutoff_eq_zero (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hξ (annularFrequencyCutoff_eq_zero (Or.inr (le_of_not_gt h)))

/--
@isnad1 id=hascompa.0h0v.s3.77a219bd127d from=translated src=- shape=54c8eceb vocab=52f34952
-/
theorem hasCompactSupport_annularFrequencyCutoff :
    HasCompactSupport annularFrequencyCutoff := by
  exact annularFrequencyCutoffData.hasCompactSupport.comp_left rfl

/-- The cutoff at frequency scale `2^j`.-/
def scaledAnnularFrequencyCutoff (j : ℤ) (ξ : ℝ) : ℂ :=
  annularFrequencyCutoff (ξ / (2 : ℝ) ^ j)

/-- The exact open annulus naturally attached to the scaled cutoff.-/
def scaledFrequencyAnnulus (j : ℤ) : Set ℝ :=
  Ioo ((1 / 16 : ℝ) * (2 : ℝ) ^ j)
    ((33 / 16 : ℝ) * (2 : ℝ) ^ j)

/--
@isnad1 id=le.0h1v.s3.70462173e27e from=translated src=- shape=fdec8f46 vocab=a7fd3040
-/
theorem scaledAnnularFrequencyCutoff_support_subset (j : ℤ) :
    Function.support (scaledAnnularFrequencyCutoff j) ⊆
      scaledFrequencyAnnulus j := by
  intro ξ hξ
  have hs := annularFrequencyCutoff_support_subset hξ
  have hpow : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  constructor
  · exact (lt_div_iff₀ hpow).mp hs.1
  · exact (div_lt_iff₀ hpow).mp hs.2

/--
@isnad1 id=contdiff.0h1v.s5.8697099e73ef from=translated src=- shape=caa53032 vocab=04be8cc9
-/
theorem contDiff_scaledAnnularFrequencyCutoff (j : ℤ) :
    ContDiff ℝ ∞ (scaledAnnularFrequencyCutoff j) := by
  exact contDiff_annularFrequencyCutoff.comp
    (contDiff_id.div_const ((2 : ℝ) ^ j))

/--
@isnad1 id=hascompa.0h1v.s3.a1e6313535a0 from=translated src=- shape=7000f90d vocab=ab2abaa8
-/
theorem hasCompactSupport_scaledAnnularFrequencyCutoff (j : ℤ) :
    HasCompactSupport (scaledAnnularFrequencyCutoff j) := by
  have hc : ((2 : ℝ) ^ j)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by norm_num))
  change HasCompactSupport (fun x : ℝ ↦
    annularFrequencyCutoff (x / (2 : ℝ) ^ j))
  simpa only [smul_eq_mul, div_eq_inv_mul, mul_comm] using
    hasCompactSupport_annularFrequencyCutoff.comp_smul hc

/-- The concrete annuli are disjoint once their scale indices differ by six.
The numerical inequality behind this is `33 < 2^6`.
@isnad1 id=disjoint.1h2v.s5.9856bf98e1cc from=translated src=- shape=b59a5c6c vocab=be3725d3
-/
theorem scaledFrequencyAnnulus_disjoint_of_add_six_le
    {j k : ℤ} (hjk : j + 6 ≤ k) :
    Disjoint (scaledFrequencyAnnulus j) (scaledFrequencyAnnulus k) := by
  rw [Set.disjoint_left]
  intro ξ hξj hξk
  have hpj : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hscale : (64 : ℝ) * (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k := by
    calc
      (64 : ℝ) * (2 : ℝ) ^ j = (2 : ℝ) ^ (j + 6) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
        ring
      _ ≤ (2 : ℝ) ^ k :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjk
  have hgap :
      (33 / 16 : ℝ) * (2 : ℝ) ^ j <
        (1 / 16 : ℝ) * (2 : ℝ) ^ k := by
    nlinarith
  exact (not_lt_of_ge (le_of_lt hgap)) (hξk.1.trans hξj.2)

/-- The integer scale in residue class `r mod 7` with nonnegative index `n`.-/
def residueScale (r : Fin 7) (n : ℕ) : ℤ :=
  (r : ℕ) + 7 * (n : ℤ)

/-- Within each of the seven residue classes, the concrete annuli are
pairwise disjoint.  Seven classes leave a one-scale margin beyond the exact
six-scale disjointness threshold, which is used by the low-pass cutoff.
@isnad1 id=pairwise.0h1v.s5.4f3cf4e4af37 from=translated src=- shape=0fe5638b vocab=cc6aa62c
-/
theorem pairwiseDisjoint_scaledFrequencyAnnulus_residueScale (r : Fin 7) :
    Pairwise fun m n : ℕ ↦
      Disjoint (scaledFrequencyAnnulus (residueScale r m))
        (scaledFrequencyAnnulus (residueScale r n)) := by
  intro m n hmn
  by_cases hlt : m < n
  · apply scaledFrequencyAnnulus_disjoint_of_add_six_le
    simp only [residueScale]
    omega
  · have hnm : n < m := lt_of_le_of_ne (Nat.le_of_not_gt hlt) hmn.symm
    exact (scaledFrequencyAnnulus_disjoint_of_add_six_le (j := residueScale r n)
      (k := residueScale r m) (by simp only [residueScale]; omega)).symm

/-- The scaled cutoff as a Schwartz multiplier.-/
def scaledAnnularFrequencySchwartz (j : ℤ) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_scaledAnnularFrequencyCutoff j).toSchwartzMap
    (contDiff_scaledAnnularFrequencyCutoff j)

/--
@isnad1 id=eq.0h2v.s5.19d210685a00 from=translated src=- shape=7a784183 vocab=b53e7543
-/
@[simp] theorem scaledAnnularFrequencySchwartz_apply (j : ℤ) (ξ : ℝ) :
    scaledAnnularFrequencySchwartz j ξ = scaledAnnularFrequencyCutoff j ξ := rfl

/-- Multiplication by the concrete annular cutoff on the Fourier side.-/
def annularFourierMultiplier (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ :=
  fun ξ ↦ scaledAnnularFrequencyCutoff j ξ *
    (Lp.fourierTransformₗᵢ ℝ ℂ v) ξ

/--
@isnad1 id=aestrong.0h2v.s8.7998e2a7da70 from=translated src=- shape=827d9555 vocab=68b7dd0e
-/
theorem aestronglyMeasurable_annularFourierMultiplier (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    AEStronglyMeasurable (annularFourierMultiplier j v) volume := by
  exact (contDiff_scaledAnnularFrequencyCutoff j).continuous.aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (Lp.fourierTransformₗᵢ ℝ ℂ v))

/--
@isnad1 id=le.0h2v.s4.e3eb315d2078 from=translated src=- shape=b7998ee9 vocab=0adbffb9
-/
theorem norm_scaledAnnularFrequencyCutoff_le_one (j : ℤ) (ξ : ℝ) :
    ‖scaledAnnularFrequencyCutoff j ξ‖ ≤ 1 := by
  rw [scaledAnnularFrequencyCutoff, annularFrequencyCutoff,
    annularFrequencyCutoffReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg annularFrequencyCutoffData.nonneg]
  exact annularFrequencyCutoffData.le_one

/--
@isnad1 id=memlp.0h2v.s8.ce1d9f0236cf from=translated src=- shape=ee2794eb vocab=67bf638e
-/
theorem memLp_annularFourierMultiplier (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    MemLp (annularFourierMultiplier j v) 2 volume := by
  apply MemLp.of_le_mul (c := 1)
    (Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ v))
  · exact aestronglyMeasurable_annularFourierMultiplier j v
  · filter_upwards with ξ
    unfold annularFourierMultiplier
    rw [norm_mul, one_mul]
    simpa using mul_le_mul_of_nonneg_right
      (norm_scaledAnnularFrequencyCutoff_le_one j ξ)
      (norm_nonneg ((Lp.fourierTransformₗᵢ ℝ ℂ v) ξ))

/-- The concrete Fourier-side annular multiplier as an `L²` element.-/
def annularMultiplierL2 (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : Lp (α := ℝ) ℂ 2 volume :=
  (memLp_annularFourierMultiplier j v).toLp (annularFourierMultiplier j v)

/-- The smooth annular projection, defined by applying the concrete cutoff
on the Fourier side and then inverse Fourier transforming.-/
def annularProjectionL2 (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : Lp (α := ℝ) ℂ 2 volume :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm (annularMultiplierL2 j v)

/--
@isnad1 id=eq.0h2v.s12.307fb37afae5 from=translated src=- shape=c5fbbaaa vocab=39e52a21
-/
theorem fourier_annularProjectionL2 (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    Lp.fourierTransformₗᵢ ℝ ℂ (annularProjectionL2 j v) =
      annularMultiplierL2 j v := by
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _

/--
@isnad1 id=eventual.0h2v.s12.88c155bc462a from=translated src=- shape=84633316 vocab=84e0f203
-/
theorem fourier_annularProjectionL2_ae (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    (fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ (annularProjectionL2 j v)) ξ) =ᵐ[volume]
      annularFourierMultiplier j v := by
  rw [fourier_annularProjectionL2]
  exact (memLp_annularFourierMultiplier j v).coeFn_toLp

/--
@isnad1 id=hasfouri.0h2v.s7.b6ee3b8347ba from=translated src=- shape=a6f9a0e3 vocab=c3c340bd
-/
theorem hasFourierSupportIn_annularProjectionL2 (j : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    KrauseLaceyQuadraticAnnularTail.HasFourierSupportIn
      (annularProjectionL2 j v) (scaledFrequencyAnnulus j) := by
  have hae :
      (fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ (annularProjectionL2 j v)) ξ) =ᵐ[volume]
        annularFourierMultiplier j v := by
    rw [fourier_annularProjectionL2]
    exact (memLp_annularFourierMultiplier j v).coeFn_toLp
  filter_upwards [hae] with ξ hξ
  intro hξout
  rw [hξ]
  have hcut : scaledAnnularFrequencyCutoff j ξ = 0 := by
    by_contra hne
    exact hξout (scaledAnnularFrequencyCutoff_support_subset j hne)
  simp [annularFourierMultiplier, hcut]

/-- Projecting arbitrary `L²` pieces at scales in one residue class produces
the exact pairwise Fourier separation needed by the abstract tail theorem.
@isnad1 id=haspairw.0h2v.s7.fd72b3c55e64 from=translated src=- shape=2cf9762a vocab=e4f71360
-/
theorem hasPairwiseSeparatedFourierSupport_annularProjection_residueScale
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) :
    KrauseLaceyQuadraticAnnularTail.HasPairwiseSeparatedFourierSupport
      (fun n ↦ annularProjectionL2 (residueScale r n) (v n)) := by
  apply KrauseLaceyQuadraticAnnularTail.hasPairwiseSeparatedFourierSupport_of_disjoint_regions
    (E := fun n ↦ scaledFrequencyAnnulus (residueScale r n))
  · exact pairwiseDisjoint_scaledFrequencyAnnulus_residueScale r
  · exact fun n ↦ hasFourierSupportIn_annularProjectionL2 _ _

/-! ## The boundary low-pass cutoff -/

/-- A smooth low-pass cutoff placed three scales below the first omitted
annulus.  The shift by three is chosen so that the cutoff is one on all
earlier annuli in a seven-residue-class split and zero on the current and
all later annuli.-/
def scaledLowPassCutoff (k : ℤ) (ξ : ℝ) : ℂ :=
  (dyadicCutoff (ξ / (2 : ℝ) ^ (k - 3)) : ℂ)

/--
@isnad1 id=contdiff.0h1v.s5.4714d693f243 from=translated src=- shape=caa53032 vocab=fcead810
-/
theorem contDiff_scaledLowPassCutoff (k : ℤ) :
    ContDiff ℝ ∞ (scaledLowPassCutoff k) := by
  exact Complex.ofRealCLM.contDiff.comp
    (dyadicCutoff_smooth.comp (contDiff_id.div_const ((2 : ℝ) ^ (k - 3))))

/--
@isnad1 id=eq.2h3v.s5.02e2b5701d11 from=translated src=- shape=8edf06f0 vocab=cf3336ac
-/
theorem scaledLowPassCutoff_eq_one_on_earlier_annulus
    {j k : ℤ} (hjk : j + 7 ≤ k) {ξ : ℝ}
    (hξ : ξ ∈ scaledFrequencyAnnulus j) :
    scaledLowPassCutoff k ξ = 1 := by
  have hpj : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hpk : 0 < (2 : ℝ) ^ (k - 3) := zpow_pos (by norm_num) (k - 3)
  have hscale : (16 : ℝ) * (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (k - 3) := by
    calc
      (16 : ℝ) * (2 : ℝ) ^ j = (2 : ℝ) ^ (j + 4) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
        ring
      _ ≤ (2 : ℝ) ^ (k - 3) := by
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        omega
  have hξpos : 0 < ξ := by
    have hlower : 0 < (1 / 16 : ℝ) * (2 : ℝ) ^ j := mul_pos (by norm_num) hpj
    exact hlower.trans hξ.1
  have hnorm : |ξ / (2 : ℝ) ^ (k - 3)| ≤ 1 / 4 := by
    rw [abs_of_pos (div_pos hξpos hpk)]
    apply (div_le_iff₀ hpk).2
    nlinarith [hξ.2]
  unfold scaledLowPassCutoff
  rw [dyadicCutoff_eq_one hnorm]
  norm_num

/--
@isnad1 id=eq.2h3v.s5.9214e9b4a9ee from=translated src=- shape=5fb259d6 vocab=9a10671d
-/
theorem scaledLowPassCutoff_eq_zero_on_current_or_later_annulus
    {j k : ℤ} (hkj : k ≤ j) {ξ : ℝ}
    (hξ : ξ ∈ scaledFrequencyAnnulus j) :
    scaledLowPassCutoff k ξ = 0 := by
  have hpj : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hpk : 0 < (2 : ℝ) ^ (k - 3) := zpow_pos (by norm_num) (k - 3)
  have hjm : 0 < (2 : ℝ) ^ (j - 3) := zpow_pos (by norm_num) (j - 3)
  have hscale : (2 : ℝ) ^ (k - 3) ≤ (2 : ℝ) ^ (j - 3) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  have hjid : (2 : ℝ) ^ j = 8 * (2 : ℝ) ^ (j - 3) := by
    calc
      (2 : ℝ) ^ j = (2 : ℝ) ^ ((j - 3) + 3) := by congr 2 <;> omega
      _ = (2 : ℝ) ^ (j - 3) * (2 : ℝ) ^ (3 : ℤ) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = 8 * (2 : ℝ) ^ (j - 3) := by norm_num; ring
  have hξpos : 0 < ξ := by
    have hlower : 0 < (1 / 16 : ℝ) * (2 : ℝ) ^ j := mul_pos (by norm_num) hpj
    exact hlower.trans hξ.1
  have hnorm : 1 / 2 ≤ |ξ / (2 : ℝ) ^ (k - 3)| := by
    rw [abs_of_pos (div_pos hξpos hpk)]
    apply (le_div_iff₀ hpk).2
    nlinarith [hξ.1]
  unfold scaledLowPassCutoff
  rw [dyadicCutoff_eq_zero hnorm]
  norm_num

/--
@isnad1 id=eq.1h3v.s5.95bfe0073529 from=translated src=- shape=7629596c vocab=fde5e806
-/
theorem scaledLowPassCutoff_mul_scaledAnnularFrequencyCutoff_of_earlier
    {j k : ℤ} (hjk : j + 7 ≤ k) (ξ : ℝ) :
    scaledLowPassCutoff k ξ * scaledAnnularFrequencyCutoff j ξ =
      scaledAnnularFrequencyCutoff j ξ := by
  by_cases hcut : scaledAnnularFrequencyCutoff j ξ = 0
  · simp [hcut]
  · rw [scaledLowPassCutoff_eq_one_on_earlier_annulus hjk
      (scaledAnnularFrequencyCutoff_support_subset j hcut), one_mul]

/--
@isnad1 id=eq.1h3v.s5.1f48a7f4cef4 from=translated src=- shape=e52782e8 vocab=8aa05c58
-/
theorem scaledLowPassCutoff_mul_scaledAnnularFrequencyCutoff_of_current_or_later
    {j k : ℤ} (hkj : k ≤ j) (ξ : ℝ) :
    scaledLowPassCutoff k ξ * scaledAnnularFrequencyCutoff j ξ = 0 := by
  by_cases hcut : scaledAnnularFrequencyCutoff j ξ = 0
  · simp [hcut]
  · rw [scaledLowPassCutoff_eq_zero_on_current_or_later_annulus hkj
      (scaledAnnularFrequencyCutoff_support_subset j hcut), zero_mul]

def lowPassFourierMultiplier (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ :=
  fun ξ ↦ scaledLowPassCutoff k ξ *
    (Lp.fourierTransformₗᵢ ℝ ℂ v) ξ

/--
@isnad1 id=le.0h2v.s4.ba00b3a9fd39 from=translated src=- shape=b7998ee9 vocab=513fb635
-/
theorem norm_scaledLowPassCutoff_le_one (k : ℤ) (ξ : ℝ) :
    ‖scaledLowPassCutoff k ξ‖ ≤ 1 := by
  rw [scaledLowPassCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (dyadicCutoff_nonneg _)]
  exact dyadicCutoff_le_one _

/--
@isnad1 id=aestrong.0h2v.s8.bbc5a07c64b4 from=translated src=- shape=827d9555 vocab=53150513
-/
theorem aestronglyMeasurable_lowPassFourierMultiplier (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    AEStronglyMeasurable (lowPassFourierMultiplier k v) volume := by
  exact (contDiff_scaledLowPassCutoff k).continuous.aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (Lp.fourierTransformₗᵢ ℝ ℂ v))

/--
@isnad1 id=memlp.0h2v.s8.5defa91f0d76 from=translated src=- shape=ee2794eb vocab=3fc6eb2a
-/
theorem memLp_lowPassFourierMultiplier (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    MemLp (lowPassFourierMultiplier k v) 2 volume := by
  apply MemLp.of_le_mul (c := 1)
    (Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ v))
  · exact aestronglyMeasurable_lowPassFourierMultiplier k v
  · filter_upwards with ξ
    unfold lowPassFourierMultiplier
    rw [norm_mul, one_mul]
    simpa using mul_le_mul_of_nonneg_right
      (norm_scaledLowPassCutoff_le_one k ξ)
      (norm_nonneg ((Lp.fourierTransformₗᵢ ℝ ℂ v) ξ))

def lowPassMultiplierL2 (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : Lp (α := ℝ) ℂ 2 volume :=
  (memLp_lowPassFourierMultiplier k v).toLp (lowPassFourierMultiplier k v)

/-- The concrete smooth low-pass projection used to recover a prefix from
the total annular sum.-/
def lowPassProjectionL2 (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) : Lp (α := ℝ) ℂ 2 volume :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm (lowPassMultiplierL2 k v)

/--
@isnad1 id=eq.0h2v.s12.4ad6c7c68fd5 from=translated src=- shape=c5fbbaaa vocab=1acd689b
-/
theorem fourier_lowPassProjectionL2 (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    Lp.fourierTransformₗᵢ ℝ ℂ (lowPassProjectionL2 k v) =
      lowPassMultiplierL2 k v := by
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _

/--
@isnad1 id=eventual.0h2v.s12.0c212f5a42ec from=translated src=- shape=84633316 vocab=37d38fe7
-/
theorem fourier_lowPassProjectionL2_ae (k : ℤ)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    (fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ (lowPassProjectionL2 k v)) ξ) =ᵐ[volume]
      lowPassFourierMultiplier k v := by
  rw [fourier_lowPassProjectionL2]
  exact (memLp_lowPassFourierMultiplier k v).coeFn_toLp

/--
@isnad1 id=eq.1h3v.s8.8c4401ba63e8 from=translated src=- shape=1f109697 vocab=e1a140d1
-/
theorem lowPassProjectionL2_annularProjectionL2_of_earlier
    {j k : ℤ} (hjk : j + 7 ≤ k)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    lowPassProjectionL2 k (annularProjectionL2 j v) =
      annularProjectionL2 j v := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_lowPassProjectionL2]
  apply Lp.ext
  filter_upwards [
    (memLp_lowPassFourierMultiplier k (annularProjectionL2 j v)).coeFn_toLp,
    fourier_annularProjectionL2_ae j v] with ξ hlow hann
  have hlow' :
      (lowPassMultiplierL2 k (annularProjectionL2 j v) : ℝ → ℂ) ξ =
        lowPassFourierMultiplier k (annularProjectionL2 j v) ξ := by
    simpa only [lowPassMultiplierL2] using hlow
  rw [hlow']
  unfold lowPassFourierMultiplier
  rw [hann]
  unfold annularFourierMultiplier
  rw [← mul_assoc,
    scaledLowPassCutoff_mul_scaledAnnularFrequencyCutoff_of_earlier hjk]

/--
@isnad1 id=eq.1h3v.s9.0c4b41f03aca from=translated src=- shape=de7ee459 vocab=0cd2d5bb
-/
theorem lowPassProjectionL2_annularProjectionL2_of_current_or_later
    {j k : ℤ} (hkj : k ≤ j)
    (v : Lp (α := ℝ) ℂ 2 volume) :
    lowPassProjectionL2 k (annularProjectionL2 j v) = 0 := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_lowPassProjectionL2, map_zero]
  apply Lp.ext
  filter_upwards [
    (memLp_lowPassFourierMultiplier k (annularProjectionL2 j v)).coeFn_toLp,
    fourier_annularProjectionL2_ae j v] with ξ hlow hann
  have hlow' :
      (lowPassMultiplierL2 k (annularProjectionL2 j v) : ℝ → ℂ) ξ =
        lowPassFourierMultiplier k (annularProjectionL2 j v) ξ := by
    simpa only [lowPassMultiplierL2] using hlow
  rw [hlow']
  unfold lowPassFourierMultiplier
  rw [hann]
  unfold annularFourierMultiplier
  rw [← mul_assoc,
    scaledLowPassCutoff_mul_scaledAnnularFrequencyCutoff_of_current_or_later hkj,
    zero_mul]
  simp

/--
@isnad1 id=eq.0h3v.s11.91f9e68dc4f0 from=translated src=- shape=c93395b9 vocab=30b1ec09
-/
theorem lowPassProjectionL2_add (k : ℤ)
    (v w : Lp (α := ℝ) ℂ 2 volume) :
    lowPassProjectionL2 k (v + w) =
      lowPassProjectionL2 k v + lowPassProjectionL2 k w := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_lowPassProjectionL2, map_add,
    fourier_lowPassProjectionL2, fourier_lowPassProjectionL2]
  apply Lp.ext
  have hFourierAdd :
      (fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ (v + w) : ℝ → ℂ) ξ) =ᵐ[volume]
        fun ξ ↦ (Lp.fourierTransformₗᵢ ℝ ℂ v : ℝ → ℂ) ξ +
          (Lp.fourierTransformₗᵢ ℝ ℂ w : ℝ → ℂ) ξ := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  filter_upwards [
    (memLp_lowPassFourierMultiplier k (v + w)).coeFn_toLp,
    (memLp_lowPassFourierMultiplier k v).coeFn_toLp,
    (memLp_lowPassFourierMultiplier k w).coeFn_toLp,
    hFourierAdd,
    Lp.coeFn_add (lowPassMultiplierL2 k v) (lowPassMultiplierL2 k w)]
      with ξ hvw hv hw hFadd hLadd
  rw [show (lowPassMultiplierL2 k (v + w) : ℝ → ℂ) ξ =
      lowPassFourierMultiplier k (v + w) ξ by
        simpa only [lowPassMultiplierL2] using hvw]
  rw [hLadd]
  change lowPassFourierMultiplier k (v + w) ξ =
    (lowPassMultiplierL2 k v : ℝ → ℂ) ξ +
      (lowPassMultiplierL2 k w : ℝ → ℂ) ξ
  rw [show (lowPassMultiplierL2 k v : ℝ → ℂ) ξ =
      lowPassFourierMultiplier k v ξ by
        simpa only [lowPassMultiplierL2] using hv]
  rw [show (lowPassMultiplierL2 k w : ℝ → ℂ) ξ =
      lowPassFourierMultiplier k w ξ by
        simpa only [lowPassMultiplierL2] using hw]
  simp only [lowPassFourierMultiplier, hFadd, mul_add]

/--
@isnad1 id=eq.0h1v.s10.d08e7194848a from=translated src=- shape=7c0878a5 vocab=fed9a8d1
-/
theorem lowPassProjectionL2_zero (k : ℤ) :
    lowPassProjectionL2 k (0 : Lp (α := ℝ) ℂ 2 volume) = 0 := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_lowPassProjectionL2, map_zero]
  apply Lp.ext
  filter_upwards [(memLp_lowPassFourierMultiplier k 0).coeFn_toLp] with ξ hξ
  rw [show (lowPassMultiplierL2 k 0 : ℝ → ℂ) ξ =
      lowPassFourierMultiplier k 0 ξ by
        simpa only [lowPassMultiplierL2] using hξ]
  simp [lowPassFourierMultiplier]

/--
@isnad1 id=eq.0h4v.s10.5f1cae33dcba from=translated src=- shape=1cd25454 vocab=04eb2cb8
-/
theorem lowPassProjectionL2_finset_sum
    {ι : Type*} (S : Finset ι) (k : ℤ)
    (v : ι → Lp (α := ℝ) ℂ 2 volume) :
    lowPassProjectionL2 k (∑ i ∈ S, v i) =
      ∑ i ∈ S, lowPassProjectionL2 k (v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [lowPassProjectionL2_zero]
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, lowPassProjectionL2_add, ih,
        Finset.sum_insert ha]

/-- The annularly projected piece at the `n`th scale of residue class `r`.-/
def annularResiduePiece (r : Fin 7)
    (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (n : ℕ) :
    Lp (α := ℝ) ℂ 2 volume :=
  annularProjectionL2 (residueScale r n) (v n)

/--
@isnad1 id=eq.1h4v.s8.288f2c654e42 from=translated src=- shape=301f2ce9 vocab=d9402b36
-/
theorem lowPassProjectionL2_annularResiduePiece_of_lt
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume)
    {m n : ℕ} (hmn : m < n) :
    lowPassProjectionL2 (residueScale r n) (annularResiduePiece r v m) =
      annularResiduePiece r v m := by
  apply lowPassProjectionL2_annularProjectionL2_of_earlier
  simp only [residueScale]
  omega

/--
@isnad1 id=eq.1h4v.s9.db2a37ee4018 from=translated src=- shape=e388cb2e vocab=383e660f
-/
theorem lowPassProjectionL2_annularResiduePiece_of_le
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume)
    {m n : ℕ} (hnm : n ≤ m) :
    lowPassProjectionL2 (residueScale r n) (annularResiduePiece r v m) = 0 := by
  apply lowPassProjectionL2_annularProjectionL2_of_current_or_later
  simp only [residueScale]
  omega

/-- Exact prefix recovery in `L²`: the boundary low-pass projection of a
finite total is precisely the sum of the pieces before the boundary index.
@isnad1 id=eq.1h4v.s10.2e0476235450 from=translated src=- shape=ae835877 vocab=6a4b8776
-/
theorem lowPassProjectionL2_finite_total_eq_prefix
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume)
    {n N : ℕ} (hnN : n ≤ N) :
    lowPassProjectionL2 (residueScale r n)
        (∑ m ∈ Finset.range N, annularResiduePiece r v m) =
      ∑ m ∈ Finset.range n, annularResiduePiece r v m := by
  classical
  rw [lowPassProjectionL2_finset_sum]
  calc
    ∑ m ∈ Finset.range N,
        lowPassProjectionL2 (residueScale r n) (annularResiduePiece r v m) =
        ∑ m ∈ Finset.range N,
          if m < n then annularResiduePiece r v m else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hmn : m < n
      · rw [ite_eq_left hmn, lowPassProjectionL2_annularResiduePiece_of_lt r v hmn]
      · rw [ite_eq_right hmn,
          lowPassProjectionL2_annularResiduePiece_of_le r v (Nat.le_of_not_gt hmn)]
    _ = ∑ m ∈ Finset.range n, annularResiduePiece r v m := by
      rw [← Finset.sum_filter]
      congr 1
      ext m
      simp only [Finset.mem_filter, Finset.mem_range]
      omega

/-! ## The inverse-Fourier kernel and its maximal majorant -/

def lowPassFrequencyCutoff (ξ : ℝ) : ℂ := (dyadicCutoff ξ : ℂ)

/--
@isnad1 id=contdiff.0h0v.s5.a38c664cfc70 from=translated src=- shape=352d7a74 vocab=17605a92
-/
theorem contDiff_lowPassFrequencyCutoff :
    ContDiff ℝ ∞ lowPassFrequencyCutoff := by
  exact Complex.ofRealCLM.contDiff.comp dyadicCutoff_smooth

/--
@isnad1 id=hascompa.0h0v.s3.f84d27cf239a from=translated src=- shape=54c8eceb vocab=f80f5a02
-/
theorem hasCompactSupport_lowPassFrequencyCutoff :
    HasCompactSupport lowPassFrequencyCutoff := by
  exact dyadicCutoffData.hasCompactSupport.comp_left rfl

def lowPassFrequencySchwartz : 𝓢(ℝ, ℂ) :=
  hasCompactSupport_lowPassFrequencyCutoff.toSchwartzMap
    contDiff_lowPassFrequencyCutoff

/--
@isnad1 id=eq.0h1v.s5.f54bd7b3525d from=translated src=- shape=58763af0 vocab=629e743e
-/
@[simp] theorem lowPassFrequencySchwartz_apply (ξ : ℝ) :
    lowPassFrequencySchwartz ξ = lowPassFrequencyCutoff ξ := rfl

/-- The fixed physical-space kernel whose Fourier transform is the base
low-pass cutoff.-/
def baseLowPassKernelSchwartz : 𝓢(ℝ, ℂ) :=
  𝓕⁻ lowPassFrequencySchwartz

/-- A concrete uniform quadratic-decay constant for the base Schwartz
kernel.-/
def baseLowPassKernelDecayConstant : ℝ :=
  SchwartzMap.seminorm ℂ 0 0 baseLowPassKernelSchwartz +
    SchwartzMap.seminorm ℂ 2 0 baseLowPassKernelSchwartz

/--
@isnad1 id=le.0h0v.s3.91113b9fcc46 from=translated src=- shape=ff3a10fc vocab=f5b2511c
-/
theorem baseLowPassKernelDecayConstant_nonneg :
    0 ≤ baseLowPassKernelDecayConstant := by
  unfold baseLowPassKernelDecayConstant
  positivity

/--
@isnad1 id=le.0h1v.s6.4981dbb939a7 from=translated src=- shape=2d7f5b9d vocab=753f9680
-/
theorem norm_baseLowPassKernelSchwartz_le (x : ℝ) :
    ‖baseLowPassKernelSchwartz x‖ ≤
      baseLowPassKernelDecayConstant / (1 + x ^ 2) := by
  have h0 := SchwartzMap.norm_le_seminorm ℂ baseLowPassKernelSchwartz x
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ
    baseLowPassKernelSchwartz 2 x
  have hden : 0 < 1 + x ^ 2 := by positivity
  apply (le_div_iff₀ hden).2
  calc
    ‖baseLowPassKernelSchwartz x‖ * (1 + x ^ 2) =
        ‖baseLowPassKernelSchwartz x‖ +
          ‖x‖ ^ 2 * ‖baseLowPassKernelSchwartz x‖ := by
      rw [Real.norm_eq_abs, sq_abs]
      ring
    _ ≤ SchwartzMap.seminorm ℂ 0 0 baseLowPassKernelSchwartz +
        SchwartzMap.seminorm ℂ 2 0 baseLowPassKernelSchwartz :=
      add_le_add h0 h2
    _ = baseLowPassKernelDecayConstant := rfl

/-- The correctly normalized physical kernel at frequency radius
`R = 2^(k-3)`.-/
def scaledLowPassKernel (k : ℤ) (t : ℝ) : ℂ :=
  (((2 : ℝ) ^ (k - 3) : ℝ) : ℂ) *
    baseLowPassKernelSchwartz ((2 : ℝ) ^ (k - 3) * t)

/--
@isnad1 id=measurab.0h1v.s3.4d5262053f6f from=translated src=- shape=7000f90d vocab=5e0a306d
-/
theorem measurable_scaledLowPassKernel (k : ℤ) :
    Measurable (scaledLowPassKernel k) := by
  exact (baseLowPassKernelSchwartz.continuous.comp
    (continuous_const.mul continuous_id)).measurable.const_mul _

/--
@isnad1 id=eq.0h2v.s5.bcfcad44c382 from=translated src=- shape=9ab52306 vocab=d389954e
-/
theorem fourier_scaledLowPassKernel (k : ℤ) (ξ : ℝ) :
    𝓕 (scaledLowPassKernel k) ξ = scaledLowPassCutoff k ξ := by
  let R : ℝ := (2 : ℝ) ^ (k - 3)
  have hR : 0 < R := by dsimp [R]; positivity
  let g : ℝ → ℂ := fun u ↦
    Complex.exp (((-2 * Real.pi * u * (ξ / R) : ℝ) : ℂ) * Complex.I) •
      baseLowPassKernelSchwartz u
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hfun : (fun t : ℝ ↦
      Complex.exp (((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) •
        scaledLowPassKernel k t) =
      fun t ↦ (R : ℂ) * g (R * t) := by
    funext t
    unfold scaledLowPassKernel g
    simp only [R, smul_eq_mul]
    have hphase :
        (((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) =
          (((-2 * Real.pi * ((2 : ℝ) ^ (k - 3) * t) *
            (ξ / (2 : ℝ) ^ (k - 3)) : ℝ) : ℂ) * Complex.I) := by
      congr 1
      norm_cast
      field_simp
    rw [hphase]
    ring
  rw [hfun, MeasureTheory.integral_const_mul,
    Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr hR)]
  rw [Complex.real_smul]
  rw [← mul_assoc]
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ hR.ne']
  norm_num
  have hg : (∫ y : ℝ, g y) =
      𝓕 (baseLowPassKernelSchwartz : ℝ → ℂ) (ξ / R) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
  rw [hg]
  rw [← SchwartzMap.fourier_coe]
  have hinv : 𝓕 baseLowPassKernelSchwartz = lowPassFrequencySchwartz := by
    exact fourier_fourierInv_eq lowPassFrequencySchwartz
  rw [hinv]
  rfl

/--
@isnad1 id=le.0h2v.s5.a80914a61b73 from=translated src=- shape=0c8345d9 vocab=6d0e67cd
-/
theorem norm_scaledLowPassKernel_le_poisson (k : ℤ) (t : ℝ) :
    ‖scaledLowPassKernel k t‖ ≤
      baseLowPassKernelDecayConstant *
        cotlarPoissonKernel ((2 : ℝ) ^ (-(k - 3))) t := by
  let R : ℝ := (2 : ℝ) ^ (k - 3)
  have hR : 0 < R := by dsimp [R]; positivity
  have hC := baseLowPassKernelDecayConstant_nonneg
  calc
    ‖scaledLowPassKernel k t‖ =
        R * ‖baseLowPassKernelSchwartz (R * t)‖ := by
      simp only [scaledLowPassKernel, R, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR]
    _ ≤ R * (baseLowPassKernelDecayConstant / (1 + (R * t) ^ 2)) :=
      mul_le_mul_of_nonneg_left (norm_baseLowPassKernelSchwartz_le _) hR.le
    _ = baseLowPassKernelDecayConstant * cotlarPoissonKernel R⁻¹ t := by
      unfold cotlarPoissonKernel
      field_simp
      <;> ring
    _ = baseLowPassKernelDecayConstant *
        cotlarPoissonKernel ((2 : ℝ) ^ (-(k - 3))) t := by
      rw [show R⁻¹ = (2 : ℝ) ^ (-(k - 3)) by
        simp only [R, zpow_neg]]

/--
@isnad1 id=integrab.0h1v.s5.1f1ff7c379ad from=translated src=- shape=5cae27e5 vocab=72790151
-/
theorem integrable_scaledLowPassKernel (k : ℤ) :
    Integrable (scaledLowPassKernel k) volume := by
  let r : ℝ := (2 : ℝ) ^ (-(k - 3))
  have hr : 0 < r := by dsimp [r]; positivity
  have hdom : Integrable
      (fun t ↦ baseLowPassKernelDecayConstant * cotlarPoissonKernel r t) volume :=
    (HilbertPoissonFourier.integrable_cotlarPoissonKernel hr).const_mul _
  apply Integrable.mono' hdom
    (measurable_scaledLowPassKernel k).aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg baseLowPassKernelDecayConstant_nonneg,
    abs_of_nonneg (cotlarPoissonKernel_nonneg hr.le)] using
      (show ‖scaledLowPassKernel k t‖ ≤
        baseLowPassKernelDecayConstant * cotlarPoissonKernel r t by
          simpa only [r] using norm_scaledLowPassKernel_le_poisson k t)

/-- The inverse-Fourier low-pass kernels, uniformly over every integer
scale, are pointwise dominated by the centered Hardy--Littlewood maximal
operator.  The proof uses the already formalized dyadic-shell majorization
of the Poisson kernel.
@isnad1 id=le.1h3v.s7.9b84393e4fb0 from=translated src=- shape=7aed4ee2 vocab=4750b9ee
-/
theorem enorm_scaledLowPassKernel_convolution_le_maximal
    (k : ℤ) {f : ℝ → ℂ} (hf : Measurable f) (x : ℝ) :
    ‖∫ y, scaledLowPassKernel k (x - y) * f y‖ₑ ≤
      (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) *
        centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  let r : ℝ := (2 : ℝ) ^ (-(k - 3))
  have hr : 0 < r := by dsimp [r]; positivity
  have hC := baseLowPassKernelDecayConstant_nonneg
  calc
    ‖∫ y, scaledLowPassKernel k (x - y) * f y‖ₑ ≤
        ∫⁻ y, ‖scaledLowPassKernel k (x - y) * f y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, (ENNReal.ofReal baseLowPassKernelDecayConstant *
          ENNReal.ofReal (cotlarPoissonKernel r (x - y))) * ‖f y‖ₑ := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [enorm_mul]
      apply mul_le_mul'
      · rw [← ofReal_norm]
        calc
          ENNReal.ofReal ‖scaledLowPassKernel k (x - y)‖ ≤
              ENNReal.ofReal (baseLowPassKernelDecayConstant *
                cotlarPoissonKernel r (x - y)) :=
            ENNReal.ofReal_le_ofReal (by
              simpa only [r] using norm_scaledLowPassKernel_le_poisson k (x - y))
          _ = ENNReal.ofReal baseLowPassKernelDecayConstant *
              ENNReal.ofReal (cotlarPoissonKernel r (x - y)) := by
            rw [ENNReal.ofReal_mul hC]
      · exact le_rfl
    _ = ENNReal.ofReal baseLowPassKernelDecayConstant *
        (∫⁻ y, ENNReal.ofReal (cotlarPoissonKernel r (x - y)) * ‖f y‖ₑ) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro y
      ac_rfl
    _ ≤ ENNReal.ofReal baseLowPassKernelDecayConstant *
        (20 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) := by
      apply mul_le_mul' le_rfl
      exact lintegral_ofReal_cotlarPoissonKernel_mul_le_maximal hr hf.enorm x
    _ = (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) *
        centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by ring

def lowPassKernelConvolution (k : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, scaledLowPassKernel k (x - y) * f y

/--
@isnad1 id=eq.0h3v.s6.1ddeb19e8074 from=translated src=- shape=79935f21 vocab=4231320b
-/
theorem lowPassKernelConvolution_eq_convolution
    (k : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    lowPassKernelConvolution k f x =
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] scaledLowPassKernel k) x := by
  rw [lowPassKernelConvolution, MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards with y
  simp only [ContinuousLinearMap.mul_apply']
  ring

/--
@isnad1 id=integrab.1h2v.s6.6d2d39e345fb from=translated src=- shape=2c930462 vocab=0a421dd4
-/
theorem integrable_lowPassKernelConvolution
    (k : ℤ) {f : ℝ → ℂ} (hf : Integrable f volume) :
    Integrable (lowPassKernelConvolution k f) volume := by
  have hconv := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_scaledLowPassKernel k)
  apply hconv.congr
  filter_upwards with x
  exact (lowPassKernelConvolution_eq_convolution k f x).symm

/-- The centered maximal function of the norm of an `L²` function is itself
an `L²` ENNReal-valued function.  This packages the already proved strong
`L²` maximal inequality for use in convolution estimates.
@isnad1 id=memlp.2h1v.s7.1bf057f7325b from=translated src=- shape=e6c1e6be vocab=31b12865
-/
theorem memLp_two_centeredHardyLittlewoodMaximal_enorm
    {f : ℝ → ℂ} (hfmeas : Measurable f) (hf₂ : MemLp f 2 volume) :
    MemLp (centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ)) 2 volume := by
  let M : ℝ → ℝ≥0∞ :=
    centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ)
  refine ⟨(measurable_centeredHardyLittlewoodMaximal
    hfmeas.enorm).aestronglyMeasurable, ?_⟩
  have hinput : (∫⁻ x, ‖f x‖ₑ ^ 2) < (⊤ : ℝ≥0∞) := by
    rw [← eLpNorm_two_sq_lintegral]
    exact ENNReal.pow_lt_top hf₂.eLpNorm_lt_top
  have hM : (∫⁻ x, M x ^ 2) < (⊤ : ℝ≥0∞) :=
    (centeredHardyLittlewoodMaximal_sq_lintegral_le hfmeas.enorm).trans_lt
      (ENNReal.mul_lt_top (by norm_num) hinput)
  have hp : eLpNorm M 2 volume ^ 2 < (⊤ : ℝ≥0∞) := by
    simpa only [eLpNorm_two_sq_lintegral, enorm_eq_self] using hM
  exact (ENNReal.pow_lt_top_iff.mp hp).resolve_right (by norm_num)

/--
@isnad1 id=memlp.3h2v.s7.660636719f76 from=translated src=- shape=df349d75 vocab=2c796aef
-/
theorem memLp_two_lowPassKernelConvolution
    (k : ℤ) {f : ℝ → ℂ} (hfmeas : Measurable f)
    (hf : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    MemLp (lowPassKernelConvolution k f) 2 volume := by
  let A : ℝ≥0∞ := 20 * ENNReal.ofReal baseLowPassKernelDecayConstant
  have hAtop : A ≠ (⊤ : ℝ≥0∞) := by
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  apply (memLp_two_centeredHardyLittlewoodMaximal_enorm hfmeas hf₂).of_enorm_le_mul
    (c := A.toNNReal)
    (integrable_lowPassKernelConvolution k hf).aestronglyMeasurable
  filter_upwards with x
  rw [ENNReal.coe_toNNReal hAtop]
  change ‖lowPassKernelConvolution k f x‖ₑ ≤
    A * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x
  exact enorm_scaledLowPassKernel_convolution_le_maximal k hfmeas x

/--
@isnad1 id=eq.1h3v.s6.4c3ee285c3e7 from=translated src=- shape=59120567 vocab=4c87baba
-/
theorem fourier_lowPassKernelConvolution
    (k : ℤ) {f : ℝ → ℂ} (hf : Integrable f volume) (ξ : ℝ) :
    𝓕 (lowPassKernelConvolution k f) ξ =
      scaledLowPassCutoff k ξ * 𝓕 f ξ := by
  rw [show lowPassKernelConvolution k f =
      f ⋆[ContinuousLinearMap.mul ℂ ℂ] scaledLowPassKernel k by
    funext x
    exact lowPassKernelConvolution_eq_convolution k f x]
  rw [Real.fourier_mul_convolution_eq hf
      (integrable_scaledLowPassKernel k) ξ,
    fourier_scaledLowPassKernel]
  ring

/-- For an `L¹ ∩ L²` representative, the concrete kernel convolution is
exactly the canonical `L²` low-pass Fourier multiplier.  Both sides are
compared by their canonical `L²` Fourier transforms; the bridge from the
integral Fourier transform is almost-everywhere, as it should be.
@isnad1 id=eq.3h2v.s8.5cd66c77dc97 from=translated src=- shape=579e0b12 vocab=71ab4ecb
-/
theorem lowPassProjectionL2_eq_toLp_lowPassKernelConvolution
    (k : ℤ) {f : ℝ → ℂ} (hfmeas : Measurable f)
    (hf : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    lowPassProjectionL2 k (hf₂.toLp f) =
      (memLp_two_lowPassKernelConvolution k hfmeas hf hf₂).toLp
        (lowPassKernelConvolution k f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [fourier_lowPassProjectionL2]
  apply Lp.ext
  filter_upwards [
    (memLp_lowPassFourierMultiplier k (hf₂.toLp f)).coeFn_toLp,
    HilbertRepresentativeBridge.fourier_toLp_ae_eq
      (integrable_lowPassKernelConvolution k hf)
      (memLp_two_lowPassKernelConvolution k hfmeas hf hf₂),
    HilbertRepresentativeBridge.fourier_toLp_ae_eq hf hf₂]
      with ξ hlow hconv hfourier
  rw [show (lowPassMultiplierL2 k (hf₂.toLp f) : ℝ → ℂ) ξ =
      lowPassFourierMultiplier k (hf₂.toLp f) ξ by
        simpa only [lowPassMultiplierL2] using hlow]
  rw [hconv, fourier_lowPassKernelConvolution k hf ξ]
  unfold lowPassFourierMultiplier
  rw [hfourier]

/-- Canonical measurable representative of the `n`th annular piece in one
of the seven separated residue classes.-/
def annularResidueRepresentative (r : Fin 7)
    (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (n : ℕ) : ℝ → ℂ :=
  annularResiduePiece r v n

/--
@isnad1 id=measurab.0h3v.s7.55ee1fd9f6b1 from=translated src=- shape=1953c4ac vocab=18382e13
-/
theorem measurable_annularResidueRepresentative
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (n : ℕ) :
    Measurable (annularResidueRepresentative r v n) :=
  (Lp.stronglyMeasurable (annularResiduePiece r v n)).measurable

/--
@isnad1 id=memlp.0h3v.s8.4f7c7d99b24a from=translated src=- shape=ab5e9c89 vocab=65bc5114
-/
theorem memLp_annularResidueRepresentative
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (n : ℕ) :
    MemLp (annularResidueRepresentative r v n) 2 volume :=
  Lp.memLp (annularResiduePiece r v n)

/-- For a finite total of annular pieces which is also integrable, every
prefix is almost everywhere convolution by the concrete boundary low-pass
kernel.  This closes the representative-level bridge without imposing any
pointwise choice on `L²` equivalence classes.
@isnad1 id=eventual.2h4v.s8.704393ce476d from=translated src=- shape=42600c3f vocab=e71f2420
-/
theorem annularResiduePrefix_ae_eq_lowPassKernelConvolution
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) {n N : ℕ}
    (hnN : n ≤ N)
    (htotalInt : Integrable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N
        (annularResidueRepresentative r v)) volume) :
    KrauseLaceyQuadraticAnnularTail.finitePiecePrefix
        (annularResidueRepresentative r v) n =ᵐ[volume]
      lowPassKernelConvolution (residueScale r n)
        (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N
          (annularResidueRepresentative r v)) := by
  let u : ℕ → ℝ → ℂ := annularResidueRepresentative r v
  have hu₂ : ∀ j, MemLp (u j) 2 volume :=
    fun j ↦ memLp_annularResidueRepresentative r v j
  have htotalMeas : Measurable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u) :=
    KrauseLaceyQuadraticAnnularTail.measurable_finitePieceTotal
      (fun j _ ↦ measurable_annularResidueRepresentative r v j)
  have htotal₂ : MemLp
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u) 2 volume :=
    KrauseLaceyQuadraticAnnularTail.memLp_finitePieceTotal hu₂
  have htotalLp :
      htotal₂.toLp
          (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u) =
        ∑ m ∈ Finset.range N, annularResiduePiece r v m := by
    simpa only [u, annularResidueRepresentative, Lp.toLp_coeFn] using
      (KrauseLaceyQuadraticAnnularTail.toLp_finitePieceTotal_eq_sum hu₂)
  have hprojection :
      lowPassProjectionL2 (residueScale r n)
          (∑ m ∈ Finset.range N, annularResiduePiece r v m) =
        (memLp_two_lowPassKernelConvolution (residueScale r n)
          htotalMeas htotalInt htotal₂).toLp
            (lowPassKernelConvolution (residueScale r n)
              (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u)) := by
    rw [← htotalLp]
    exact lowPassProjectionL2_eq_toLp_lowPassKernelConvolution
      (residueScale r n) htotalMeas htotalInt htotal₂
  have hLp :
      (∑ m ∈ Finset.range n, annularResiduePiece r v m) =
        (memLp_two_lowPassKernelConvolution (residueScale r n)
          htotalMeas htotalInt htotal₂).toLp
            (lowPassKernelConvolution (residueScale r n)
              (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u)) := by
    rw [← lowPassProjectionL2_finite_total_eq_prefix r v hnN]
    exact hprojection
  have hprefixCoe := Lp.coeFn_finsetSum (Finset.range n)
    (fun m ↦ annularResiduePiece r v m)
  have hLpCoe :
      (⇑(∑ m ∈ Finset.range n, annularResiduePiece r v m) : ℝ → ℂ) =ᵐ[volume]
        ⇑((memLp_two_lowPassKernelConvolution (residueScale r n)
          htotalMeas htotalInt htotal₂).toLp
            (lowPassKernelConvolution (residueScale r n)
              (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u))) := by
    rw [hLp]
  have hconvCoe :=
    (memLp_two_lowPassKernelConvolution (residueScale r n)
      htotalMeas htotalInt htotal₂).coeFn_toLp
  filter_upwards [hprefixCoe, hLpCoe, hconvCoe] with x hprefix hEq hconv
  unfold KrauseLaceyQuadraticAnnularTail.finitePiecePrefix
  calc
    ∑ j ∈ Finset.range n, annularResidueRepresentative r v j x =
        (∑ j ∈ Finset.range n, annularResiduePiece r v j) x := by
      simpa only [annularResidueRepresentative, Finset.sum_apply] using hprefix.symm
    _ = _ := hEq.trans hconv

/-- Fully instantiated a.e. low-pass prefix control for one separated
residue class.  The only application hypothesis is integrability of the
finite total; its `L²` membership is automatic.
@isnad1 id=hasaelow.1h3v.s8.bd58923d3b03 from=translated src=- shape=ef5c508a vocab=60fc95a7
-/
theorem hasAELowPassPrefixControl_annularResidueRepresentative
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (N : ℕ)
    (htotalInt : Integrable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N
        (annularResidueRepresentative r v)) volume) :
    KrauseLaceyQuadraticAnnularTail.HasAELowPassPrefixControl N
      (annularResidueRepresentative r v)
      (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) := by
  intro n hn
  have htotalMeas : Measurable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N
        (annularResidueRepresentative r v)) :=
    KrauseLaceyQuadraticAnnularTail.measurable_finitePieceTotal
      (fun j _ ↦ measurable_annularResidueRepresentative r v j)
  filter_upwards [annularResiduePrefix_ae_eq_lowPassKernelConvolution
    r v hn htotalInt] with x hx
  rw [hx]
  exact enorm_scaledLowPassKernel_convolution_le_maximal
    (residueScale r n) htotalMeas x

/-- Concrete cardinality-free maximal-tail `L²` estimate for one residue
class of annular projections.  Frequency separation, exact low-pass prefix
recovery, the inverse-Fourier convolution identity, and Hardy--Littlewood
control have all been instantiated.
@isnad1 id=le.1h3v.s8.48ab1e55b605 from=translated src=- shape=854798cc vocab=a7eebc81
-/
theorem annularResidueTailMax_sq_lintegral_le_sum
    (r : Fin 7) (v : ℕ → Lp (α := ℝ) ℂ 2 volume) (N : ℕ)
    (htotalInt : Integrable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N
        (annularResidueRepresentative r v)) volume) :
    (∫⁻ x, KrauseLaceyQuadraticAnnularTail.finitePieceTailMax N
      (annularResidueRepresentative r v) x ^ 2) ≤
      (4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ∑ j ∈ Finset.range N,
          ∫⁻ x, ‖annularResidueRepresentative r v j x‖ₑ ^ 2 := by
  apply KrauseLaceyQuadraticAnnularTail.finitePieceTailMax_sq_lintegral_le_sum_ae
    (fun j ↦ measurable_annularResidueRepresentative r v j)
    (fun j ↦ memLp_annularResidueRepresentative r v j)
  · simpa only [annularResidueRepresentative, Lp.toLp_coeFn,
      annularResiduePiece] using
      (hasPairwiseSeparatedFourierSupport_annularProjection_residueScale r v)
  · exact hasAELowPassPrefixControl_annularResidueRepresentative
      r v N htotalInt

/-- Once a pointwise prefix is identified with convolution by the concrete
scaled inverse-Fourier kernel, all analytic hypotheses of
`HasLowPassPrefixControl` are discharged.  In particular, no compact-support
fiction is imposed on the Schwartz kernel: the preceding dyadic-shell
argument supplies the uniform constant.
@isnad1 id=haslowpa.2h3v.s6.b55901d7f981 from=translated src=- shape=60ecc897 vocab=a99f3288
-/
theorem hasLowPassPrefixControl_of_scaledLowPassKernel_representation
    {N : ℕ} {u : ℕ → ℝ → ℂ} (hu : ∀ j, Measurable (u j))
    (boundaryScale : ℕ → ℤ)
    (hprefix : ∀ n ≤ N, ∀ x,
      KrauseLaceyQuadraticAnnularTail.finitePiecePrefix u n x =
        ∫ y, scaledLowPassKernel (boundaryScale n) (x - y) *
          KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u y) :
    KrauseLaceyQuadraticAnnularTail.HasLowPassPrefixControl N u
      (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) := by
  intro n hn x
  rw [hprefix n hn x]
  have htotal : Measurable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u) := by
    apply KrauseLaceyQuadraticAnnularTail.measurable_finitePieceTotal
    exact fun j _ ↦ hu j
  exact enorm_scaledLowPassKernel_convolution_le_maximal
    (boundaryScale n) htotal x

/-- The a.e. representative version of the concrete low-pass adapter.
This is the natural output of `L²` Fourier multiplier identities and is
already sufficient for the maximal-tail `lintegral` theorem.
@isnad1 id=hasaelow.2h3v.s7.371b68488c86 from=translated src=- shape=56bf2a0e vocab=23b49279
-/
theorem hasAELowPassPrefixControl_of_scaledLowPassKernel_representation
    {N : ℕ} {u : ℕ → ℝ → ℂ} (hu : ∀ j, Measurable (u j))
    (boundaryScale : ℕ → ℤ)
    (hprefix : ∀ n ≤ N,
      KrauseLaceyQuadraticAnnularTail.finitePiecePrefix u n =ᵐ[volume]
        fun x ↦ ∫ y, scaledLowPassKernel (boundaryScale n) (x - y) *
          KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u y) :
    KrauseLaceyQuadraticAnnularTail.HasAELowPassPrefixControl N u
      (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) := by
  intro n hn
  have htotal : Measurable
      (KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u) := by
    apply KrauseLaceyQuadraticAnnularTail.measurable_finitePieceTotal
    exact fun j _ ↦ hu j
  filter_upwards [hprefix n hn] with x hx
  rw [hx]
  exact enorm_scaledLowPassKernel_convolution_le_maximal
    (boundaryScale n) htotal x

end
end QuadraticCarleson.KrauseLaceyQuadraticSmoothProjection
