/- This file was machine generated -/

module
public import Tengoku.LeanNct.LeanNct.Auto.Preliminaries.BumpsAndEstimates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Windows and pairs

Formalization of the ``Windows and pairs'' subsection of the reduction argument.
-/

@[expose] public section
namespace Auto

open MeasureTheory Filter
open scoped FourierTransform Real Convolution Pointwise

noncomputable section
/--
**Definition ($(c,N)$-window).**

Let $c > 0$, $N\in\mathbb{N}$. A *$(c,N)$-window* is a Schwartz function
$\phi:\mathbb{R}\to\mathbb{R}$ such that

1. For all $\xi\in \mathbb{R}$, $\widehat{\phi}$ is real and

   $$
   0\le \widehat{\phi}(\xi)\le 1.
   $$

1. For all $\xi\in \mathbb{R}\setminus [-1,1]$ we have

   $$
   \widehat{\phi}(\xi)=0.
   $$

1. For all $\xi\in   [-\frac12,\frac12]$ we have

   $$
   \widehat{\phi}(\xi)=1.
   $$

1. For all $\xi \in [-1,1]$ and all $m\le N$,

   $$
   |\widehat{\phi}^{(m)}(\xi)| \leq c.
   $$-/
def cnWindow (c : ℝ) (N : ℕ) (φ : SchwartzMap ℝ ℝ) : Prop :=
  0 < c ∧
  (∀ ξ : ℝ, ∃ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧
    FourierTransform.fourier (fun x : ℝ => (φ x : ℂ)) ξ = r) ∧
  Function.support (FourierTransform.fourier (fun x : ℝ => (φ x : ℂ))) ⊆
    Set.Icc (-1 : ℝ) 1 ∧
  (∀ ξ ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
    FourierTransform.fourier (fun x : ℝ => (φ x : ℂ)) ξ = 1) ∧
  ∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ∀ m : ℕ, m ≤ N →
    ‖iteratedDeriv m (FourierTransform.fourier (fun x : ℝ => (φ x : ℂ))) ξ‖ ≤ c

/--
**Definition ($(c,N)$-pair).**

Let $c > 0$, $N\in\mathbb{N}$.  A pair $(\phi_0,\phi_1)$ of $(c,N)$-windows is a *$(c,N)$-pair* if

$$
(\widehat{\phi_0})^2+(1-\widehat{\phi_1})^2=1.
$$-/
def cPair (c : ℝ) (N : ℕ) (φ₀ φ₁ : SchwartzMap ℝ ℝ) : Prop :=
  cnWindow c N φ₀ ∧ cnWindow c N φ₁ ∧
    ∀ ξ : ℝ,
      FourierTransform.fourier (fun x : ℝ => (φ₀ x : ℂ)) ξ ^ 2 +
        (1 - FourierTransform.fourier (fun x : ℝ => (φ₁ x : ℂ)) ξ) ^ 2 = 1

/-- The order fixed in Definition `Auto.uniPair`.-/
def N_uniPair : ℕ := 3

/-- The derivative constant fixed in Definition `Auto.uniPair`.-/
def C_uniPair : ℝ := 2 ^ 15

/--
**Definition (Universal pair).**

Set

$$
N_{\text{Universal pair}}=3,
$$

and

$$
C_{\text{Universal pair}}=2^{15}.
$$

A universal pair is a $(C_{\text{Universal pair}},N_{\text{Universal pair}})$-pair.

See also `Auto.uniPair`.-/
def uniPair (φ₀ φ₁ : SchwartzMap ℝ ℝ) : Prop :=
  cPair C_uniPair N_uniPair φ₀ φ₁

/--
**Definition (Windows).**

A function is a window if it is one of the two components of a universal pair.-/
def window (φ : SchwartzMap ℝ ℝ) : Prop :=
  ∃ φ₀ φ₁ : SchwartzMap ℝ ℝ, uniPair φ₀ φ₁ ∧ (φ = φ₀ ∨ φ = φ₁)

/--
For `existsUniversalPair`, Fourier inversion preserves a real-even compact smooth
frequency profile after taking the real part of its inverse transform.
@isnad1 id=eq.5h2v.s7.0d940ac38f2e from=translated src=- shape=07a1b7e4 vocab=499482d3
-/
theorem aux_fourier_re_fourierInv_of_real_even
    (f : ℝ → ℂ) (hcont : Continuous f) (hint : Integrable f)
    (hinvint : Integrable (FourierTransformInv.fourierInv f))
    (hreal : ∀ xi : ℝ, ∃ r : ℝ, f xi = r)
    (heven : ∀ xi : ℝ, f (-xi) = f xi) (xi : ℝ) :
    FourierTransform.fourier
      (fun q => ((FourierTransformInv.fourierInv f q).re : ℂ)) xi = f xi := by
  let g : ℝ → ℝ := fun q => (f q).re
  have hfg : f = fun q => (g q : ℂ) := by
    funext q
    rcases hreal q with ⟨r, hr⟩
    calc
      f q = (r : ℂ) := hr
      _ = ((f q).re : ℂ) := by
        congr 1
        rw [hr]
        simp
      _ = (g q : ℂ) := by rfl
  have hgint : Integrable g := by
    change Integrable (fun q => RCLike.re (f q))
    exact hint.re
  have hgeven : ∀ q : ℝ, g (-q) = g q := fun q =>
    congrArg Complex.re (heven q)
  have him (q : ℝ) : (FourierTransformInv.fourierInv f q).im = 0 := by
    rw [hfg]
    exact aux_diagonalSquareRoot_inverseFourier_real_of_even g hgint hgeven q
  have hinvreal : FourierTransformInv.fourierInv f =
      fun q => ((FourierTransformInv.fourierInv f q).re : ℂ) := by
    funext q
    apply Complex.ext <;> simp [him q]
  have hinv_eq_fourier : FourierTransformInv.fourierInv f =
      FourierTransform.fourier f := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    funext q
    apply Real.fourier_congr_ae
    filter_upwards [] with x
    exact heven x
  have hfourierint : Integrable (FourierTransform.fourier f) := by
    rw [← hinv_eq_fourier]
    exact hinvint
  rw [← hinvreal]
  exact congrFun (hcont.fourier_fourierInv_eq hint hfourierint) xi

/-- An even real-valued Fourier profile has an even inverse Fourier transform.
@isnad1 id=eq.1h2v.s6.05626b91dfe0 from=translated src=- shape=bc48ff2c vocab=d7f702e5
-/
theorem aux_fourierInv_even_of_even (H : ℝ → ℂ)
    (heven : ∀ x : ℝ, H (-x) = H x) (x : ℝ) :
    FourierTransformInv.fourierInv H (-x) = FourierTransformInv.fourierInv H x := by
  have hfourier : FourierTransform.fourier H (-x) = FourierTransform.fourier H x := by
    change FourierTransform.fourier H ((LinearIsometryEquiv.neg ℝ) x) = _
    rw [← Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) H x]
    apply Real.fourier_congr_ae
    filter_upwards [] with y
    simpa [Function.comp_def] using heven y
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
  simpa only [neg_neg] using hfourier.symm

/--
Construct a real even Schwartz function with a prescribed real-even, compactly supported
smooth Fourier profile.
@isnad1 id=ex.4h1v.s8.448ca2e84625 from=translated src=- shape=d345c817 vocab=7561f5c7
-/
theorem exists_real_even_schwartz_fourier_eq
    (H : ℝ → ℂ) (hcompact : HasCompactSupport H)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) H)
    (hreal : ∀ x : ℝ, ∃ r : ℝ, H x = r)
    (heven : ∀ x : ℝ, H (-x) = H x) :
    ∃ phi : SchwartzMap ℝ ℝ,
      (∀ xi : ℝ, FourierTransform.fourier (fun x : ℝ => (phi x : ℂ)) xi = H xi) ∧
      ∀ x : ℝ, phi (-x) = phi x := by
  let HC : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hsmooth
  let G : SchwartzMap ℝ ℂ := FourierTransformInv.fourierInv HC
  let phi : SchwartzMap ℝ ℝ := G.postcompCLM (𝕜 := ℝ) Complex.reCLM
  refine ⟨phi, ?_, ?_⟩
  · intro xi
    have hHC : (HC : ℝ → ℂ) = H := by
      funext x
      rfl
    have hG : (G : ℝ → ℂ) = FourierTransformInv.fourierInv H := by
      change (FourierTransformInv.fourierInv HC : ℝ → ℂ) = _
      rw [SchwartzMap.fourierInv_coe, hHC]
    change FourierTransform.fourier (fun x : ℝ => ((G x).re : ℂ)) xi = H xi
    rw [hG]
    apply aux_fourier_re_fourierInv_of_real_even
    · exact hsmooth.continuous
    · exact hsmooth.continuous.integrable_of_hasCompactSupport hcompact
    · rw [← hG]
      exact G.integrable
    · exact hreal
    · exact heven
  · intro x
    have hHC : (HC : ℝ → ℂ) = H := by
      funext y
      rfl
    have hG : (G : ℝ → ℂ) = FourierTransformInv.fourierInv H := by
      change (FourierTransformInv.fourierInv HC : ℝ → ℂ) = _
      rw [SchwartzMap.fourierInv_coe, hHC]
    change (G (-x)).re = (G x).re
    rw [hG]
    exact congrArg Complex.re (aux_fourierInv_even_of_even H heven x)

/-- For `existsUniversalPair`, package two suitable frequency profiles into a `(c,N)`-pair.
@isnad1 id=ex.16h4v.s9.47bac88bb662 from=translated src=- shape=8ce96839 vocab=f6846efe
-/
theorem aux_exists_cPair_of_profiles
    (c : ℝ) (N : ℕ) (A B : ℝ → ℂ) (hc : 0 < c)
    (hAcompact : HasCompactSupport A) (hAsmooth : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAreal : ∀ xi : ℝ, ∃ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧ A xi = r)
    (hAeven : ∀ xi : ℝ, A (-xi) = A xi)
    (hAsupport : Function.support A ⊆ Set.Icc (-1 : ℝ) 1)
    (hAone : ∀ xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), A xi = 1)
    (hAderiv : ∀ xi ∈ Set.Icc (-1 : ℝ) 1, ∀ m : ℕ, m ≤ N →
      ‖iteratedDeriv m A xi‖ ≤ c)
    (hBcompact : HasCompactSupport B) (hBsmooth : ContDiff ℝ (⊤ : ℕ∞) B)
    (hBreal : ∀ xi : ℝ, ∃ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧ B xi = r)
    (hBeven : ∀ xi : ℝ, B (-xi) = B xi)
    (hBsupport : Function.support B ⊆ Set.Icc (-1 : ℝ) 1)
    (hBone : ∀ xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), B xi = 1)
    (hBderiv : ∀ xi ∈ Set.Icc (-1 : ℝ) 1, ∀ m : ℕ, m ≤ N →
      ‖iteratedDeriv m B xi‖ ≤ c)
    (hpartition : ∀ xi : ℝ, A xi ^ 2 + (1 - B xi) ^ 2 = 1) :
    ∃ phi0 phi1 : SchwartzMap ℝ ℝ, cPair c N phi0 phi1 := by
  obtain ⟨phi0, hphi0, _⟩ := exists_real_even_schwartz_fourier_eq A hAcompact hAsmooth
    (fun xi => by
      rcases hAreal xi with ⟨r, _, hr⟩
      exact ⟨r, hr⟩) hAeven
  obtain ⟨phi1, hphi1, _⟩ := exists_real_even_schwartz_fourier_eq B hBcompact hBsmooth
    (fun xi => by
      rcases hBreal xi with ⟨r, _, hr⟩
      exact ⟨r, hr⟩) hBeven
  have hF0 : FourierTransform.fourier (fun x : ℝ => (phi0 x : ℂ)) = A := by
    funext x
    exact hphi0 x
  have hF1 : FourierTransform.fourier (fun x : ℝ => (phi1 x : ℂ)) = B := by
    funext x
    exact hphi1 x
  refine ⟨phi0, phi1, ?_, ?_, ?_⟩
  · refine ⟨hc, ?_, ?_, ?_, ?_⟩
    · intro xi
      rcases hAreal xi with ⟨r, hr, hAr⟩
      exact ⟨r, hr, by rw [hphi0 xi, hAr]⟩
    · intro xi hxi
      rw [hF0] at hxi
      exact hAsupport hxi
    · intro xi hxi
      rw [hphi0 xi]
      exact hAone xi hxi
    · intro xi hxi m hm
      rw [hF0]
      exact hAderiv xi hxi m hm
  · refine ⟨hc, ?_, ?_, ?_, ?_⟩
    · intro xi
      rcases hBreal xi with ⟨r, hr, hBr⟩
      exact ⟨r, hr, by rw [hphi1 xi, hBr]⟩
    · intro xi hxi
      rw [hF1] at hxi
      exact hBsupport hxi
    · intro xi hxi
      rw [hphi1 xi]
      exact hBone xi hxi
    · intro xi hxi m hm
      rw [hF1]
      exact hBderiv xi hxi m hm
  · intro xi
    rw [hphi0 xi, hphi1 xi]
    exact hpartition xi

/--
A small smooth probability kernel used to turn a finite density into a smooth
frequency profile for `existsUniversalPair`.-/
def aux_uniPairKappa : ContDiffBump (0 : ℝ) :=
  { rIn := 1 / 128
    rOut := 1 / 64
    rIn_pos := by norm_num
    rIn_lt_rOut := by norm_num }

def aux_uniPairK : ℝ → ℝ := aux_uniPairKappa.normed volume
def aux_uniPairDensity : ℝ → ℝ := aux_standardBumpFiniteDensity 4
def aux_uniPairProfile : ℝ → ℝ :=
  aux_uniPairDensity ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK

/--
@isnad1 id=le.0h0v.s5.eef2b58b5d29 from=translated src=- shape=01610d88 vocab=16b324ec
-/
theorem aux_uniPairK_support :
    Function.support aux_uniPairK ⊆ Set.Icc (-(1 / 64 : ℝ)) (1 / 64) := by
  rw [aux_uniPairK, ContDiffBump.support_normed_eq]
  intro x hx
  rw [Metric.mem_ball, Real.dist_eq] at hx
  have hx' : |x| < (1 / 64 : ℝ) := by simpa [aux_uniPairKappa] using hx
  exact abs_le.mp hx'.le

/--
@isnad1 id=le.0h1v.s3.9ad8c0310106 from=translated src=- shape=8a62b088 vocab=536ae394
-/
theorem aux_uniPairK_nonneg (x : ℝ) : 0 ≤ aux_uniPairK x := by
  exact aux_uniPairKappa.nonneg_normed x

/--
@isnad1 id=integrab.0h0v.s4.c35f8d776678 from=translated src=- shape=e14394ff vocab=62100ae6
-/
theorem aux_uniPairK_integrable : Integrable aux_uniPairK := by
  exact aux_uniPairKappa.integrable_normed

/--
@isnad1 id=eq.0h0v.s5.8b9b718f5751 from=translated src=- shape=f0e61117 vocab=aa20504c
-/
theorem aux_uniPairK_mass : ∫ x : ℝ, aux_uniPairK x = 1 := by
  exact aux_uniPairKappa.integral_normed

/--
@isnad1 id=eq.0h1v.s3.30dc344b2856 from=translated src=- shape=cd419dad vocab=60a429d0
-/
theorem aux_uniPairK_even (x : ℝ) : aux_uniPairK (-x) = aux_uniPairK x := by
  simpa [aux_uniPairK] using (aux_uniPairKappa.normed_neg (μ := volume) x)

/--
@isnad1 id=hascompa.0h0v.s3.5e23812584b4 from=translated src=- shape=e3d48bcb vocab=eea16597
-/
theorem aux_uniPairK_compact : HasCompactSupport aux_uniPairK := by
  exact aux_uniPairKappa.hasCompactSupport_normed

/--
@isnad1 id=contdiff.0h0v.s5.7fa8a894f158 from=translated src=- shape=3cea26be vocab=a2076c82
-/
theorem aux_uniPairK_smooth : ContDiff ℝ (⊤ : ℕ∞) aux_uniPairK := by
  exact aux_uniPairKappa.contDiff_normed

/--
@isnad1 id=le.0h0v.s6.8ef9517e7ba5 from=translated src=- shape=096525e8 vocab=1d0ed972
-/
theorem aux_uniPairDensity_support :
    Function.support aux_uniPairDensity ⊆
      Set.Icc (-1 + (1 / 64 : ℝ)) (1 - 1 / 64) := by
  intro x hx
  have h := aux_standardBumpFiniteDensity_support_stated 4 hx
  norm_num at h ⊢
  exact h

/--
@isnad1 id=le.0h0v.s4.8ca043e69fc8 from=translated src=- shape=66c352d6 vocab=63f0a96b
-/
theorem aux_uniPairProfile_support :
    Function.support aux_uniPairProfile ⊆ Set.Icc (-1 : ℝ) 1 := by
  calc
    Function.support aux_uniPairProfile ⊆
        Function.support aux_uniPairDensity + Function.support aux_uniPairK := by
      exact MeasureTheory.support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)
    _ ⊆ Set.Icc (-1 + (1 / 64 : ℝ)) (1 - 1 / 64) +
        Set.Icc (-(1 / 64 : ℝ)) (1 / 64) :=
      Set.add_subset_add aux_uniPairDensity_support aux_uniPairK_support
    _ = Set.Icc (-1 : ℝ) 1 := by rw [Set.Icc_add_Icc] <;> norm_num

/--
@isnad1 id=le.0h1v.s3.d00c6570f718 from=translated src=- shape=8a62b088 vocab=65ed181e
-/
theorem aux_uniPairProfile_nonneg (x : ℝ) : 0 ≤ aux_uniPairProfile x := by
  apply aux_standardBumpConvolution_nonneg aux_uniPairDensity aux_uniPairK
  · exact fun y => aux_standardBumpFiniteDensity_nonneg 4 y
  · exact aux_uniPairK_nonneg

/--
@isnad1 id=le.0h1v.s3.2aee808ed3e8 from=translated src=- shape=b14ee516 vocab=65ed181e
-/
theorem aux_uniPairProfile_le_one (x : ℝ) : aux_uniPairProfile x ≤ 1 := by
  apply aux_standardBumpConvolution_le_one aux_uniPairDensity aux_uniPairK
  · exact aux_standardBumpFiniteDensity_integrable 4
  · exact aux_uniPairK_integrable
  · exact fun y => aux_standardBumpFiniteDensity_nonneg 4 y
  · exact fun y => aux_standardBumpFiniteDensity_le_one 4 y
  · exact aux_uniPairK_nonneg
  · exact aux_uniPairK_mass

/--
@isnad1 id=eq.1h1v.s6.7cda3a7d05ff from=translated src=- shape=312c1e8c vocab=a0c46ebd
-/
theorem aux_uniPairProfile_one (x : ℝ)
    (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) : aux_uniPairProfile x = 1 := by
  apply aux_standardBumpConvolution_eq_one_on aux_uniPairDensity aux_uniPairK
    (-(1 / 2 : ℝ) - 1 / 64) (1 / 2 + 1 / 64) (1 / 64) x
  · exact aux_uniPairK_support
  · exact aux_uniPairK_mass
  · intro z hz
    apply aux_standardBumpFiniteDensity_eq_one_on_stated 4 z
    norm_num at hz ⊢
    exact hz
  · constructor <;> linarith [hx.1, hx.2]

/--
@isnad1 id=eq.0h1v.s3.a210d47585c9 from=translated src=- shape=cd419dad vocab=f10f7e2d
-/
theorem aux_uniPairProfile_even (x : ℝ) :
    aux_uniPairProfile (-x) = aux_uniPairProfile x := by
  apply MeasureTheory.convolution_neg_of_neg_eq (ContinuousLinearMap.mul ℝ ℝ)
  · exact Filter.Eventually.of_forall fun y => aux_standardBumpFiniteDensity_even 4 y
  · exact Filter.Eventually.of_forall fun y => aux_uniPairK_even y

/--
@isnad1 id=contdiff.0h0v.s5.543c47f5a3b1 from=translated src=- shape=3cea26be vocab=93f7f346
-/
theorem aux_uniPairProfile_smooth :
    ContDiff ℝ (⊤ : ℕ∞) aux_uniPairProfile := by
  exact aux_uniPairK_compact.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (aux_standardBumpFiniteDensity_integrable 4).locallyIntegrable aux_uniPairK_smooth

/--
@isnad1 id=hascompa.0h0v.s3.ca7e64b68c47 from=translated src=- shape=e3d48bcb vocab=47ba5f7f
-/
theorem aux_uniPairDensity_compact : HasCompactSupport aux_uniPairDensity := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc aux_uniPairDensity_support

/--
@isnad1 id=integrab.1h1v.s5.7add63f73bc0 from=translated src=- shape=06748d80 vocab=608eaabe
-/
theorem aux_uniPairDensity_iteratedDeriv_integrable (m : ℕ) (hm : m ≤ 3) :
    Integrable (iteratedDeriv m aux_uniPairDensity) := by
  have hcont : Continuous (iteratedDeriv m aux_uniPairDensity) :=
    aux_standardBumpFiniteDensity_four_contDiff.continuous_iteratedDeriv m (by
      exact_mod_cast hm)
  have hcompact : HasCompactSupport (iteratedDeriv m aux_uniPairDensity) := by
    interval_cases m
    · simpa only [iteratedDeriv_zero] using aux_uniPairDensity_compact
    · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        aux_uniPairDensity_compact.deriv
    · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        aux_uniPairDensity_compact.deriv.deriv
    · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        aux_uniPairDensity_compact.deriv.deriv.deriv
  exact hcont.integrable_of_hasCompactSupport hcompact

/--
@isnad1 id=hasderiv.2h2v.s8.9aa30d771761 from=translated src=- shape=4fee7a41 vocab=3ff9ba6d
-/
theorem aux_uniPair_derivative_transfer
    (f : ℝ → ℝ) (hfcompact : HasCompactSupport f) (hfsmooth : ContDiff ℝ 1 f) (x : ℝ) :
    HasDerivAt (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK)
      ((deriv f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK) x) x := by
  exact hfcompact.hasDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
    hfsmooth aux_uniPairK_integrable.locallyIntegrable x

/--
@isnad1 id=eq.3h2v.s8.97cc7aa1f629 from=translated src=- shape=e59f400f vocab=465d9c9c
-/
theorem aux_uniPair_iteratedDeriv_convolution_transfer_three (f : ℝ → ℝ)
    (hfcompact : HasCompactSupport f) (hfsmooth : ContDiff ℝ 3 f) (m : ℕ) (hm : m ≤ 3) :
    iteratedDeriv m (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK) =
      iteratedDeriv m f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK := by
  have hf1 : ContDiff ℝ 1 f := hfsmooth.of_le (by norm_num)
  have hEq1 : deriv (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK) =
      deriv f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK := by
    funext x
    exact (aux_uniPair_derivative_transfer f hfcompact hf1 x).deriv
  have hfsmooth' : ContDiff ℝ (2 + 1) f := by norm_num; exact hfsmooth
  have hfderiv2 : ContDiff ℝ 2 (deriv f) := hfsmooth'.deriv'
  have hEq2 : deriv (deriv (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK)) =
      deriv (deriv f) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK := by
    rw [hEq1]
    funext x
    exact (aux_uniPair_derivative_transfer (deriv f) hfcompact.deriv
      (hfderiv2.of_le (by norm_num)) x).deriv
  have hfderiv2' : ContDiff ℝ (1 + 1) (deriv f) := by norm_num; exact hfderiv2
  have hfderivderiv1 : ContDiff ℝ 1 (deriv (deriv f)) := hfderiv2'.deriv'
  have hEq3 : deriv (deriv (deriv (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK))) =
      deriv (deriv (deriv f)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK := by
    rw [hEq2]
    funext x
    exact (aux_uniPair_derivative_transfer (deriv (deriv f)) hfcompact.deriv.deriv
      hfderivderiv1 x).deriv
  interval_cases m
  · simp
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hEq1
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hEq2
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hEq3

/--
@isnad1 id=le.5h4v.s7.d47d30af401f from=translated src=- shape=dad799e4 vocab=440a1843
-/
theorem aux_uniPair_convolution_abs_le_of_bound (f k : ℝ → ℝ) (C x : ℝ)
    (hf : Integrable f) (hk : Integrable k)
    (hk_nonneg : ∀ t, 0 ≤ k t) (hk_mass : ∫ t : ℝ, k t = 1)
    (hbound : ∀ t, |f t| ≤ C) :
    |(f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] k) x| ≤ C := by
  rw [MeasureTheory.convolution_mul_swap]
  have hprod : Integrable (fun t : ℝ => f (x - t) * k t) := by
    refine (hk.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · exact (hf.comp_sub_left x).aestronglyMeasurable.mul hk.aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs]
      change |f (x - t)| * |k t| ≤ C * k t
      rw [abs_of_nonneg (hk_nonneg t)]
      exact mul_le_mul_of_nonneg_right (hbound (x - t)) (hk_nonneg t)
  calc
    |∫ t : ℝ, f (x - t) * k t| = ‖∫ t : ℝ, f (x - t) * k t‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∫ t : ℝ, ‖f (x - t) * k t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, C * k t := by
      apply integral_mono hprod.norm (hk.const_mul C)
      intro t
      change ‖f (x - t) * k t‖ ≤ C * k t
      rw [norm_mul, Real.norm_eq_abs]
      change |f (x - t)| * |k t| ≤ C * k t
      rw [abs_of_nonneg (hk_nonneg t)]
      exact mul_le_mul_of_nonneg_right (hbound (x - t)) (hk_nonneg t)
    _ = C := by rw [integral_const_mul, hk_mass, mul_one]

/--
@isnad1 id=le.2h2v.s6.a6bde9259644 from=translated src=- shape=fd47b502 vocab=6b886ffc
-/
theorem aux_uniPairProfile_deriv_bound (m : ℕ) (hm : 1 ≤ m) (hm3 : m ≤ 3)
    (x : ℝ) :
    ‖iteratedDeriv m aux_uniPairProfile x‖ ≤
      if m = 1 then 8 else if m = 2 then 128 else 4096 := by
  change ‖iteratedDeriv m
    (aux_uniPairDensity ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] aux_uniPairK) x‖ ≤ _
  rw [aux_uniPair_iteratedDeriv_convolution_transfer_three aux_uniPairDensity
    aux_uniPairDensity_compact aux_standardBumpFiniteDensity_four_contDiff m hm3]
  rw [Real.norm_eq_abs]
  apply aux_uniPair_convolution_abs_le_of_bound _ aux_uniPairK _ x
  · exact aux_uniPairDensity_iteratedDeriv_integrable m hm3
  · exact aux_uniPairK_integrable
  · exact aux_uniPairK_nonneg
  · exact aux_uniPairK_mass
  · intro t
    rcases aux_standardBumpFiniteDensity_four_sharp_iteratedDeriv t with ⟨h1, h2, h3⟩
    interval_cases m
    · simpa [aux_uniPairDensity] using h1
    · simpa [aux_uniPairDensity] using h2
    · simpa [aux_uniPairDensity] using h3

def aux_uniPairPhase (x : ℝ) : ℝ :=
  (Real.pi / 2) * (1 - aux_uniPairProfile x)

def aux_uniPairAReal (x : ℝ) : ℝ := Real.cos (aux_uniPairPhase x)
def aux_uniPairBReal (x : ℝ) : ℝ := 1 - Real.sin (aux_uniPairPhase x)
def aux_uniPairA (x : ℝ) : ℂ := aux_uniPairAReal x
def aux_uniPairB (x : ℝ) : ℂ := aux_uniPairBReal x

/--
@isnad1 id=contdiff.0h0v.s5.273fcded5771 from=translated src=- shape=3cea26be vocab=9bad6a79
-/
theorem aux_uniPairPhase_smooth : ContDiff ℝ (⊤ : ℕ∞) aux_uniPairPhase := by
  unfold aux_uniPairPhase
  exact contDiff_const.mul (contDiff_const.sub aux_uniPairProfile_smooth)

/--
@isnad1 id=contdiff.0h0v.s5.b4b97b083ab0 from=translated src=- shape=3cea26be vocab=9d5cb993
-/
theorem aux_uniPairAReal_smooth : ContDiff ℝ (⊤ : ℕ∞) aux_uniPairAReal := by
  exact Real.contDiff_cos.comp aux_uniPairPhase_smooth

/--
@isnad1 id=contdiff.0h0v.s5.975669c63a3f from=translated src=- shape=3cea26be vocab=6bce7edf
-/
theorem aux_uniPairBReal_smooth : ContDiff ℝ (⊤ : ℕ∞) aux_uniPairBReal := by
  exact contDiff_const.sub (Real.contDiff_sin.comp aux_uniPairPhase_smooth)

/--
@isnad1 id=contdiff.0h0v.s5.3d20cff3b751 from=translated src=- shape=352d7a74 vocab=d187b991
-/
theorem aux_uniPairA_smooth : ContDiff ℝ (⊤ : ℕ∞) aux_uniPairA := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => (aux_uniPairAReal x : ℂ))
  simpa [Function.comp_def] using Complex.ofRealCLM.contDiff.comp aux_uniPairAReal_smooth

/--
@isnad1 id=contdiff.0h0v.s5.a4c398027e65 from=translated src=- shape=352d7a74 vocab=679654ff
-/
theorem aux_uniPairB_smooth : ContDiff ℝ (⊤ : ℕ∞) aux_uniPairB := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => (aux_uniPairBReal x : ℂ))
  simpa [Function.comp_def] using Complex.ofRealCLM.contDiff.comp aux_uniPairBReal_smooth

/--
@isnad1 id=mem.0h1v.s5.8db580b9b8cf from=translated src=- shape=32c532c2 vocab=7bdb6d12
-/
theorem aux_uniPairPhase_mem (x : ℝ) :
    aux_uniPairPhase x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  unfold aux_uniPairPhase
  have h0 : 0 ≤ 1 - aux_uniPairProfile x := sub_nonneg.mpr
    (aux_uniPairProfile_le_one x)
  have h1 : 1 - aux_uniPairProfile x ≤ 1 := by
    linarith [aux_uniPairProfile_nonneg x]
  constructor
  · exact mul_nonneg (by positivity) h0
  · calc
      (Real.pi / 2) * (1 - aux_uniPairProfile x) ≤ (Real.pi / 2) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.pi / 2 := by ring

/--
@isnad1 id=ex.0h1v.s5.07d90be05611 from=translated src=- shape=320e6dbf vocab=89b1030b
-/
theorem aux_uniPairA_real (x : ℝ) :
    ∃ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧ aux_uniPairA x = r := by
  refine ⟨aux_uniPairAReal x, ?_, rfl⟩
  have hp := aux_uniPairPhase_mem x
  constructor
  · apply Real.cos_nonneg_of_mem_Icc
    constructor
    · linarith [hp.1, Real.pi_pos]
    · exact hp.2
  · exact Real.cos_le_one _

/--
@isnad1 id=ex.0h1v.s5.6c32d49c5f8d from=translated src=- shape=320e6dbf vocab=13f1e7e7
-/
theorem aux_uniPairB_real (x : ℝ) :
    ∃ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧ aux_uniPairB x = r := by
  refine ⟨aux_uniPairBReal x, ?_, rfl⟩
  unfold aux_uniPairBReal
  have hp := aux_uniPairPhase_mem x
  constructor
  · exact sub_nonneg.mpr (Real.sin_le_one _)
  · linarith [Real.sin_nonneg_of_nonneg_of_le_pi hp.1
      (by nlinarith [hp.2, Real.pi_pos])]

/--
@isnad1 id=le.0h0v.s4.01cc87c68714 from=translated src=- shape=9a6f0bd2 vocab=6fa6d4f4
-/
theorem aux_uniPairA_support : Function.support aux_uniPairA ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro x hx
  by_contra hnot
  have hprofile : aux_uniPairProfile x = 0 := by
    by_contra hne
    exact hnot (aux_uniPairProfile_support hne)
  have hphase : aux_uniPairPhase x = Real.pi / 2 := by
    rw [aux_uniPairPhase, hprofile]
    ring
  simp only [Function.mem_support, aux_uniPairA] at hx
  norm_cast at hx
  rw [aux_uniPairAReal, hphase, Real.cos_pi_div_two] at hx
  exact hx rfl

/--
@isnad1 id=le.0h0v.s4.965c9647774b from=translated src=- shape=9a6f0bd2 vocab=7732436d
-/
theorem aux_uniPairB_support : Function.support aux_uniPairB ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro x hx
  by_contra hnot
  have hprofile : aux_uniPairProfile x = 0 := by
    by_contra hne
    exact hnot (aux_uniPairProfile_support hne)
  have hphase : aux_uniPairPhase x = Real.pi / 2 := by
    rw [aux_uniPairPhase, hprofile]
    ring
  simp only [Function.mem_support, aux_uniPairB] at hx
  norm_cast at hx
  rw [aux_uniPairBReal, hphase, Real.sin_pi_div_two] at hx
  norm_num at hx

/--
@isnad1 id=eq.1h1v.s6.ab1111789b38 from=translated src=- shape=a8996673 vocab=d516d706
-/
theorem aux_uniPairA_one (x : ℝ)
    (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) : aux_uniPairA x = 1 := by
  have hphase : aux_uniPairPhase x = 0 := by
    rw [aux_uniPairPhase, aux_uniPairProfile_one x hx]
    ring
  rw [aux_uniPairA, aux_uniPairAReal, hphase]
  norm_num

/--
@isnad1 id=eq.1h1v.s6.b3ec59da14b3 from=translated src=- shape=a8996673 vocab=8b54d372
-/
theorem aux_uniPairB_one (x : ℝ)
    (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) : aux_uniPairB x = 1 := by
  have hphase : aux_uniPairPhase x = 0 := by
    rw [aux_uniPairPhase, aux_uniPairProfile_one x hx]
    ring
  rw [aux_uniPairB, aux_uniPairBReal, hphase]
  norm_num

/--
@isnad1 id=eq.0h1v.s3.7fcff42340e2 from=translated src=- shape=8fc7e33b vocab=02c44ef9
-/
theorem aux_uniPairA_even (x : ℝ) : aux_uniPairA (-x) = aux_uniPairA x := by
  unfold aux_uniPairA aux_uniPairAReal aux_uniPairPhase
  rw [aux_uniPairProfile_even]

/--
@isnad1 id=eq.0h1v.s3.082dddb93664 from=translated src=- shape=8fc7e33b vocab=085835a3
-/
theorem aux_uniPairB_even (x : ℝ) : aux_uniPairB (-x) = aux_uniPairB x := by
  unfold aux_uniPairB aux_uniPairBReal aux_uniPairPhase
  rw [aux_uniPairProfile_even]

/--
@isnad1 id=hascompa.0h0v.s3.5d66dd204e8f from=translated src=- shape=54c8eceb vocab=9d3af687
-/
theorem aux_uniPairA_compact : HasCompactSupport aux_uniPairA := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc aux_uniPairA_support

/--
@isnad1 id=hascompa.0h0v.s3.bb87eed0a367 from=translated src=- shape=54c8eceb vocab=fa0fc54b
-/
theorem aux_uniPairB_compact : HasCompactSupport aux_uniPairB := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc aux_uniPairB_support

/--
@isnad1 id=eq.0h1v.s6.3447209bc594 from=translated src=- shape=da32dcc4 vocab=0dae972b
-/
theorem aux_uniPair_partition (x : ℝ) :
    aux_uniPairA x ^ 2 + (1 - aux_uniPairB x) ^ 2 = 1 := by
  unfold aux_uniPairA aux_uniPairB aux_uniPairAReal aux_uniPairBReal
  push_cast
  convert Complex.cos_sq_add_sin_sq (aux_uniPairPhase x : ℂ) using 1; ring

def aux_uniPairPhaseOne (x : ℝ) : ℝ :=
  -(Real.pi / 2) * iteratedDeriv 1 aux_uniPairProfile x

def aux_uniPairPhaseTwo (x : ℝ) : ℝ :=
  -(Real.pi / 2) * iteratedDeriv 2 aux_uniPairProfile x

def aux_uniPairPhaseThree (x : ℝ) : ℝ :=
  -(Real.pi / 2) * iteratedDeriv 3 aux_uniPairProfile x

/--
@isnad1 id=hasderiv.0h2v.s6.688c5b992e06 from=translated src=- shape=6e9f0007 vocab=6b344e6d
-/
theorem aux_uniPairProfile_iteratedDeriv_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n aux_uniPairProfile)
      (iteratedDeriv (n + 1) aux_uniPairProfile x) x := by
  have hdiff : Differentiable ℝ (iteratedDeriv n aux_uniPairProfile) := by
    apply ContDiff.differentiable_iteratedDeriv' n
    exact aux_uniPairProfile_smooth.of_le (by
      exact_mod_cast (show (n + 1 : ℕ∞) ≤ ⊤ by exact le_top))
  simpa only [iteratedDeriv_succ] using (hdiff x).hasDerivAt

/--
@isnad1 id=hasderiv.0h1v.s5.d984a956b926 from=translated src=- shape=475e04ea vocab=225a680f
-/
theorem aux_uniPairPhase_hasDerivAt (x : ℝ) :
    HasDerivAt aux_uniPairPhase (aux_uniPairPhaseOne x) x := by
  have hprofile : HasDerivAt aux_uniPairProfile
      (iteratedDeriv 1 aux_uniPairProfile x) x := by
    simpa only [iteratedDeriv_zero] using aux_uniPairProfile_iteratedDeriv_hasDerivAt 0 x
  have hmain : HasDerivAt
      (fun y : ℝ => -(Real.pi / 2) * aux_uniPairProfile y + Real.pi / 2)
      (aux_uniPairPhaseOne x) x := by
    change HasDerivAt
      (fun y : ℝ => -(Real.pi / 2) * aux_uniPairProfile y + Real.pi / 2)
      (-(Real.pi / 2) * iteratedDeriv 1 aux_uniPairProfile x) x
    exact (hprofile.const_mul (-(Real.pi / 2))).add_const (Real.pi / 2)
  convert hmain using 1
  ext y
  simp only [aux_uniPairPhase]
  ring

/--
@isnad1 id=hasderiv.0h1v.s5.5fc39bea221b from=translated src=- shape=475e04ea vocab=ea354b9c
-/
theorem aux_uniPairPhaseOne_hasDerivAt (x : ℝ) :
    HasDerivAt aux_uniPairPhaseOne (aux_uniPairPhaseTwo x) x := by
  have hprofile : HasDerivAt (iteratedDeriv 1 aux_uniPairProfile)
      (iteratedDeriv 2 aux_uniPairProfile x) x := by
    simpa only [show (1 + 1 : ℕ) = 2 by norm_num] using
      aux_uniPairProfile_iteratedDeriv_hasDerivAt 1 x
  change HasDerivAt
    (fun y : ℝ => -(Real.pi / 2) * iteratedDeriv 1 aux_uniPairProfile y)
    (-(Real.pi / 2) * iteratedDeriv 2 aux_uniPairProfile x) x
  exact hprofile.const_mul (-(Real.pi / 2))

/--
@isnad1 id=hasderiv.0h1v.s5.84d6cc65e7aa from=translated src=- shape=475e04ea vocab=c35ed66f
-/
theorem aux_uniPairPhaseTwo_hasDerivAt (x : ℝ) :
    HasDerivAt aux_uniPairPhaseTwo (aux_uniPairPhaseThree x) x := by
  have hprofile : HasDerivAt (iteratedDeriv 2 aux_uniPairProfile)
      (iteratedDeriv 3 aux_uniPairProfile x) x := by
    simpa only [show (2 + 1 : ℕ) = 3 by norm_num] using
      aux_uniPairProfile_iteratedDeriv_hasDerivAt 2 x
  change HasDerivAt
    (fun y : ℝ => -(Real.pi / 2) * iteratedDeriv 2 aux_uniPairProfile y)
    (-(Real.pi / 2) * iteratedDeriv 3 aux_uniPairProfile x) x
  exact hprofile.const_mul (-(Real.pi / 2))

/--
@isnad1 id=le.0h0v.s5.be05f9262101 from=translated src=- shape=d247c0ad vocab=5b159bee
-/
theorem aux_uniPair_halfPi_abs_le_two : |Real.pi / 2| ≤ (2 : ℝ) := by
  rw [abs_of_nonneg (by positivity)]
  nlinarith [Real.pi_le_four]

/--
@isnad1 id=le.0h1v.s4.3d4468889851 from=translated src=- shape=38becc55 vocab=a0585edd
-/
theorem aux_uniPairPhaseOne_bound (x : ℝ) : |aux_uniPairPhaseOne x| ≤ 16 := by
  have hprofile := aux_uniPairProfile_deriv_bound 1 (by norm_num) (by norm_num) x
  norm_num at hprofile
  have hprofile' : |iteratedDeriv 1 aux_uniPairProfile x| ≤ 8 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hprofile
  rw [aux_uniPairPhaseOne, abs_mul, abs_neg]
  calc
    |Real.pi / 2| * |iteratedDeriv 1 aux_uniPairProfile x| ≤ 2 * 8 :=
      mul_le_mul aux_uniPair_halfPi_abs_le_two hprofile' (abs_nonneg _) (by norm_num)
    _ = 16 := by norm_num

/--
@isnad1 id=le.0h1v.s4.83f7a2940901 from=translated src=- shape=38becc55 vocab=3db44c8b
-/
theorem aux_uniPairPhaseTwo_bound (x : ℝ) : |aux_uniPairPhaseTwo x| ≤ 256 := by
  have hprofile := aux_uniPairProfile_deriv_bound 2 (by norm_num) (by norm_num) x
  norm_num at hprofile
  rw [aux_uniPairPhaseTwo, abs_mul, abs_neg]
  calc
    |Real.pi / 2| * |iteratedDeriv 2 aux_uniPairProfile x| ≤ 2 * 128 :=
      mul_le_mul aux_uniPair_halfPi_abs_le_two hprofile (abs_nonneg _) (by norm_num)
    _ = 256 := by norm_num

/--
@isnad1 id=le.0h1v.s4.ba2950cd1834 from=translated src=- shape=38becc55 vocab=2d8b20c3
-/
theorem aux_uniPairPhaseThree_bound (x : ℝ) : |aux_uniPairPhaseThree x| ≤ 8192 := by
  have hprofile := aux_uniPairProfile_deriv_bound 3 (by norm_num) (by norm_num) x
  norm_num at hprofile
  rw [aux_uniPairPhaseThree, abs_mul, abs_neg]
  calc
    |Real.pi / 2| * |iteratedDeriv 3 aux_uniPairProfile x| ≤ 2 * 4096 :=
      mul_le_mul aux_uniPair_halfPi_abs_le_two hprofile (abs_nonneg _) (by norm_num)
    _ = 8192 := by norm_num

/- Quantitative composition estimates used for the universal-pair profiles. -/
namespace aux_uniPairTrig

def u (H : ℝ → ℝ) : ℝ → ℝ := fun x => (Real.pi / 2) * (1 - H x)
def A (H : ℝ → ℝ) : ℝ → ℝ := Real.cos ∘ u H
def B (H : ℝ → ℝ) : ℝ → ℝ := fun x => 1 - Real.sin (u H x)

/--
@isnad1 id=contdiff.1h2v.s6.ba9751e0bd95 from=translated src=- shape=bf3b315c vocab=cc5a6fc2
-/
theorem u_contDiff {H : ℝ → ℝ} {n : ℕ∞} (hH : ContDiff ℝ n H) :
    ContDiff ℝ n (u H) := by
  unfold u
  fun_prop

/--
@isnad1 id=eq.1h3v.s6.17c461d21f60 from=translated src=- shape=849ba07e vocab=2bc0e461
-/
theorem u_iteratedDeriv {H : ℝ → ℝ} (q : ℕ) (hq : 0 < q) (x : ℝ) :
    iteratedDeriv q (u H) x = -(Real.pi / 2) * iteratedDeriv q H x := by
  unfold u
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_const_sub hq]
  simp only [iteratedDeriv_neg]
  ring

/--
@isnad1 id=le.2h4v.s6.c4f850806271 from=translated src=- shape=16e5e12e vocab=c74d2f8e
-/
theorem u_iteratedDeriv_norm_le {H : ℝ → ℝ} (q : ℕ) (hq : 0 < q) (C : ℝ)
    (hH : ∀ x, ‖iteratedDeriv q H x‖ ≤ C) (x : ℝ) :
    ‖iteratedDeriv q (u H) x‖ ≤ (8 / 5 : ℝ) * C := by
  rw [u_iteratedDeriv q hq]
  calc
    ‖-(Real.pi / 2) * iteratedDeriv q H x‖ = |Real.pi / 2| *
        ‖iteratedDeriv q H x‖ := by rw [norm_mul, Real.norm_eq_abs, abs_neg]
    _ ≤ (8 / 5 : ℝ) * C := by
      gcongr
      · rw [abs_of_nonneg (by positivity)]
        nlinarith [Real.pi_lt_d2]
      · exact hH x

/--
@isnad1 id=le.1h4v.s6.64511f25af81 from=translated src=- shape=c88b355d vocab=b4205d7d
-/
theorem scale_iteratedDeriv_norm_le {H : ℝ → ℝ} (q : ℕ) (C : ℝ)
    (hH : ∀ x, ‖iteratedDeriv q H x‖ ≤ C) (x : ℝ) :
    ‖-(Real.pi / 2) * iteratedDeriv q H x‖ ≤ (8 / 5 : ℝ) * C := by
  calc
    ‖-(Real.pi / 2) * iteratedDeriv q H x‖ = |Real.pi / 2| *
        ‖iteratedDeriv q H x‖ := by rw [norm_mul, Real.norm_eq_abs, abs_neg]
    _ ≤ (8 / 5 : ℝ) * C := by
      gcongr
      · rw [abs_of_nonneg (by positivity)]
        nlinarith [Real.pi_lt_d2]
      · exact hH x

/--
@isnad1 id=eq.1h2v.s7.bd9586ab14f7 from=translated src=- shape=e04236ca vocab=54a0905c
-/
theorem u_deriv_eq {H : ℝ → ℝ} (_hH : ContDiff ℝ 1 H) (x : ℝ) :
    deriv (u H) x = -(Real.pi / 2) * iteratedDeriv 1 H x := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using u_iteratedDeriv (H := H) 1
    (by norm_num) x

/--
@isnad1 id=le.4h3v.s7.2449d539885b from=translated src=- shape=fefc437f vocab=6f36de17
-/
theorem comp_deriv_bound_one (g H : ℝ → ℝ)
    (hg : Differentiable ℝ g) (hH : ContDiff ℝ 1 H)
    (hg1 : ∀ x, ‖deriv g x‖ ≤ 1)
    (hH1 : ∀ x, ‖iteratedDeriv 1 H x‖ ≤ 8) (x : ℝ) :
    ‖iteratedDeriv 1 (g ∘ u H) x‖ ≤ 64 / 5 := by
  rw [iteratedDeriv_succ, iteratedDeriv_zero, deriv_comp x (hg.differentiableAt)
    ((u_contDiff hH).differentiable_one.differentiableAt), u_deriv_eq hH]
  calc
    ‖deriv g (u H x) * (-(Real.pi / 2) * iteratedDeriv 1 H x)‖ =
        ‖deriv g (u H x)‖ * ‖-(Real.pi / 2) * iteratedDeriv 1 H x‖ := norm_mul _ _
    _ ≤ 1 * ((8 / 5 : ℝ) * 8) := by
      exact mul_le_mul (hg1 _) (scale_iteratedDeriv_norm_le 1 8 hH1 x)
        (norm_nonneg _) (by norm_num)
    _ = 64 / 5 := by norm_num

/--
@isnad1 id=le.5h3v.s8.5ba4f2742fa7 from=translated src=- shape=1c02deb2 vocab=c9003f9a
-/
theorem comp_deriv_bound_two (g H : ℝ → ℝ)
    (hg : ContDiff ℝ 2 g) (hH : ContDiff ℝ 2 H)
    (hg2 : ∀ q : ℕ, q ≤ 2 → ∀ x, ‖iteratedDeriv q g x‖ ≤ 1)
    (hH1 : ∀ x, ‖iteratedDeriv 1 H x‖ ≤ 8)
    (hH2 : ∀ x, ‖iteratedDeriv 2 H x‖ ≤ 128) (x : ℝ) :
    ‖iteratedDeriv 2 (g ∘ u H) x‖ ≤ 9216 / 25 := by
  rw [iteratedDeriv_comp_two (hg.contDiffAt) ((u_contDiff hH).contDiffAt)]
  have hu1 : ‖deriv (u H) x‖ ≤ 64 / 5 := by
    rw [u_deriv_eq (hH.of_le (by norm_num))]
    simpa only [show (8 / 5 : ℝ) * 8 = 64 / 5 by norm_num] using
      scale_iteratedDeriv_norm_le 1 8 hH1 x
  have hu2 : ‖iteratedDeriv 2 (u H) x‖ ≤ 1024 / 5 := by
    simpa only [show (8 / 5 : ℝ) * 128 = 1024 / 5 by norm_num] using
      u_iteratedDeriv_norm_le 2 (by norm_num) 128 hH2 x
  calc
    ‖iteratedDeriv 2 g (u H x) * deriv (u H) x ^ 2 +
        deriv g (u H x) * iteratedDeriv 2 (u H) x‖ ≤
        ‖iteratedDeriv 2 g (u H x)‖ * ‖deriv (u H) x‖ ^ 2 +
          ‖deriv g (u H x)‖ * ‖iteratedDeriv 2 (u H) x‖ := by
      calc
        _ ≤ ‖iteratedDeriv 2 g (u H x) * deriv (u H) x ^ 2‖ +
            ‖deriv g (u H x) * iteratedDeriv 2 (u H) x‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul, norm_pow, norm_mul]
    _ ≤ 1 * (64 / 5 : ℝ) ^ 2 + 1 * (1024 / 5 : ℝ) := by
      apply add_le_add
      · calc
          ‖iteratedDeriv 2 g (u H x)‖ * ‖deriv (u H) x‖ ^ 2 ≤
              1 * ‖deriv (u H) x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hg2 2 (by norm_num) _) (sq_nonneg _)
          _ ≤ 1 * (64 / 5 : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu1 2) zero_le_one
      · calc
          ‖deriv g (u H x)‖ * ‖iteratedDeriv 2 (u H) x‖ ≤
              1 * ‖iteratedDeriv 2 (u H) x‖ :=
            mul_le_mul_of_nonneg_right
              (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
                hg2 1 (by norm_num) _)
              (norm_nonneg _)
          _ ≤ 1 * (1024 / 5 : ℝ) := mul_le_mul_of_nonneg_left hu2 zero_le_one
    _ = 9216 / 25 := by norm_num

/--
@isnad1 id=le.6h3v.s8.b8f44970ac5f from=translated src=- shape=627c0665 vocab=c9003f9a
-/
theorem comp_deriv_bound_three (g H : ℝ → ℝ)
    (hg : ContDiff ℝ 3 g) (hH : ContDiff ℝ 3 H)
    (hg3 : ∀ q : ℕ, q ≤ 3 → ∀ x, ‖iteratedDeriv q g x‖ ≤ 1)
    (hH1 : ∀ x, ‖iteratedDeriv 1 H x‖ ≤ 8)
    (hH2 : ∀ x, ‖iteratedDeriv 2 H x‖ ≤ 128)
    (hH3 : ∀ x, ‖iteratedDeriv 3 H x‖ ≤ 4096) (x : ℝ) :
    ‖iteratedDeriv 3 (g ∘ u H) x‖ ≤ 2064384 / 125 := by
  rw [iteratedDeriv_comp_three (hg.contDiffAt) ((u_contDiff hH).contDiffAt)]
  have hu1 : ‖deriv (u H) x‖ ≤ 64 / 5 := by
    rw [u_deriv_eq (hH.of_le (by norm_num))]
    simpa only [show (8 / 5 : ℝ) * 8 = 64 / 5 by norm_num] using
      scale_iteratedDeriv_norm_le 1 8 hH1 x
  have hu2 : ‖iteratedDeriv 2 (u H) x‖ ≤ 1024 / 5 := by
    simpa only [show (8 / 5 : ℝ) * 128 = 1024 / 5 by norm_num] using
      u_iteratedDeriv_norm_le 2 (by norm_num) 128 hH2 x
  have hu3 : ‖iteratedDeriv 3 (u H) x‖ ≤ 32768 / 5 := by
    simpa only [show (8 / 5 : ℝ) * 4096 = 32768 / 5 by norm_num] using
      u_iteratedDeriv_norm_le 3 (by norm_num) 4096 hH3 x
  calc
    ‖iteratedDeriv 3 g (u H x) * deriv (u H) x ^ 3 +
        3 * iteratedDeriv 2 g (u H x) * iteratedDeriv 2 (u H) x * deriv (u H) x +
        deriv g (u H x) * iteratedDeriv 3 (u H) x‖ ≤
        ‖iteratedDeriv 3 g (u H x)‖ * ‖deriv (u H) x‖ ^ 3 +
          3 * ‖iteratedDeriv 2 g (u H x)‖ * ‖iteratedDeriv 2 (u H) x‖ *
            ‖deriv (u H) x‖ +
          ‖deriv g (u H x)‖ * ‖iteratedDeriv 3 (u H) x‖ := by
      calc
        _ ≤ ‖iteratedDeriv 3 g (u H x) * deriv (u H) x ^ 3 +
              3 * iteratedDeriv 2 g (u H x) * iteratedDeriv 2 (u H) x * deriv (u H) x‖ +
            ‖deriv g (u H x) * iteratedDeriv 3 (u H) x‖ := norm_add_le _ _
        _ ≤ (‖iteratedDeriv 3 g (u H x) * deriv (u H) x ^ 3‖ +
              ‖3 * iteratedDeriv 2 g (u H x) * iteratedDeriv 2 (u H) x *
                deriv (u H) x‖) +
            ‖deriv g (u H x) * iteratedDeriv 3 (u H) x‖ := by
          gcongr
          exact norm_add_le _ _
        _ = _ := by simp only [norm_mul, norm_pow, Real.norm_ofNat]
    _ ≤ 1 * (64 / 5 : ℝ) ^ 3 + 3 * 1 * (1024 / 5 : ℝ) * (64 / 5 : ℝ) +
        1 * (32768 / 5 : ℝ) := by
      apply add_le_add
      · apply add_le_add
        · calc
            ‖iteratedDeriv 3 g (u H x)‖ * ‖deriv (u H) x‖ ^ 3 ≤
                1 * ‖deriv (u H) x‖ ^ 3 :=
              mul_le_mul_of_nonneg_right (hg3 3 (by norm_num) _)
                (pow_nonneg (norm_nonneg _) _)
            _ ≤ 1 * (64 / 5 : ℝ) ^ 3 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu1 3) zero_le_one
        · calc
            3 * ‖iteratedDeriv 2 g (u H x)‖ * ‖iteratedDeriv 2 (u H) x‖ *
                ‖deriv (u H) x‖ =
                3 * (‖iteratedDeriv 2 g (u H x)‖ * ‖iteratedDeriv 2 (u H) x‖) *
                  ‖deriv (u H) x‖ := by ring
            _ ≤ 3 * (1 * ‖iteratedDeriv 2 (u H) x‖) * ‖deriv (u H) x‖ := by
              gcongr
              exact hg3 2 (by norm_num) _
            _ = 3 * (‖iteratedDeriv 2 (u H) x‖ * ‖deriv (u H) x‖) := by ring
            _ ≤ 3 * ((1024 / 5 : ℝ) * (64 / 5 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul hu2 hu1 (norm_nonneg _) (by norm_num)) (by norm_num)
            _ = 3 * 1 * (1024 / 5 : ℝ) * (64 / 5 : ℝ) := by ring
      · calc
          ‖deriv g (u H x)‖ * ‖iteratedDeriv 3 (u H) x‖ ≤
              1 * ‖iteratedDeriv 3 (u H) x‖ :=
            mul_le_mul_of_nonneg_right
              (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
                hg3 1 (by norm_num) _)
              (norm_nonneg _)
          _ ≤ 1 * (32768 / 5 : ℝ) := mul_le_mul_of_nonneg_left hu3 zero_le_one
    _ = 2064384 / 125 := by norm_num

/--
@isnad1 id=and.4h2v.s8.14f59323596d from=translated src=- shape=dd1332f3 vocab=55c7bcaf
-/
theorem profiles_deriv_bound {H : ℝ → ℝ} (hH : ContDiff ℝ 3 H)
    (hH1 : ∀ x, ‖iteratedDeriv 1 H x‖ ≤ 8)
    (hH2 : ∀ x, ‖iteratedDeriv 2 H x‖ ≤ 128)
    (hH3 : ∀ x, ‖iteratedDeriv 3 H x‖ ≤ 4096) (x : ℝ) :
    (∀ m : ℕ, 1 ≤ m → m ≤ 3 → ‖iteratedDeriv m (A H) x‖ ≤ 2 ^ 15) ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ 3 → ‖iteratedDeriv m (B H) x‖ ≤ 2 ^ 15) := by
  have hcos : ∀ q : ℕ, q ≤ 3 → ∀ y : ℝ, ‖iteratedDeriv q Real.cos y‖ ≤ 1 := by
    intro q _ y
    rw [Real.norm_eq_abs]
    exact Real.abs_iteratedDeriv_cos_le_one q y
  have hsin : ∀ q : ℕ, q ≤ 3 → ∀ y : ℝ, ‖iteratedDeriv q Real.sin y‖ ≤ 1 := by
    intro q _ y
    rw [Real.norm_eq_abs]
    exact Real.abs_iteratedDeriv_sin_le_one q y
  have hcos2 : ContDiff ℝ 2 Real.cos := Real.contDiff_cos
  have hcos3 : ContDiff ℝ 3 Real.cos := Real.contDiff_cos
  have hsin2 : ContDiff ℝ 2 Real.sin := Real.contDiff_sin
  have hsin3 : ContDiff ℝ 3 Real.sin := Real.contDiff_sin
  constructor
  · intro m _ hm3
    interval_cases m
    · simpa only [A] using
        (comp_deriv_bound_one Real.cos H Real.differentiable_cos
          (hH.of_le (by norm_num))
          (fun y => by
            simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hcos 1 (by norm_num) y)
          hH1 x).trans (by norm_num)
    · simpa only [A] using
        (comp_deriv_bound_two Real.cos H hcos2
          (hH.of_le (by norm_num))
          (fun q hq y => hcos q (le_trans hq (by norm_num)) y)
          hH1 hH2 x).trans (by norm_num)
    · simpa only [A] using
        (comp_deriv_bound_three Real.cos H hcos3 hH hcos hH1 hH2 hH3 x).trans (by norm_num)
  · intro m hm _
    have hsin1 : ∀ y : ℝ, ‖deriv Real.sin y‖ ≤ 1 := fun y => by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hsin 1 (by norm_num) y
    have hbound : ‖iteratedDeriv m (Real.sin ∘ u H) x‖ ≤ 2 ^ 15 := by
      interval_cases m
      · exact (comp_deriv_bound_one Real.sin H Real.differentiable_sin
          (hH.of_le (by norm_num)) hsin1 hH1 x).trans (by norm_num)
      · exact (comp_deriv_bound_two Real.sin H hsin2
          (hH.of_le (by norm_num)) (fun q hq y => hsin q (le_trans hq (by norm_num)) y)
          hH1 hH2 x).trans (by norm_num)
      · exact (comp_deriv_bound_three Real.sin H hsin3 hH hsin hH1 hH2 hH3 x).trans (by norm_num)
    rw [show B H = fun y => 1 - (Real.sin ∘ u H) y by rfl,
      iteratedDeriv_const_sub hm 1, iteratedDeriv_neg, norm_neg]
    exact hbound

/--
@isnad1 id=and.5h3v.s8.0e72bde8f4dc from=translated src=- shape=7cfeffa6 vocab=c4b3ecac
-/
theorem profiles_complex_deriv_bound {H : ℝ → ℝ}
    (hH : ContDiff ℝ 4 H)
    (hH1 : ∀ x, ‖iteratedDeriv 1 H x‖ ≤ 8)
    (hH2 : ∀ x, ‖iteratedDeriv 2 H x‖ ≤ 128)
    (hH3 : ∀ x, ‖iteratedDeriv 3 H x‖ ≤ 4096)
    (m : ℕ) (hm : m ≤ 3) (x : ℝ) :
    ‖iteratedDeriv m (fun y => (A H y : ℂ)) x‖ ≤ 2 ^ 15 ∧
      ‖iteratedDeriv m (fun y => (B H y : ℂ)) x‖ ≤ 2 ^ 15 := by
  have hA : ContDiff ℝ 4 (A H) := (u_contDiff hH).cos
  have hB : ContDiff ℝ 4 (B H) := by
    unfold B
    exact contDiff_const.sub (u_contDiff hH).sin
  have hm4 : m + 1 ≤ 4 := by omega
  have hAm : ContDiff ℝ (m + 1) (A H) := hA.of_le (by exact_mod_cast hm4)
  have hBm : ContDiff ℝ (m + 1) (B H) := hB.of_le (by exact_mod_cast hm4)
  rw [aux_gaussianBumpEstimate_iteratedDeriv_ofReal m (A H) hAm x, Complex.norm_real,
    aux_gaussianBumpEstimate_iteratedDeriv_ofReal m (B H) hBm x, Complex.norm_real]
  have hreal := profiles_deriv_bound (hH.of_le (by norm_num)) hH1 hH2 hH3 x
  constructor
  · interval_cases m
    · change |Real.cos (u H x)| ≤ (2 : ℝ) ^ 15
      exact (Real.abs_cos_le_one _).trans (by norm_num)
    · exact hreal.1 1 (by norm_num) (by norm_num)
    · exact hreal.1 2 (by norm_num) (by norm_num)
    · exact hreal.1 3 (by norm_num) (by norm_num)
  · interval_cases m
    · change |1 - Real.sin (u H x)| ≤ (2 : ℝ) ^ 15
      calc
        |1 - Real.sin (u H x)| = |1 + -Real.sin (u H x)| := by rw [sub_eq_add_neg]
        _ ≤ |1| + |-Real.sin (u H x)| := abs_add_le _ _
        _ ≤ 1 + 1 := by
          rw [abs_neg]
          apply add_le_add
          · norm_num
          · exact Real.abs_sin_le_one _
        _ ≤ (2 : ℝ) ^ 15 := by norm_num
    · exact hreal.2 1 (by norm_num) (by norm_num)
    · exact hreal.2 2 (by norm_num) (by norm_num)
    · exact hreal.2 3 (by norm_num) (by norm_num)

end aux_uniPairTrig

/--
@isnad1 id=and.1h2v.s6.3d76e73fda90 from=translated src=- shape=ec8ac169 vocab=402e952c
-/
theorem aux_uniPair_profiles_deriv_bound (m : ℕ) (hm : m ≤ 3) (x : ℝ) :
    ‖iteratedDeriv m aux_uniPairA x‖ ≤ C_uniPair ∧
      ‖iteratedDeriv m aux_uniPairB x‖ ≤ C_uniPair := by
  have hprofile4 : ContDiff ℝ 4 aux_uniPairProfile := by
    apply aux_uniPairProfile_smooth.of_le
    exact WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ by exact le_top)
  have hprofile1 : ∀ y : ℝ, ‖iteratedDeriv 1 aux_uniPairProfile y‖ ≤ 8 := by
    intro y
    have h := aux_uniPairProfile_deriv_bound 1 (by norm_num) (by norm_num) y
    norm_num at h
    simpa [Real.norm_eq_abs] using h
  have hprofile2 : ∀ y : ℝ, ‖iteratedDeriv 2 aux_uniPairProfile y‖ ≤ 128 := by
    intro y
    have h := aux_uniPairProfile_deriv_bound 2 (by norm_num) (by norm_num) y
    norm_num at h
    simpa [Real.norm_eq_abs] using h
  have hprofile3 : ∀ y : ℝ, ‖iteratedDeriv 3 aux_uniPairProfile y‖ ≤ 4096 := by
    intro y
    have h := aux_uniPairProfile_deriv_bound 3 (by norm_num) (by norm_num) y
    norm_num at h
    simpa [Real.norm_eq_abs] using h
  have hmain := aux_uniPairTrig.profiles_complex_deriv_bound hprofile4 hprofile1 hprofile2
    hprofile3 m hm x
  have hAeq : (fun y => (aux_uniPairTrig.A aux_uniPairProfile y : ℂ)) = aux_uniPairA := by
    rfl
  have hBeq : (fun y => (aux_uniPairTrig.B aux_uniPairProfile y : ℂ)) = aux_uniPairB := by
    rfl
  rw [hAeq, hBeq] at hmain
  simpa [C_uniPair] using hmain

/--
**Lemma (Existence of a universal pair).**

There exists a universal pair.
@isnad1 id=ex.0h0v.s6.993f85f6fa43 from=translated src=- shape=8fdac9f3 vocab=d13ab3b4
-/
theorem existsUniversalPair : ∃ φ₀ φ₁ : SchwartzMap ℝ ℝ, uniPair φ₀ φ₁ := by
  exact aux_exists_cPair_of_profiles C_uniPair N_uniPair aux_uniPairA aux_uniPairB
    (by norm_num [C_uniPair])
    aux_uniPairA_compact aux_uniPairA_smooth aux_uniPairA_real aux_uniPairA_even
    aux_uniPairA_support aux_uniPairA_one
    (fun xi _ m hm =>
      (aux_uniPair_profiles_deriv_bound m (by simpa [N_uniPair] using hm) xi).1)
    aux_uniPairB_compact aux_uniPairB_smooth aux_uniPairB_real aux_uniPairB_even
    aux_uniPairB_support aux_uniPairB_one
    (fun xi _ m hm =>
      (aux_uniPair_profiles_deriv_bound m (by simpa [N_uniPair] using hm) xi).2)
    aux_uniPair_partition

end

end Auto
