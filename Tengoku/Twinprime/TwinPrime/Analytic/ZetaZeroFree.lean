import Tengoku.Twinprime.TwinPrime.Analytic.ZetaLocalExpansion
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionNonquadraticZeroFree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# An explicit zero-free region for regularized zeta

The entire regularization retains value one at the principal pole. Its
actual zeros provide the selected reciprocal term in three-four-one.
An explicit disk handles small heights; the principal pole contributions
are controlled directly at larger heights.
-/

noncomputable section

open Function Metric MeromorphicOn

namespace TwinPrime.Analytic

/--
@isnad1 id=ne.0h1v.s4.5e4b2f325b55 from=translated src=- shape=d72ec3d6 vocab=a52b4bb2
-/
theorem meromorphicOrderAt_regularizedZeta_ne_top (ρ : ℂ) :
    meromorphicOrderAt regularizedRiemannZeta ρ ≠ ⊤ := by
  have hF : AnalyticOnNhd ℂ regularizedRiemannZeta Set.univ :=
    fun z _ => differentiable_regularizedRiemannZeta.analyticAt z
  apply hF.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (1 : ℂ)) (Set.mem_univ ρ)
  have hn := (differentiable_regularizedRiemannZeta.analyticAt (1 : ℂ)).meromorphicNFAt
  rw [hn.meromorphicOrderAt_eq_zero_iff.mpr (by simp : regularizedRiemannZeta 1 ≠ 0)]
  simp

/--
@isnad1 id=le.2h2v.s6.525b7891a2ff from=translated src=- shape=7e56f093 vocab=6116802f
-/
theorem one_le_regularizedZeta_divisor_of_zero (K : Set ℂ) (ρ : ℂ)
    (hK : ρ ∈ K) (hρ : regularizedRiemannZeta ρ = 0) :
    1 ≤ divisor regularizedRiemannZeta K ρ := by
  have hF : AnalyticOnNhd ℂ regularizedRiemannZeta K :=
    fun z _ => differentiable_regularizedRiemannZeta.analyticAt z
  have hn : MeromorphicNFOn regularizedRiemannZeta K := fun z hz => (hF z hz).meromorphicNFAt
  have heq := hn.zero_set_eq_divisor_support (fun z => meromorphicOrderAt_regularizedZeta_ne_top z)
  have hsupport : ρ ∈ (divisor regularizedRiemannZeta K).support := heq.subset ⟨hK, hρ⟩
  have hnonneg : 0 ≤ divisor regularizedRiemannZeta K ρ := hF.divisor_nonneg ρ
  change divisor regularizedRiemannZeta K ρ ≠ 0 at hsupport
  omega

/--
@isnad1 id=eq.0h2v.s7.eb0f0f33889f from=translated src=- shape=2d405db0 vocab=a1a980c3
-/
theorem localZetaZeroSum_re (c s : ℂ) :
    (localZetaZeroSum c s).re =
      ∑ᶠ ρ, ((divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) / (s - ρ)).re :=
  Complex.reAddGroupHom.map_finsum (localZetaZeroTerm_hasFiniteSupport c s)

/--
@isnad1 id=le.1h3v.s7.c024edeac655 from=translated src=- shape=d57e97d0 vocab=1a6dc97b
-/
theorem regularizedZeta_divisor_term_re_le_zeroSum (c s ρ : ℂ) (hs : 1 < s.re) :
    ((divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) / (s - ρ)).re ≤
      (localZetaZeroSum c s).re := by
  rw [localZetaZeroSum_re]
  apply single_le_finsum ρ
  · apply ((divisor regularizedRiemannZeta (closedBall c (5 / 4))).finiteSupport
      (isCompact_closedBall c (5 / 4))).subset
    intro u hu
    change divisor regularizedRiemannZeta (closedBall c (5 / 4)) u ≠ 0
    intro hD
    exact hu (by simp [hD])
  · exact fun u => regularizedZeta_divisor_term_re_nonneg _ s u hs

/-- A selected actual zero of the entire regularization contributes with
positive integer multiplicity. The pole at one is never counted as a zero.
@isnad1 id=le.3h3v.s7.370b8bfc251f from=translated src=- shape=0ffb5d49 vocab=5fbb7caf
-/
theorem one_div_sub_le_localZetaZeroSum_re_of_zero (β t σ : ℝ)
    (hβ : 3 / 4 ≤ β) (hσ : 1 < σ)
    (hzero : regularizedRiemannZeta ((β : ℂ) + Complex.I * t) = 0) :
    1 / (σ - β) ≤
      (localZetaZeroSum ((2 : ℂ) + Complex.I * t) ((σ : ℂ) + Complex.I * t)).re := by
  let ρ : ℂ := (β : ℂ) + Complex.I * t
  let c : ℂ := (2 : ℂ) + Complex.I * t
  let s : ℂ := (σ : ℂ) + Complex.I * t
  have hβ1 : β < 1 := by simpa [ρ] using regularizedRiemannZeta_zero_re_lt_one ρ hzero
  have hdiff : ρ - c = ((β - 2 : ℝ) : ℂ) := by dsimp [ρ, c]; push_cast; ring
  have hmem : ρ ∈ closedBall c (5 / 4) := by
    rw [mem_closedBall_iff_norm, hdiff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hmult := one_le_regularizedZeta_divisor_of_zero (closedBall c (5 / 4)) ρ hmem hzero
  have hmultR : (1 : ℝ) ≤ divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ := by
    exact_mod_cast hmult
  have heval : s - ρ = ((σ - β : ℝ) : ℂ) := by dsimp [s, ρ]; push_cast; ring
  have hs : 1 < s.re := by simpa [s] using hσ
  calc
    _ ≤ (divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℝ) / (σ - β) :=
      div_le_div_of_nonneg_right hmultR (by linarith)
    _ = ((divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) / (s - ρ)).re := by
      rw [heval, Complex.div_ofReal_re, Complex.intCast_re]
    _ ≤ _ := regularizedZeta_divisor_term_re_le_zeroSum c s ρ hs

/--
@isnad1 id=eq.0h2v.s6.fdfd36c83046 from=translated src=- shape=342a3ca7 vocab=8cbd1687
-/
theorem principal_pole_re_at_height (a t : ℝ) :
    (1 / ((a : ℂ) + Complex.I * t)).re = a / (a ^ 2 + t ^ 2) := by
  simp only [Complex.div_re, Complex.normSq_apply, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/--
@isnad1 id=le.2h2v.s6.408c33e5292a from=translated src=- shape=a68f8ebd vocab=a183a737
-/
theorem principal_pole_re_le_one_seventeenth (a t : ℝ) (ha : 0 < a) (ht : 4 * a ≤ |t|) :
    (1 / ((a : ℂ) + Complex.I * t)).re ≤ 1 / (17 * a) := by
  rw [principal_pole_re_at_height]
  have hsq : 16 * a ^ 2 ≤ t ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : 0 ≤ 4 * a) ht
    nlinarith [sq_abs t]
  apply (div_le_div_iff₀ (by positivity : 0 < a ^ 2 + t ^ 2)
    (by positivity : 0 < 17 * a)).mpr
  nlinarith

/--
@isnad1 id=not.3h2v.s7.40d5e072f738 from=translated src=- shape=378aea26 vocab=70d00927
-/
theorem four_three_five_seventeenths_pole_contradiction {E δ : ℝ} (hE : 0 < E)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (80 * E)) :
    ¬ 4 / (1 / (4 * E) + δ) ≤
      3 / (1 / (4 * E)) + 5 / (17 * (1 / (4 * E))) + E := by
  have ha : 0 < 1 / (4 * E) := by positivity
  have hden : 0 < 1 / (4 * E) + δ := by linarith
  have hsum : 1 / (4 * E) + 1 / (80 * E) = 21 / (80 * E) := by field_simp; ring
  have hbound : 1 / (4 * E) + δ ≤ 21 / (80 * E) := by linarith
  have hlo : 320 * E / 21 ≤ 4 / (1 / (4 * E) + δ) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 320 * E / 21)
    have heq : (320 * E / 21) * (21 / (80 * E)) = 4 := by field_simp; ring
    linarith
  have hr : 3 / (1 / (4 * E)) + 5 / (17 * (1 / (4 * E))) + E = 241 * E / 17 := by
    field_simp
    ring
  rw [hr]
  linarith

def zetaZeroFreeBudget (t : ℝ) : ℝ :=
  120 + 4 * zetaLogBudget t + zetaLogBudget (2 * t)

/--
@isnad1 id=le.0h1v.s3.3575f1dbc973 from=translated src=- shape=8a62b088 vocab=b211da6f
-/
theorem zetaZeroFreeBudget_ge (t : ℝ) : 120 ≤ zetaZeroFreeBudget t := by
  have hZ := zetaLogBudget_nonneg t
  have hZ2 := zetaLogBudget_nonneg (2 * t)
  unfold zetaZeroFreeBudget
  linarith

end TwinPrime.Analytic
