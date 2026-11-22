import Tengoku.NavierStokesEuler.Euler.MeanBoundaryDerivative
import Tengoku.Seed.Analysis.Calculus.ContDiff.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Full spatial-parameter smoothness of the actual localized Newtonian operators. -/

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest Filter
open scoped ContDiff Topology

/--
@isnad1 id=eq.0h3v.s6.0fa52fe163a8 from=translated src=- shape=69b0a24e vocab=ae925940
-/
theorem Cutoff.translate_add (χ : Cutoff) (a b : Space) :
    (χ.translate a).translate b = χ.translate (a+b) := by
  apply Cutoff.ext
  funext x
  change χ.field ((x+b)+a) = χ.field (x+(a+b))
  congr 1
  abel

/--
@isnad1 id=eq.0h3v.s4.ab186db4c103 from=translated src=- shape=b0b12c89 vocab=5f3f00c4
-/
theorem Cutoff.directional_translate (χ : Cutoff) (a b : Space) :
    (χ.translate b).directional a = (χ.directional a).translate b := by
  apply Cutoff.ext
  funext x
  change (fderiv ℝ (fun y => χ.field (y+b)) x) a = (fderiv ℝ χ.field (x+b)) a
  rw [fderiv_comp_add_right]

/--
@isnad1 id=eq.0h3v.s6.2062fa7e25cf from=translated src=- shape=4f2ea1dd vocab=f80fb30f
-/
theorem Cutoff.directional_add (χ : Cutoff) (a b : Space) :
    χ.directional (a+b) = (χ.directional a).add (χ.directional b) := by
  apply Cutoff.ext
  exact funext fun x => (fderiv ℝ χ.field x).map_add a b

/--
@isnad1 id=eq.0h3v.s6.9cdb0a03f2c8 from=translated src=- shape=68f0bef6 vocab=a1963b87
-/
theorem Cutoff.directional_smul (χ : Cutoff) (c : ℝ) (a : Space) :
    χ.directional (c • a) = (χ.directional a).scale c := by
  apply Cutoff.ext
  exact funext fun x => (fderiv ℝ χ.field x).map_smul c a

section LinearCutoffOperation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative with respect to a translation parameter of an operation linear in the cutoff. -/
def cutoffDirectionalMap (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ) (χ : Cutoff) : Space →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => L (χ.directional a)
      map_add' := fun a b => by rw [Cutoff.directional_add, hadd]
      map_smul' := fun c a => by rw [Cutoff.directional_smul, hsmul]; rfl }

/--
@isnad1 id=eq.2h4v.s9.184b0be53eec from=translated src=- shape=fe81321d vocab=6bb05873
-/
@[simp] theorem cutoffDirectionalMap_apply (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ) (χ : Cutoff) (a : Space) :
    cutoffDirectionalMap L hadd hsmul χ a = L (χ.directional a) := rfl

/--
@isnad1 id=eq.2h5v.s8.e548782b857d from=translated src=- shape=03fc1e33 vocab=973aa95d
-/
theorem cutoffOperation_differenceError (L : Cutoff → E)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ)
    (hsub : ∀ χ ψ, L (χ.sub ψ) = L χ - L ψ) (χ : Cutoff) (a b : Space) :
    L ((χ.translate a).differenceError (b-a) 1) =
      L (χ.translate b) - L (χ.translate a) - L ((χ.translate a).directional (b-a)) := by
  rw [Cutoff.differenceError, hsub, Cutoff.differenceQuotient, hsmul, hsub]
  simp only [inv_one, one_smul, Cutoff.translate_add, add_sub_cancel]

/-- The proved cutoff dual norm and a genuine Taylor remainder give the full Fréchet derivative.
@isnad1 id=hasfderi.4h4v.s8.61cec6fab8a3 from=translated src=- shape=c8d7e5af vocab=40a64dd9
-/
theorem cutoffOperation_hasFDerivAt (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ)
    (hsub : ∀ χ ψ, L (χ.sub ψ) = L χ - L ψ)
    (hbound : ∀ χ, ‖L χ‖ ≤ cutoffBound χ) (χ : Cutoff) (a : Space) :
    HasFDerivAt (fun b : Space => L (χ.translate b))
      (cutoffDirectionalMap L hadd hsmul (χ.translate a)) a := by
  obtain ⟨R, M₂, M₃, hM₂, hM₃, hs, h₂, h₃⟩ := (χ.translate a).exists_taylor_controls
  have hstep : ∀ᶠ b : Space in 𝓝 a, ‖b-a‖ ≤ 1 := by
    have hc : ContinuousAt (fun b : Space => ‖b-a‖) a := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simp : ‖a-a‖ < 1))).mono (fun _ h => h.le)
  have hrem (b : Space) (hb : ‖b-a‖ ≤ 1) :
      ‖L (χ.translate b) - L (χ.translate a) -
        cutoffDirectionalMap L hadd hsmul (χ.translate a) (b-a)‖ ≤
          cutoffDifferenceConstant R M₂ M₃ * ‖b-a‖^2 := by
    rw [cutoffDirectionalMap_apply, ← cutoffOperation_differenceError L hsmul hsub]
    have H := (hbound _).trans
      (cutoffBound_differenceError (χ.translate a) R M₂ M₃ hM₂ hM₃ hs h₂ h₃
        (b-a) 1 one_ne_zero (by simpa only [one_smul] using hb))
    simpa only [abs_one, mul_one] using H
  apply hasFDerivAt_iff_tendsto.mpr
  refine squeeze_zero' (Eventually.of_forall (fun b =>
    mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))) ?_ ?_
      (g := fun b : Space => cutoffDifferenceConstant R M₂ M₃ * ‖b-a‖)
  · filter_upwards [hstep] with b hb
    calc
      _ ≤ ‖b-a‖⁻¹ * (cutoffDifferenceConstant R M₂ M₃ * ‖b-a‖^2) :=
        mul_le_mul_of_nonneg_left (hrem b hb) (inv_nonneg.mpr (norm_nonneg _))
      _ = cutoffDifferenceConstant R M₂ M₃ * ‖b-a‖ := by
        by_cases h : ‖b-a‖ = 0
        · simp only [h, inv_zero, zero_mul, mul_zero]
        · field_simp
  · have hc : Continuous (fun b : Space => cutoffDifferenceConstant R M₂ M₃ * ‖b-a‖) := by fun_prop
    simpa only [sub_self, norm_zero, mul_zero] using hc.tendsto a

/-- Induction differentiates the actual cutoff repeatedly, with no smoothness hypothesis on L.
@isnad1 id=contdiff.4h3v.s8.518b6439db57 from=translated src=- shape=639e65a3 vocab=56f29c73
-/
theorem cutoffOperation_contDiff (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ)
    (hsub : ∀ χ ψ, L (χ.sub ψ) = L χ - L ψ)
    (hbound : ∀ χ, ‖L χ‖ ≤ cutoffBound χ) (χ : Cutoff) :
    ContDiff ℝ ∞ (fun a : Space => L (χ.translate a)) := by
  have hnat : ∀ n : ℕ, ∀ ψ : Cutoff, ContDiff ℝ n (fun a : Space => L (ψ.translate a)) := by
    intro n
    induction n with
    | zero =>
      intro ψ
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
        (fun a => (cutoffOperation_hasFDerivAt L hadd hsmul hsub hbound ψ a).continuousAt))
    | succ n ih =>
      intro ψ
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun a => cutoffDirectionalMap L hadd hsmul (ψ.translate a), ?_,
        fun a => cutoffOperation_hasFDerivAt L hadd hsmul hsub hbound ψ a⟩
      apply contDiff_clm_apply_iff.mpr
      intro b
      simpa only [cutoffDirectionalMap_apply, Cutoff.directional_translate] using ih (ψ.directional b)
  exact contDiff_iff_forall_nat_le.mpr (fun n _ => hnat n χ)

end LinearCutoffOperation

/-- Actual Fréchet derivative of the cutoff-curl extension.
@isnad1 id=hasfderi.0h2v.s21.f33748dd04c2 from=translated src=- shape=2489077b vocab=35df30e9
-/
theorem cutoffCurl_hasFDerivAt (χ : Cutoff) (a : Space) :
    HasFDerivAt (fun b : Space => cutoffCurl (χ.translate b))
      (cutoffDirectionalMap cutoffCurl cutoffCurl_add cutoffCurl_scale (χ.translate a)) a :=
  cutoffOperation_hasFDerivAt cutoffCurl cutoffCurl_add cutoffCurl_scale cutoffCurl_sub
    cutoffCurl_norm_le χ a

/-- Actual Fréchet derivative of the weak Newtonian potential.
@isnad1 id=hasfderi.0h2v.s21.b5a2a53234f7 from=translated src=- shape=f634dcc8 vocab=73d435b9
-/
theorem weakPotential_hasFDerivAt (χ : Cutoff) (a : Space) :
    HasFDerivAt (fun b : Space => weakPotential (χ.translate b))
      (cutoffDirectionalMap weakPotential weakPotential_add weakPotential_scale (χ.translate a)) a :=
  cutoffOperation_hasFDerivAt weakPotential weakPotential_add weakPotential_scale weakPotential_sub
    weakPotential_operatorNorm_le χ a

/--
@isnad1 id=contdiff.0h1v.s18.0a98706f0781 from=translated src=- shape=ab4a1524 vocab=1c9f1779
-/
theorem cutoffCurl_contDiff (χ : Cutoff) :
    ContDiff ℝ ∞ (fun a : Space => cutoffCurl (χ.translate a)) :=
  cutoffOperation_contDiff cutoffCurl cutoffCurl_add cutoffCurl_scale cutoffCurl_sub
    cutoffCurl_norm_le χ

/--
@isnad1 id=contdiff.0h1v.s18.17125e80192f from=translated src=- shape=151d3375 vocab=a6a18bd2
-/
theorem weakPotential_contDiff (χ : Cutoff) :
    ContDiff ℝ ∞ (fun a : Space => weakPotential (χ.translate a)) :=
  cutoffOperation_contDiff weakPotential weakPotential_add weakPotential_scale weakPotential_sub
    weakPotential_operatorNorm_le χ

/-- Joint translation of both cutoffs is smooth in the full three-dimensional parameter.
@isnad1 id=contdiff.0h2v.s16.e23f17e833fa from=translated src=- shape=59eeea15 vocab=cd191a29
-/
theorem mixedBoundaryOperator_contDiff (χ ψ : Cutoff) :
    ContDiff ℝ ∞ (fun a : Space =>
      mixedBoundaryOperator (χ.translate a) (ψ.translate a)) :=
  (cutoffCurl_contDiff χ).clm_comp (weakPotential_contDiff ψ)

end EulerMeanBoundary
