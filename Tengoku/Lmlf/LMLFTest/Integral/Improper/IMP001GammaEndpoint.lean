import Tengoku.Lmlf.LMLF.Integral.Improper.Bochner
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory Set
open scoped Real

noncomputable section

namespace LMLFTest.Integral.Improper

open LMLF.Integral

private def gammaEndpointBase (u : ℝ) : ℝ :=
  if 0 < u then Real.exp (-u) / Real.sqrt u else 0

private theorem gammaEndpointBase_eq_gammaIntegrand
    {u : ℝ} (hu : u ∈ Ioi (0 : ℝ)) :
    gammaEndpointBase u =
      Real.exp (-u) * u ^ ((1 / 2 : ℝ) - 1) := by
  have hu' : 0 < u := hu
  rw [gammaEndpointBase, ite_eq_left hu']
  rw [div_eq_mul_inv, Real.sqrt_eq_rpow,
    ← Real.rpow_neg hu'.le]
  norm_num

private theorem gammaEndpointBase_integrable :
    IntegrableOn gammaEndpointBase (Ioi (0 : ℝ)) := by
  refine (Real.GammaIntegral_convergent (s := (1 / 2 : ℝ)) (by norm_num)).congr_fun ?_
    measurableSet_Ioi
  intro u hu
  exact (gammaEndpointBase_eq_gammaIntegrand hu).symm

private theorem gammaEndpointBase_integral :
    (∫ u in Ioi (0 : ℝ), gammaEndpointBase u) =
      Real.Gamma (1 / 2 : ℝ) := by
  calc
    (∫ u in Ioi (0 : ℝ), gammaEndpointBase u) =
        ∫ u in Ioi (0 : ℝ),
          Real.exp (-u) * u ^ ((1 / 2 : ℝ) - 1) :=
      setIntegral_congr_fun measurableSet_Ioi
        (fun _ hu ↦ gammaEndpointBase_eq_gammaIntegrand hu)
    _ = Real.Gamma (1 / 2 : ℝ) :=
      (Real.Gamma_eq_integral (s := (1 / 2 : ℝ)) (by norm_num)).symm

/-- REG.44--REG.45 / positive IMP-R22: the exact translated
`exp (-(t-k)) / sqrt (t-k)` singularity is honestly Bochner integrable on the
open initial ray, has the positive value `Gamma (1/2)`, and public T07 accepts
it for every finite exceptional set satisfying its exact above-`k` premise.
@isnad1 id=and.1h2v.s8.d0b2c1341031 from=translated src=- shape=24450d2c vocab=56cd99aa
-/
theorem initialEndpoint_integrable_example (k : ℝ) (S : Finset ℝ)
    (hS : ∀ c ∈ S, k < c) :
    IntegrableOn
        (fun t : ℝ ↦
          if k < t then Real.exp (-(t - k)) / Real.sqrt (t - k) else 0)
        (Ioi k) ∧
      (∫ t in Ioi k,
          (if k < t then Real.exp (-(t - k)) / Real.sqrt (t - k) else 0)) =
        Real.Gamma (1 / 2 : ℝ) ∧
      0 < Real.Gamma (1 / 2 : ℝ) ∧
      HasImproperIntegralAtTopExcept
        (fun t : ℝ ↦
          if k < t then Real.exp (-(t - k)) / Real.sqrt (t - k) else 0)
        k S (Real.Gamma (1 / 2 : ℝ)) := by
  let s : ℝ → ℝ := fun t ↦
    if k < t then Real.exp (-(t - k)) / Real.sqrt (t - k) else 0
  let φ : ℝ → ℝ := fun u ↦ u + k
  have hφ : MeasurePreserving φ volume volume := by
    exact measurePreserving_add_right volume k
  have hφemb : MeasurableEmbedding φ :=
    (Homeomorph.addRight k).isClosedEmbedding.measurableEmbedding
  have hpre : φ ⁻¹' Ioi k = Ioi (0 : ℝ) := by
    ext u
    simp [φ]
  have hcomp : s ∘ φ = gammaEndpointBase := by
    funext u
    by_cases hu : 0 < u
    · simp [s, φ, gammaEndpointBase, hu]
    · simp [s, φ, gammaEndpointBase, hu]
  have hsInt : IntegrableOn s (Ioi k) := by
    apply (hφ.integrableOn_comp_preimage hφemb).mp
    rw [hpre, hcomp]
    exact gammaEndpointBase_integrable
  have htranslated := hφ.setIntegral_preimage_emb hφemb s (Ioi k)
  change (∫ u in φ ⁻¹' Ioi k, (s ∘ φ) u) = ∫ t in Ioi k, s t at htranslated
  rw [hpre, hcomp] at htranslated
  have hsValue : (∫ t in Ioi k, s t) = Real.Gamma (1 / 2 : ℝ) :=
    htranslated.symm.trans gammaEndpointBase_integral
  have hsRel : HasImproperIntegralAtTopExcept s k S (Real.Gamma (1 / 2 : ℝ)) := by
    have := HasImproperIntegralAtTopExcept.of_integrableOn_Ioi s k S hS hsInt
    rwa [hsValue] at this
  change IntegrableOn s (Ioi k) ∧
    (∫ t in Ioi k, s t) = Real.Gamma (1 / 2 : ℝ) ∧
    0 < Real.Gamma (1 / 2 : ℝ) ∧
    HasImproperIntegralAtTopExcept s k S (Real.Gamma (1 / 2 : ℝ))
  exact ⟨hsInt, hsValue, Real.Gamma_pos_of_pos (by norm_num), hsRel⟩

end LMLFTest.Integral.Improper
