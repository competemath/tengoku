import Tengoku.Seed.MeasureTheory.Integral.Prod
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion

set_option autoImplicit false

open MeasureTheory Set

namespace FbSwap

/--
@isnad1 id=eq.1h3v.s7.f415395011e3 from=translated src=- shape=adb1b99e vocab=0f4f0a00
-/
lemma section_fst (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ) (σ : ℝ) :
    (∫ w : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w))
      = (Ioi (0 : ℝ)).indicator (fun σ : ℝ => ∫ w in Ioi (v / σ), f (σ, w)) σ := by
  by_cases hσ : 0 < σ
  · rw [indicator_of_mem (mem_Ioi.mpr hσ), ← integral_indicator measurableSet_Ioi]
    congr 1
    funext w
    have hiff : (σ, w) ∈ {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} ↔ w ∈ Ioi (v / σ) := by
      simp only [mem_ofPred_eq, mem_Ioi]
      constructor
      · rintro ⟨-, -, h⟩
        rw [div_lt_iff₀ hσ]
        linarith [mul_comm σ w]
      · intro h
        have h' := (div_lt_iff₀ hσ).mp h
        refine ⟨hσ, ?_, by linarith [mul_comm σ w]⟩
        by_contra hw'
        have hw'' := not_lt.mp hw'
        nlinarith
    by_cases hmem : w ∈ Ioi (v / σ)
    · rw [indicator_of_mem hmem, indicator_of_mem (hiff.mpr hmem)]
    · rw [indicator_of_notMem hmem, indicator_of_notMem (fun h => hmem (hiff.mp h))]
  · rw [indicator_of_notMem (fun h : σ ∈ Ioi (0:ℝ) => hσ (mem_Ioi.mp h))]
    have hzero : ∀ w : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w) = 0 := by
      intro w
      apply indicator_of_notMem
      intro h
      exact hσ h.1
    simp [hzero]

/--
@isnad1 id=eq.1h3v.s7.2f762cca8feb from=translated src=- shape=c23370b8 vocab=0f4f0a00
-/
lemma section_snd (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ) (w : ℝ) :
    (∫ σ : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w))
      = (Ioi (0 : ℝ)).indicator (fun w : ℝ => ∫ σ in Ioi (v / w), f (σ, w)) w := by
  by_cases hw : 0 < w
  · rw [indicator_of_mem (mem_Ioi.mpr hw), ← integral_indicator measurableSet_Ioi]
    congr 1
    funext σ
    have hiff : (σ, w) ∈ {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} ↔ σ ∈ Ioi (v / w) := by
      simp only [mem_ofPred_eq, mem_Ioi]
      constructor
      · rintro ⟨-, -, h⟩
        rw [div_lt_iff₀ hw]
        linarith
      · intro h
        have h' := (div_lt_iff₀ hw).mp h
        refine ⟨?_, hw, by linarith⟩
        by_contra hs
        have hs' := not_lt.mp hs
        nlinarith
    by_cases hmem : σ ∈ Ioi (v / w)
    · rw [indicator_of_mem hmem, indicator_of_mem (hiff.mpr hmem)]
    · rw [indicator_of_notMem hmem, indicator_of_notMem (fun h => hmem (hiff.mp h))]
  · rw [indicator_of_notMem (fun h : w ∈ Ioi (0:ℝ) => hw (mem_Ioi.mp h))]
    have hzero : ∀ σ : ℝ, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f (σ, w) = 0 := by
      intro σ
      apply indicator_of_notMem
      intro h
      exact hw h.2.1
    simp [hzero]

/--
@isnad1 id=measurab.0h1v.s6.b98717e09c43 from=translated src=- shape=c61e2810 vocab=50e50625
-/
lemma measurableSet_region (v : ℝ) :
    MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_const (measurable_fst.mul measurable_snd)))

/--
@isnad1 id=and.2h2v.s8.5e485a1247d8 from=translated src=- shape=777c932c vocab=53c94b5e
-/
theorem main (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ)
    (hf : IntegrableOn f {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}) :
    (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q ∧
      (∫ w in Ioi (0 : ℝ), ∫ σ in Ioi (v / w), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q := by
  have hR := measurableSet_region v
  have hint : Integrable ({q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have := hf.integrable_indicator hR
    rwa [Measure.volume_eq_prod] at this
  have key : ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q
      = ∫ q, {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}.indicator f q
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [integral_indicator hR, Measure.volume_eq_prod]
  constructor
  · rw [key, integral_prod _ hint, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext σ
    exact (section_fst v hv f σ).symm
  · rw [key, integral_prod_symm _ hint, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext w
    exact (section_snd v hv f w).symm

end FbSwap

/--
@isnad1 id=and.2h2v.s8.5e485a1247d8 from=translated src=- shape=777c932c vocab=53c94b5e
-/
theorem solution
    (v : ℝ) (hv : 0 < v) (f : ℝ × ℝ → ℂ)
    (hf : IntegrableOn f {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}) :
    (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q ∧
      (∫ w in Ioi (0 : ℝ), ∫ σ in Ioi (v / w), f (σ, w)) = ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, f q :=
  FbSwap.main v hv f hf
