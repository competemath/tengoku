import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicFourier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicFourier_comp_add_right_mem_pureTensorSet.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicFourier_comp_add_right_mem_pureTensorSet

open NumberField NumberField.AdelicFourier
open scoped SchwartzMap Classical

/--
@isnad1 id=mem.1h3v.s8.956fee3e0b3e from=translated src=- shape=079aad32 vocab=d6d248ca
-/
theorem solution
    {F : Type*} [Field F] [NumberField F] (y : AdeleRing (𝓞 F) F)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x => f (x + y)) ∈ pureTensorSet F := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf
  set c := InfiniteAdeleRing.ringEquiv_mixedSpace F y.1
  have hTG : Function.HasTemperateGrowth (fun z : mixedEmbedding.mixedSpace F => z + c) :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const c)
  have hUp : ∃ (k : ℕ) (C : ℝ), ∀ z : mixedEmbedding.mixedSpace F,
      ‖z‖ ≤ C * (1 + ‖z + c‖) ^ k := by
    refine ⟨1, 1 + ‖c‖, fun z => ?_⟩
    have h1 : ‖z‖ ≤ ‖z + c‖ + ‖c‖ := by
      have := norm_add_le (z + c) (-c); simp only [add_neg_cancel_right, norm_neg] at this
      exact this
    nlinarith [norm_nonneg (z + c), norm_nonneg c]
  refine ⟨SchwartzMap.compCLM ℝ hTG hUp g, fun z => h (z + y.2),
    hlc.comp_continuous (continuous_add_const y.2),
    hcs.comp_homeomorph (Homeomorph.addRight y.2), ?_⟩
  funext x

  simp only [SchwartzMap.compCLM_apply, Function.comp_apply]
  congr 1
  rw [show (x + y).1 = x.1 + y.1 from rfl]
  exact congrArg g (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) x.1 y.1)
