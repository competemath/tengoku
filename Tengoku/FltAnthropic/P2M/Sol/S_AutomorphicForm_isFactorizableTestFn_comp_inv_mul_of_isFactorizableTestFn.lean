import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FactorizableTestFn

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn

open NumberField
open scoped Classical
open IsDedekindDomain AutomorphicForm

namespace TierTranslate

private theorem archEntries_mul (K : Type) [Field K] (a h : GL (Fin 2) (InfiniteAdeleRing K)) (i j : Fin 2) :
    archEntries K (a * h) i j = ∑ k : Fin 2, archEntries K a i k * archEntries K h k j := by
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

private theorem isArchTestFactor_comp_mul_left (K : Type) [Field K] [NumberField K]
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (hfa : IsArchTestFactor K fa)
    (a : GL (Fin 2) (InfiniteAdeleRing K)) : IsArchTestFactor K (fun h => fa (a * h)) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨⟨fun X => Φ (fun i j => ∑ k : Fin 2, archEntries K a i k * X k j), ?_, ?_⟩, ?_⟩
  · exact hΦ.comp (by fun_prop)
  · intro h
    show fa (a * h) = Φ (fun i j => ∑ k : Fin 2, archEntries K a i k * archEntries K h k j)
    rw [hfaΦ]
    congr 1
    funext i j
    exact archEntries_mul K a h i j
  · exact hsupp.comp_homeomorph (Homeomorph.mulLeft a)

private theorem isFinTestFactor_comp_mul_left (K : Type) [Field K] [NumberField K]
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (hff : IsFinTestFactor K ff)
    (b : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : IsFinTestFactor K (fun h => ff (b * h)) :=
  ⟨hff.1.comp_continuous (continuous_const_mul b), hff.2.comp_homeomorph (Homeomorph.mulLeft b)⟩

end TierTranslate

open TierTranslate in
/--
@isnad1 id=isfactor.1h3v.s9.bc6d17da40f9 from=translated src=- shape=09ea5c2d vocab=4a28915e
-/
theorem solution
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hf : IsFactorizableTestFn K f)
    (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    IsFactorizableTestFn K (fun y => f (t⁻¹ * y)) := by
  obtain ⟨fa, ff, hfa, hff, hfx⟩ := hf
  refine ⟨fun h => fa (AdelicLevel.glArch (𝓞 K) K t⁻¹ * h),
    fun h => ff (AdelicLevel.glFin (𝓞 K) K t⁻¹ * h),
    isArchTestFactor_comp_mul_left K hfa _, isFinTestFactor_comp_mul_left K hff _, ?_⟩
  intro y
  show f (t⁻¹ * y) = fa (AdelicLevel.glArch (𝓞 K) K t⁻¹ * AdelicLevel.glArch (𝓞 K) K y) *
    ff (AdelicLevel.glFin (𝓞 K) K t⁻¹ * AdelicLevel.glFin (𝓞 K) K y)
  rw [hfx (t⁻¹ * y), map_mul (AdelicLevel.glArch (𝓞 K) K) t⁻¹ y,
    map_mul (AdelicLevel.glFin (𝓞 K) K) t⁻¹ y]
