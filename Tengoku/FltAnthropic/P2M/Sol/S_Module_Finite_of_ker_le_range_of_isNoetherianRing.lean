import Tengoku.Seed.RingTheory.Noetherian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_Finite_of_ker_le_range_of_isNoetherianRing.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_Finite_of_ker_le_range_of_isNoetherianRing

/--
@isnad1 id=finite.1h6v.s8.9afd5b3f605d from=translated src=- shape=3080b100 vocab=bbc93497
-/
theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] {M N₁ N₂ : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₁] [Module.Finite R N₂]
    (α : N₁ →ₗ[R] M) (β : M →ₗ[R] N₂) (h : LinearMap.ker β ≤ LinearMap.range α) : Module.Finite R M := by
  have hN₁ : Module.Finite R N₁ := inferInstance
  have hN₂ : Module.Finite R N₂ := inferInstance
  haveI : IsNoetherian R (LinearMap.range α) :=
    isNoetherian_of_fg_of_noetherian _ (LinearMap.range_eq_map α ▸ (Module.finite_def.mp hN₁).map _)
  haveI : IsNoetherian R N₂ := isNoetherian_of_isNoetherianRing_of_finite R N₂
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker β ?_ ?_⟩
  · rw [Submodule.map_top]; exact IsNoetherian.noetherian _
  · rw [top_inf_eq]
    have hcomap : ((LinearMap.ker β).comap (LinearMap.range α).subtype).FG := IsNoetherian.noetherian _
    have hmap := hcomap.map (LinearMap.range α).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr h] at hmap
