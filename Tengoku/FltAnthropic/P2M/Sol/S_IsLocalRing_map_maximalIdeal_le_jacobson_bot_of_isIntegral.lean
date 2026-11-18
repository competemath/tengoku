import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral

open IsLocalRing

theorem solution {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Algebra.IsIntegral R S] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ Ideal.jacobson (⊥ : Ideal S) := by
  refine le_sInf fun M ⟨_, hM⟩ ↦ Ideal.map_le_iff_le_comap.mpr ?_
  haveI : M.IsMaximal := hM
  haveI : (M.comap (algebraMap R S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  exact (eq_maximalIdeal this).ge
