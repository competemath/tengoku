import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_maximalIdeal_eq_of_le_sup_sq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_maximalIdeal_eq_of_le_sup_sq

set_option autoImplicit false

universe u

open IsLocalRing

/--
@isnad1 id=eq.2h2v.s8.ded05fe380b2 from=translated src=- shape=ead75b59 vocab=95893b03
-/
theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : Ideal R) (hN : N ≤ maximalIdeal R) (h : maximalIdeal R ≤ N ⊔ maximalIdeal R ^ 2) :
    maximalIdeal R = N := by
  classical
  refine le_antisymm ?_ hN
  have hfg : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (N := N) hfg ?_ ?_
  · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  · rw [Ideal.smul_eq_mul, ← pow_two]; exact h
