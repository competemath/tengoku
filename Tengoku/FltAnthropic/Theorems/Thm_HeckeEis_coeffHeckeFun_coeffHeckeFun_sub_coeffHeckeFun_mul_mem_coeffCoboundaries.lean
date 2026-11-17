import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

/--
@isnad1 id=mem.7h10v.s16.60ae3f1f29f4 from=translated src=- shape=2afceba2 vocab=217ae6e1
-/
theorem HeckeEis.coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries
    (N ℓ ℓ' m : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero m] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (hℓℓ' : ¬ ℓ ∣ ℓ') (hm : m = ℓ * ℓ')
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a a' : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(HeckeEis.heckeUpper N ℓ'),
      a' ∘ₗ ρ (HeckeEis.heckeConj N ℓ' u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a')
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCocycles ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a (HeckeEis.coeffHeckeFun N ℓ' ρ a' z)
      - HeckeEis.coeffHeckeFun N m ρ (a ∘ₗ a') z ∈ HeckeEis.coeffCoboundaries ρ := by exact @_root_.P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.solution N ℓ ℓ' m _ _ _ hℓ hℓN hℓℓ' hm K _ V _ _ ρ a a' ha ha' z hz
