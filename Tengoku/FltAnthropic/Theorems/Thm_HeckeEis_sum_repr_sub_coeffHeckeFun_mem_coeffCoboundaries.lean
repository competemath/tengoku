import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    (s : CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ → CongruenceSubgroup.Gamma0 N)
    (t : CongruenceSubgroup.Gamma0 N → CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ →
      ↥(HeckeEis.heckeUpper N ℓ))
    (hs : ∀ q, (s q : CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) = q)
    (hst : ∀ g q, s (g • q) * (t g q : CongruenceSubgroup.Gamma0 N) = g * s q)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCocycles ρ) :
    (fun g => letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
        ∑ q : CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ,
          ρ (s (g • q)) (a (z (HeckeEis.heckeConj N ℓ (t g q)))))
      - HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffCoboundaries ρ := by exact @_root_.P2MW.S_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries.solution N ℓ _ K _ V _ _ ρ a ha s t hs hst z hz
