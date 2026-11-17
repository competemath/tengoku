import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_coeffHeckeFun_mem_coeffCocycles.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffCocycles

set_option autoImplicit false

open scoped MatrixGroups

set_option autoImplicit false

namespace HeckeEis
export _root_.HeckeEis (heckeUpper heckeConj transferAux coe_transferAux transferAux_mul coeffCocycles coeffCoboundaryMap_apply coeffCoboundaries coeffHeckeFun coeffHeckeFun_apply)
open _root_.HeckeEis
namespace Sh2
open CongruenceSubgroup
open scoped MatrixGroups

variable (N ℓ : ℕ) [NeZero ℓ]
  {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
  (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)

local notation "U" => heckeUpper N ℓ
local notation "c" => heckeConj N ℓ

include ha in
theorem ha_apply (u : ↥U) (v : V) : a (ρ (c u) v) = ρ (u : Gamma0 N) (a v) := by
  have := LinearMap.congr_fun (ha u) v
  simpa using this

theorem out_mul_transferAux (g : Gamma0 N) (q : Gamma0 N ⧸ U) :
    (g • q).out * (transferAux U g q : Gamma0 N) = g * q.out := by
  rw [coe_transferAux, mul_inv_cancel_left]

include ha in

theorem mem_coeffCocycles {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) :
    coeffHeckeFun N ℓ ρ a z ∈ coeffCocycles ρ := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  intro g h
  simp only [coeffHeckeFun_apply]
  have key : ∀ q : Gamma0 N ⧸ U,
      ρ ((g * h) • q).out (a (z (c (transferAux U (g * h) q))))
        = ρ (g • (h • q)).out (a (z (c (transferAux U g (h • q)))))
          + ρ g (ρ (h • q).out (a (z (c (transferAux U h q))))) := by
    intro q
    rw [transferAux_mul, map_mul, hz, map_add, map_add, mul_smul]
    congr 1
    rw [ha_apply N ℓ ρ a ha, ← Module.End.mul_apply, ← map_mul, out_mul_transferAux, map_mul,
      Module.End.mul_apply]
  rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_add_distrib, map_sum]
  congr 1
  exact Fintype.sum_bijective (h • ·) (MulAction.bijective h) _ _ fun q => rfl

end Sh2
end HeckeEis

theorem solution (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCocycles ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffCocycles ρ :=
  HeckeEis.Sh2.mem_coeffCocycles N ℓ ρ a ha hz
