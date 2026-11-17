import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries

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
/--
@isnad1 id=eq.1h8v.s15.5e32dbafaf98 from=translated src=- shape=b2bacfc7 vocab=da90c168
-/
theorem ha_apply (u : ↥U) (v : V) : a (ρ (c u) v) = ρ (u : Gamma0 N) (a v) := by
  have := LinearMap.congr_fun (ha u) v
  simpa using this

/--
@isnad1 id=eq.0h4v.s13.91ddf92035ae from=translated src=- shape=d59dc66c vocab=219bf6ed
-/
theorem out_mul_transferAux (g : Gamma0 N) (q : Gamma0 N ⧸ U) :
    (g • q).out * (transferAux U g q : Gamma0 N) = g * q.out := by
  rw [coe_transferAux, mul_inv_cancel_left]

include ha in

/--
@isnad1 id=mem.2h7v.s15.ccb2afe662a1 from=translated src=- shape=b74d68b2 vocab=ca6ee3f8
-/
theorem mem_coeffCoboundaries {z : Gamma0 N → V} (hz : z ∈ coeffCoboundaries ρ) :
    coeffHeckeFun N ℓ ρ a z ∈ coeffCoboundaries ρ := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  obtain ⟨v, rfl⟩ := hz
  refine ⟨∑ q : Gamma0 N ⧸ U, ρ q.out (a v), ?_⟩
  funext g
  simp only [coeffCoboundaryMap_apply, coeffHeckeFun_apply, map_sub, map_sum, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [ha_apply N ℓ ρ a ha]
    rw [← Module.End.mul_apply (ρ (g • q).out) (ρ _), ← map_mul, out_mul_transferAux, map_mul, Module.End.mul_apply]
  · exact (Fintype.sum_bijective (g • ·) (MulAction.bijective g)
      (fun q : Gamma0 N ⧸ U => ρ (g • q).out (a v)) (fun q : Gamma0 N ⧸ U => ρ q.out (a v)) fun q => rfl).symm

end Sh2
end HeckeEis

/--
@isnad1 id=mem.2h7v.s15.ccb2afe662a1 from=translated src=- shape=b74d68b2 vocab=ca6ee3f8
-/
theorem solution (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCoboundaries ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffCoboundaries ρ :=
  HeckeEis.Sh2.mem_coeffCoboundaries N ℓ ρ a ha hz
