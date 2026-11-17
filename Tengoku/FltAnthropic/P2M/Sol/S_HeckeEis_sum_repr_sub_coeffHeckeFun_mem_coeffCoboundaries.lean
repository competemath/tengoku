import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries

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
@isnad1 id=eq.1h5v.s12.8e8cd475d64e from=translated src=- shape=b17f6ca1 vocab=b426f7cd
-/
theorem cocycle_one {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h

  have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

/--
@isnad1 id=eq.1h7v.s16.7e7cc05a28ef from=translated src=- shape=d441b99e vocab=37170b18
-/
theorem cocycle_map_inv {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) (x : ↥U) :
    z (c x⁻¹) = -(ρ (c x⁻¹) (z (c x))) := by
  have h1 : z (c x⁻¹ * c x) = z (c x⁻¹) + ρ (c x⁻¹) (z (c x)) := hz _ _
  rw [← map_mul, inv_mul_cancel, map_one, cocycle_one N ρ hz] at h1
  exact eq_neg_of_add_eq_zero_left h1.symm

/--
@isnad1 id=eq.0h4v.s13.91ddf92035ae from=translated src=- shape=d59dc66c vocab=219bf6ed
-/
theorem out_mul_transferAux (g : Gamma0 N) (q : Gamma0 N ⧸ U) :
    (g • q).out * (transferAux U g q : Gamma0 N) = g * q.out := by
  rw [coe_transferAux, mul_inv_cancel_left]

include ha in

/--
@isnad1 id=mem.4h9v.s16.59fa6295443d from=translated src=- shape=69629e33 vocab=bfacafc1
-/
theorem sum_repr_sub_mem_coeffCoboundaries
    (s : Gamma0 N ⧸ U → Gamma0 N) (t : Gamma0 N → Gamma0 N ⧸ U → ↥U)
    (hs : ∀ q, (s q : Gamma0 N ⧸ U) = q)
    (hst : ∀ g q, s (g • q) * (t g q : Gamma0 N) = g * s q)
    {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) :
    (fun g => letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
        ∑ q : Gamma0 N ⧸ U, ρ (s (g • q)) (a (z (c (t g q)))))
      - coeffHeckeFun N ℓ ρ a z ∈ coeffCoboundaries ρ := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  have hu_mem : ∀ q : Gamma0 N ⧸ U, (q.out)⁻¹ * s q ∈ U := fun q =>
    QuotientGroup.eq.mp ((QuotientGroup.out_eq' q).trans (hs q).symm)
  have hex : ∀ q : Gamma0 N ⧸ U, ∃ uq : ↥U, s q = q.out * (uq : Gamma0 N) := fun q =>
    ⟨⟨_, hu_mem q⟩, by rw [Subgroup.coe_mk, mul_inv_cancel_left]⟩
  choose u hsq using hex
  have ht : ∀ g q, t g q = (u (g • q))⁻¹ * transferAux U g q * u q := by
    intro g q
    apply Subtype.ext
    have h1 := hst g q
    rw [hsq, hsq] at h1
    push_cast [coe_transferAux]
    calc ((t g q : ↥U) : Gamma0 N)
        = ((g • q).out * ↑(u (g • q)))⁻¹ * (((g • q).out * ↑(u (g • q))) * ↑(t g q)) := by group
      _ = ((g • q).out * ↑(u (g • q)))⁻¹ * (g * (q.out * ↑(u q))) := by rw [h1]
      _ = (↑(u (g • q)))⁻¹ * ((g • q).out⁻¹ * (g * q.out)) * ↑(u q) := by group

  set F : V := ∑ q : Gamma0 N ⧸ U, ρ q.out (a (z (c (u q)))) with hF
  refine ⟨F, ?_⟩
  funext g
  simp only [coeffCoboundaryMap_apply, Pi.sub_apply, coeffHeckeFun_apply]

  have key : ∀ q : Gamma0 N ⧸ U,
      ρ (s (g • q)) (a (z (c (t g q))))
        = -(ρ (g • q).out (a (z (c (u (g • q))))))
          + ρ (g • q).out (a (z (c (transferAux U g q))))
          + ρ g (ρ q.out (a (z (c (u q))))) := by
    intro q
    rw [hsq (g • q), ht g q, map_mul c, map_mul c,
      hz (c (u (g • q))⁻¹ * c (transferAux U g q)) (c (u q)),
      hz (c (u (g • q))⁻¹) (c (transferAux U g q)),
      cocycle_map_inv N ℓ ρ hz (u (g • q)), ← map_mul c]
    simp only [map_add, map_neg, ha_apply N ℓ ρ a ha]
    have e12 : ∀ v : V, ρ ((g • q).out * ((u (g • q) : ↥U) : Gamma0 N)) (ρ (((u (g • q))⁻¹ : ↥U) : Gamma0 N) v)
        = ρ (g • q).out v := by
      intro v
      rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel_right]
    have e3 : ∀ v : V, ρ ((g • q).out * ((u (g • q) : ↥U) : Gamma0 N))
        (ρ (((u (g • q))⁻¹ * transferAux U g q : ↥U) : Gamma0 N) v) = ρ g (ρ q.out v) := by
      intro v
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← out_mul_transferAux N ℓ g q]
      group
    rw [e12, e12, e3]
  rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← map_sum]
  have hre : ∑ q : Gamma0 N ⧸ U, ρ (g • q).out (a (z (c (u (g • q))))) = F :=
    Fintype.sum_bijective (g • ·) (MulAction.bijective g) _ _ fun q => rfl
  rw [hre]
  abel

end Sh2
end HeckeEis

/--
@isnad1 id=mem.4h9v.s16.59fa6295443d from=translated src=- shape=69629e33 vocab=bfacafc1
-/
theorem solution (N ℓ : ℕ) [NeZero ℓ]
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
      - HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffCoboundaries ρ :=
  HeckeEis.Sh2.sum_repr_sub_mem_coeffCoboundaries N ℓ ρ a ha s t hs hst hz
