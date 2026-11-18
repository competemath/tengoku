import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic
import Tengoku.Seed.LinearAlgebra.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IharaLemma_resKer_localized.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IharaLemma_resKer_localized

set_option autoImplicit false

theorem solution {R : Type*} [CommRing R] (S : Submonoid R) {V Vk V' Vk' : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup Vk] [Module R Vk]
    [AddCommGroup V'] [Module R V'] [AddCommGroup Vk'] [Module R Vk']
    (ϖ : R) (redV : V →ₗ[R] Vk)
    (hker : ∀ v, redV v = 0 → ∃ v₁, v = ϖ • v₁)
    (gV : V →ₗ[R] V') [IsLocalizedModule S gV] (gK : Vk →ₗ[R] Vk') [IsLocalizedModule S gK]
    (red' : V' →ₗ[R] Vk') (hsq : ∀ v, red' (gV v) = gK (redV v)) :
    ∀ v' : V', red' v' = 0 → ∃ v₁' : V', v' = ϖ • v₁' := by
  intro v' hv'
  obtain ⟨⟨v, s⟩, hs⟩ := IsLocalizedModule.surj S gV v'
  have hs' : (s : R) • v' = gV v := by rw [← Submonoid.smul_def]; exact hs
  have h0 : gK (redV v) = 0 := by
    rw [← hsq, ← hs', map_smul, hv', smul_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff S gK).mp h0
  rw [Submonoid.smul_def] at ht
  have ht' : redV ((t : R) • v) = 0 := by rw [map_smul, ht]
  obtain ⟨w, hw⟩ := hker _ ht'
  have key : ((t * s : S) : R) • v' = ϖ • gV w := by
    rw [Submonoid.coe_mul, mul_smul, hs', ← map_smul, hw, map_smul]
  obtain ⟨y, hy⟩ :=
    ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units gV (t * s))).2 (gV w)
  rw [Module.algebraMap_end_apply] at hy
  refine ⟨y, IsLocalizedModule.smul_injective gV (t * s) ?_⟩
  show (t * s) • v' = (t * s) • (ϖ • y)
  rw [Submonoid.smul_def, Submonoid.smul_def, key, smul_comm _ ϖ y, hy]
