import Tengoku.Seed.LinearAlgebra.Charpoly.ToMatrix
import Tengoku.Seed.LinearAlgebra.GeneralLinearGroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MonoidHom_charpoly_apply_mul_mul_inv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MonoidHom_charpoly_apply_mul_mul_inv

theorem solution {R : Type*} {M : Type*} {G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [Group G] (ρ : G →* Module.End R M) (σ τ : G) : (ρ (τ * σ * τ⁻¹)).charpoly = (ρ σ).charpoly := by
  let e : M ≃ₗ[R] M := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.toHomUnits τ)
  have he : e.conj (ρ σ) = ρ (τ * σ * τ⁻¹) := by
    rw [map_mul, map_mul]
    rfl
  rw [← he, LinearEquiv.charpoly_conj]
