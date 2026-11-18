import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LevelModuliPackage
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LevelModuliPackageAbs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq

set_option autoImplicit false

universe u

open ModularCurve

theorem solution
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P P' : LevelModuliPackageAbs A D) :
    ∃ e : P.B₀ ≃ₐ[A] P'.B₀, D.map (e : P.B₀ →ₐ[A] P'.B₀) P.univ = P'.univ := by
  classical
  let φ : P.B₀ →ₐ[A] P'.B₀ := P.classify P'.univ
  let ψ : P'.B₀ →ₐ[A] P.B₀ := P'.classify P.univ
  have hφ : D.map φ P.univ = P'.univ := P.map_classify P'.univ
  have hψ : D.map ψ P'.univ = P.univ := P'.map_classify P.univ
  have h1 : ψ.comp φ = AlgHom.id A P.B₀ := by
    have hc : D.map (ψ.comp φ) P.univ = P.univ := by rw [D.map_comp, hφ, hψ]
    have hi : D.map (AlgHom.id A P.B₀) P.univ = P.univ := D.map_id _ _
    exact (P.classify_unique P.univ (ψ.comp φ) hc).trans (P.classify_unique P.univ (AlgHom.id A P.B₀) hi).symm
  have h2 : φ.comp ψ = AlgHom.id A P'.B₀ := by
    have hc : D.map (φ.comp ψ) P'.univ = P'.univ := by rw [D.map_comp, hψ, hφ]
    have hi : D.map (AlgHom.id A P'.B₀) P'.univ = P'.univ := D.map_id _ _
    exact (P'.classify_unique P'.univ (φ.comp ψ) hc).trans (P'.classify_unique P'.univ (AlgHom.id A P'.B₀) hi).symm
  refine ⟨AlgEquiv.ofAlgHom φ ψ h2 h1, ?_⟩
  exact hφ
