import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LevelModuliPackage
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LevelModuliPackageAbs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq_act.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq_act

set_option autoImplicit false

universe u

/--
@isnad1 id=ex.2h5v.s9.45d39c8c2010 from=translated src=- shape=c26e19b9 vocab=e9c1e5a7
-/
theorem solution
    {A : Type u} [CommRing A] {D : ModularCurve.LevelModuliDatum.{u} A} (P : ModularCurve.LevelModuliPackageAbs A D)
    (ρ ρ' : D.ProblemAut)
    (h₁ : ∀ (T : Type u) [CommRing T] [Algebra A T] (y : D.Pt T), ρ'.act (ρ.act y) = y)
    (h₂ : ∀ (T : Type u) [CommRing T] [Algebra A T] (y : D.Pt T), ρ.act (ρ'.act y) = y) :
    ∃ σ : P.B₀ ≃ₐ[A] P.B₀,
      D.map (σ : P.B₀ →ₐ[A] P.B₀) P.univ = ρ.act P.univ ∧
      D.map (σ.symm : P.B₀ →ₐ[A] P.B₀) P.univ = ρ'.act P.univ := by
  classical
  let φ : P.B₀ →ₐ[A] P.B₀ := P.classify (ρ.act P.univ)
  let φ' : P.B₀ →ₐ[A] P.B₀ := P.classify (ρ'.act P.univ)
  have hφ : D.map φ P.univ = ρ.act P.univ := P.map_classify _
  have hφ' : D.map φ' P.univ = ρ'.act P.univ := P.map_classify _
  have hid : ∀ ψ : P.B₀ →ₐ[A] P.B₀, D.map ψ P.univ = P.univ → ψ = AlgHom.id A P.B₀ := by
    intro ψ hψ
    rw [P.classify_unique P.univ ψ hψ, P.classify_unique P.univ (AlgHom.id A P.B₀) (D.map_id _ _)]
  have c1 : φ'.comp φ = AlgHom.id A P.B₀ := hid _ (by
    rw [D.map_comp, hφ, ← ρ.act_map, hφ', h₂])
  have c2 : φ.comp φ' = AlgHom.id A P.B₀ := hid _ (by
    rw [D.map_comp, hφ', ← ρ'.act_map, hφ, h₁])
  refine ⟨AlgEquiv.ofAlgHom φ φ' c2 c1, ?_, ?_⟩
  · rw [AlgEquiv.toAlgHom_ofAlgHom]; exact hφ
  · rw [AlgEquiv.ofAlgHom_symm, AlgEquiv.toAlgHom_ofAlgHom]; exact hφ'
