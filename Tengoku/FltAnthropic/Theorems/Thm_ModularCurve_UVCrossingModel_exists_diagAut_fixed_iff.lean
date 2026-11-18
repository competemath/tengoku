import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_UVCrossingModel_exists_diagAut_fixed_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_UVCrossingModel_exists_diagAut_fixed_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.exists_diagAut_fixed_iff
    {W : Type*} [CommRing W] (π : W) [IsPrecomplete (Ideal.span {π}) W]
    (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0) (e : ℕ) (he : e ≠ 0)
    (ζ ζ' : W) (hζ : ζ ^ e = 1) (hζζ' : ζ * ζ' = 1)
    (hreg : ∀ m : ℕ, 0 < m → m < e → ζ ^ m - 1 ∈ nonZeroDivisors W) :
    ∃ δ : UVCrossingModel W π ≃ₐ[W] UVCrossingModel W π,
      (∀ F : MvPowerSeries (Fin 2) W, δ (mk π F) = mk π (MvPowerSeries.rescale ![ζ, ζ'] F)) ∧
      ∀ z : UVCrossingModel W π, δ z = z ↔
        ∃ F : MvPowerSeries (Fin 2) W,
          (∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F ≠ 0 → (e : ℤ) ∣ (d 0 : ℤ) - d 1) ∧ mk π F = z := by exact @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_diagAut_fixed_iff.solution W _ π _ hsep e he ζ ζ' hζ hζζ' hreg
