import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_LocalChart
import Tengoku.FltAnthropic.P2M.Sol.S_DrinfeldCurve_LocalChart_exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DrinfeldCurve_LocalChart_exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsLocalRing

/--
@isnad1 id=ex.12h13v.s15.2239d3fa9250 from=translated src=- shape=0d282a0b vocab=2a111b61
-/
theorem DrinfeldCurve.LocalChart.exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C
    (q : ℕ) [Fact q.Prime]
    (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
    (π₁ : W₁) (hπ₁ : maximalIdeal W₁ = Ideal.span {π₁}) (hq₁ : (q : W₁) ∈ maximalIdeal W₁)
    (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
    (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
    (W₂ : Type) [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂]
    (π₂ : W₂) (hπ₂ : maximalIdeal W₂ = Ideal.span {π₂}) (hq₂ : (q : W₂) ∈ maximalIdeal W₂)
    (f₂ u₂ v₂ : MvPowerSeries (Fin 2) W₂) (hu₂ : IsUnit u₂) (hv₂ : IsUnit v₂)
    (hf₂ : f₂ - DrinfeldCurve.LocalChart.drinfeldForm q W₂ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ (q + 2))
    (ρ : W₁ →+* W₂) (hρ : ρ π₁ = π₂)
    (ψ : (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C π₁ * v₁ - f₁ * u₁}) ≃+*
      (MvPowerSeries (Fin 2) W₂ ⧸ Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂}))
    (hψ : ∀ w : W₁, ψ (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (ρ w))) :
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) W₂,
      (∀ i : Fin 2, MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) (g i) = 0) ∧
      (∀ i : Fin 2, ψ (Ideal.Quotient.mk _ (MvPowerSeries.X i)) =
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂}) (g i)) ∧
      ∀ a b : W₂, (a ∉ maximalIdeal W₂ ∨ b ∉ maximalIdeal W₂) → a ^ q * b - a * b ^ q ∈ maximalIdeal W₂ →
        ∃ (lam : W₂) (n₀ n₁ : ℕ), IsUnit lam ∧ (n₀ = 1 ∨ (n₀ = 0 ∧ n₁ = 1)) ∧ n₁ < q ∧
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (g 0) * a +
              MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (g 0) * b - lam * (n₀ : W₂) ∈ maximalIdeal W₂ ∧
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (g 1) * a +
              MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (g 1) * b - lam * (n₁ : W₂) ∈ maximalIdeal W₂ := by exact @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_apply_mk_X_eq_mk_linearPart_rational_of_ringEquiv_of_forall_apply_mk_C.solution q _ W₁ _ _ _ π₁ hπ₁ hq₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ W₂ _ _ _ π₂ hπ₂ hq₂ f₂ u₂ v₂ hu₂ hv₂ hf₂ ρ hρ ψ hψ
