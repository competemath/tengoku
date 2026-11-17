import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_LocalChart
import Tengoku.FltAnthropic.P2M.Sol.S_DrinfeldCurve_LocalChart_exists_linearPart_conj_ringEquiv_of_apply_mk_X_mem_span

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DrinfeldCurve_LocalChart_exists_linearPart_conj_ringEquiv_of_apply_mk_X_mem_span.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem DrinfeldCurve.LocalChart.exists_linearPart_conj_ringEquiv_of_apply_mk_X_mem_span
    (q : ℕ) [Fact q.Prime]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    (t₀ : W₀) (ht₀ : t₀ ∈ IsLocalRing.maximalIdeal W₀) (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ (q + 2))
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (t : W) (ht : t ∈ IsLocalRing.maximalIdeal W) (f u v : MvPowerSeries (Fin 2) W)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (β : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) ≃+*
      (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C t * v - f * u}))
    (βW : W₀ ≃+* W)
    (hβ : ∀ w : W₀, β (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (βW w)))
    (hβJ : ∀ jj : Fin 2, β (Ideal.Quotient.mk _ (MvPowerSeries.X jj)) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 1)})
    (hβJ' : ∀ jj : Fin 2, β.symm (Ideal.Quotient.mk _ (MvPowerSeries.X jj)) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) (MvPowerSeries.X 1)})

    (θ₀ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) ≃+*
      (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}))
    (σW₀ : W₀ ≃+* W₀) (hσ : ∀ w : W₀, σW₀ w - w ∈ IsLocalRing.maximalIdeal W₀)
    (hsemi₀ : ∀ w : W₀, θ₀ (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (σW₀ w)))
    (M₀ : Matrix (Fin 2) (Fin 2) W₀)
    (hlin₀ : ∀ jj : Fin 2, θ₀ (Ideal.Quotient.mk _ (MvPowerSeries.X jj)) -
        Ideal.Quotient.mk _ (∑ ii : Fin 2, MvPowerSeries.C (M₀ ii jj) * MvPowerSeries.X ii) ∈
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t₀ * v₀ - f₀ * u₀}) (MvPowerSeries.X 1)}) ^ 2) :
    let S := MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C t * v - f * u}
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u})
    let θ : S ≃+* S := β.symm.trans (θ₀.trans β)
    let σW : W ≃+* W := βW.symm.trans (σW₀.trans βW)
    ∃ (B : Matrix (Fin 2) (Fin 2) W) (B' : Matrix (Fin 2) (Fin 2) W₀) (M : Matrix (Fin 2) (Fin 2) W),

      (∀ jj : Fin 2, β (Ideal.Quotient.mk _ (MvPowerSeries.X jj)) -
          mkS (∑ ii : Fin 2, MvPowerSeries.C (B ii jj) * MvPowerSeries.X ii) ∈
        (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧

      (∀ ii jj : Fin 2, (B * B'.map βW) ii jj - (1 : Matrix (Fin 2) (Fin 2) W) ii jj ∈ IsLocalRing.maximalIdeal W) ∧

      (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) ∧

      (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
          mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
        (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧

      (∀ ii jj : Fin 2, M ii jj - (B * M₀.map βW * B'.map βW) ii jj ∈ IsLocalRing.maximalIdeal W) := by exact @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_linearPart_conj_ringEquiv_of_apply_mk_X_mem_span.solution q _ W₀ _ _ _ _ t₀ ht₀ f₀ u₀ v₀ hf₀ W _ _ _ _ t ht f u v hf β βW hβ hβJ hβJ' θ₀ σW₀ hσ hsemi₀ M₀ hlin₀
