import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w t

open scoped TensorProduct

theorem MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le
    {σ : Type w} [Finite σ] {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    {ι : Type t} (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ N ≤
      Ideal.span (Set.range φ)) :
    ∃ e : S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) ≃ₐ[S]
        (MvPowerSeries σ S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i))),
      ∀ (s : S) (q : MvPowerSeries σ R),
        e (s ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range φ)) q) =
          s • Ideal.Quotient.mk (Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i)))
            (MvPowerSeries.map (algebraMap R S) q) := by exact @_root_.P2MW.S_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le.solution σ _ R _ S _ _ ι φ N hN
