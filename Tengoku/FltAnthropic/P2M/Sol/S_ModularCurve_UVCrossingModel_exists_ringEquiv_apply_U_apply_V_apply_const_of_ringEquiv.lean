import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_UVCrossingModel_exists_ringEquiv_apply_U_apply_V_apply_const_of_ringEquiv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_apply_U_apply_V_apply_const_of_ringEquiv

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

namespace ModelTransport

noncomputable def mapEquiv {σ : Type*} {W W' : Type*} [CommRing W] [CommRing W'] (ρ : W ≃+* W') :
    MvPowerSeries σ W ≃+* MvPowerSeries σ W' :=
  RingEquiv.ofRingHom (MvPowerSeries.map (ρ : W →+* W')) (MvPowerSeries.map (ρ.symm : W' →+* W))
    (by
      ext p n
      simp)
    (by
      ext p n
      simp)

/--
@isnad1 id=eq.0h5v.s8.cc03e9b73189 from=translated src=- shape=56a29c03 vocab=b736dc1b
-/
theorem mapEquiv_apply {σ : Type*} {W W' : Type*} [CommRing W] [CommRing W'] (ρ : W ≃+* W')
    (p : MvPowerSeries σ W) : mapEquiv ρ p = MvPowerSeries.map (ρ : W →+* W') p := rfl

end ModelTransport

open ModelTransport in
/--
@isnad1 id=ex.0h4v.s13.6af33d392ee1 from=translated src=- shape=5f9f265e vocab=5f9988d1
-/
theorem solution
    (W W' : Type) [CommRing W] [CommRing W'] (ρ : W ≃+* W') (π : W) :
    ∃ θ : UVCrossingModel W π ≃+* UVCrossingModel W' (ρ π),
      θ (U π) = U (ρ π) ∧ θ (V π) = V (ρ π) ∧ ∀ w : W, θ (const π w) = const (ρ π) (ρ w) := by
  classical
  have hIJ : uvCrossingIdeal W' (ρ π) = (uvCrossingIdeal W π).map (mapEquiv (σ := Fin 2) ρ : MvPowerSeries (Fin 2) W →+* MvPowerSeries (Fin 2) W') := by
    show Ideal.span _ = Ideal.map _ (Ideal.span _)
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    show _ = mapEquiv ρ _
    rw [mapEquiv_apply, map_sub, map_mul, MvPowerSeries.map_X, MvPowerSeries.map_X, MvPowerSeries.map_C]
    rfl
  refine ⟨Ideal.quotientEquiv _ _ (mapEquiv (σ := Fin 2) ρ) hIJ, ?_, ?_, ?_⟩
  · show Ideal.quotientEquiv _ _ _ hIJ (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = Ideal.Quotient.mk _ (MvPowerSeries.X 0)
    rw [Ideal.quotientEquiv_mk, mapEquiv_apply, MvPowerSeries.map_X]
  · show Ideal.quotientEquiv _ _ _ hIJ (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = Ideal.Quotient.mk _ (MvPowerSeries.X 1)
    rw [Ideal.quotientEquiv_mk, mapEquiv_apply, MvPowerSeries.map_X]
  · intro w
    show Ideal.quotientEquiv _ _ _ hIJ (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = Ideal.Quotient.mk _ (MvPowerSeries.C (ρ w))
    rw [Ideal.quotientEquiv_mk, mapEquiv_apply, MvPowerSeries.map_C]
    rfl
