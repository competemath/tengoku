import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra

set_option autoImplicit false

universe u v w

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type w) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [FiniteDimensional K L]
    (B : Subalgebra R L) :
    IsNoetherianRing ↥B ∧ ringKrullDim ↥B ≤ 1 := by
  haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hR
  obtain ⟨hN, hD, -⟩ :=
    Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite (K := K) B
  haveI := hD
  exact ⟨hN, Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ↥B)⟩
