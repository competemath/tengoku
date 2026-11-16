import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Differentials

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_pullbackDiff_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_pullbackDiff_smul

set_option autoImplicit false

open AlgebraicCurve in

/--
@isnad1 id=eq.0h6v.s9.753cf1e170ab from=translated src=- shape=7a8cb416 vocab=2fccf99c
-/
theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (g : F) (ω : Ω[F⁄K]) :
    pullbackDiff φ (g • ω) = φ g • pullbackDiff φ ω := by
  letI : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  show (KaehlerDifferential.map K K F F') (g • ω) = φ g • (KaehlerDifferential.map K K F F') ω
  rw [map_smul]
  exact (algebraMap_smul F' g _).symm
