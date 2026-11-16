import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Correspondence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_finiteAlong_comp.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_finiteAlong_comp

set_option autoImplicit false

open AlgebraicCurve

/--
@isnad1 id=finiteal.2h6v.s7.d0a81251ddf3 from=translated src=- shape=53eee17a vocab=0e2e3031
-/
theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : FiniteAlong K φ) (hχ : FiniteAlong K χ) : FiniteAlong K (χ.comp φ) := by
  letI := algebraAlong φ
  letI := algebraAlong χ
  letI := algebraAlong (χ.comp φ)
  haveI : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite F F' := hφ
  haveI : Module.Finite F' F'' := hχ
  exact Module.Finite.trans F' F''
