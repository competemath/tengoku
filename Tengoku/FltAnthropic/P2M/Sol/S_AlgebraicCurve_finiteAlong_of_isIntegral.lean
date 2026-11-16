import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Correspondence
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Algebra
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_finiteAlong_of_isIntegral.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_finiteAlong_of_isIntegral

set_option autoImplicit false

open AlgebraicCurve

/--
@isnad1 id=finiteal.1h4v.s7.802764fa3af4 from=translated src=- shape=77e19c5d vocab=0a2468af
-/
theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra.EssFiniteType K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) :
    FiniteAlong K φ := by
  classical
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Algebra.EssFiniteType F F' := Algebra.EssFiniteType.of_comp K F F'
  obtain ⟨s, hs⟩ := IntermediateField.fg_top F F'
  have hfin : FiniteDimensional F (IntermediateField.adjoin F (s : Set F')) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [hs] at hfin
  show Module.Finite F F'
  exact (IntermediateField.topEquiv (F := F) (E := F')).toLinearEquiv.finiteDimensional
