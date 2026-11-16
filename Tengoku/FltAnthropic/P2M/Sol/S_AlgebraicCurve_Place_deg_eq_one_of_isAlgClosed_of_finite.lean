import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite

open AlgebraicCurve

/--
@isnad1 id=eq.0h3v.s7.f20f544719b4 from=translated src=- shape=79f591ed vocab=a8abd381
-/
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (v : Place K F)
    [Module.Finite K v.ResidueField] : v.deg = 1 := by
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm
