import Tengoku.FltAnthropic.Definitions.Def_ModularForm_HeckeOperator
import Tengoku.Seed.NumberTheory.ModularForms.Discriminant
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Tengoku.Seed.LinearAlgebra.Matrix.SpecialLinearGroup
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_discriminant_slash_fricke_eq_discriminant_slash_heckeDiagMatrix.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_discriminant_slash_fricke_eq_discriminant_slash_heckeDiagMatrix
set_option autoImplicit false
open UpperHalfPlane Matrix MatrixGroups
open scoped ModularForm

namespace S09WD5

private theorem slash_mapGL (k : ℤ) (f : ℍ → ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = f ∣[k] γ := rfl

private theorem coe_mapGL_eq_map (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)
      = ((γ : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ ℝ) := rfl

end S09WD5

private theorem ModularCurve.discriminant_slash_fricke_eq_discriminant_slash_heckeDiagMatrix (p : ℕ) [NeZero p] (W : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) : ModularForm.discriminant ∣[(12 : ℤ)] W = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p := by
  have hp : p ≠ 0 := NeZero.ne p
  have hS : ((Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S :
      Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 0] := by
    rw [S09WD5.coe_mapGL_eq_map, ModularGroup.coe_S]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hW1 : W = Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * ModularForm.heckeDiagMatrix p := by
    apply Units.ext
    rw [Units.val_mul, hS, ModularForm.val_heckeDiagMatrix hp, hW]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hW1, SlashAction.slash_mul, S09WD5.slash_mapGL, ModularForm.discriminant_S_invariant]

/--
@isnad1 id=eq.1h2v.s9.f68fd6256608 from=translated src=- shape=87a66e75 vocab=48d0bf8a
-/
theorem solution (p : ℕ) [NeZero p] (W : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) : ModularForm.discriminant ∣[(12 : ℤ)] W = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p :=
  ModularCurve.discriminant_slash_fricke_eq_discriminant_slash_heckeDiagMatrix p W hW
