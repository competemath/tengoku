import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL

set_option autoImplicit false

namespace HeckeEis
export _root_.HeckeEis (eval_smul_of_isHomogeneous BinaryForm binarySubst binarySubst_X binaryFormRepSL binaryFormRepSL_apply_coe jFactor jFactor_ne_zero coe_smul_mul_jFactor)
namespace PeriodFnAux
open _root_.HeckeEis

open UpperHalfPlane MvPolynomial
open scoped MatrixGroups

theorem eval_binarySubst {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → K)
    (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval v (binarySubst K M P)
      = MvPolynomial.eval (fun j => ∑ i : Fin 2, ((M i j : ℤ) : K) * v i) P := by
  have key : (MvPolynomial.eval v).comp (binarySubst K M : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K).toRingHom
      = MvPolynomial.eval (fun j => ∑ i : Fin 2, ((M i j : ℤ) : K) * v i) :=
    MvPolynomial.ringHom_ext (fun a => by simp) (fun j => by simp [binarySubst_X])
  exact RingHom.congr_fun key P

theorem det_entries (g : SL(2, ℤ)) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)
      - ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

theorem jFactor_pow_mul_eval_binaryFormRepSL (n : ℕ) (g : SL(2, ℤ)) (τ : ℍ) (P : ↥(BinaryForm ℂ n)) :
    jFactor g τ ^ n * MvPolynomial.eval ![(1 : ℂ), -(((g • τ : ℍ)) : ℂ)]
        ((binaryFormRepSL ℂ n g P : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
      = MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] (P : MvPolynomial (Fin 2) ℂ) := by
  rw [binaryFormRepSL_apply_coe, eval_binarySubst]
  have hj : jFactor g τ ≠ 0 := jFactor_ne_zero g τ
  have hJ : jFactor g τ = ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) + ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) := rfl
  have hmul := coe_smul_mul_jFactor g τ
  have hdet := det_entries g
  have hrow : ∀ j : Fin 2, jFactor g τ * (∑ i : Fin 2, (((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ)
        * (![(1 : ℂ), -(((g • τ : ℍ)) : ℂ)]) i) = (![(1 : ℂ), -(τ : ℂ)]) j := by
    intro j
    fin_cases j
    · simp only [Fin.sum_univ_two, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, mul_one]
      linear_combination (-(((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℂ)) * hmul
        + (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℂ) * hJ + hdet
    · simp only [Fin.sum_univ_two, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, mul_one]
      linear_combination (-(((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℂ)) * hmul
        + (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℂ) * hJ - (τ : ℂ) * hdet
  have hpt : (fun j : Fin 2 => ∑ i : Fin 2, (((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ)
        * (![(1 : ℂ), -(((g • τ : ℍ)) : ℂ)]) i)
      = (jFactor g τ)⁻¹ • ![(1 : ℂ), -(τ : ℂ)] := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, ← hrow j, ← mul_assoc, inv_mul_cancel₀ hj, one_mul]
  rw [hpt, eval_smul_of_isHomogeneous ((mem_homogeneousSubmodule n _).mp P.2), ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hj, one_pow, one_mul]

end HeckeEis.PeriodFnAux

open scoped MatrixGroups in

theorem solution (n : ℕ) (g : SL(2, ℤ)) (τ : UpperHalfPlane)
    (P : ↥(HeckeEis.BinaryForm ℂ n)) :
    HeckeEis.jFactor g τ ^ n * MvPolynomial.eval ![(1 : ℂ), -(((g • τ : UpperHalfPlane)) : ℂ)]
        ((HeckeEis.binaryFormRepSL ℂ n g P : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
      = MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] (P : MvPolynomial (Fin 2) ℂ) :=
  HeckeEis.PeriodFnAux.jFactor_pow_mul_eval_binaryFormRepSL n g τ P

