import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral

import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm
import Tengoku.FltAnthropic.Theorems.Thm_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range

set_option autoImplicit false

open scoped Manifold MatrixGroups

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binaryFormRepSL binaryFormRepSL_apply_coe linePow coe_linePow IsEichlerIntegral coeff_single_one_eq_eval_of_mem_binaryForm mem_range_binaryFormRepSL_T_zpow_sub_one)
namespace CuspInftySol
open _root_.HeckeEis

open _root_.UpperHalfPlane open _root_.MvPolynomial open _root_.HeckeEis open _root_.P2MW.S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range.HeckeEis
open scoped Manifold MatrixGroups

theorem eval_binarySubst_T_zpow (h : ℤ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![0, 1] (binarySubst ℂ ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P)
      = MvPolynomial.eval ![0, 1] P := by
  have key : (fun j : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℂ) (![0, 1] : Fin 2 → ℂ)
      (∑ i : Fin 2, C ((((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ) * X i))
      = (![0, 1] : Fin 2 → ℂ) := by
    funext j
    fin_cases j <;> simp [ModularGroup.coe_T_zpow, Fin.sum_univ_two]
  rw [binarySubst, MvPolynomial.aeval_eq_bind₁, MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁, key]

theorem coeff_single_one_binaryFormRepSL_T_zpow (n : ℕ) (h : ℤ) (P : ↥(BinaryForm ℂ n)) :
    MvPolynomial.coeff (Finsupp.single 1 n)
        ((binaryFormRepSL ℂ n (ModularGroup.T ^ h) P : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
      = MvPolynomial.coeff (Finsupp.single 1 n) (P : MvPolynomial (Fin 2) ℂ) := by
  rw [coeff_single_one_eq_eval_of_mem_binaryForm (binaryFormRepSL ℂ n _ P).2,
    coeff_single_one_eq_eval_of_mem_binaryForm P.2, binaryFormRepSL_apply_coe, eval_binarySubst_T_zpow]

theorem coeff_single_one_linePow (n : ℕ) (z : ℂ) :
    MvPolynomial.coeff (Finsupp.single 1 n) ((linePow n z : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = 1 := by
  rw [coeff_single_one_eq_eval_of_mem_binaryForm (linePow n z).2, coe_linePow]
  simp

end HeckeEis.CuspInftySol

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range.HeckeEis HeckeEis.CuspInftySol UpperHalfPlane MvPolynomial in
theorem solution {n : ℕ} {h : ℤ} (hh : h ≠ 0)
    {g : UpperHalfPlane → ℂ} {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) ((h : ℝ) : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hzero : UpperHalfPlane.IsZeroAtImInfty g) (τ : UpperHalfPlane) :
    G ((h : ℝ) +ᵥ τ) - HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)
      ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) - 1) := by
  apply mem_range_binaryFormRepSL_T_zpow_sub_one n hh
  rw [Submodule.coe_sub, coeff_sub, coeff_single_one_binaryFormRepSL_T_zpow, sub_eq_zero]
  set φ : ℂ → ℂ := fun z =>
    MvPolynomial.coeff (Finsupp.single 1 n) ((G (ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) with hφdef
  have hφ : ∀ σ : ℍ, HasDerivAt φ (g σ) ↑σ := fun σ => by
    have := hG (Finsupp.single 1 n) σ
    rw [coeff_single_one_linePow, mul_one] at this
    exact this
  suffices hs : φ ((((h : ℝ) +ᵥ τ : ℍ) : ℂ)) = φ (τ : ℂ) by
    simpa only [hφdef, ofComplex_apply] using hs
  rw [coe_vadd, add_comm]
  rcases lt_or_gt_of_ne hh with hneg | hpos
  · have hper' : Function.Periodic (g ∘ ofComplex) (((-h : ℤ) : ℝ) : ℂ) := by
      push_cast
      exact hper.neg
    have key := UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty (h := ((-h : ℤ) : ℝ))
      (by exact_mod_cast (neg_pos.mpr hneg)) hper' hhol hzero hφ ((h : ℝ) +ᵥ τ)
    rw [coe_vadd] at key
    push_cast at key ⊢
    have e : (h : ℂ) + (τ : ℂ) + -(h : ℂ) = (τ : ℂ) := by ring
    rw [e] at key
    rw [add_comm]
    exact key.symm
  · have key := UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty (h := ((h : ℤ) : ℝ))
      (by exact_mod_cast hpos) hper hhol hzero hφ τ
    push_cast at key ⊢
    exact key

end
