import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self

set_option autoImplicit false

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binarySubst_X binaryFormRepSL binaryFormRepSL_apply_coe exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self)
open _root_.HeckeEis

open MvPolynomial
open scoped MatrixGroups

theorem UnipotentFixedAux.eq_S_mul_T_zpow_neg_mul_S_inv {h : ℤ} (g : SL(2, ℤ))
    (hg : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; h, 1]) :
    g = ModularGroup.S * ModularGroup.T ^ (-h) * ModularGroup.S⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, ModularGroup.coe_T_zpow, ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h2v.s9.f59169d86b3c from=translated src=- shape=c6edfdaf vocab=dc39d1dd
-/
theorem UnipotentFixedAux.binarySubst_S_X_zero_pow (R : Type*) [CommRing R] (n : ℕ) :
    binarySubst R ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (MvPolynomial.X 0 ^ n)
      = (MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) R) := by
  rw [map_pow, binarySubst_X, ModularGroup.coe_S]
  simp [Fin.sum_univ_two]

open UnipotentFixedAux in

/--
@isnad1 id=ex.4h5v.s12.8094864e1ab6 from=translated src=- shape=4e5afc0d vocab=0bb5f9ec
-/
theorem SolMain.A3 {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {h : ℤ} (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0)
    (g : SL(2, ℤ)) (hg : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; h, 1])
    (P : ↥(BinaryForm R n)) (hP : binaryFormRepSL R n g P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 1 ^ n := by
  have hgS := eq_S_mul_T_zpow_neg_mul_S_inv g hg
  set Q : ↥(BinaryForm R n) := binaryFormRepSL R n ModularGroup.S⁻¹ P with hQ
  have hQfix : binaryFormRepSL R n (ModularGroup.T ^ (-h)) Q = Q := by
    have h1 : binaryFormRepSL R n ModularGroup.S⁻¹ (binaryFormRepSL R n g P) = Q := by rw [hP]
    rwa [hgS, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (binaryFormRepSL R n _),
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
  have hh' : ((-h : ℤ) : R) ≠ 0 := by rw [Int.cast_neg]; exact neg_ne_zero.mpr hh
  obtain ⟨c, hc⟩ := exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self n hh' hn Q hQfix
  refine ⟨c, ?_⟩
  have hPQ : P = binaryFormRepSL R n ModularGroup.S Q := by
    rw [hQ, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hPQ, binaryFormRepSL_apply_coe, hc, map_smul, binarySubst_S_X_zero_pow]

end HeckeEis

open scoped MatrixGroups in
/--
@isnad1 id=ex.4h5v.s12.8094864e1ab6 from=translated src=- shape=4e5afc0d vocab=0bb5f9ec
-/
theorem solution {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {h : ℤ} (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0)
    (g : SL(2, ℤ)) (hg : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; h, 1])
    (P : ↥(HeckeEis.BinaryForm R n)) (hP : HeckeEis.binaryFormRepSL R n g P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 1 ^ n :=
  HeckeEis.SolMain.A3 n hh hn g hg P hP

