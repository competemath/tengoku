import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj

set_option autoImplicit false

namespace HeckeEis
export _root_.HeckeEis (heckeConjMat heckeUpper mem_heckeUpper heckeConjSL coe_heckeConjSL heckeConj binarySubst binarySubst_mul binaryFormRepSL binaryFormAlphaAdj)
open _root_.HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups

theorem alphaAdjMat_mul_heckeConjMat {ℓ : ℕ} {g : Matrix (Fin 2) (Fin 2) ℤ} (hg : (ℓ : ℤ) ∣ g 0 1) :
    !![(ℓ : ℤ), 0; 0, 1] * heckeConjMat ℓ g = g * !![(ℓ : ℤ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, heckeConjMat, Int.mul_ediv_cancel' hg, mul_comm]

theorem SolMain.A1 (K : Type*) [CommRing K] (n N ℓ : ℕ) [NeZero ℓ]
    (u : ↥(heckeUpper N ℓ)) :
    binaryFormAlphaAdj K n ℓ ∘ₗ ((binaryFormRepSL K n).comp (Gamma0 N).subtype) (heckeConj N ℓ u)
      = ((binaryFormRepSL K n).comp (Gamma0 N).subtype) (u : Gamma0 N) ∘ₗ binaryFormAlphaAdj K n ℓ := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  change binarySubst K !![(ℓ : ℤ), 0; 0, 1]
      (binarySubst K ((heckeConjSL N ℓ u : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (v : MvPolynomial (Fin 2) K))
    = binarySubst K ((((u : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      (binarySubst K !![(ℓ : ℤ), 0; 0, 1] (v : MvPolynomial (Fin 2) K))
  rw [← AlgHom.comp_apply, ← binarySubst_mul, ← AlgHom.comp_apply, ← binarySubst_mul, coe_heckeConjSL,
    alphaAdjMat_mul_heckeConjMat ((mem_heckeUpper N ℓ).mp u.2)]

end HeckeEis

open scoped MatrixGroups in
theorem solution (K : Type*) [CommRing K] (n N ℓ : ℕ) [NeZero ℓ]
    (u : ↥(HeckeEis.heckeUpper N ℓ)) :
    HeckeEis.binaryFormAlphaAdj K n ℓ ∘ₗ ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.heckeConj N ℓ u)
      = ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) (u : CongruenceSubgroup.Gamma0 N)
          ∘ₗ HeckeEis.binaryFormAlphaAdj K n ℓ :=
  HeckeEis.SolMain.A1 K n N ℓ u

