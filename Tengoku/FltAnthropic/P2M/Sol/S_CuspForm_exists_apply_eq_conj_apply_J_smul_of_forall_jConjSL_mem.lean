import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PeriodHomPair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem

set_option autoImplicit false

open UpperHalfPlane Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm ComplexConjugate Pointwise

noncomputable section

namespace CuspForm
export _root_.CuspForm (translate ext)
namespace ConjInvolution
open _root_.CuspForm

/--
@isnad1 id=eq.0h1v.s10.c4cffff0b514 from=translated src=- shape=cc935429 vocab=d1af7eee
-/
theorem J_inv_mul_mapGL_mul_J (γ : SL(2, ℤ)) :
    UpperHalfPlane.J⁻¹ * (mapGL ℝ γ : GL (Fin 2) ℝ) * UpperHalfPlane.J =
      (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) := by
  have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two, ModularCurve.Period.jConjMat,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.vecMul, dotProduct]

/--
@isnad1 id=eq.1h1v.s11.830216630437 from=translated src=- shape=ca8330ba vocab=18d45b31
-/
theorem conjAct_J_inv_smul_eq (Γ : Subgroup SL(2, ℤ))
    (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) :
    ConjAct.toConjAct (UpperHalfPlane.J)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) =
      (Γ : Subgroup (GL (Fin 2) ℝ)) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  constructor
  · rintro ⟨γ, hγ, hx⟩
    refine ⟨ModularCurve.Period.jConjSL γ, hΓ γ hγ, ?_⟩
    rw [← J_inv_mul_mapGL_mul_J]
    rw [show (mapGL ℝ γ : GL (Fin 2) ℝ) = UpperHalfPlane.J * x * UpperHalfPlane.J⁻¹ from hx]
    group
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨ModularCurve.Period.jConjSL γ, hΓ γ hγ, ?_⟩
    change (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) = _
    rw [← J_inv_mul_mapGL_mul_J]
    have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
      rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
    rw [hJ]

def conjOf (Γ : Subgroup SL(2, ℤ)) (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) {k : ℤ}
    (f : CuspForm Γ k) : CuspForm Γ k :=
  (CuspForm.translate f UpperHalfPlane.J).copy ((⇑f) ∣[k] UpperHalfPlane.J) rfl
    (conjAct_J_inv_smul_eq Γ hΓ).symm

/--
@isnad1 id=eq.1h4v.s10.d691f4f3daf3 from=translated src=- shape=fc218028 vocab=a80d79b9
-/
theorem conjOf_apply (Γ : Subgroup SL(2, ℤ)) (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) {k : ℤ}
    (f : CuspForm Γ k) (τ : ℍ) : conjOf Γ hΓ f τ = conj (f (UpperHalfPlane.J • τ)) := by
  show ((⇑f) ∣[k] UpperHalfPlane.J) τ = _
  rw [ModularForm.slash_def]
  simp [UpperHalfPlane.sigma_J, UpperHalfPlane.denom_J, UpperHalfPlane.det_J]

end CuspForm.ConjInvolution

end

/--
@isnad1 id=ex.1h3v.s11.0bf98f058f35 from=translated src=- shape=88486107 vocab=893d3cf7
-/
theorem solution
    (Γ : Subgroup SL(2, ℤ)) (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) (k : ℤ)
    (f : CuspForm Γ k) :
    ∃ g : CuspForm Γ k, ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)) :=
  ⟨CuspForm.ConjInvolution.conjOf Γ hΓ f, CuspForm.ConjInvolution.conjOf_apply Γ hΓ f⟩
