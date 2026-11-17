import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one

set_option autoImplicit false

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace FrickeGamma1

open ConjAct Pointwise

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable (M : ℕ) [NeZero M]

noncomputable def frickeGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

/--
@isnad1 id=eq.0h1v.s8.4c62961a9540 from=translated src=- shape=29ac05b7 vocab=de86d62f
-/
@[scoped simp] theorem val_frickeGL :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

/--
@isnad1 id=eq.0h1v.s8.8476debe49a9 from=translated src=- shape=da3d4a8d vocab=ddf79548
-/
theorem det_frickeGL : ((frickeGL M).det : ℝ) = M := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]; ring

/--
@isnad1 id=lt.0h1v.s8.1290ead68c7c from=translated src=- shape=e86674f2 vocab=7f3b95b2
-/
theorem det_frickeGL_pos : 0 < ((frickeGL M).det : ℝ) := by
  rw [det_frickeGL]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)

variable {M}

def frickeConj (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 1 1, -(γ 1 0 / M); -(M * γ 0 1), γ 0 0], by
    rw [Matrix.det_fin_two_of]
    have h1 := Matrix.det_fin_two γ.1
    rw [γ.2] at h1
    obtain ⟨c', hc'⟩ := hγ
    have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
    rw [hc', Int.mul_ediv_cancel_left _ hM]
    rw [hc'] at h1
    linear_combination (-1 : ℤ) * h1⟩

/--
@isnad1 id=ex.1h2v.s9.dbcebb1705ea from=translated src=- shape=d2bf57af vocab=b6a45def
-/
theorem frickeConj_mem_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    ∃ hd : (M : ℤ) ∣ γ 1 0, frickeConj γ hd ∈ Gamma1 M := by
  rw [Gamma1_mem] at hγ
  obtain ⟨ha, hd, hc⟩ := hγ
  have hdvd : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 hc
  refine ⟨hdvd, ?_⟩
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · show (((γ 1 1 : ℤ)) : ZMod M) = 1; exact hd
  · show (((γ 0 0 : ℤ)) : ZMod M) = 1; exact ha
  · show (((-(M * γ 0 1) : ℤ)) : ZMod M) = 0
    rw [Int.cast_neg, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, neg_zero]

/--
@isnad1 id=eq.1h3v.s9.49bc4b06dec9 from=translated src=- shape=bf150676 vocab=39515c6e
-/
theorem coe_frickeConj (γ : SL(2, ℤ)) (c' : ℤ) (hc' : γ 1 0 = M * c') :
    ((frickeConj γ ⟨c', hc'⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 1 1, -c'; -(M * γ 0 1), γ 0 0] := by
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hq : γ 1 0 / M = c' := by rw [hc', Int.mul_ediv_cancel_left _ hM]
  simp [frickeConj, hq]

/--
@isnad1 id=eq.1h2v.s11.8ff705220fd4 from=translated src=- shape=ca13747f vocab=e0ff28b5
-/
theorem frickeGL_mul_coe (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) :
    frickeGL M * (γ : GL (Fin 2) ℝ) = ((frickeConj γ hγ : SL(2, ℤ)) : GL (Fin 2) ℝ) * frickeGL M := by
  obtain ⟨c', hc'⟩ := hγ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_frickeConj γ c' hc', hc'] <;> ring

/--
@isnad1 id=eq.1h2v.s11.adeca05674cb from=translated src=- shape=6215dec5 vocab=e0ff28b5
-/
theorem coe_mul_frickeGL (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) :
    (γ : GL (Fin 2) ℝ) * frickeGL M = frickeGL M * ((frickeConj γ hγ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  obtain ⟨c', hc'⟩ := hγ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_frickeConj γ c' hc', hc'] <;> ring

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
/--
@isnad1 id=iff.0h2v.s10.4a1b10a48608 from=translated src=- shape=c96aa11b vocab=8b532cc7
-/
theorem mem_map_Gamma1_iff (x : GL (Fin 2) ℝ) :
    x ∈ (Γ₁ℝ M) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 M ∧ (γ : GL (Fin 2) ℝ) = x :=
  Subgroup.mem_map

/--
@isnad1 id=mem.1h2v.s10.d580761cc10a from=translated src=- shape=6cecea9a vocab=4e73a245
-/
theorem frickeGL_mul_mul_inv_mem {x : GL (Fin 2) ℝ} (hx : x ∈ (Γ₁ℝ M)) :
    frickeGL M * x * (frickeGL M)⁻¹ ∈ (Γ₁ℝ M) := by
  obtain ⟨γ, hγ, rfl⟩ := (mem_map_Gamma1_iff x).1 hx
  obtain ⟨hd, hmem⟩ := frickeConj_mem_Gamma1 hγ
  rw [frickeGL_mul_coe γ hd, mul_inv_cancel_right]
  exact (mem_map_Gamma1_iff _).2 ⟨_, hmem, rfl⟩

/--
@isnad1 id=mem.1h2v.s10.e3350076b736 from=translated src=- shape=3f713a55 vocab=4e73a245
-/
theorem frickeGL_inv_mul_mul_mem {x : GL (Fin 2) ℝ} (hx : x ∈ (Γ₁ℝ M)) :
    (frickeGL M)⁻¹ * x * frickeGL M ∈ (Γ₁ℝ M) := by
  obtain ⟨γ, hγ, rfl⟩ := (mem_map_Gamma1_iff x).1 hx
  obtain ⟨hd, hmem⟩ := frickeConj_mem_Gamma1 hγ
  rw [mul_assoc, coe_mul_frickeGL γ hd, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (mem_map_Gamma1_iff _).2 ⟨_, hmem, rfl⟩

/--
@isnad1 id=eq.0h1v.s11.f01465b11b1c from=translated src=- shape=c92f6a80 vocab=79defd9f
-/
theorem toConjAct_frickeGL_inv_smul :
    toConjAct (frickeGL M)⁻¹ • (Γ₁ℝ M) = (Γ₁ℝ M) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul]
  constructor
  · intro h
    have := frickeGL_inv_mul_mul_mem h
    rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right] at this
  · exact frickeGL_mul_mul_inv_mem

/--
@isnad1 id=eq.0h2v.s8.8ad33cdd950f from=translated src=- shape=ee4d1bfc vocab=2ead24a5
-/
theorem coe_frickeGL_smul (τ : ℍ) : (↑(frickeGL M • τ) : ℂ) = -1 / ((M : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom]

/--
@isnad1 id=eq.0h2v.s5.8374bc169f88 from=translated src=- shape=7cd46847 vocab=af5a2683
-/
theorem denom_frickeGL (τ : ℍ) : UpperHalfPlane.denom (frickeGL M) τ = (M : ℂ) * (τ : ℂ) := by
  simp [UpperHalfPlane.denom]

/--
@isnad1 id=eq.0h4v.s8.f958aa70894f from=translated src=- shape=b50c44f6 vocab=4dfdbaf9
-/
theorem slash_frickeGL_apply (f : ℍ → ℂ) (k : ℤ) (τ : ℍ) :
    (f ∣[k] frickeGL M) τ = (M : ℂ)⁻¹ * (τ : ℂ) ^ (-k) * f (frickeGL M • τ) := by
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, ite_eq_left (det_frickeGL_pos M), det_frickeGL,
    denom_frickeGL]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  rw [ContinuousAlgEquiv.refl_apply,
    abs_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M) : (0 : ℝ) < M),
    Complex.ofReal_natCast, mul_zpow, zpow_neg (M : ℂ) k, zpow_sub_one₀ hM]
  field_simp

noncomputable def frickeForm {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) : CuspForm (Γ₁ℝ M) k :=
  ((M : ℝ) • CuspForm.translate g (frickeGL M)).copy
    (fun τ => (τ : ℂ) ^ (-k) * g (frickeGL M • τ))
    (by
      funext τ
      rw [FunLike.coe_smul, Pi.smul_apply, CuspForm.translate]
      show _ = (M : ℝ) • ((⇑g ∣[k] frickeGL M) τ)
      rw [slash_frickeGL_apply, Complex.real_smul, Complex.ofReal_natCast]
      have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
      field_simp)
    (toConjAct_frickeGL_inv_smul).symm

/--
@isnad1 id=eq.0h4v.s9.150877945dae from=translated src=- shape=35761523 vocab=75b87f83
-/
theorem frickeForm_apply {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) (τ : ℍ) :
    frickeForm g τ = (τ : ℂ) ^ (-k) * g (frickeGL M • τ) := rfl

theorem eq_frickeGL_smul {τ τ' : ℍ} (h : (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1) :
    τ' = frickeGL M • τ := by
  apply UpperHalfPlane.ext
  rw [coe_frickeGL_smul]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp
  linear_combination h

/--
@isnad1 id=eq.1h5v.s9.5c2dddcbfa8d from=translated src=- shape=4504ab73 vocab=9755d618
-/
theorem apply_eq_zpow_mul_frickeForm {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) {τ τ' : ℍ}
    (h : (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1) :
    g τ' = (τ : ℂ) ^ k * frickeForm g τ := by
  rw [frickeForm_apply, eq_frickeGL_smul h, ← mul_assoc, ← zpow_add₀ (UpperHalfPlane.ne_zero τ),
    add_neg_cancel, zpow_zero, one_mul]

end FrickeGamma1
open scoped _root_.P2MW.S_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one.FrickeGamma1

/--
@isnad1 id=ex.0h3v.s10.b9388be66ab1 from=translated src=- shape=8caefadc vocab=111482eb
-/
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (g : CuspForm (Gamma1 M) k) :
    ∃ h : CuspForm (Gamma1 M) k,
      ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
        g τ' = (τ : ℂ) ^ k * h τ :=
  ⟨FrickeGamma1.frickeForm g, fun _ _ h => FrickeGamma1.apply_eq_zpow_mul_frickeForm g h⟩
