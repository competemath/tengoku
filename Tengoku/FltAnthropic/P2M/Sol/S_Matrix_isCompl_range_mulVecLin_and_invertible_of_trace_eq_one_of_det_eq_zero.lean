import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero

set_option autoImplicit false

open TensorProduct

namespace Matrix
export _root_.Matrix (sub_mulVec ext one_mulVec comp mulVec_single_one mulVecLin det_fin_two mulVecLin_apply rank mulVec_mulVec zero_apply single mulVec_sub neg_apply smul_apply det add_apply comp_apply of one mul_apply trace module mulVecLin_mul trace_fin_two mulVec)
namespace RankOneProjectorPlane
open _root_.Matrix

variable {R : Type*} [CommRing R] (e : Matrix (Fin 2) (Fin 2) R)

/--
@isnad1 id=eq.1h2v.s7.6c7bc0ec2f6c from=translated src=- shape=495e13e5 vocab=80f0a393
-/
theorem trace_eq (htr : e.trace = 1) : e 0 0 + e 1 1 = 1 := by
  rw [Matrix.trace_fin_two] at htr; exact htr

/--
@isnad1 id=eq.1h2v.s7.49ecd900784d from=translated src=- shape=36508f88 vocab=556c2a3c
-/
theorem det_eq (hdet : e.det = 0) : e 0 0 * e 1 1 = e 0 1 * e 1 0 := by
  rw [Matrix.det_fin_two] at hdet; exact sub_eq_zero.mp hdet

/--
@isnad1 id=eq.0h4v.s7.7f407c54a301 from=translated src=- shape=1a691a5a vocab=c262cbaf
-/
theorem mulVec_apply (M : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) (i : Fin 2) :
    M.mulVec v i = M i 0 * v 0 + M i 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h2v.s8.d1691d1517b7 from=translated src=- shape=91345052 vocab=0c81ccc9
-/
theorem one_sub_apply_00 : (1 - e) 0 0 = 1 - e 0 0 := by simp
/--
@isnad1 id=eq.0h2v.s8.627fccc18f31 from=translated src=- shape=91345052 vocab=0c81ccc9
-/
theorem one_sub_apply_11 : (1 - e) 1 1 = 1 - e 1 1 := by simp
/--
@isnad1 id=eq.0h2v.s7.00baf5aef783 from=translated src=- shape=42265c8b vocab=6debb8d4
-/
theorem one_sub_apply_01 : (1 - e) 0 1 = -e 0 1 := by simp
/--
@isnad1 id=eq.0h2v.s7.bc9d871ebcfd from=translated src=- shape=42265c8b vocab=6debb8d4
-/
theorem one_sub_apply_10 : (1 - e) 1 0 = -e 1 0 := by simp

/--
@isnad1 id=eq.2h2v.s7.dda3189bd81f from=translated src=- shape=469b3126 vocab=2566d505
-/
theorem mul_self_eq (htr : e.trace = 1) (hdet : e.det = 0) : e * e = e := by
  have ht := trace_eq e htr
  have hd := det_eq e hdet
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]; linear_combination e 0 0 * ht - hd
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; linear_combination e 0 1 * ht
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta]; linear_combination e 1 0 * ht
  · simp only [Fin.mk_one, Fin.isValue]; linear_combination e 1 1 * ht - hd

abbrev P : Submodule R (Fin 2 → R) := LinearMap.range (Matrix.mulVecLin e)

abbrev Q : Submodule R (Fin 2 → R) := LinearMap.range (Matrix.mulVecLin (1 - e))

/--
@isnad1 id=iff.2h3v.s8.8803d6fc67fc from=translated src=- shape=98d18b59 vocab=bf3af070
-/
theorem mem_P_iff (htr : e.trace = 1) (hdet : e.det = 0) (v : Fin 2 → R) : v ∈ P e ↔ e.mulVec v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    show e.mulVec (e.mulVec w) = e.mulVec w
    rw [Matrix.mulVec_mulVec, mul_self_eq e htr hdet]
  · intro hv; exact ⟨v, hv⟩

/--
@isnad1 id=iff.2h3v.s8.272583a63ff0 from=translated src=- shape=613799d4 vocab=4f2d489d
-/
theorem mem_Q_iff (htr : e.trace = 1) (hdet : e.det = 0) (v : Fin 2 → R) : v ∈ Q e ↔ e.mulVec v = 0 := by
  have hid : ∀ w : Fin 2 → R, (1 - e).mulVec w = w - e.mulVec w := fun w => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨w, rfl⟩
    show e.mulVec ((1 - e).mulVec w) = 0
    rw [hid, Matrix.mulVec_sub, Matrix.mulVec_mulVec, mul_self_eq e htr hdet, sub_self]
  · intro hv
    refine ⟨v, ?_⟩
    show (1 - e).mulVec v = v
    rw [hid, hv, sub_zero]

/--
@isnad1 id=iscompl.2h2v.s8.532d55fc80ab from=translated src=- shape=3991bb91 vocab=7aff8f4a
-/
theorem isCompl_P_Q (htr : e.trace = 1) (hdet : e.det = 0) : IsCompl (P e) (Q e) := by
  have hidem : IsIdempotentElem (Matrix.mulVecLin e) := by
    show Matrix.mulVecLin e * Matrix.mulVecLin e = Matrix.mulVecLin e
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, mul_self_eq e htr hdet]
  have hQ : Q e = LinearMap.ker (Matrix.mulVecLin e) := by
    ext v
    rw [mem_Q_iff e htr hdet, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [hQ]
  exact LinearMap.IsIdempotentElem.isCompl hidem

section Abstract

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/--
@isnad1 id=and.5h11v.s10.d486831c513d from=translated src=- shape=13e3a566 vocab=557d8709
-/
theorem key (a b c d : R) (ht : a + d = 1) (g₀ g₁ : M) (h₀ h₁ : N)
    (r1 : d • g₀ = c • g₁) (r2 : b • g₀ = a • g₁) (r3 : a • h₀ = -(c • h₁)) (r4 : b • h₀ = -(d • h₁)) :
    (-c) • (g₀ ⊗ₜ[R] h₁ - g₁ ⊗ₜ[R] h₀) = g₀ ⊗ₜ[R] h₀ ∧
      a • (g₀ ⊗ₜ[R] h₁ - g₁ ⊗ₜ[R] h₀) = g₀ ⊗ₜ[R] h₁ ∧
      (-d) • (g₀ ⊗ₜ[R] h₁ - g₁ ⊗ₜ[R] h₀) = g₁ ⊗ₜ[R] h₀ ∧
      b • (g₀ ⊗ₜ[R] h₁ - g₁ ⊗ₜ[R] h₀) = g₁ ⊗ₜ[R] h₁ := by
  have hc1 : c • h₁ = -(a • h₀) := by rw [r3, neg_neg]
  have hd1 : d • h₁ = -(b • h₀) := by rw [r4, neg_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (-c) • (g₀ ⊗ₜ[R] h₁ - g₁ ⊗ₜ[R] h₀)
          = -(c • (g₀ ⊗ₜ[R] h₁)) + c • (g₁ ⊗ₜ[R] h₀) := by
            rw [smul_sub, neg_smul, neg_smul, sub_neg_eq_add]
      _ = -(g₀ ⊗ₜ[R] (c • h₁)) + (c • g₁) ⊗ₜ[R] h₀ := by
            rw [TensorProduct.smul_tmul' c g₀ h₁, TensorProduct.smul_tmul c g₀ h₁,
              TensorProduct.smul_tmul' c g₁ h₀]
      _ = -(g₀ ⊗ₜ[R] (-(a • h₀))) + (d • g₀) ⊗ₜ[R] h₀ := by rw [hc1, r1]
      _ = a • (g₀ ⊗ₜ[R] h₀) + d • (g₀ ⊗ₜ[R] h₀) := by
            rw [TensorProduct.tmul_neg, neg_neg, TensorProduct.tmul_smul, TensorProduct.smul_tmul' d g₀ h₀]
      _ = g₀ ⊗ₜ[R] h₀ := by rw [← add_smul, ht, one_smul]
  · calc a • (g₀ ⊗ₜ[R] h₁ - g₁ ⊗ₜ[R] h₀)
          = a • (g₀ ⊗ₜ[R] h₁) - g₁ ⊗ₜ[R] (a • h₀) := by
            rw [smul_sub, TensorProduct.smul_tmul' a g₁ h₀, TensorProduct.smul_tmul a g₁ h₀]
      _ = a • (g₀ ⊗ₜ[R] h₁) - g₁ ⊗ₜ[R] (-(c • h₁)) := by rw [r3]
      _ = a • (g₀ ⊗ₜ[R] h₁) + (c • g₁) ⊗ₜ[R] h₁ := by
            rw [TensorProduct.tmul_neg, sub_neg_eq_add, ← TensorProduct.smul_tmul c g₁ h₁]
      _ = a • (g₀ ⊗ₜ[R] h₁) + d • (g₀ ⊗ₜ[R] h₁) := by rw [← r1, TensorProduct.smul_tmul' d g₀ h₁]
      _ = g₀ ⊗ₜ[R] h₁ := by rw [← add_smul, ht, one_smul]
  · calc (-d) • (g₀ ⊗ₜ[R] h₁ - g₁ ⊗ₜ[R] h₀)
          = -(d • (g₀ ⊗ₜ[R] h₁)) + d • (g₁ ⊗ₜ[R] h₀) := by
            rw [smul_sub, neg_smul, neg_smul, sub_neg_eq_add]
      _ = -(g₀ ⊗ₜ[R] (d • h₁)) + d • (g₁ ⊗ₜ[R] h₀) := by
            rw [TensorProduct.smul_tmul' d g₀ h₁, TensorProduct.smul_tmul d g₀ h₁]
      _ = -(g₀ ⊗ₜ[R] (-(b • h₀))) + d • (g₁ ⊗ₜ[R] h₀) := by rw [hd1]
      _ = (b • g₀) ⊗ₜ[R] h₀ + d • (g₁ ⊗ₜ[R] h₀) := by
            rw [TensorProduct.tmul_neg, neg_neg, ← TensorProduct.smul_tmul b g₀ h₀]
      _ = a • (g₁ ⊗ₜ[R] h₀) + d • (g₁ ⊗ₜ[R] h₀) := by rw [r2, TensorProduct.smul_tmul' a g₁ h₀]
      _ = g₁ ⊗ₜ[R] h₀ := by rw [← add_smul, ht, one_smul]
  · calc b • (g₀ ⊗ₜ[R] h₁ - g₁ ⊗ₜ[R] h₀)
          = (b • g₀) ⊗ₜ[R] h₁ - g₁ ⊗ₜ[R] (b • h₀) := by
            rw [smul_sub, TensorProduct.smul_tmul' b g₀ h₁, TensorProduct.smul_tmul' b g₁ h₀,
              TensorProduct.smul_tmul b g₁ h₀]
      _ = (a • g₁) ⊗ₜ[R] h₁ - g₁ ⊗ₜ[R] (-(d • h₁)) := by rw [r2, r4]
      _ = a • (g₁ ⊗ₜ[R] h₁) + d • (g₁ ⊗ₜ[R] h₁) := by
            rw [TensorProduct.tmul_neg, sub_neg_eq_add, TensorProduct.tmul_smul,
              TensorProduct.smul_tmul' a g₁ h₁]
      _ = g₁ ⊗ₜ[R] h₁ := by rw [← add_smul, ht, one_smul]

end Abstract

section Columns

def g (j : Fin 2) : ↥(P e) :=
  ⟨fun i => e i j, ⟨Pi.single j 1, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]; rfl⟩⟩

def h (j : Fin 2) : ↥(Q e) :=
  ⟨fun i => (1 - e) i j, ⟨Pi.single j 1, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]; rfl⟩⟩

/--
@isnad1 id=eq.0h4v.s8.7114d01d3c7c from=translated src=- shape=91fdd6e3 vocab=2e29fb3f
-/
@[scoped simp] theorem g_val (j i : Fin 2) : ((g e j : ↥(P e)) : Fin 2 → R) i = e i j := rfl
/--
@isnad1 id=eq.0h4v.s8.dee194b2fe2f from=translated src=- shape=1c574849 vocab=8785022d
-/
@[scoped simp] theorem h_val (j i : Fin 2) : ((h e j : ↥(Q e)) : Fin 2 → R) i = (1 - e) i j := rfl

def det₂ : (Fin 2 → R) →ₗ[R] (Fin 2 → R) →ₗ[R] R :=
  LinearMap.mk₂ R (fun v w => v 0 * w 1 - v 1 * w 0)
    (fun v v' w => by simp only [Pi.add_apply]; ring)
    (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun v w w' => by simp only [Pi.add_apply]; ring)
    (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

def δ : ↥(P e) ⊗[R] ↥(Q e) →ₗ[R] R :=
  TensorProduct.lift (((det₂ (R := R)).comp (P e).subtype).compl₂ (Q e).subtype)

/--
@isnad1 id=eq.0h4v.s13.47957e0b6b4c from=translated src=- shape=be3e7d74 vocab=1667fca7
-/
theorem δ_tmul (p : ↥(P e)) (q : ↥(Q e)) :
    δ e (p ⊗ₜ q) = (p : Fin 2 → R) 0 * (q : Fin 2 → R) 1 - (p : Fin 2 → R) 1 * (q : Fin 2 → R) 0 := by
  rw [δ, TensorProduct.lift.tmul]; rfl

def w₀ : ↥(P e) ⊗[R] ↥(Q e) :=
  g e 0 ⊗ₜ h e 1 - g e 1 ⊗ₜ h e 0

variable (htr : e.trace = 1) (hdet : e.det = 0)
include htr hdet

theorem eq_smul_g_add (p : ↥(P e)) :
    p = (p : Fin 2 → R) 0 • g e 0 + (p : Fin 2 → R) 1 • g e 1 := by
  have hp := (mem_P_iff e htr hdet _).1 p.2
  apply Subtype.ext
  funext i
  have := congrFun hp i
  rw [mulVec_apply] at this
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, g_val, smul_eq_mul]
  rw [← this]; ring

theorem eq_smul_h_add (q : ↥(Q e)) :
    q = (q : Fin 2 → R) 0 • h e 0 + (q : Fin 2 → R) 1 • h e 1 := by
  have hq := (mem_Q_iff e htr hdet _).1 q.2
  apply Subtype.ext
  funext i
  have h0 := congrFun hq i
  rw [mulVec_apply] at h0
  simp only [Pi.zero_apply] at h0
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, h_val, smul_eq_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at h0 ⊢
    rw [one_sub_apply_00, one_sub_apply_01]
    linear_combination h0
  · simp only [Fin.mk_one, Fin.isValue] at h0 ⊢
    rw [one_sub_apply_10, one_sub_apply_11]
    linear_combination h0

/--
@isnad1 id=eq.2h2v.s11.be9cab1d0437 from=translated src=- shape=1d08a378 vocab=9ce17830
-/
theorem rel_g₁ : e 1 1 • g e 0 = e 1 0 • g e 1 := by
  have hd := det_eq e hdet
  apply Subtype.ext; funext i
  simp only [Submodule.coe_smul, Pi.smul_apply, g_val, smul_eq_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; linear_combination hd
  · simp only [Fin.mk_one, Fin.isValue]; ring

/--
@isnad1 id=eq.2h2v.s11.a0d105af463c from=translated src=- shape=1d08a378 vocab=9ce17830
-/
theorem rel_g₂ : e 0 1 • g e 0 = e 0 0 • g e 1 := by
  have hd := det_eq e hdet
  apply Subtype.ext; funext i
  simp only [Submodule.coe_smul, Pi.smul_apply, g_val, smul_eq_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; ring
  · simp only [Fin.mk_one, Fin.isValue]; linear_combination -hd

/--
@isnad1 id=eq.2h2v.s11.b7eb10750172 from=translated src=- shape=1817af66 vocab=de198483
-/
theorem rel_h₁ : e 0 0 • h e 0 = -(e 1 0 • h e 1) := by
  have hd := det_eq e hdet
  have ht := trace_eq e htr
  apply Subtype.ext; funext i
  simp only [Submodule.coe_smul, Submodule.coe_neg, Pi.smul_apply, Pi.neg_apply, h_val, smul_eq_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; rw [one_sub_apply_00, one_sub_apply_01]
    linear_combination hd - e 0 0 * ht
  · simp only [Fin.mk_one, Fin.isValue]; rw [one_sub_apply_10, one_sub_apply_11]
    linear_combination (-e 1 0) * ht

/--
@isnad1 id=eq.2h2v.s11.2795dc4853e2 from=translated src=- shape=1817af66 vocab=de198483
-/
theorem rel_h₂ : e 0 1 • h e 0 = -(e 1 1 • h e 1) := by
  have hd := det_eq e hdet
  have ht := trace_eq e htr
  apply Subtype.ext; funext i
  simp only [Submodule.coe_smul, Submodule.coe_neg, Pi.smul_apply, Pi.neg_apply, h_val, smul_eq_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; rw [one_sub_apply_00, one_sub_apply_01]
    linear_combination (-e 0 1) * ht
  · simp only [Fin.mk_one, Fin.isValue]; rw [one_sub_apply_10, one_sub_apply_11]
    linear_combination hd - e 1 1 * ht

/--
@isnad1 id=eq.2h2v.s12.4bcf30c0af9e from=translated src=- shape=41b2f4e3 vocab=e1c0ee9d
-/
theorem δ_g_h_00 : δ e (g e 0 ⊗ₜ h e 0) = -e 1 0 := by
  rw [δ_tmul, g_val, g_val, h_val, h_val, one_sub_apply_10, one_sub_apply_00]; ring

/--
@isnad1 id=eq.2h2v.s12.f7a42628256c from=translated src=- shape=7cbb378a vocab=23a3f152
-/
theorem δ_g_h_01 : δ e (g e 0 ⊗ₜ h e 1) = e 0 0 := by
  have hd := det_eq e hdet
  rw [δ_tmul, g_val, g_val, h_val, h_val, one_sub_apply_11, one_sub_apply_01]; linear_combination -hd

/--
@isnad1 id=eq.2h2v.s12.371b65431cdb from=translated src=- shape=41b2f4e3 vocab=e1c0ee9d
-/
theorem δ_g_h_10 : δ e (g e 1 ⊗ₜ h e 0) = -e 1 1 := by
  have hd := det_eq e hdet
  rw [δ_tmul, g_val, g_val, h_val, h_val, one_sub_apply_10, one_sub_apply_00]; linear_combination hd

/--
@isnad1 id=eq.2h2v.s12.fdf984969664 from=translated src=- shape=7cbb378a vocab=23a3f152
-/
theorem δ_g_h_11 : δ e (g e 1 ⊗ₜ h e 1) = e 0 1 := by
  rw [δ_tmul, g_val, g_val, h_val, h_val, one_sub_apply_11, one_sub_apply_01]; ring

/--
@isnad1 id=eq.2h2v.s12.007565d6e64e from=translated src=- shape=c1231126 vocab=83ccfbb3
-/
theorem δ_w₀ : δ e (w₀ e) = 1 := by
  have ht := trace_eq e htr
  rw [w₀, map_sub, δ_g_h_01 e htr hdet, δ_g_h_10 e htr hdet]; linear_combination ht

/--
@isnad1 id=eq.2h4v.s13.b9738226cc36 from=translated src=- shape=791b909a vocab=dc5e5611
-/
theorem smul_w₀_eq_tmul (i j : Fin 2) :
    δ e (g e i ⊗ₜ h e j) • w₀ e = g e i ⊗ₜ h e j := by
  obtain ⟨k00, k01, k10, k11⟩ := key (R := R) (e 0 0) (e 0 1) (e 1 0) (e 1 1) (trace_eq e htr)
    (g e 0) (g e 1) (h e 0) (h e 1)
    (rel_g₁ e htr hdet) (rel_g₂ e htr hdet) (rel_h₁ e htr hdet) (rel_h₂ e htr hdet)
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]; rw [δ_g_h_00 e htr hdet]; exact k00
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; rw [δ_g_h_01 e htr hdet]; exact k01
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta]; rw [δ_g_h_10 e htr hdet]; exact k10
  · simp only [Fin.mk_one, Fin.isValue]; rw [δ_g_h_11 e htr hdet]; exact k11

/--
@isnad1 id=eq.2h4v.s13.f1e38aeb82f1 from=translated src=- shape=1f64d3fe vocab=7fd72170
-/
theorem smul_w₀_eq_tmul' (p : ↥(P e)) (q : ↥(Q e)) :
    δ e (p ⊗ₜ q) • w₀ e = p ⊗ₜ q := by
  have hp := eq_smul_g_add e htr hdet p
  have hq := eq_smul_h_add e htr hdet q
  set p0 := (p : Fin 2 → R) 0
  set p1 := (p : Fin 2 → R) 1
  set q0 := (q : Fin 2 → R) 0
  set q1 := (q : Fin 2 → R) 1
  rw [hp, hq]
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    map_add, map_smul, add_smul, smul_add, smul_assoc, smul_w₀_eq_tmul e htr hdet]

def pairing : ↥(P e) ⊗[R] ↥(Q e) ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (δ e) (LinearMap.toSpanSingleton R _ (w₀ e))
    (by
      apply LinearMap.ext_ring
      rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, one_smul, δ_w₀ e htr hdet, LinearMap.id_apply])
    (by
      apply TensorProduct.ext'
      intro p q
      rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, LinearMap.id_apply, smul_w₀_eq_tmul' e htr hdet])

/--
@isnad1 id=invertib.2h2v.s9.4ea4a7875e5d from=translated src=- shape=2940fda4 vocab=2138f6f3
-/
theorem invertible_P : Module.Invertible R ↥(P e) := Module.Invertible.left (pairing e htr hdet)

/--
@isnad1 id=invertib.2h2v.s9.7860265795a3 from=translated src=- shape=2940fda4 vocab=3583e437
-/
theorem invertible_Q : Module.Invertible R ↥(Q e) := Module.Invertible.right (pairing e htr hdet)

end Columns

end Matrix.RankOneProjectorPlane
open scoped _root_.P2MW.S_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero.Matrix _root_.P2MW.S_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero.Matrix.RankOneProjectorPlane
open scoped _root_.P2MW.S_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero.Matrix

/--
@isnad1 id=and.2h2v.s11.14da23041468 from=translated src=- shape=31948f89 vocab=ec2c2964
-/
theorem solution
    {R : Type*} [CommRing R] (e : Matrix (Fin 2) (Fin 2) R) (htr : e.trace = 1) (hdet : e.det = 0) :
    e * e = e ∧
      IsCompl (LinearMap.range (Matrix.mulVecLin e)) (LinearMap.range (Matrix.mulVecLin (1 - e))) ∧
      Module.Invertible R ↥(LinearMap.range (Matrix.mulVecLin e)) ∧
      Module.Invertible R ↥(LinearMap.range (Matrix.mulVecLin (1 - e))) :=
  ⟨Matrix.RankOneProjectorPlane.mul_self_eq e htr hdet, Matrix.RankOneProjectorPlane.isCompl_P_Q e htr hdet,
    Matrix.RankOneProjectorPlane.invertible_P e htr hdet, Matrix.RankOneProjectorPlane.invertible_Q e htr hdet⟩
