import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

namespace TN
namespace ThetaNormalMatrix

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B)

/--
@isnad1 id=eq.2h4v.s7.0530e12d329d from=translated src=- shape=a781cd06 vocab=1a6b5aa5
-/
theorem pow_two_d (ζ : B) (hζ : ζ ^ d = 1) (hω : ω ^ 2 = ζ) : ω ^ (2 * d) = 1 := by
  rw [pow_mul, hω, hζ]

/--
@isnad1 id=eq.0h7v.s6.a63812a9f5fc from=translated src=- shape=09dc0f7f vocab=067b0225
-/
theorem thetaChar_apply (k h : HH δ) : thetaChar δ d B ω k h = omegaPow d B ω (pair δ d k h) := rfl

/--
@isnad1 id=eq.1h8v.s7.166df925f558 from=translated src=- shape=7f09f6b7 vocab=4e21c4ec
-/
theorem thetaChar_add_right (h2d : ω ^ (2 * d) = 1) (k a b : HH δ) :
    thetaChar δ d B ω k (a + b) = thetaChar δ d B ω k a * thetaChar δ d B ω k b := by
  simp only [thetaChar_apply, pair_add_right, omegaPow_add d B ω h2d]

/--
@isnad1 id=eq.1h8v.s7.c03018c1450d from=translated src=- shape=60cba78a vocab=4e21c4ec
-/
theorem thetaChar_add_left (h2d : ω ^ (2 * d) = 1) (k l a : HH δ) :
    thetaChar δ d B ω (k + l) a = thetaChar δ d B ω k a * thetaChar δ d B ω l a := by
  simp only [thetaChar_apply, pair_add_left, omegaPow_add d B ω h2d]

/--
@isnad1 id=eq.0h6v.s6.09d38a2f683c from=translated src=- shape=9467bf8a vocab=fbf486d1
-/
theorem thetaChar_zero_right (k : HH δ) : thetaChar δ d B ω k 0 = 1 := by
  simp only [thetaChar_apply, pair_zero_right, omegaPow_zero]

/--
@isnad1 id=eq.0h6v.s6.bd997daaef52 from=translated src=- shape=e40b4fe7 vocab=fbf486d1
-/
theorem thetaChar_zero_left (a : HH δ) : thetaChar δ d B ω 0 a = 1 := by
  simp only [thetaChar_apply, pair_zero_left, omegaPow_zero]

/--
@isnad1 id=eq.0h7v.s5.656518a0df42 from=translated src=- shape=e0a44461 vocab=6eadff91
-/
theorem thetaChar_comm (k h : HH δ) : thetaChar δ d B ω k h = thetaChar δ d B ω h k := by
  simp only [thetaChar_apply, pair_comm]

/--
@isnad1 id=eq.1h7v.s7.56637c162e49 from=translated src=- shape=1320dabc vocab=6cef77a4
-/
theorem thetaChar_neg_mul_self (h2d : ω ^ (2 * d) = 1) (k a : HH δ) :
    thetaChar δ d B ω k (-a) * thetaChar δ d B ω k a = 1 := by
  rw [← thetaChar_add_right δ d B ω h2d, neg_add_cancel, thetaChar_zero_right]

/--
@isnad1 id=eq.0h7v.s7.82c6eba1d8fd from=translated src=- shape=b606f425 vocab=3bfee5c1
-/
theorem thetaChar_neg_right (k a : HH δ) : thetaChar δ d B ω k (-a) = thetaChar δ d B ω (-k) a := by
  simp only [thetaChar_apply, pair_neg_right, pair_neg_left]

/--
@isnad1 id=eq.1h3v.s6.d51f73eda207 from=translated src=- shape=2e4511b4 vocab=2ce2af52
-/
theorem card_HH (hδd : ∏ i, δ i = d) : Fintype.card (HH δ) = d := by
  rw [← hδd]
  simp [HH, Fintype.card_pi, ZMod.card]

/--
@isnad1 id=ex.5h7v.s8.f9e14f2cc8e5 from=translated src=- shape=50328442 vocab=0f6b1ae3
-/
theorem exists_isUnit_one_sub_thetaChar (hδd : ∏ i, δ i = d) (ζ : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) (x : HH δ) (hx : x ≠ 0) :
    ∃ k : HH δ, IsUnit (1 - omegaPow d B ω (pair δ d k x)) := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  refine ⟨Pi.single i₀ 1, ?_⟩
  have hdvd : δ i₀ ∣ d := hδd ▸ Finset.dvd_prod_of_mem δ (Finset.mem_univ i₀)
  have hdvd2 : δ i₀ ∣ 2 * d := Dvd.dvd.mul_left hdvd 2
  have hpair : pair δ d (Pi.single i₀ 1) x = iota δ d i₀ (x i₀) := by
    rw [pair, Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      simp [hi]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  obtain ⟨m, hm⟩ := hdvd
  set v : ℕ := (x i₀).val with hv
  have hvpos : 0 < v := by
    rw [hv, Nat.pos_iff_ne_zero]; exact fun h0 => hi₀ ((ZMod.val_eq_zero _).mp h0)
  have hvlt : v < δ i₀ := ZMod.val_lt _
  have hcast : (x i₀ : ZMod (δ i₀)) = ((v : ℕ) : ZMod (δ i₀)) := by rw [hv, ZMod.natCast_zmod_val]
  have hq : 2 * d / δ i₀ = 2 * m := by
    rw [hm, show 2 * (δ i₀ * m) = (2 * m) * δ i₀ by ring, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne _))]
  have hval : iota δ d i₀ (x i₀) = ((2 * (m * v) : ℕ) : ZMod (2 * d)) := by
    rw [hcast, iota_natCast δ d i₀ hdvd2, hq]; push_cast; ring
  have h2d : ω ^ (2 * d) = 1 := by rw [pow_mul, hω, hζ]
  rw [hpair, hval, omegaPow_natCast d B ω h2d, pow_mul, hω]
  have hm0 : m ≠ 0 := by rintro rfl; exact NeZero.ne d (by rw [hm, mul_zero])
  have hmv1 : 0 < m * v := Nat.mul_pos (Nat.pos_of_ne_zero hm0) hvpos
  have hmv2 : m * v < d := by
    calc m * v < m * δ i₀ := Nat.mul_lt_mul_of_pos_left hvlt (Nat.pos_of_ne_zero hm0)
      _ = d := by rw [hm, mul_comm]
  exact hζu _ hmv1 hmv2

/--
@isnad1 id=eq.4h7v.s8.5ab096c9cf9b from=translated src=- shape=f677f022 vocab=c76b0be0
-/
theorem sum_thetaChar (hδd : ∏ i, δ i = d) (ζ : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) (k : HH δ) :
    ∑ a, thetaChar δ d B ω k a = if k = 0 then (d : B) else 0 := by
  classical
  have h2d := pow_two_d d B ω ζ hζ hω
  split_ifs with hk
  · subst hk
    simp only [thetaChar_zero_left, Finset.sum_const, Finset.card_univ, card_HH δ d hδd, nsmul_eq_mul, mul_one]
  · obtain ⟨x, hxu⟩ := exists_isUnit_one_sub_thetaChar δ d B ω hδd ζ hζ hζu hω k hk

    have hshift : ∑ a, thetaChar δ d B ω k a = ∑ a, thetaChar δ d B ω k (a + x) :=
      (Fintype.sum_equiv (Equiv.addRight x) _ _ (fun a => rfl)).symm
    have hfac : ∑ a, thetaChar δ d B ω k (a + x) = thetaChar δ d B ω k x * ∑ a, thetaChar δ d B ω k a := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [thetaChar_add_right δ d B ω h2d, mul_comm]
    have hkey : (1 - omegaPow d B ω (pair δ d x k)) * ∑ a, thetaChar δ d B ω k a = 0 := by
      rw [pair_comm, ← thetaChar_apply, sub_mul, one_mul, ← hfac, ← hshift, sub_self]
    exact (hxu.mul_right_eq_zero).mp hkey

noncomputable def four (dinv : B) (lam : HH δ → B) (k : HH δ) : B :=
  dinv * ∑ a, lam a * thetaChar δ d B ω k (-a)

/--
@isnad1 id=eq.2h9v.s7.f1e10f1304e2 from=translated src=- shape=6344120e vocab=dbedb6e6
-/
theorem mul_four (h2d : ω ^ (2 * d) = 1) (dinv : B) (lam : HH δ → B)
    (hmul : ∀ a b, lam (a + b) = lam a * lam b) (k b : HH δ) :
    lam b * four δ d B ω dinv lam k = thetaChar δ d B ω k b * four δ d B ω dinv lam k := by
  classical
  have key : lam b * ∑ a, lam a * thetaChar δ d B ω k (-a) =
      thetaChar δ d B ω k b * ∑ a, lam a * thetaChar δ d B ω k (-a) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [Fintype.sum_equiv (Equiv.addRight b) (fun a => lam b * (lam a * thetaChar δ d B ω k (-a)))
      (fun c => lam c * thetaChar δ d B ω k (b - c)) (fun a => by
        simp only [Equiv.coe_addRight]
        rw [hmul, show b - (a + b) = -a by abel]; ring)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show b - c = b + -c by abel, thetaChar_add_right δ d B ω h2d]; ring
  simp only [four]
  rw [mul_left_comm, key, mul_left_comm]

/--
@isnad1 id=eq.6h8v.s8.37372626cb23 from=translated src=- shape=8f280ac6 vocab=8c1a9389
-/
theorem sum_four (hδd : ∏ i, δ i = d) (ζ : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ)
    (dinv : B) (hdinv : dinv * (d : B) = 1) (lam : HH δ → B) (h0 : lam 0 = 1) :
    ∑ k, four δ d B ω dinv lam k = 1 := by
  classical
  simp only [four]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have inner : ∀ a : HH δ, ∑ k, lam a * thetaChar δ d B ω k (-a) = lam a * (if -a = 0 then (d : B) else 0) := by
    intro a
    rw [← Finset.mul_sum]
    congr 1
    rw [← sum_thetaChar δ d B ω hδd ζ hζ hζu hω (-a)]
    exact Finset.sum_congr rfl fun k _ => thetaChar_comm δ d B ω k (-a)
  simp_rw [inner]
  rw [Finset.sum_eq_single (0 : HH δ)]
  · simp [h0, mul_comm, hdinv]
  · intro a _ ha
    rw [ite_eq_right (by simpa using ha), mul_zero]
  · intro hh; exact absurd (Finset.mem_univ _) hh

/--
@isnad1 id=eq.6h10v.s8.98de6dd94f5e from=translated src=- shape=e14711b4 vocab=53f39c9c
-/
theorem four_mul_four (hδd : ∏ i, δ i = d) (ζ : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ)
    (dinv : B) (lam : HH δ → B)
    (hmul : ∀ a b, lam (a + b) = lam a * lam b) (k l : HH δ) (hkl : k ≠ l) :
    four δ d B ω dinv lam k * four δ d B ω dinv lam l = 0 := by
  classical
  have h2d := pow_two_d d B ω ζ hζ hω

  rw [mul_comm]
  have step : four δ d B ω dinv lam l * four δ d B ω dinv lam k =
      dinv * four δ d B ω dinv lam k * ∑ a, thetaChar δ d B ω (k - l) a := by
    conv_lhs => rw [four]
    rw [mul_assoc, Finset.sum_mul, mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, mul_comm (thetaChar δ d B ω l (-a)), ← mul_assoc (lam a), mul_four δ d B ω h2d dinv lam hmul k a,
      show k - l = k + -l by abel, thetaChar_add_left δ d B ω h2d, ← thetaChar_neg_right]
    ring
  rw [step, sum_thetaChar δ d B ω hδd ζ hζ hζu hω, ite_eq_right (sub_ne_zero.mpr hkl), mul_zero]

/--
@isnad1 id=complete.7h8v.s8.0378e6be9f73 from=translated src=- shape=d9acb502 vocab=d9edacc2
-/
theorem completeOrthogonalIdempotents_four (hδd : ∏ i, δ i = d) (ζ : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ)
    (dinv : B) (hdinv : dinv * (d : B) = 1) (lam : HH δ → B) (h0 : lam 0 = 1)
    (hmul : ∀ a b, lam (a + b) = lam a * lam b) :
    CompleteOrthogonalIdempotents (four δ d B ω dinv lam) := by
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  exact ⟨fun k l hkl => four_mul_four δ d B ω hδd ζ hζ hζu hω dinv lam hmul k l hkl,
    sum_four δ d B ω hδd ζ hζ hζu hω dinv hdinv lam h0⟩

end TN.ThetaNormalMatrix

namespace TN
namespace ThetaNormalMatrix

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B) {n : ℕ}
  (e : Fin n ≃ HH δ)

/--
@isnad1 id=eq.1h8v.s8.bca805a73bd3 from=translated src=- shape=9ed9b06f vocab=875dfd9a
-/
theorem schrodMat_smul_base (h2d : ω ^ (2 * d) = 1) (z : Heis δ d) :
    schrodMat δ d B ω e z = omegaPow d B ω z.a • schrodMat δ d B ω e ⟨0, z.h, z.k⟩ := by
  ext i j
  simp only [schrodMat_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs with hij
  · rw [zero_add, omegaPow_add d B ω h2d]
  · rw [mul_zero]

/--
@isnad1 id=eq.0h5v.s7.6980cb5c4401 from=translated src=- shape=9d34c3ec vocab=7f15fa91
-/
theorem theta_mul_eta (h k : HH δ) : (Heis.theta h * Heis.eta k : Heis δ d) = ⟨0, h, k⟩ := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [Heis.theta, Heis.eta, pair_zero_right]

theorem eq_zero_of_smul_eq_zero_of_isUnit (i₀ : Fin n) (c : B) (M : Matrix (Fin n) (Fin n) B) (hM : IsUnit M)
    (h : c • M = 0) : c = 0 := by
  obtain ⟨u, rfl⟩ := hM
  have h1 : c • (1 : Matrix (Fin n) (Fin n) B) = 0 := by
    rw [← u.mul_inv, ← Matrix.smul_mul, h, Matrix.zero_mul]
  have h2 := congrFun (congrFun h1 i₀) i₀
  simpa using h2

/--
@isnad1 id=and.5h8v.s9.df612582f29e from=translated src=- shape=72b19708 vocab=a678d868
-/
theorem char_of_proj_comm (i₀ : Fin n) (P : HH δ → Matrix (Fin n) (Fin n) B) (hP0 : P 0 = 1)
    (hPmul : ∀ a b, P (a + b) = P a * P b) (hPu : ∀ a, IsUnit (P a))
    (T : Matrix (Fin n) (Fin n) B) (hT : IsUnit T) (lam : HH δ → B)
    (hc : ∀ a, T * P a = lam a • (P a * T)) :
    lam 0 = 1 ∧ ∀ a b, lam (a + b) = lam a * lam b := by
  constructor
  · have h := hc 0
    rw [hP0, Matrix.mul_one, Matrix.one_mul] at h
    have h' : (1 - lam 0) • T = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    have := eq_zero_of_smul_eq_zero_of_isUnit B i₀ _ T hT h'
    exact (sub_eq_zero.mp this).symm
  · intro a b
    have h1 : T * P (a + b) = (lam a * lam b) • (P (a + b) * T) := by
      rw [hPmul, ← Matrix.mul_assoc, hc a, Matrix.smul_mul, Matrix.mul_assoc, hc b, Matrix.mul_smul, smul_smul,
        Matrix.mul_assoc]
    have h2 := hc (a + b)
    have h3 : (lam (a + b) - lam a * lam b) • (P (a + b) * T) = 0 := by
      rw [sub_smul, ← h1, ← h2, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_smul_eq_zero_of_isUnit B i₀ _ _ ((hPu _).mul hT) h3)

/--
@isnad1 id=eq.6h15v.s10.d77959aeb840 from=translated src=- shape=3d57987e vocab=e376dc04
-/
theorem piece_comm (ζ : B) (hζ : ζ ^ d = 1) (hω : ω ^ 2 = ζ)
    (T : Matrix (Fin n) (Fin n) B) (lam mu : HH δ → B)
    (hθ : ∀ h' : HH δ, T * schrodMat δ d B ω e (Heis.theta h') = lam h' • (schrodMat δ d B ω e (Heis.theta h') * T))
    (hη : ∀ k' : HH δ, T * schrodMat δ d B ω e (Heis.eta k') = mu k' • (schrodMat δ d B ω e (Heis.eta k') * T))
    (h k : HH δ) (ε : B) (hεl : ∀ h', ε * lam h' = thetaChar δ d B ω k h' * ε)
    (hεm : ∀ k', ε * mu k' = thetaChar δ d B ω (-h) k' * ε) (z : Heis δ d) :
    (ε • (T * schrodMat δ d B ω e (⟨0, h, k⟩ : Heis δ d)⁻¹)) * schrodMat δ d B ω e z =
      schrodMat δ d B ω e z * (ε • (T * schrodMat δ d B ω e (⟨0, h, k⟩ : Heis δ d)⁻¹)) := by
  have h2d := pow_two_d d B ω ζ hζ hω
  have HM := schrodMat_one_and_schrodMat_mul δ d B ω h2d e
  set w : Heis δ d := ⟨0, h, k⟩ with hw

  have R1 : ∀ h', schrodMat δ d B ω e (Heis.theta h') * schrodMat δ d B ω e w⁻¹ = omegaPow d B ω (pair δ d k h') • (schrodMat δ d B ω e w⁻¹ * schrodMat δ d B ω e (Heis.theta h')) := by
    intro h'
    rw [← HM.2, ← HM.2, schrodMat_smul_base δ d B ω e h2d (Heis.theta h' * w⁻¹),
      schrodMat_smul_base δ d B ω e h2d (w⁻¹ * Heis.theta h'), smul_smul, ← omegaPow_add d B ω h2d]
    congr 2
    · simp only [Heis.mul_a, Heis.inv_a, Heis.theta_a, Heis.theta_k, Heis.theta_h, Heis.inv_k, Heis.inv_h, hw,
        pair_zero_left, pair_neg_left]; abel
    · refine Heis.ext rfl ?_ ?_ <;>
        simp only [Heis.mul_h, Heis.mul_k, Heis.inv_h, Heis.inv_k, Heis.theta_h, Heis.theta_k] <;> abel
  have R2 : ∀ k', schrodMat δ d B ω e w⁻¹ * schrodMat δ d B ω e (Heis.eta k') = omegaPow d B ω (pair δ d k' h) • (schrodMat δ d B ω e (Heis.eta k') * schrodMat δ d B ω e w⁻¹) := by
    intro k'
    rw [← HM.2, ← HM.2, schrodMat_smul_base δ d B ω e h2d (Heis.eta k' * w⁻¹),
      schrodMat_smul_base δ d B ω e h2d (w⁻¹ * Heis.eta k'), smul_smul, ← omegaPow_add d B ω h2d]
    congr 2
    · simp only [Heis.mul_a, Heis.inv_a, Heis.eta_a, Heis.eta_k, Heis.eta_h, Heis.inv_k, Heis.inv_h, hw,
        pair_zero_right, pair_neg_right]; abel
    · refine Heis.ext rfl ?_ ?_ <;>
        simp only [Heis.mul_h, Heis.mul_k, Heis.inv_h, Heis.inv_k, Heis.eta_h, Heis.eta_k] <;> abel

  have Cθ : ∀ h', (ε • (T * schrodMat δ d B ω e w⁻¹)) * schrodMat δ d B ω e (Heis.theta h') = schrodMat δ d B ω e (Heis.theta h') * (ε • (T * schrodMat δ d B ω e w⁻¹)) := by
    intro h'
    have hunit : thetaChar δ d B ω k (-h') * omegaPow d B ω (pair δ d k h') = 1 := by
      rw [← thetaChar_apply, thetaChar_neg_mul_self δ d B ω h2d]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    calc ε • (T * (schrodMat δ d B ω e w⁻¹ * schrodMat δ d B ω e (Heis.theta h')))
        = (ε * (thetaChar δ d B ω k (-h') * omegaPow d B ω (pair δ d k h'))) • (T * (schrodMat δ d B ω e w⁻¹ * schrodMat δ d B ω e (Heis.theta h'))) := by
          rw [hunit, mul_one]
      _ = (ε * thetaChar δ d B ω k (-h')) • (T * (omegaPow d B ω (pair δ d k h') • (schrodMat δ d B ω e w⁻¹ * schrodMat δ d B ω e (Heis.theta h')))) := by
          rw [Matrix.mul_smul, smul_smul, mul_assoc]
      _ = (ε * thetaChar δ d B ω k (-h')) • ((T * schrodMat δ d B ω e (Heis.theta h')) * schrodMat δ d B ω e w⁻¹) := by
          rw [← R1, Matrix.mul_assoc]
      _ = (ε * lam h' * thetaChar δ d B ω k (-h')) • (schrodMat δ d B ω e (Heis.theta h') * T * schrodMat δ d B ω e w⁻¹) := by
          rw [hθ, Matrix.smul_mul, smul_smul]; congr 1; ring
      _ = ε • (schrodMat δ d B ω e (Heis.theta h') * (T * schrodMat δ d B ω e w⁻¹)) := by
          rw [hεl, Matrix.mul_assoc]; congr 1
          calc thetaChar δ d B ω k h' * ε * thetaChar δ d B ω k (-h')
              = ε * (thetaChar δ d B ω k (-h') * thetaChar δ d B ω k h') := by ring
            _ = ε := by rw [thetaChar_neg_mul_self δ d B ω h2d, mul_one]

  have Cη : ∀ k', (ε • (T * schrodMat δ d B ω e w⁻¹)) * schrodMat δ d B ω e (Heis.eta k') = schrodMat δ d B ω e (Heis.eta k') * (ε • (T * schrodMat δ d B ω e w⁻¹)) := by
    intro k'
    have hunit : thetaChar δ d B ω (-h) k' * omegaPow d B ω (pair δ d k' h) = 1 := by
      rw [thetaChar_comm, ← thetaChar_apply, thetaChar_neg_mul_self δ d B ω h2d]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, R2, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hη,
      Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
    congr 1
    calc ε * omegaPow d B ω (pair δ d k' h) * mu k' = ε * mu k' * omegaPow d B ω (pair δ d k' h) := by ring
      _ = ε := by rw [hεm, mul_right_comm, hunit, one_mul]

  have hz : schrodMat δ d B ω e z = omegaPow d B ω z.a • (schrodMat δ d B ω e (Heis.theta z.h) * schrodMat δ d B ω e (Heis.eta z.k)) := by
    rw [← HM.2, theta_mul_eta, ← schrodMat_smul_base δ d B ω e h2d]
  generalize ε • (T * schrodMat δ d B ω e w⁻¹) = X at Cθ Cη ⊢
  rw [hz, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, Cθ, Matrix.mul_assoc, Cη, ← Matrix.mul_assoc]

end TN.ThetaNormalMatrix

open TN.ThetaNormalMatrix in
/--
@isnad1 id=ex.8h11v.s9.2d6eac8a2601 from=translated src=- shape=d162d8af vocab=4d07291a
-/
theorem solution
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (T : Matrix (Fin n) (Fin n) B) (hT : IsUnit T) (lam mu : HH δ → B)
    (hθ : ∀ h' : HH δ, T * schrodMat δ d B ω e (Heis.theta h') = lam h' • (schrodMat δ d B ω e (Heis.theta h') * T))
    (hη : ∀ k' : HH δ, T * schrodMat δ d B ω e (Heis.eta k') = mu k' • (schrodMat δ d B ω e (Heis.eta k') * T)) :
    ∃ (ε : HH δ × HH δ → B) (u : Bˣ), CompleteOrthogonalIdempotents ε ∧
      ∀ c : HH δ × HH δ, ε c • T = (ε c * u) • schrodMat δ d B ω e ⟨0, c.1, c.2⟩ := by
  classical
  have h2d := pow_two_d d B ω ζ hζ hω
  have HM := schrodMat_one_and_schrodMat_mul δ d B ω h2d e
  have i₀ : Fin n := e.symm 0

  have hWu : ∀ z : Heis δ d, IsUnit (schrodMat δ d B ω e z) := fun z =>
    ⟨⟨schrodMat δ d B ω e z, schrodMat δ d B ω e z⁻¹, by rw [← HM.2, mul_inv_cancel, HM.1],
      by rw [← HM.2, inv_mul_cancel, HM.1]⟩, rfl⟩

  obtain ⟨hl0, hlmul⟩ := char_of_proj_comm δ B i₀ (fun a => schrodMat δ d B ω e (Heis.theta a))
    (by
      show schrodMat δ d B ω e (Heis.theta 0) = 1
      rw [show (Heis.theta 0 : Heis δ d) = 1 from Heis.ext rfl rfl rfl, HM.1])
    (fun a b => by
      show schrodMat δ d B ω e (Heis.theta (a + b)) = schrodMat δ d B ω e (Heis.theta a) * schrodMat δ d B ω e (Heis.theta b)
      rw [← HM.2]; congr 1
      refine Heis.ext ?_ ?_ ?_ <;> simp [pair_zero_left])
    (fun a => hWu _) T hT lam hθ
  obtain ⟨hm0, hmmul⟩ := char_of_proj_comm δ B i₀ (fun a => schrodMat δ d B ω e (Heis.eta a))
    (by
      show schrodMat δ d B ω e (Heis.eta 0) = 1
      rw [show (Heis.eta 0 : Heis δ d) = 1 from Heis.ext rfl rfl rfl, HM.1])
    (fun a b => by
      show schrodMat δ d B ω e (Heis.eta (a + b)) = schrodMat δ d B ω e (Heis.eta a) * schrodMat δ d B ω e (Heis.eta b)
      rw [← HM.2]; congr 1
      refine Heis.ext ?_ ?_ ?_ <;> simp [pair_zero_right])
    (fun a => hWu _) T hT mu hη
  obtain ⟨dinv, hdinv⟩ := hd.exists_left_inv

  have Cl := completeOrthogonalIdempotents_four δ d B ω hδd ζ hζ hζu hω dinv hdinv lam hl0 hlmul
  have Cm := completeOrthogonalIdempotents_four δ d B ω hδd ζ hζ hζu hω dinv hdinv mu hm0 hmmul
  let ε : HH δ × HH δ → B := fun c => four δ d B ω dinv mu (-c.1) * four δ d B ω dinv lam c.2
  have hε : CompleteOrthogonalIdempotents ε := by
    rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
    constructor
    · intro c c' hcc'
      show four δ d B ω dinv mu (-c.1) * four δ d B ω dinv lam c.2 *
          (four δ d B ω dinv mu (-c'.1) * four δ d B ω dinv lam c'.2) = 0
      by_cases h1 : c.1 = c'.1
      · have h2 : c.2 ≠ c'.2 := fun h2 => hcc' (Prod.ext h1 h2)
        rw [mul_mul_mul_comm, Cl.ortho h2, mul_zero]
      · rw [mul_mul_mul_comm, Cm.ortho (fun h => h1 (neg_injective h)), zero_mul]
    · show ∑ c : HH δ × HH δ, four δ d B ω dinv mu (-c.1) * four δ d B ω dinv lam c.2 = 1
      rw [Fintype.sum_prod_type]
      simp only
      rw [← Finset.sum_mul_sum, Cl.complete, mul_one,
        Fintype.sum_equiv (Equiv.neg (HH δ)) (fun x => four δ d B ω dinv mu (-x)) (four δ d B ω dinv mu)
          (fun x => rfl), Cm.complete]

  have hεl : ∀ c : HH δ × HH δ, ∀ h', ε c * lam h' = thetaChar δ d B ω c.2 h' * ε c := by
    intro c h'
    have := mul_four δ d B ω h2d dinv lam hlmul c.2 h'
    show four δ d B ω dinv mu (-c.1) * four δ d B ω dinv lam c.2 * lam h' =
      thetaChar δ d B ω c.2 h' * (four δ d B ω dinv mu (-c.1) * four δ d B ω dinv lam c.2)
    calc four δ d B ω dinv mu (-c.1) * four δ d B ω dinv lam c.2 * lam h'
        = four δ d B ω dinv mu (-c.1) * (lam h' * four δ d B ω dinv lam c.2) := by ring
      _ = four δ d B ω dinv mu (-c.1) * (thetaChar δ d B ω c.2 h' * four δ d B ω dinv lam c.2) := by rw [this]
      _ = _ := by ring
  have hεm : ∀ c : HH δ × HH δ, ∀ k', ε c * mu k' = thetaChar δ d B ω (-c.1) k' * ε c := by
    intro c k'
    have := mul_four δ d B ω h2d dinv mu hmmul (-c.1) k'
    show four δ d B ω dinv mu (-c.1) * four δ d B ω dinv lam c.2 * mu k' =
      thetaChar δ d B ω (-c.1) k' * (four δ d B ω dinv mu (-c.1) * four δ d B ω dinv lam c.2)
    calc four δ d B ω dinv mu (-c.1) * four δ d B ω dinv lam c.2 * mu k'
        = (mu k' * four δ d B ω dinv mu (-c.1)) * four δ d B ω dinv lam c.2 := by ring
      _ = (thetaChar δ d B ω (-c.1) k' * four δ d B ω dinv mu (-c.1)) * four δ d B ω dinv lam c.2 := by rw [this]
      _ = _ := by ring

  have key : ∀ c : HH δ × HH δ, ∃ s : B,
      ε c • (T * schrodMat δ d B ω e (⟨0, c.1, c.2⟩ : Heis δ d)⁻¹) = s • (1 : Matrix (Fin n) (Fin n) B) :=
    fun c => exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul δ d hδd B ζ ω hζ hζu hω e _
      (fun z => piece_comm δ d B ω e ζ hζ hω T lam mu hθ hη c.1 c.2 (ε c) (hεl c) (hεm c) z)
  choose s hs using key
  have hsW : ∀ c : HH δ × HH δ, ε c • T = s c • schrodMat δ d B ω e ⟨0, c.1, c.2⟩ := by
    intro c
    have h1 := congrArg (fun M => M * schrodMat δ d B ω e ⟨0, c.1, c.2⟩) (hs c)
    rwa [Matrix.smul_mul, Matrix.mul_assoc, ← HM.2, inv_mul_cancel, HM.1, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul] at h1

  let u : B := ∑ c, ε c * s c
  have hεu : ∀ c, ε c * u = ε c * s c := by
    intro c
    show ε c * ∑ c', ε c' * s c' = ε c * s c
    rw [Finset.mul_sum, Finset.sum_eq_single c]
    · rw [← mul_assoc, (hε.idem c).eq]
    · intro c' _ hc'
      rw [← mul_assoc, hε.ortho (Ne.symm hc'), zero_mul]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  obtain ⟨Tu, hTu⟩ := hT
  let t : HH δ × HH δ → B := fun c => (schrodMat δ d B ω e ⟨0, c.1, c.2⟩ * (↑Tu⁻¹ : Matrix (Fin n) (Fin n) B)) i₀ i₀
  have hst : ∀ c, s c * t c = ε c := by
    intro c
    have h1 : ε c • (1 : Matrix (Fin n) (Fin n) B) =
        s c • (schrodMat δ d B ω e ⟨0, c.1, c.2⟩ * (↑Tu⁻¹ : Matrix (Fin n) (Fin n) B)) := by
      rw [← Matrix.smul_mul, ← hsW, Matrix.smul_mul, ← hTu, Units.mul_inv]
    have h2 := congrFun (congrFun h1 i₀) i₀
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
    exact h2.symm
  have hu : IsUnit u := by
    refine IsUnit.of_mul_eq_one (∑ c, ε c * t c) ?_
    show (∑ c, ε c * s c) * (∑ c, ε c * t c) = 1
    rw [Finset.sum_mul_sum, ← hε.complete]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · calc ε c * s c * (ε c * t c) = ε c * ε c * (s c * t c) := by ring
        _ = ε c := by rw [(hε.idem c).eq, hst, (hε.idem c).eq]
    · intro c' _ hc'
      calc ε c * s c * (ε c' * t c') = (ε c * ε c') * (s c * t c') := by ring
        _ = 0 := by rw [hε.ortho (Ne.symm hc'), zero_mul]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  refine ⟨ε, hu.unit, hε, fun c => ?_⟩
  rw [IsUnit.unit_spec, hεu]
  calc ε c • T = (ε c * ε c) • T := by rw [(hε.idem c).eq]
    _ = ε c • (ε c • T) := by rw [← smul_smul]
    _ = ε c • (s c • schrodMat δ d B ω e ⟨0, c.1, c.2⟩) := by rw [hsW]
    _ = (ε c * s c) • schrodMat δ d B ω e ⟨0, c.1, c.2⟩ := by rw [smul_smul]
