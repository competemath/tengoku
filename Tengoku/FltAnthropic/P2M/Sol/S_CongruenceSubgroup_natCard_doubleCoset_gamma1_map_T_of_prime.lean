import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_of_prime.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_of_prime

set_option autoImplicit false

open scoped MatrixGroups

namespace CuspKit

/--
@isnad1 id=eq.0h4v.s9.d2718224572c from=translated src=- shape=ca7fbf22 vocab=fc437038
-/
theorem map_apply (N : ℕ) (γ : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N)) γ) i j = ((γ i j : ℤ) : ZMod N) := by
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

/--
@isnad1 id=iff.0h2v.s9.e1a4dd37d17b from=translated src=- shape=a31834f8 vocab=bd13a8eb
-/
theorem mem_map_gamma1_iff (N : ℕ) [NeZero N] (g : SL(2, ZMod N)) :
    g ∈ (CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) ↔
      g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1 := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [SetLike.mem_coe, CongruenceSubgroup.Gamma1_mem] at hγ
    obtain ⟨h00, h11, h10⟩ := hγ
    refine ⟨?_, ?_, ?_⟩ <;> rw [map_apply]
    · exact h00
    · exact h10
    · exact h11
  · rintro ⟨h00, h10, h11⟩
    refine ⟨ModularGroup.T ^ ((g 0 1).val : ℤ), ?_, ?_⟩
    · rw [SetLike.mem_coe, CongruenceSubgroup.Gamma1_mem]
      simp [ModularGroup.coe_T_zpow]
    · ext i j
      rw [map_apply]
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h00, h10, h11, ZMod.natCast_zmod_val]

/--
@isnad1 id=iff.0h2v.s9.5f7d4657aef7 from=translated src=- shape=1563e5b4 vocab=c78f75b3
-/
theorem mem_map_zpowers_T_iff (N : ℕ) [NeZero N] (g : SL(2, ZMod N)) :
    g ∈ (Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) ↔
      g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1 := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hγ
    obtain ⟨n, rfl⟩ := hγ
    refine ⟨?_, ?_, ?_⟩ <;> rw [map_apply] <;> simp [ModularGroup.coe_T_zpow]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨ModularGroup.T ^ ((g 0 1).val : ℤ), ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff]
      exact ⟨_, rfl⟩
    · ext i j
      rw [map_apply]
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h00, h10, h11, ZMod.natCast_zmod_val]

section Unipotent

variable {R : Type*} [CommRing R]

/--
@isnad1 id=eq.2h3v.s9.9acd1d880f71 from=translated src=- shape=7495e3ab vocab=ff007dc7
-/
theorem mul_apply_10_of_left (a M : SL(2, R)) (ha : a 1 0 = 0) (ha1 : a 1 1 = 1) : (a * M) 1 0 = M 1 0 := by
  show ((a : Matrix (Fin 2) (Fin 2) R) * M) 1 0 = M 1 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha, ha1]

/--
@isnad1 id=eq.2h3v.s9.87af8a4a645d from=translated src=- shape=7495e3ab vocab=ff007dc7
-/
theorem mul_apply_11_of_left (a M : SL(2, R)) (ha : a 1 0 = 0) (ha1 : a 1 1 = 1) : (a * M) 1 1 = M 1 1 := by
  show ((a : Matrix (Fin 2) (Fin 2) R) * M) 1 1 = M 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha, ha1]

/--
@isnad1 id=eq.1h3v.s9.c6fe523e532c from=translated src=- shape=434cfdc6 vocab=1f5eb86d
-/
theorem mul_apply_00_of_left (a M : SL(2, R)) (ha0 : a 0 0 = 1) : (a * M) 0 0 = M 0 0 + a 0 1 * M 1 0 := by
  show ((a : Matrix (Fin 2) (Fin 2) R) * M) 0 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha0]

/--
@isnad1 id=eq.1h3v.s9.19dced7a4d6e from=translated src=- shape=434cfdc6 vocab=1f5eb86d
-/
theorem mul_apply_01_of_left (a M : SL(2, R)) (ha0 : a 0 0 = 1) : (a * M) 0 1 = M 0 1 + a 0 1 * M 1 1 := by
  show ((a : Matrix (Fin 2) (Fin 2) R) * M) 0 1 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha0]

/--
@isnad1 id=eq.2h3v.s9.afec8b7d52c0 from=translated src=- shape=257c47fb vocab=ff007dc7
-/
theorem mul_apply_10_of_right (M b : SL(2, R)) (hb0 : b 0 0 = 1) (hb : b 1 0 = 0) : (M * b) 1 0 = M 1 0 := by
  show ((M : Matrix (Fin 2) (Fin 2) R) * b) 1 0 = M 1 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb0, hb]

/--
@isnad1 id=eq.2h3v.s9.69a4a7a48275 from=translated src=- shape=257c47fb vocab=ff007dc7
-/
theorem mul_apply_00_of_right (M b : SL(2, R)) (hb0 : b 0 0 = 1) (hb : b 1 0 = 0) : (M * b) 0 0 = M 0 0 := by
  show ((M : Matrix (Fin 2) (Fin 2) R) * b) 0 0 = M 0 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb0, hb]

/--
@isnad1 id=eq.1h3v.s9.4627b0658062 from=translated src=- shape=4134ca0f vocab=1f5eb86d
-/
theorem mul_apply_11_of_right (M b : SL(2, R)) (hb1 : b 1 1 = 1) : (M * b) 1 1 = M 1 0 * b 0 1 + M 1 1 := by
  show ((M : Matrix (Fin 2) (Fin 2) R) * b) 1 1 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb1]

/--
@isnad1 id=eq.0h2v.s8.45dc2504c619 from=translated src=- shape=beb1d2c3 vocab=d104cdc8
-/
theorem det_eq (M : SL(2, R)) : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
  have := M.prop
  rw [Matrix.det_fin_two] at this
  exact this

def uni (s : R) : SL(2, R) := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/--
@isnad1 id=eq.0h2v.s6.33a73290fc1c from=translated src=- shape=edc69b66 vocab=10342946
-/
@[scoped simp] theorem uni_01 (s : R) : (uni s) 0 1 = s := rfl

end Unipotent

end CuspKit
open scoped _root_.P2MW.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_of_prime.CuspKit

namespace CuspKit

open Matrix

variable (p : ℕ) [Fact p.Prime]

local notation "Gp" => SL(2, ZMod p)
local notation "rp" => (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod p)))

noncomputable def inv (g : Gp) : (ZMod p)ˣ ⊕ (ZMod p)ˣ :=
  if h : g 1 0 = 0 then Sum.inr (Units.mk0 (g 0 0) (by
    intro h0
    have := det_eq g
    rw [h, h0, zero_mul, mul_zero, sub_zero] at this
    exact zero_ne_one this))
  else Sum.inl (Units.mk0 (g 1 0) h)

/--
@isnad1 id=eq.3h5v.s10.960b84e9d00a from=translated src=- shape=240ee4b8 vocab=8faaf6e9
-/
theorem inv_eq_of_rel {x y : Gp} (a b : Gp) (ha : a 0 0 = 1 ∧ a 1 0 = 0 ∧ a 1 1 = 1) (hb : b 0 0 = 1 ∧ b 1 0 = 0 ∧ b 1 1 = 1)
    (hy : y = a * x * b) : inv p x = inv p y := by
  obtain ⟨ha0, ha, ha1⟩ := ha
  obtain ⟨hb0, hb, hb1⟩ := hb
  have h10 : y 1 0 = x 1 0 := by
    rw [hy, mul_apply_10_of_right _ _ hb0 hb, mul_apply_10_of_left _ _ ha ha1]
  unfold inv
  by_cases hx : x 1 0 = 0
  · have hy10 : y 1 0 = 0 := h10.trans hx
    have h00 : y 0 0 = x 0 0 := by
      rw [hy, mul_apply_00_of_right _ _ hb0 hb, mul_apply_00_of_left _ _ ha0, hx, mul_zero, add_zero]
    rw [dite_eq_left hx, dite_eq_left hy10]
    congr 1
    exact Units.ext h00.symm
  · have hy10 : y 1 0 ≠ 0 := fun h => hx (h10 ▸ h)
    rw [dite_eq_right hx, dite_eq_right hy10]
    congr 1
    exact Units.ext h10.symm

/--
@isnad1 id=eq.4h3v.s9.c6d4fc36bb4b from=translated src=- shape=b48e47d4 vocab=4391c934
-/
theorem ext_of_row (x y : Gp) (h00 : x 0 0 = y 0 0) (h10 : x 1 0 = y 1 0) (h11 : x 1 1 = y 1 1) (hc : x 1 0 ≠ 0) : x = y := by
  have hx := det_eq x
  have hy := det_eq y
  have h01 : x 0 1 = y 0 1 := by
    apply mul_right_cancel₀ hc
    have e1 : x 0 1 * x 1 0 = x 0 0 * x 1 1 - 1 := by linear_combination -hx
    rw [e1, h10]
    have e2 : y 0 1 * y 1 0 = y 0 0 * y 1 1 - 1 := by linear_combination -hy
    rw [e2, h00, h11]
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/--
@isnad1 id=eq.4h3v.s9.08ac6bc18abc from=translated src=- shape=ecab871f vocab=4391c934
-/
theorem ext_of_diag (x y : Gp) (h00 : x 0 0 = y 0 0) (h01 : x 0 1 = y 0 1) (h10 : x 1 0 = 0) (h10' : y 1 0 = 0) : x = y := by
  have hx := det_eq x
  have hy := det_eq y
  rw [h10, mul_zero, sub_zero] at hx
  rw [h10', mul_zero, sub_zero] at hy
  have ha : x 0 0 ≠ 0 := fun h => by rw [h, zero_mul] at hx; exact zero_ne_one hx
  have h11 : x 1 1 = y 1 1 := by
    apply mul_left_cancel₀ ha
    rw [hx, h00, hy]
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10.trans h10'.symm
  · exact h11

/--
@isnad1 id=eq.0h1v.s9.42b81843983f from=translated src=- shape=b5900817 vocab=83c2ae98
-/
theorem natCard_doubleCoset_unipotent :
    Nat.card (DoubleCoset.Quotient
      (((CongruenceSubgroup.Gamma1 p).map rp : Subgroup Gp) : Set Gp)
      (((Subgroup.zpowers ModularGroup.T).map rp : Subgroup Gp) : Set Gp)) = 2 * (p - 1) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set U : Subgroup Gp := (CongruenceSubgroup.Gamma1 p).map rp with hUdef
  set V : Subgroup Gp := (Subgroup.zpowers ModularGroup.T).map rp with hVdef
  have hU : ∀ g : Gp, g ∈ U ↔ g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1 := fun g => mem_map_gamma1_iff p g
  have hV : ∀ g : Gp, g ∈ V ↔ g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1 := fun g => mem_map_zpowers_T_iff p g

  let f : DoubleCoset.Quotient (U : Set Gp) (V : Set Gp) → (ZMod p)ˣ ⊕ (ZMod p)ˣ :=
    Quotient.lift (inv p) (fun x y hxy => by
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp hxy
      exact inv_eq_of_rel p a b ((hU a).mp ha) ((hV b).mp hb) rfl)
  have hf : ∀ g : Gp, f (Quotient.mk _ g) = inv p g := fun _ => rfl

  have hbij : Function.Bijective f := by
    constructor
    · intro q₁ q₂ h
      induction q₁ using Quotient.inductionOn with
      | h x =>
      induction q₂ using Quotient.inductionOn with
      | h y =>
      apply Quotient.sound
      rw [hf, hf] at h
      unfold inv at h
      by_cases hx : x 1 0 = 0
      · by_cases hy : y 1 0 = 0
        · rw [dite_eq_left hx, dite_eq_left hy] at h
          have h00 : x 0 0 = y 0 0 := by
            have := Sum.inr_injective h
            exact congrArg Units.val this

          refine DoubleCoset.rel_iff.mpr ⟨uni ((y 0 1 - x 0 1) * x 0 0), (hU _).mpr ⟨rfl, rfl, rfl⟩, 1, V.one_mem, ?_⟩
          rw [mul_one]
          apply ext_of_diag p _ _ _ _ hy (by rw [mul_apply_10_of_left _ _ rfl rfl]; exact hx)
          · rw [mul_apply_00_of_left _ _ rfl, hx, mul_zero, add_zero, h00]
          · rw [mul_apply_01_of_left _ _ rfl, uni_01]
            have hx11 : x 0 0 * x 1 1 = 1 := by have := det_eq x; rw [hx, mul_zero, sub_zero] at this; exact this
            have : (y 0 1 - x 0 1) * x 0 0 * x 1 1 = y 0 1 - x 0 1 := by rw [mul_assoc, hx11, mul_one]
            rw [this]; ring
        · rw [dite_eq_left hx, dite_eq_right hy] at h
          exact absurd h Sum.inr_ne_inl
      · by_cases hy : y 1 0 = 0
        · rw [dite_eq_right hx, dite_eq_left hy] at h
          exact absurd h Sum.inl_ne_inr
        · rw [dite_eq_right hx, dite_eq_right hy] at h
          have hc : x 1 0 = y 1 0 := congrArg Units.val (Sum.inl_injective h)

          refine DoubleCoset.rel_iff.mpr ⟨uni ((y 0 0 - x 0 0) * (x 1 0)⁻¹), (hU _).mpr ⟨rfl, rfl, rfl⟩,
            uni ((y 1 1 - x 1 1) * (x 1 0)⁻¹), (hV _).mpr ⟨rfl, rfl, rfl⟩, ?_⟩
          symm
          apply ext_of_row p
          · rw [mul_apply_00_of_right _ _ rfl rfl, mul_apply_00_of_left _ _ rfl, uni_01]
            field_simp
            ring
          · rw [mul_apply_10_of_right _ _ rfl rfl, mul_apply_10_of_left _ _ rfl rfl, hc]
          · rw [mul_apply_11_of_right _ _ rfl, mul_apply_10_of_left _ _ rfl rfl, mul_apply_11_of_left _ _ rfl rfl, uni_01]
            field_simp
            ring
          · rw [mul_apply_10_of_right _ _ rfl rfl, mul_apply_10_of_left _ _ rfl rfl]; exact hx
    · rintro (u | u)
      ·
        let g₁ : Gp := ⟨!![0, -((u⁻¹ : (ZMod p)ˣ) : ZMod p); (u : ZMod p), 0], by
          rw [Matrix.det_fin_two_of]; simp only [zero_mul, neg_mul, sub_neg_eq_add, zero_add, Units.inv_mul]⟩
        refine ⟨Quotient.mk _ g₁, ?_⟩
        rw [hf]
        unfold inv
        have hne : g₁ 1 0 ≠ 0 := by show (u : ZMod p) ≠ 0; exact u.ne_zero
        rw [dite_eq_right hne]
        congr 1
        exact Units.ext rfl
      ·
        let g₂ : Gp := ⟨!![(u : ZMod p), 0; 0, ((u⁻¹ : (ZMod p)ˣ) : ZMod p)], by
          rw [Matrix.det_fin_two_of, mul_zero, sub_zero, Units.mul_inv]⟩
        refine ⟨Quotient.mk _ g₂, ?_⟩
        rw [hf]
        unfold inv
        have heq : g₂ 1 0 = 0 := rfl
        rw [dite_eq_left heq]
        congr 1
        exact Units.ext rfl
  rw [Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_sum, Nat.card_eq_fintype_card, ZMod.card_units]
  omega

end CuspKit
open scoped _root_.P2MW.S_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_of_prime.CuspKit

/--
@isnad1 id=eq.0h1v.s9.42b81843983f from=translated src=- shape=b5900817 vocab=83c2ae98
-/
theorem solution
    (p : ℕ) [Fact p.Prime] :
    Nat.card (DoubleCoset.Quotient (((CongruenceSubgroup.Gamma1 p).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod p)))) : Set SL(2, ZMod p)) (((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod p)))) : Set SL(2, ZMod p))) = 2 * (p - 1) :=
  CuspKit.natCard_doubleCoset_unipotent p
