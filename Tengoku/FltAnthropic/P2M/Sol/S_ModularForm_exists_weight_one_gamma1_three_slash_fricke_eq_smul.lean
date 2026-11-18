import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul
import Tengoku.FltAnthropic.Theorems.Thm_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.lean`: wrote out 14 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 14 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul

set_option autoImplicit false

open Complex Real Set

namespace A2Theta3
namespace LatticeSum

def hexForm (v : ℤ × ℤ) : ℤ :=
  v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2

/--
@isnad1 id=eq.0h2v.s6.a1ffe68ffa00 from=translated src=- shape=70758fe2 vocab=0d45ddb4
-/
@[scoped simp] lemma hexForm_mk (m n : ℤ) : hexForm (m, n) = m ^ 2 + m * n + n ^ 2 := rfl

/--
@isnad1 id=le.0h1v.s3.92adf8291ed3 from=translated src=- shape=70dff6bb vocab=948895eb
-/
lemma hexForm_nonneg (v : ℤ × ℤ) : 0 ≤ hexForm v := by
  obtain ⟨a, b⟩ := v
  simp only [hexForm_mk]
  nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]

/--
@isnad1 id=iff.0h1v.s5.b77a4e2370d3 from=translated src=- shape=105a1e1d vocab=e730d396
-/
lemma hexForm_eq_zero_iff (v : ℤ × ℤ) : hexForm v = 0 ↔ v = (0, 0) := by
  obtain ⟨a, b⟩ := v
  simp only [hexForm_mk, Prod.mk.injEq]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
  · rintro ⟨rfl, rfl⟩; ring

/--
@isnad1 id=le.0h1v.s6.036ea4c0472b from=translated src=- shape=64955c5e vocab=bc53ccad
-/
lemma sq_add_sq_le_two_mul_hexForm (v : ℤ × ℤ) :
    v.1 ^ 2 + v.2 ^ 2 ≤ 2 * hexForm v := by
  obtain ⟨a, b⟩ := v
  simp only [hexForm_mk]
  nlinarith [sq_nonneg (a + b)]

def hexFormNat (v : ℤ × ℤ) : ℕ :=
  (hexForm v).toNat

/--
@isnad1 id=eq.0h1v.s3.8290d3adced8 from=translated src=- shape=2c3b3e84 vocab=da35eb54
-/
@[scoped simp] lemma coe_hexFormNat (v : ℤ × ℤ) : (hexFormNat v : ℤ) = hexForm v :=
  Int.toNat_of_nonneg (hexForm_nonneg v)

/--
@isnad1 id=iff.0h2v.s4.abd9155f1cd7 from=translated src=- shape=e590b7a5 vocab=16831a0d
-/
lemma hexFormNat_eq_iff (v : ℤ × ℤ) (n : ℕ) : hexFormNat v = n ↔ hexForm v = (n : ℤ) := by
  rw [← coe_hexFormNat, Int.natCast_inj]

noncomputable def latticeTerm (τ : ℂ) (v : ℤ × ℤ) : ℂ :=
  Complex.exp (2 * (π : ℂ) * Complex.I * (hexFormNat v : ℂ) * τ)

/--
@isnad1 id=eq.0h2v.s5.5076ee251c81 from=translated src=- shape=ed6b40db vocab=4572ee39
-/
lemma norm_latticeTerm (τ : ℂ) (v : ℤ × ℤ) :
    ‖latticeTerm τ v‖ = Real.exp (-(2 * π * (hexFormNat v : ℝ) * τ.im)) := by
  rw [latticeTerm, show (2 * (π : ℂ) * Complex.I * (hexFormNat v : ℂ) * τ)
      = ((2 * π * (hexFormNat v : ℝ) : ℝ) : ℂ) * τ * Complex.I by push_cast; ring]
  rw [Complex.norm_exp, mul_I_re, im_ofReal_mul]

/--
@isnad1 id=le.2h3v.s7.2917f244fc5a from=translated src=- shape=9c81f0f8 vocab=845c402e
-/
lemma norm_latticeTerm_le_of_le_im {T : ℝ} (hT : 0 < T) {τ : ℂ} (hτ : T ≤ τ.im) (v : ℤ × ℤ) :
    ‖latticeTerm τ v‖ ≤
      Real.exp (-(π * T * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * T * (v.2 : ℝ) ^ 2)) := by
  rw [norm_latticeTerm, ← Real.exp_add, Real.exp_le_exp]
  have hQ : (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 ≤ 2 * (hexFormNat v : ℝ) := by
    have := sq_add_sq_le_two_mul_hexForm v
    have h2 : ((2 * hexForm v : ℤ) : ℝ) = 2 * (hexFormNat v : ℝ) := by
      push_cast [coe_hexFormNat]; ring_nf
      norm_cast
      simp [coe_hexFormNat]
    calc (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 = ((v.1 ^ 2 + v.2 ^ 2 : ℤ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * hexForm v : ℤ) : ℝ) := by exact_mod_cast this
      _ = 2 * (hexFormNat v : ℝ) := h2
  have hQ0 : (0 : ℝ) ≤ (hexFormNat v : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ π * T),
    mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ 2 * π * (hexFormNat v : ℝ))]

/--
@isnad1 id=summable.1h1v.s6.4f240042dd64 from=translated src=- shape=1aeaf676 vocab=fdde6e68
-/
lemma summable_gaussian_int {t : ℝ} (ht : 0 < t) :
    Summable fun m : ℤ ↦ Real.exp (-(π * t * (m : ℝ) ^ 2)) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 ht 0
  simpa only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero, neg_mul, mul_assoc] using h

/--
@isnad1 id=summable.1h1v.s6.8d30c703e1ed from=translated src=- shape=1c22b244 vocab=fcc0091e
-/
lemma summable_gaussian_prod {t : ℝ} (ht : 0 < t) :
    Summable fun v : ℤ × ℤ ↦
      Real.exp (-(π * t * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * t * (v.2 : ℝ) ^ 2)) :=
  (summable_gaussian_int ht).mul_of_nonneg (summable_gaussian_int ht)
    (fun _ ↦ (Real.exp_pos _).le) (fun _ ↦ (Real.exp_pos _).le)

/--
@isnad1 id=summable.1h1v.s5.725aa1b8d549 from=translated src=- shape=d2cf2fee vocab=b3e5a7f6
-/
theorem summable_latticeTerm {τ : ℂ} (hτ : 0 < τ.im) : Summable (latticeTerm τ) :=
  (summable_gaussian_prod hτ).of_norm_bounded (norm_latticeTerm_le_of_le_im hτ le_rfl)

noncomputable def latticeSum (τ : ℂ) : ℂ :=
  ∑' v : ℤ × ℤ, latticeTerm τ v

noncomputable def repCount (n : ℕ) : ℕ :=
  (hexFormNat ⁻¹' {n}).ncard

/--
@isnad1 id=eq.0h0v.s3.5ecb4e43f737 from=translated src=- shape=3c26ae4f vocab=73a323c0
-/
@[scoped simp] theorem repCount_zero : repCount 0 = 1 := by
  have h : hexFormNat ⁻¹' {0} = {((0 : ℤ), (0 : ℤ))} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hexFormNat_eq_iff, Int.natCast_zero,
      hexForm_eq_zero_iff]
  rw [repCount, h, Set.ncard_singleton]

/--
@isnad1 id=eq.0h2v.s7.9d70b20d099a from=translated src=- shape=f662539d vocab=0e6239be
-/
lemma tsum_fiber_eq (τ : ℂ) (n : ℕ) :
    ∑' v : (hexFormNat ⁻¹' {n}), latticeTerm τ v
      = (repCount n : ℂ) * Complex.exp (2 * (π : ℂ) * Complex.I * (n : ℂ) * τ) := by
  have hconst : ∀ v : (hexFormNat ⁻¹' {n}),
      latticeTerm τ v = Complex.exp (2 * (π : ℂ) * Complex.I * (n : ℂ) * τ) := by
    rintro ⟨v, hv⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hv
    simp [latticeTerm, hv]
  rw [tsum_congr hconst, tsum_const, Nat.card_coe_set_eq, nsmul_eq_mul, repCount]

/--
@isnad1 id=hassum.1h1v.s6.773b1d297d35 from=translated src=- shape=de024950 vocab=ddcb5fbf
-/
theorem hasSum_repCount_qpow {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ ↦ (repCount n : ℂ) * Complex.exp (2 * (π : ℂ) * Complex.I * (n : ℂ) * τ))
      (latticeSum τ) := by
  have h := ((summable_latticeTerm hτ).hasSum).tsum_fiberwise hexFormNat
  simp only [tsum_fiber_eq τ] at h
  exact h

end A2Theta3.LatticeSum
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3

namespace A2Theta3

noncomputable section

open Complex Real

def hexThetaTerm (σ : ℂ) (p : ℤ × ℤ) : ℂ :=
  cexp (2 * π * I * σ * ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2))

def hexTheta (σ : ℂ) : ℂ :=
  ∑' p : ℤ × ℤ, hexThetaTerm σ p

/--
@isnad1 id=ne.1h1v.s4.b6cf537274cc from=translated src=- shape=2154ac66 vocab=3c72e7c9
-/
lemma ne_zero_of_im_pos {σ : ℂ} (hσ : 0 < σ.im) : σ ≠ 0 := by
  rintro rfl
  simp at hσ

/--
@isnad1 id=lt.1h1v.s5.7327e937ddcc from=translated src=- shape=3766181f vocab=2c79fcc4
-/
lemma im_neg_one_div_three_mul_pos {σ : ℂ} (hσ : 0 < σ.im) : 0 < (-1 / (3 * σ)).im := by
  have h3σ : (3 : ℂ) * σ ≠ 0 := mul_ne_zero (by norm_num) (ne_zero_of_im_pos hσ)
  have him : ((3 : ℂ) * σ).im = 3 * σ.im := by
    simp [Complex.mul_im]
  rw [show (-1 / (3 * σ) : ℂ) = -((3 : ℂ) * σ)⁻¹ by rw [neg_div, one_div]]
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg, him]
  exact div_pos (by linarith) (Complex.normSq_pos.mpr h3σ)

/--
@isnad1 id=ne.0h0v.s4.b5fd22c1bf1d from=translated src=- shape=43016b0b vocab=5679d3a5
-/
lemma sqrt_three_ne_zero : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'

/--
@isnad1 id=eq.1h1v.s6.0f64b1e212ff from=translated src=- shape=703e8aea vocab=0f227843
-/
theorem hexTheta_fricke {σ : ℂ} (hσ : 0 < σ.im) :
    hexTheta (-1 / (3 * σ)) = -I * (Real.sqrt 3 : ℂ) * σ * hexTheta σ :=
  (HexagonalLattice.summable_thetaTerm_and_tsum_neg_inv_three_mul σ hσ).2

end
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum

end A2Theta3
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum

open Matrix CongruenceSubgroup Subgroup ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold Pointwise

namespace A2Theta3

namespace Gamma0Three

/--
@isnad1 id=fact.0h0v.s2.fdf266938498 from=translated src=- shape=8d7dbbf6 vocab=c1c9ca6d
-/
scoped instance fact_prime_three_A2T3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩

def repOfLabel : Option (ZMod 3) → SL(2, ℤ)
  | none => 1
  | some k => ⟨!![0, -1; 1, (k.val : ℤ)], by simp [Matrix.det_fin_two_of]⟩

/--
@isnad1 id=eq.0h0v.s6.d276d7c1b82c from=translated src=- shape=d32e451a vocab=4bb505c2
-/
@[scoped simp] lemma repOfLabel_none : repOfLabel none = 1 := rfl

/--
@isnad1 id=eq.0h1v.s6.023e2f65b897 from=translated src=- shape=bb17f649 vocab=7245a740
-/
@[scoped simp] lemma repOfLabel_some_one_zero (k : ZMod 3) : repOfLabel (some k) 1 0 = 1 := rfl

/--
@isnad1 id=eq.0h1v.s7.521b298fa609 from=translated src=- shape=167414b4 vocab=d0e1a223
-/
@[scoped simp] lemma repOfLabel_some_one_one (k : ZMod 3) :
    repOfLabel (some k) 1 1 = (k.val : ℤ) := rfl

/--
@isnad1 id=eq.0h0v.s7.a406afd5260e from=translated src=- shape=04eee0ce vocab=568d92df
-/
@[scoped simp] lemma one_apply_one_zero : (1 : SL(2, ℤ)) 1 0 = 0 := rfl

/--
@isnad1 id=eq.0h0v.s7.5416eec10a68 from=translated src=- shape=04eee0ce vocab=568d92df
-/
@[scoped simp] lemma one_apply_one_one : (1 : SL(2, ℤ)) 1 1 = 1 := rfl

def transversal : Set SL(2, ℤ) := Set.range repOfLabel

def label (g : SL(2, ℤ)) : Option (ZMod 3) :=
  if (g 1 0 : ZMod 3) = 0 then none
  else some ((g 1 1 : ZMod 3) / (g 1 0 : ZMod 3))

private lemma intCast_val (k : ZMod 3) : (((k.val : ℕ) : ℤ) : ZMod 3) = k := by
  exact_mod_cast ZMod.natCast_rightInverse k

/--
@isnad1 id=ne.1h1v.s8.77a26e577108 from=translated src=- shape=58cd7501 vocab=dff4a5aa
-/
lemma apply_one_one_ne_zero (g : SL(2, ℤ)) (hc : (g 1 0 : ZMod 3) = 0) :
    (g 1 1 : ZMod 3) ≠ 0 := by
  intro hd
  have hdet : (g 0 0 : ℤ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h2 := g.2
    rw [Matrix.det_fin_two] at h2
    exact h2
  have hcast : (g 0 0 : ZMod 3) * (g 1 1 : ZMod 3)
      - (g 0 1 : ZMod 3) * (g 1 0 : ZMod 3) = 1 := by
    have h3 : (((g 0 0 : ℤ) * g 1 1 - g 0 1 * g 1 0 : ℤ) : ZMod 3) = ((1 : ℤ) : ZMod 3) := by
      rw [hdet]
    push_cast at h3
    exact h3
  rw [hc, hd, mul_zero, mul_zero, sub_zero] at hcast
  exact zero_ne_one hcast

private theorem mul_entry (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  show ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem inv_entries (A : SL(2, ℤ)) :
    A⁻¹ 0 0 = A 1 1 ∧ A⁻¹ 0 1 = -A 0 1 ∧ A⁻¹ 1 0 = -A 1 0 ∧ A⁻¹ 1 1 = A 0 0 := by
  have h : ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h]

/--
@isnad1 id=eq.0h2v.s9.a27e34aa398c from=translated src=- shape=5a2ca795 vocab=f3f3675c
-/
lemma mul_inv_apply_one_zero (g h : SL(2, ℤ)) :
    (g * h⁻¹) 1 0 = g 1 0 * h 1 1 - g 1 1 * h 1 0 := by
  rw [mul_entry, (inv_entries h).1, (inv_entries h).2.2.1]
  ring

/--
@isnad1 id=iff.0h2v.s10.d86fc01a948b from=translated src=- shape=9a6ebe4a vocab=a1300a27
-/
theorem mul_inv_mem_iff (g h : SL(2, ℤ)) :
    g * h⁻¹ ∈ Gamma0 3 ↔
      (g 1 0 : ZMod 3) * (h 1 1 : ZMod 3) = (g 1 1 : ZMod 3) * (h 1 0 : ZMod 3) := by
  rw [Gamma0_mem, mul_inv_apply_one_zero]
  push_cast
  exact sub_eq_zero

/--
@isnad1 id=iff.0h2v.s8.8349e62d4ddf from=translated src=- shape=071fbf96 vocab=9ac04f69
-/
theorem mul_inv_repOfLabel_mem_iff (g : SL(2, ℤ)) (l : Option (ZMod 3)) :
    g * (repOfLabel l)⁻¹ ∈ Gamma0 3 ↔ l = label g := by
  rw [mul_inv_mem_iff]
  unfold label
  cases l with
  | none =>
    rw [repOfLabel_none, one_apply_one_one, one_apply_one_zero, Int.cast_one, mul_one,
      Int.cast_zero, mul_zero]
    by_cases hc : (g 1 0 : ZMod 3) = 0
    · rw [ite_eq_left hc]
      exact iff_of_true hc rfl
    · rw [ite_eq_right hc]
      exact iff_of_false hc (by simp)
  | some k =>
    rw [repOfLabel_some_one_one, repOfLabel_some_one_zero, Int.cast_one, mul_one,
      intCast_val]
    by_cases hc : (g 1 0 : ZMod 3) = 0
    · rw [ite_eq_left hc]
      refine iff_of_false (fun hcontra => ?_) (by simp)
      rw [hc, zero_mul] at hcontra
      exact apply_one_one_ne_zero g hc hcontra.symm
    · rw [ite_eq_right hc, Option.some_inj, eq_div_iff hc]
      constructor <;> intro h <;> linear_combination h

end Gamma0Three
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum

def U₃ : SL(2, ℤ) := ⟨!![1, 0; -3, 1], by simp [Matrix.det_fin_two_of]⟩

/--
@isnad1 id=eq.0h0v.s6.72688fcb0f7f from=translated src=- shape=552b42ea vocab=171262ae
-/
@[scoped simp] lemma U₃_one_zero : U₃ 1 0 = -3 := rfl
/--
@isnad1 id=eq.0h0v.s6.c9520a640dce from=translated src=- shape=669cc5ff vocab=e2d892b1
-/
@[scoped simp] lemma U₃_one_one : U₃ 1 1 = 1 := rfl

/--
@isnad1 id=mem.0h0v.s7.196b421842dd from=translated src=- shape=95df9e21 vocab=8624f481
-/
lemma T_mem_gamma0_three : ModularGroup.T ∈ Gamma0 3 := by
  rw [Gamma0_mem]; decide

/--
@isnad1 id=mem.0h0v.s7.6d325fa70766 from=translated src=- shape=95df9e21 vocab=b5d01dfa
-/
lemma U₃_mem_gamma0_three : U₃ ∈ Gamma0 3 := by
  rw [Gamma0_mem]; decide

/--
@isnad1 id=mem.0h0v.s8.ebb0d762efe9 from=translated src=- shape=99b5c3fa vocab=3a18f723
-/
lemma neg_one_mem_gamma0_three : (-1 : SL(2, ℤ)) ∈ Gamma0 3 := by
  rw [Gamma0_mem]; decide

def gens : Set SL(2, ℤ) := {ModularGroup.T, U₃, -1}

/--
@isnad1 id=le.0h0v.s7.6d56e0c48458 from=translated src=- shape=1eb93031 vocab=38c4e8e2
-/
lemma gens_subset_gamma0_three : gens ⊆ (Gamma0 3 : Subgroup SL(2, ℤ)) := by
  rintro x (rfl | rfl | rfl)
  · exact T_mem_gamma0_three
  · exact U₃_mem_gamma0_three
  · exact neg_one_mem_gamma0_three

/--
@isnad1 id=eq.0h0v.s6.7bfff77c5e62 from=translated src=- shape=ab32f238 vocab=6af3b117
-/
theorem closure_T_U_neg_one_eq : Subgroup.closure gens = Gamma0 3 :=
  CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three U₃ rfl

def chi3 (γ : SL(2, ℤ)) : ℤ :=
  if (γ 1 1 : ZMod 3) = 1 then 1 else -1

/--
@isnad1 id=or.0h1v.s5.8d528b1d0100 from=translated src=- shape=9dedbdad vocab=a4a6faa8
-/
lemma chi3_eq_one_or_neg_one (γ : SL(2, ℤ)) : chi3 γ = 1 ∨ chi3 γ = -1 := by
  unfold chi3; split <;> simp

/--
@isnad1 id=eq.0h1v.s5.825c61afae2d from=translated src=- shape=1e92ce31 vocab=1f939ca7
-/
lemma chi3_mul_self (γ : SL(2, ℤ)) : chi3 γ * chi3 γ = 1 := by
  rcases chi3_eq_one_or_neg_one γ with h | h <;> rw [h] <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.a1106b58b524 from=translated src=- shape=e9fbbcc9 vocab=797f5335
-/
@[scoped simp] lemma chi3_one : chi3 1 = 1 := by unfold chi3; norm_num

/--
@isnad1 id=eq.0h0v.s3.8626c29b698b from=translated src=- shape=b0ae1d2b vocab=1994d5fe
-/
@[scoped simp] lemma chi3_T : chi3 ModularGroup.T = 1 := by
  unfold chi3; rw [show (ModularGroup.T 1 1 : ZMod 3) = 1 by decide]; simp

/--
@isnad1 id=eq.0h0v.s3.ab2ea0691fe5 from=translated src=- shape=b0ae1d2b vocab=acd69766
-/
@[scoped simp] lemma chi3_U₃ : chi3 U₃ = 1 := by
  unfold chi3; rw [show (U₃ 1 1 : ZMod 3) = 1 by decide]; simp

/--
@isnad1 id=eq.0h0v.s6.1bc215a35ab8 from=translated src=- shape=6180c7c1 vocab=a4a6faa8
-/
@[scoped simp] lemma chi3_neg_one : chi3 (-1 : SL(2, ℤ)) = -1 := by
  unfold chi3; rw [show ((-1 : SL(2, ℤ)) 1 1 : ZMod 3) = 2 by decide]; decide

/--
@isnad1 id=ne.1h1v.s8.084cfb62b464 from=translated src=- shape=cb8c8818 vocab=6d9848f5
-/
lemma apply_one_one_ne_zero_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 3) :
    (γ 1 1 : ZMod 3) ≠ 0 :=
  Gamma0Three.apply_one_one_ne_zero γ (Gamma0_mem.mp hγ)

/--
@isnad1 id=eq.2h2v.s9.ec425988c324 from=translated src=- shape=6be88f89 vocab=25c0bdab
-/
lemma coe_mul_apply_one_one {γ δ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 3) (hδ : δ ∈ Gamma0 3) :
    ((γ * δ) 1 1 : ZMod 3) = (γ 1 1 : ZMod 3) * (δ 1 1 : ZMod 3) := by
  have := map_mul (Gamma0Map 3) (⟨γ, hγ⟩ : Gamma0 3) (⟨δ, hδ⟩ : Gamma0 3)
  simpa [Gamma0Map] using this

/--
@isnad1 id=eq.2h2v.s9.d495acedac64 from=translated src=- shape=fccd3be2 vocab=e16e8d08
-/
theorem chi3_mul {γ δ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 3) (hδ : δ ∈ Gamma0 3) :
    chi3 (γ * δ) = chi3 γ * chi3 δ := by
  have key : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide
  unfold chi3
  rw [coe_mul_apply_one_one hγ hδ]
  rcases key _ (apply_one_one_ne_zero_of_mem hγ) with h1 | h1 <;>
    rcases key _ (apply_one_one_ne_zero_of_mem hδ) with h2 | h2 <;>
      rw [h1, h2] <;> decide

/--
@isnad1 id=eq.1h1v.s7.ea9497f29643 from=translated src=- shape=b688f4e0 vocab=ec17ef7a
-/
theorem chi3_eq_one_of_mem_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 3) : chi3 γ = 1 := by
  unfold chi3
  rw [((Gamma1_mem 3 γ).mp hγ).2.1]
  simp

section Sweep

variable (F : ℍ → ℂ)

/--
@isnad1 id=eq.0h1v.s8.cfa6ed90ae44 from=translated src=- shape=6260d37b vocab=2921ea66
-/
theorem slash_neg_one :
    F ∣[(1 : ℤ)] (-1 : SL(2, ℤ)) = ((chi3 (-1 : SL(2, ℤ)) : ℤ) : ℂ) • F := by
  rw [chi3_neg_one]
  ext τ
  rw [ModularForm.SL_slash_apply]
  have hsmul : ((-1 : SL(2, ℤ)) • τ : ℍ) = τ := by
    rw [show (-1 : SL(2, ℤ)) = -(1 : SL(2, ℤ)) from rfl, ModularGroup.SL_neg_smul, one_smul]
  have hden : denom (-1 : SL(2, ℤ)) τ = -1 := by
    rw [ModularGroup.denom_apply]
    norm_num [show ((-1 : SL(2, ℤ)) 1 0) = 0 from rfl, show ((-1 : SL(2, ℤ)) 1 1) = -1 from rfl]
  rw [hsmul, hden]
  have hpow : ((-1 : ℂ)) ^ (-(1 : ℤ)) = -1 := by norm_num
  rw [hpow]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/--
@isnad1 id=eq.3h2v.s8.7e221fa0ea4e from=translated src=- shape=cee314b6 vocab=4c45c9aa
-/
theorem slash_eq_chi3_smul
    (hT : F ∣[(1 : ℤ)] ModularGroup.T = F) (hU : F ∣[(1 : ℤ)] U₃ = F)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 3) :
    F ∣[(1 : ℤ)] γ = (chi3 γ : ℂ) • F := by

  let p : (g : SL(2, ℤ)) → g ∈ Subgroup.closure gens → Prop :=
    fun g _ => F ∣[(1 : ℤ)] g = (chi3 g : ℂ) • F

  have hmem_iff : ∀ {g : SL(2, ℤ)}, g ∈ Subgroup.closure gens ↔ g ∈ Gamma0 3 := by
    intro g; rw [closure_T_U_neg_one_eq]
  refine Subgroup.closure_induction (k := gens) (p := p) ?_ ?_ ?_ ?_ (hmem_iff.mpr hγ)
  ·
    rintro x (rfl | rfl | rfl)
    · show F ∣[(1 : ℤ)] ModularGroup.T = (chi3 ModularGroup.T : ℂ) • F
      rw [hT, chi3_T]; simp
    · show F ∣[(1 : ℤ)] U₃ = (chi3 U₃ : ℂ) • F
      rw [hU, chi3_U₃]; simp
    · exact slash_neg_one F
  ·
    show F ∣[(1 : ℤ)] (1 : SL(2, ℤ)) = (chi3 1 : ℂ) • F
    rw [SlashAction.slash_one, chi3_one]
    simp
  ·
    intro x y hx hy hpx hpy
    show F ∣[(1 : ℤ)] (x * y) = (chi3 (x * y) : ℂ) • F
    have hx' : x ∈ Gamma0 3 := hmem_iff.mp hx
    have hy' : y ∈ Gamma0 3 := hmem_iff.mp hy
    calc F ∣[(1 : ℤ)] (x * y) = (F ∣[(1 : ℤ)] x) ∣[(1 : ℤ)] y := by
            rw [SlashAction.slash_mul]
      _ = ((chi3 x : ℂ) • F) ∣[(1 : ℤ)] y := by rw [hpx]
      _ = (chi3 x : ℂ) • (F ∣[(1 : ℤ)] y) := by rw [ModularForm.SL_smul_slash]
      _ = (chi3 x : ℂ) • ((chi3 y : ℂ) • F) := by rw [hpy]
      _ = ((chi3 x * chi3 y : ℤ) : ℂ) • F := by rw [smul_smul]; norm_num
      _ = (chi3 (x * y) : ℂ) • F := by rw [← chi3_mul hx' hy']
  ·
    intro x hx hpx
    show F ∣[(1 : ℤ)] x⁻¹ = (chi3 x⁻¹ : ℂ) • F
    have hx' : x ∈ Gamma0 3 := hmem_iff.mp hx
    have hxinv : x⁻¹ ∈ Gamma0 3 := inv_mem hx'

    have hchi : chi3 x⁻¹ = chi3 x := by
      have h1 : chi3 (x⁻¹ * x) = chi3 x⁻¹ * chi3 x := chi3_mul hxinv hx'
      rw [inv_mul_cancel, chi3_one] at h1
      rcases chi3_eq_one_or_neg_one x with h | h <;>
        rcases chi3_eq_one_or_neg_one x⁻¹ with h' | h' <;> rw [h, h'] <;> rw [h, h'] at h1 <;>
          omega

    have h2 : (F ∣[(1 : ℤ)] x) ∣[(1 : ℤ)] x⁻¹ = ((chi3 x : ℂ) • F) ∣[(1 : ℤ)] x⁻¹ := by
      rw [hpx]
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      ModularForm.SL_smul_slash] at h2

    have h3 := congrArg (fun G => (chi3 x : ℂ) • G) h2
    simp only [smul_smul] at h3
    rw [show ((chi3 x : ℂ) * (chi3 x : ℂ)) = ((chi3 x * chi3 x : ℤ) : ℂ) by push_cast; ring,
      chi3_mul_self] at h3
    rw [hchi]
    simpa using h3.symm

/--
@isnad1 id=eq.3h2v.s8.c176acf14b69 from=translated src=- shape=3cee13ae vocab=94de9fa8
-/
theorem slash_eq_self_of_mem_Gamma1
    (hT : F ∣[(1 : ℤ)] ModularGroup.T = F) (hU : F ∣[(1 : ℤ)] U₃ = F)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 3) :
    F ∣[(1 : ℤ)] γ = F := by
  rw [slash_eq_chi3_smul F hT hU (Gamma1_in_Gamma0 3 hγ), chi3_eq_one_of_mem_Gamma1 hγ]
  simp

end Sweep
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum
section Packaging

def slashInvariantForm_of_T_U (F : ℍ → ℂ)
    (hT : F ∣[(1 : ℤ)] ModularGroup.T = F) (hU : F ∣[(1 : ℤ)] U₃ = F) :
    SlashInvariantForm (Gamma1 3) 1 where
  toFun := F
  slash_action_eq' := by
    rintro γ ⟨δ, hδ, rfl⟩

    exact slash_eq_self_of_mem_Gamma1 F hT hU hδ

end Packaging
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum

end A2Theta3
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum

open Complex Real Matrix CongruenceSubgroup Subgroup ModularForm UpperHalfPlane
open A2Theta3.LatticeSum
open scoped MatrixGroups ModularForm Manifold

namespace A2Theta3

noncomputable section

/--
@isnad1 id=eq.0h2v.s3.b6ca3a779cca from=translated src=- shape=041c21f9 vocab=adc080b8
-/
lemma latticeTerm_eq_hexThetaTerm (τ : ℂ) (v : ℤ × ℤ) :
    latticeTerm τ v = hexThetaTerm τ v := by
  unfold latticeTerm hexThetaTerm
  congr 1
  have h : ((hexFormNat v : ℤ) : ℂ) = (v.1 : ℂ) ^ 2 + (v.1 : ℂ) * (v.2 : ℂ) + (v.2 : ℂ) ^ 2 := by
    rw [coe_hexFormNat]
    unfold hexForm
    push_cast
    ring
  push_cast at h
  rw [h]
  ring

/--
@isnad1 id=eq.0h1v.s3.ac6b40fe9aa9 from=translated src=- shape=0fc427d2 vocab=0ef7614d
-/
theorem latticeSum_eq_hexTheta (τ : ℂ) : latticeSum τ = hexTheta τ :=
  tsum_congr fun v => latticeTerm_eq_hexThetaTerm τ v

def hexThetaH : ℍ → ℂ := fun τ => latticeSum (τ : ℂ)

/--
@isnad1 id=eq.0h1v.s3.671a365b6ea2 from=translated src=- shape=69b989be vocab=6cff656d
-/
@[scoped simp] lemma hexThetaH_apply (τ : ℍ) : hexThetaH τ = latticeSum (τ : ℂ) := rfl

/--
@isnad1 id=eq.0h1v.s3.f7c44c9021b3 from=translated src=- shape=69b989be vocab=d56d1973
-/
lemma hexThetaH_eq_hexTheta (τ : ℍ) : hexThetaH τ = hexTheta (τ : ℂ) :=
  latticeSum_eq_hexTheta _

/--
@isnad1 id=eq.0h2v.s4.079e91058e75 from=translated src=- shape=ce17660f vocab=e0613151
-/
lemma hexThetaTerm_add_one (σ : ℂ) (v : ℤ × ℤ) :
    hexThetaTerm (σ + 1) v = hexThetaTerm σ v := by
  rw [← latticeTerm_eq_hexThetaTerm, ← latticeTerm_eq_hexThetaTerm]
  unfold latticeTerm
  rw [show 2 * (π : ℂ) * Complex.I * (hexFormNat v : ℂ) * (σ + 1)
      = 2 * (π : ℂ) * Complex.I * (hexFormNat v : ℂ) * σ
        + (hexFormNat v : ℂ) * (2 * (π : ℂ) * Complex.I) by ring,
    Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/--
@isnad1 id=eq.0h1v.s4.3e28172ff33b from=translated src=- shape=3150584f vocab=b07881b8
-/
theorem hexTheta_add_one (σ : ℂ) : hexTheta (σ + 1) = hexTheta σ :=
  tsum_congr fun v => hexThetaTerm_add_one σ v

/--
@isnad1 id=eq.0h0v.s6.32074bd2791a from=translated src=- shape=656092e4 vocab=8cc09de6
-/
theorem hexThetaH_slash_T : hexThetaH ∣[(1 : ℤ)] ModularGroup.T = hexThetaH := by
  funext z
  refine (slash_action_eq'_iff 1 hexThetaH ModularGroup.T z).mpr ?_
  rw [show ModularGroup.T 1 0 = 0 from rfl, show ModularGroup.T 1 1 = 1 from rfl,
    modular_T_smul]
  simp only [Int.cast_zero, Int.cast_one, zero_mul, zero_add, zpow_one, one_mul]
  show latticeSum (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = latticeSum (z : ℂ)
  rw [UpperHalfPlane.coe_vadd, latticeSum_eq_hexTheta, latticeSum_eq_hexTheta,
    Complex.ofReal_one, add_comm, hexTheta_add_one]

/--
@isnad1 id=eq.0h0v.s5.3ad392d40293 from=translated src=- shape=71ddb1a6 vocab=5737b69d
-/
lemma sqrt_three_mul_sqrt_three : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/--
@isnad1 id=ne.1h1v.s5.ee89095d884b from=translated src=- shape=9b138ed7 vocab=3410ccea
-/
lemma U_denom_ne_zero {z : ℂ} (hz : 0 < z.im) : (-3 : ℂ) * z + 1 ≠ 0 := by
  intro h
  have him : ((-3 : ℂ) * z + 1).im = -3 * z.im := by
    simp [Complex.add_im, Complex.mul_im]
  rw [h] at him
  simp only [Complex.zero_im] at him
  nlinarith

/--
@isnad1 id=eq.1h1v.s7.a83b6ba141a8 from=translated src=- shape=71074c86 vocab=f9f8a77f
-/
lemma U_smul_eq_fricke_translate_fricke {z : ℂ} (hz : 0 < z.im) :
    z / ((-3) * z + 1) = -1 / (3 * (-1 / (3 * z) + 1)) := by
  have hz0 : z ≠ 0 := ne_zero_of_im_pos hz
  have hden : (-3 : ℂ) * z + 1 ≠ 0 := U_denom_ne_zero hz

  have h1 : (3 : ℂ) * (-1 / (3 * z) + 1) = (3 * z - 1) / z := by
    field_simp
    ring
  have h2 : ((3 : ℂ) * z - 1) / z ≠ 0 := by
    refine div_ne_zero (fun h => hden ?_) hz0
    linear_combination -h
  rw [h1, div_eq_div_iff hden h2, mul_div_assoc', div_eq_iff hz0]
  ring

/--
@isnad1 id=eq.1h1v.s7.8d2a209f78ba from=translated src=- shape=11cc33d3 vocab=63ec1879
-/
lemma fricke_double_multiplier {z : ℂ} (hz : 0 < z.im) :
    -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
      * (-Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * z) = (-3) * z + 1 := by
  have hz0 : z ≠ 0 := ne_zero_of_im_pos hz
  have key : (-1 / (3 * z) + 1) * z = z - 1 / 3 := by
    field_simp
    ring
  calc -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
        * (-Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * z)
      = (Complex.I * Complex.I) * (((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ))
          * ((-1 / (3 * z) + 1) * z) := by ring
    _ = (-1) * 3 * (z - 1 / 3) := by rw [Complex.I_mul_I, sqrt_three_mul_sqrt_three, key]
    _ = (-3) * z + 1 := by ring

/--
@isnad1 id=eq.1h1v.s6.70d47e797401 from=translated src=- shape=d275afaf vocab=4736a11d
-/
theorem hexTheta_U_law {z : ℂ} (hz : 0 < z.im) :
    hexTheta (z / ((-3) * z + 1)) = ((-3) * z + 1) * hexTheta z := by

  have hσ : 0 < (-1 / (3 * z)).im := im_neg_one_div_three_mul_pos hz
  have hσ1 : 0 < (-1 / (3 * z) + 1).im := by
    rwa [Complex.add_im, Complex.one_im, add_zero]
  calc hexTheta (z / ((-3) * z + 1))
      = hexTheta (-1 / (3 * (-1 / (3 * z) + 1))) := by
        rw [U_smul_eq_fricke_translate_fricke hz]
    _ = -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
          * hexTheta (-1 / (3 * z) + 1) := hexTheta_fricke hσ1
    _ = -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
          * hexTheta (-1 / (3 * z)) := by rw [hexTheta_add_one]
    _ = -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
          * (-Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * z * hexTheta z) := by
        rw [hexTheta_fricke hz]
    _ = ((-3) * z + 1) * hexTheta z := by
        rw [show -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
              * (-Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * z * hexTheta z)
            = -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (-1 / (3 * z) + 1)
              * (-Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * z) * hexTheta z by ring,
          fricke_double_multiplier hz]

/--
@isnad1 id=eq.0h1v.s7.0bac734b8ded from=translated src=- shape=db878cbd vocab=9d0f96f7
-/
lemma coe_U_smul (z : ℍ) : ((U₃ • z : ℍ) : ℂ) = (z : ℂ) / ((-3) * (z : ℂ) + 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [show U₃ 0 0 = 1 from rfl, show U₃ 0 1 = 0 from rfl,
    show U₃ 1 0 = -3 from rfl, show U₃ 1 1 = 1 from rfl, eq_intCast]
  push_cast
  rw [one_mul, add_zero]

/--
@isnad1 id=eq.0h0v.s6.a40e0714c6a2 from=translated src=- shape=656092e4 vocab=9f4b5ec4
-/
theorem hexThetaH_slash_U : hexThetaH ∣[(1 : ℤ)] U₃ = hexThetaH := by
  funext z
  refine (slash_action_eq'_iff 1 hexThetaH U₃ z).mpr ?_
  have hz : 0 < (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact z.im_pos
  rw [U₃_one_zero, U₃_one_one]
  push_cast
  rw [zpow_one]
  show latticeSum ((U₃ • z : ℍ) : ℂ) = _ * latticeSum (z : ℂ)
  rw [coe_U_smul, latticeSum_eq_hexTheta, latticeSum_eq_hexTheta, hexTheta_U_law hz]

def thetaBound : ℝ :=
  ∑' v : ℤ × ℤ, Real.exp (-(π * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * (v.2 : ℝ) ^ 2))

/--
@isnad1 id=le.1h1v.s4.73c889c28611 from=translated src=- shape=5cff623d vocab=15e6fed5
-/
theorem norm_latticeSum_le_of_one_le_im {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖latticeSum τ‖ ≤ thetaBound := by
  have hτ0 : 0 < τ.im := lt_of_lt_of_le one_pos hτ

  have hdom : ∀ v : ℤ × ℤ, ‖latticeTerm τ v‖
      ≤ Real.exp (-(π * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * (v.2 : ℝ) ^ 2)) := by
    intro v
    have h := norm_latticeTerm_le_of_le_im one_pos hτ v
    simpa only [mul_one, one_mul] using h

  have hgauss : Summable fun v : ℤ × ℤ =>
      Real.exp (-(π * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * (v.2 : ℝ) ^ 2)) := by
    simpa only [mul_one, one_mul] using summable_gaussian_prod one_pos
  have hsum_norm : Summable fun v : ℤ × ℤ => ‖latticeTerm τ v‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hgauss
  calc ‖latticeSum τ‖ ≤ ∑' v : ℤ × ℤ, ‖latticeTerm τ v‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' v : ℤ × ℤ, Real.exp (-(π * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * (v.2 : ℝ) ^ 2)) :=
        hsum_norm.tsum_le_tsum hdom hgauss
    _ = thetaBound := rfl

/--
@isnad1 id=isbounde.0h0v.s2.e6416af39603 from=translated src=- shape=25b03439 vocab=a263954a
-/
theorem isBoundedAtImInfty_hexThetaH : IsBoundedAtImInfty hexThetaH := by
  refine UpperHalfPlane.isBoundedAtImInfty_iff.mpr ⟨thetaBound, 1, fun z hz => ?_⟩
  exact norm_latticeSum_le_of_one_le_im (by rwa [UpperHalfPlane.coe_im])

/--
@isnad1 id=eq.0h2v.s5.04d4f4a1b672 from=translated src=- shape=21a44742 vocab=67c53065
-/
lemma im_add_natCast_div_three (w : ℂ) (n : ℕ) : ((w + (n : ℂ)) / 3).im = w.im / 3 := by
  rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im]
  simp [Complex.add_im]

/--
@isnad1 id=le.0h0v.s5.d55ea1acaaca from=translated src=- shape=a05b7e42 vocab=e6874edf
-/
lemma norm_neg_I_div_sqrt_three_le_one :
    ‖(-Complex.I / ((Real.sqrt 3 : ℝ) : ℂ))‖ ≤ 1 := by
  have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  rw [norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 3), div_le_one (by linarith)]
  exact h3

/--
@isnad1 id=eq.0h2v.s7.99f2c9941223 from=translated src=- shape=8522f791 vocab=372b3b74
-/
theorem hexThetaH_slash_repOfLabel_apply (k : ZMod 3) (z : ℍ) :
    (hexThetaH ∣[(1 : ℤ)] Gamma0Three.repOfLabel (some k)) z
      = (-Complex.I / ((Real.sqrt 3 : ℝ) : ℂ)) * hexTheta (((z : ℂ) + (k.val : ℂ)) / 3) := by
  have hz : 0 < (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact z.im_pos

  have hden_im : ((z : ℂ) + (k.val : ℂ)).im = (z : ℂ).im := by
    simp only [Complex.add_im, Complex.natCast_im, add_zero]
  have hden_ne : (z : ℂ) + (k.val : ℂ) ≠ 0 := by
    intro h
    rw [← Complex.zero_im, ← h, hden_im] at hz
    exact lt_irrefl _ hz

  have hσ_im : 0 < (((z : ℂ) + (k.val : ℂ)) / 3).im := by
    rw [im_add_natCast_div_three]
    positivity

  have hsmul : ((Gamma0Three.repOfLabel (some k) • z : ℍ) : ℂ)
      = -1 / ((z : ℂ) + (k.val : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [show Gamma0Three.repOfLabel (some k) 0 0 = 0 from rfl,
      show Gamma0Three.repOfLabel (some k) 0 1 = -1 from rfl,
      show Gamma0Three.repOfLabel (some k) 1 0 = 1 from rfl,
      show Gamma0Three.repOfLabel (some k) 1 1 = (k.val : ℤ) from rfl, eq_intCast]
    push_cast
    rw [zero_mul, zero_add, one_mul]

  have hdenom : denom (Gamma0Three.repOfLabel (some k)) z = (z : ℂ) + (k.val : ℂ) := by
    rw [ModularGroup.denom_apply,
      show Gamma0Three.repOfLabel (some k) 1 0 = 1 from rfl,
      show Gamma0Three.repOfLabel (some k) 1 1 = (k.val : ℤ) from rfl]
    push_cast
    rw [one_mul]

  have hfricke : hexTheta (-1 / ((z : ℂ) + (k.val : ℂ)))
      = -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (((z : ℂ) + (k.val : ℂ)) / 3)
        * hexTheta (((z : ℂ) + (k.val : ℂ)) / 3) := by
    have h := hexTheta_fricke hσ_im
    rw [show (3 : ℂ) * (((z : ℂ) + (k.val : ℂ)) / 3) = (z : ℂ) + (k.val : ℂ) by ring] at h
    exact h

  have hmul : -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (((z : ℂ) + (k.val : ℂ)) / 3)
      * ((z : ℂ) + (k.val : ℂ))⁻¹ = -Complex.I / ((Real.sqrt 3 : ℝ) : ℂ) := by
    rw [eq_div_iff sqrt_three_ne_zero,
      show -Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (((z : ℂ) + (k.val : ℂ)) / 3)
          * ((z : ℂ) + (k.val : ℂ))⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)
        = -Complex.I * (((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ))
          * (((z : ℂ) + (k.val : ℂ)) * ((z : ℂ) + (k.val : ℂ))⁻¹) / 3 by ring,
      sqrt_three_mul_sqrt_three, mul_inv_cancel₀ hden_ne]
    ring

  rw [ModularForm.SL_slash_apply, hdenom, _root_.zpow_neg, zpow_one]
  show latticeSum ((Gamma0Three.repOfLabel (some k) • z : ℍ) : ℂ) * _ = _
  rw [hsmul, latticeSum_eq_hexTheta, hfricke]
  linear_combination (hexTheta (((z : ℂ) + (k.val : ℂ)) / 3)) * hmul

/--
@isnad1 id=isbounde.0h1v.s6.35fdc4911db8 from=translated src=- shape=74fa5347 vocab=4f327962
-/
theorem isBoundedAtImInfty_hexThetaH_slash (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (hexThetaH ∣[(1 : ℤ)] γ) := by

  set r := Gamma0Three.repOfLabel (Gamma0Three.label γ) with hr
  have hδ : γ * r⁻¹ ∈ Gamma0 3 :=
    (Gamma0Three.mul_inv_repOfLabel_mem_iff γ (Gamma0Three.label γ)).mpr rfl
  have hfact : γ = γ * r⁻¹ * r := (inv_mul_cancel_right γ r).symm
  rw [hfact, SlashAction.slash_mul,
    slash_eq_chi3_smul hexThetaH hexThetaH_slash_T hexThetaH_slash_U hδ,
    ModularForm.SL_smul_slash]

  refine Filter.BoundedAtFilter.smul _ ?_

  rcases hcase : Gamma0Three.label γ with _ | k
  ·
    rw [hr, hcase, Gamma0Three.repOfLabel_none, SlashAction.slash_one]
    exact isBoundedAtImInfty_hexThetaH
  ·
    rw [hr, hcase]
    refine UpperHalfPlane.isBoundedAtImInfty_iff.mpr ⟨thetaBound, 3, fun z hz => ?_⟩
    rw [hexThetaH_slash_repOfLabel_apply k z, norm_mul]
    have him : 1 ≤ (((z : ℂ) + (k.val : ℂ)) / 3).im := by
      rw [im_add_natCast_div_three, UpperHalfPlane.coe_im, le_div_iff₀ (by norm_num)]
      linarith
    have hbound : ‖hexTheta (((z : ℂ) + (k.val : ℂ)) / 3)‖ ≤ thetaBound := by
      rw [← latticeSum_eq_hexTheta]
      exact norm_latticeSum_le_of_one_le_im him
    calc ‖(-Complex.I / ((Real.sqrt 3 : ℝ) : ℂ))‖ * ‖hexTheta (((z : ℂ) + (k.val : ℂ)) / 3)‖
        ≤ 1 * thetaBound :=
          mul_le_mul norm_neg_I_div_sqrt_three_le_one hbound (norm_nonneg _) zero_le_one
      _ = thetaBound := one_mul _

/--
@isnad1 id=isbounde.1h1v.s7.309c9ffa7898 from=translated src=- shape=458b6360 vocab=3df4c3cf
-/
theorem hexThetaH_isBoundedAt_cusp (c : OnePoint ℝ)
    (hc : IsCusp c ((Gamma1 3 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    c.IsBoundedAt hexThetaH 1 := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  refine (OnePoint.isBoundedAt_iff rfl).mpr ?_
  exact isBoundedAtImInfty_hexThetaH_slash γ

end
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum

end A2Theta3
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum

open Complex Real Filter
open A2Theta3.LatticeSum
open scoped Manifold Topology

namespace A2Theta3

noncomputable section

/--
@isnad1 id=differen.0h1v.s6.dd0a05529f57 from=translated src=- shape=fe270221 vocab=b40d1820
-/
lemma differentiable_latticeTerm (v : ℤ × ℤ) :
    Differentiable ℂ fun τ : ℂ => latticeTerm τ v := by
  unfold latticeTerm
  fun_prop

def thetaBoundAt (T : ℝ) : ℝ :=
  ∑' v : ℤ × ℤ, Real.exp (-(π * T * (v.1 : ℝ) ^ 2)) * Real.exp (-(π * T * (v.2 : ℝ) ^ 2))

/--
@isnad1 id=isopen.0h1v.s4.7faedd2a5855 from=translated src=- shape=c7f34c7d vocab=1a83d814
-/
lemma isOpen_lt_im (T : ℝ) : IsOpen {z : ℂ | T < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

/--
@isnad1 id=differen.1h1v.s6.3ac9dd3ce400 from=translated src=- shape=ec63d216 vocab=0d7b489b
-/
theorem differentiableOn_latticeSum_of_lt_im {T : ℝ} (hT : 0 < T) :
    DifferentiableOn ℂ latticeSum {z : ℂ | T < z.im} := by
  have h := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (v : ℤ × ℤ) (τ : ℂ) => latticeTerm τ v)
    (summable_gaussian_prod hT)
    (fun v => (differentiable_latticeTerm v).differentiableOn)
    (isOpen_lt_im T)
    (fun v w hw => norm_latticeTerm_le_of_le_im hT (le_of_lt hw) v)
  exact h

/--
@isnad1 id=differen.1h1v.s6.41575d55b04e from=translated src=- shape=f4fff64d vocab=54686937
-/
theorem differentiableAt_latticeSum {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ latticeSum τ := by
  have hT : (0 : ℝ) < τ.im / 2 := by positivity
  have hmem : τ ∈ {z : ℂ | τ.im / 2 < z.im} := by
    simp only [Set.mem_ofPred_eq]
    linarith
  exact (differentiableOn_latticeSum_of_lt_im hT).differentiableAt
    ((isOpen_lt_im _).mem_nhds hmem)

/--
@isnad1 id=differen.0h0v.s6.7ac7dc833008 from=translated src=- shape=71829fdc vocab=0d7b489b
-/
theorem differentiableOn_latticeSum :
    DifferentiableOn ℂ latticeSum {z : ℂ | 0 < z.im} :=
  fun _ hz => (differentiableAt_latticeSum hz).differentiableWithinAt

/--
@isnad1 id=mdiffere.0h0v.s6.b4b0b0c6d77d from=translated src=- shape=38f10366 vocab=6f73cab4
-/
theorem mdifferentiable_hexThetaH : MDiff hexThetaH := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := latticeSum) differentiableOn_latticeSum
    (fun z hz => ?_)
  simp [hexThetaH, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

end
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum

end A2Theta3
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum

open Complex Real Matrix CongruenceSubgroup Subgroup ModularForm UpperHalfPlane
open A2Theta3.LatticeSum
open scoped MatrixGroups ModularForm Manifold

namespace A2Theta3

noncomputable section

def thetaForm : ModularForm (Gamma1 3) 1 :=
  { slashInvariantForm_of_T_U hexThetaH hexThetaH_slash_T hexThetaH_slash_U with
    holo' := mdifferentiable_hexThetaH
    bdd_at_cusps' := fun {c} hc => hexThetaH_isBoundedAt_cusp c hc }

/--
@isnad1 id=eq.0h0v.s8.cc4594e7e4a4 from=translated src=- shape=c661b139 vocab=e8ec3f81
-/
@[scoped simp] theorem coe_thetaForm : (⇑thetaForm : ℍ → ℂ) = hexThetaH := rfl

/--
@isnad1 id=mem.0h0v.s7.16d664052a8d from=translated src=- shape=22184087 vocab=1bbc2817
-/
theorem one_mem_strictPeriods_Gamma1_three :
    (1 : ℝ) ∈ ((Gamma1 3 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

/--
@isnad1 id=eq.0h1v.s8.07c9fe4d436e from=translated src=- shape=df9a20ba vocab=01e9b5b6
-/
theorem qExpansion_coeff_thetaForm (n : ℕ) :
    (qExpansion 1 (⇑thetaForm : ℍ → ℂ)).coeff n = (repCount n : ℂ) := by
  symm
  refine ModularFormClass.qExpansion_coeff_unique (c := fun n => (repCount n : ℂ)) one_pos
    one_mem_strictPeriods_Gamma1_three (f := thetaForm) (fun τ => ?_) n
  have hτ : 0 < (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact τ.im_pos
  have h := hasSum_repCount_qpow hτ
  rw [coe_thetaForm, hexThetaH_apply]
  convert h using 1
  funext m
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/--
@isnad1 id=eq.1h1v.s10.d3a988b68ee4 from=translated src=- shape=c33c9286 vocab=e24d68ab
-/
theorem thetaForm_slash_fricke (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; 3, 0]) :
    (⇑thetaForm : ℍ → ℂ) ∣[(1 : ℤ)] W = (-Complex.I / (Real.sqrt 3 : ℂ)) • (⇑thetaForm : ℍ → ℂ) := by
  funext τ
  have hdet : (W.det : ℝ) = 3 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hW, Matrix.det_fin_two_of]; norm_num
  have hdetpos : 0 < (W.det : ℝ) := by rw [hdet]; norm_num
  have hτ : 0 < (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact τ.im_pos
  have hτ0 : (τ : ℂ) ≠ 0 := ne_zero_of_im_pos hτ
  rw [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul]
  have hσ : σ W = ContinuousAlgEquiv.refl ℝ ℂ := by rw [σ, ite_eq_left hdetpos]
  have hsm : ((W • τ : ℍ) : ℂ) = -1 / (3 * (τ : ℂ)) := by
    rw [coe_smul_of_det_pos hdetpos]
    simp [num, denom, hW]
  have hden : denom W τ = 3 * (τ : ℂ) := by simp [denom, hW]
  rw [hσ, ContinuousAlgEquiv.refl_apply, hdet, coe_thetaForm, hexThetaH_eq_hexTheta, hexThetaH_eq_hexTheta, hsm,
    hexTheta_fricke hτ, hden]
  have hs0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := sqrt_three_ne_zero
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; rfl
  rw [sub_self, zpow_zero, mul_one, _root_.zpow_neg, zpow_one]
  field_simp
  linear_combination (-hexTheta (τ : ℂ)) * hs3

end
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum

end A2Theta3
open scoped _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3 _root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.A2Theta3.LatticeSum

open scoped MatrixGroups ModularForm in
/--
@isnad1 id=ex.0h0v.s11.e982a577a2cb from=translated src=- shape=17c478a2 vocab=e7e8a4bb
-/
theorem solution :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma1 3 : Subgroup (GL (Fin 2) ℝ)) 1,
      (∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 g).coeff n = (r : ℂ)) ∧
      (UpperHalfPlane.qExpansion 1 g).coeff 0 = 1 ∧
      ∀ W : GL (Fin 2) ℝ, (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; 3, 0] →
        (⇑g : UpperHalfPlane → ℂ) ∣[(1 : ℤ)] W =
          (-Complex.I / (Real.sqrt 3 : ℂ)) • (⇑g : UpperHalfPlane → ℂ) := by
  refine ⟨A2Theta3.thetaForm, fun n => ⟨(A2Theta3.LatticeSum.repCount n : ℚ), ?_⟩, ?_,
    fun W hW => A2Theta3.thetaForm_slash_fricke W hW⟩
  · rw [A2Theta3.qExpansion_coeff_thetaForm]; push_cast; rfl
  · rw [A2Theta3.qExpansion_coeff_thetaForm, A2Theta3.LatticeSum.repCount_zero]; push_cast; rfl
