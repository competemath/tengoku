/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.CircleChordBounds
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.Basic
import Tengoku.Seed.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pointwise comparison of the literal cardinal functions

An evaluation point separated from every node controls an evaluation point close
to some other node in each cardinal product. One selected numerator factor uses
the small distance bound; the other factors use the unit-circle diameter. The
denominators belong to the same injective family throughout. No numerator is
required to be nonzero. These are pointwise estimates, not a boundary coercivity
theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

def cardinalNormNumerator (z : Fin n → ℂ) (k : Fin n) (w : ℂ) : ℝ :=
  ∏ l ∈ Finset.univ.erase k, ‖w - z l‖

def cardinalNormDenominator (z : Fin n → ℂ) (k : Fin n) : ℝ :=
  ∏ l ∈ Finset.univ.erase k, ‖z k - z l‖

/--
@isnad1 id=eq.0h4v.s5.3ead56b1a1e4 from=translated src=- shape=2f2b0a2f vocab=d6d8d6b5
-/
lemma norm_cardinal_eq_numerator_div_denominator (z : Fin n → ℂ) (k : Fin n)
    (w : ℂ) :
    ‖cardinal z k w‖ = cardinalNormNumerator z k w / cardinalNormDenominator z k := by
  unfold cardinal cardinalNormNumerator cardinalNormDenominator
  rw [norm_prod]
  simp_rw [norm_div]
  rw [Finset.prod_div_distrib]

/--
@isnad1 id=lt.1h3v.s4.6b786be80849 from=translated src=- shape=0608b4f6 vocab=1a00360c
-/
lemma cardinalNormDenominator_pos (z : Fin n → ℂ) (hinj : Function.Injective z)
    (k : Fin n) : 0 < cardinalNormDenominator z k := by
  apply Finset.prod_pos
  intro l hl
  exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun heq =>
    (Finset.mem_erase.mp hl).1 (hinj heq).symm))

/--
@isnad1 id=le.2h5v.s8.10a6889a6741 from=translated src=- shape=9ad6c2ee vocab=ffb7d42c
-/
lemma circle_cardinal_numerator_lower (z : Fin n → Circle) (k : Fin n) (y : Circle)
    (c : ℝ) (hc : 0 ≤ c) (hsep : ∀ l, c ≤ ‖(y : ℂ) - (z l : ℂ)‖) :
    c ^ (n - 1) ≤ cardinalNormNumerator (fun l => (z l : ℂ)) k (y : ℂ) := by
  have hprod : (∏ _l ∈ Finset.univ.erase k, c) ≤
      ∏ l ∈ Finset.univ.erase k, ‖(y : ℂ) - (z l : ℂ)‖ :=
    Finset.prod_le_prod (fun _ _ => hc) (fun l _ => hsep l)
  simpa only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k),
    Finset.card_univ, Fintype.card_fin, cardinalNormNumerator] using hprod

/-- A selected near node can be removed from the finite product even if its distance is zero.
@isnad1 id=le.3h6v.s8.2b5b08969f99 from=translated src=- shape=aa1e95cb vocab=e5d2de27
-/
lemma circle_cardinal_numerator_upper_of_near_node (z : Fin n → Circle)
    (k l : Fin n) (hkl : l ≠ k) (x : Circle) (b : ℝ) (hb : 0 ≤ b)
    (hnear : ‖(x : ℂ) - (z l : ℂ)‖ ≤ b) :
    cardinalNormNumerator (fun i => (z i : ℂ)) k (x : ℂ) ≤ b * 2 ^ (n - 2) := by
  let s : Finset (Fin n) := Finset.univ.erase k
  have hl : l ∈ s := Finset.mem_erase.mpr ⟨hkl, Finset.mem_univ l⟩
  have hrest : (∏ i ∈ s.erase l, ‖(x : ℂ) - (z i : ℂ)‖) ≤
      (2 : ℝ) ^ (n - 2) := by
    have hprod := Finset.prod_le_prod
      (fun i (_ : i ∈ s.erase l) => norm_nonneg ((x : ℂ) - (z i : ℂ)))
      (fun i (_ : i ∈ s.erase l) => norm_circle_sub_le_two x (z i))
    have hcard : (s.erase l).card = n - 2 := by
      rw [Finset.card_erase_of_mem hl]
      simp only [s, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
        Fintype.card_fin]
      omega
    simpa only [Finset.prod_const, hcard] using hprod
  have hrest0 : 0 ≤ ∏ i ∈ s.erase l, ‖(x : ℂ) - (z i : ℂ)‖ :=
    Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  change (∏ i ∈ s, ‖(x : ℂ) - (z i : ℂ)‖) ≤ _
  rw [← Finset.mul_prod_erase s (fun i => ‖(x : ℂ) - (z i : ℂ)‖) hl]
  exact mul_le_mul hnear hrest hrest0 hb

/-- This normalization retains the exact exponent at the two-node endpoint.
@isnad1 id=eq.1h2v.s7.d5f8cadd2b9d from=translated src=- shape=6270fce6 vocab=5ce83074
-/
lemma cardinal_comparison_factor_mul_pow (hsize : 2 ≤ n) (c : ℝ) :
    (2 * (c / 2) ^ (n - 1)) * (2 : ℝ) ^ (n - 2) = c ^ (n - 1) := by
  have hexp : n - 1 = (n - 2) + 1 := by omega
  have htwo : (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ (n - 2) * 2 := by
    rw [hexp, pow_succ]
  rw [div_pow, htwo]
  field_simp

/-- The literal cardinal comparison for one selected other node.
@isnad1 id=le.7h8v.s9.05844674fcec from=translated src=- shape=fb1eb5f8 vocab=f3e059f1
-/
lemma circle_cardinal_comparison_of_near_node (hsize : 2 ≤ n)
    (z : Fin n → Circle) (hinj : Function.Injective z) (k l : Fin n) (hkl : l ≠ k)
    (y x : Circle) (c b : ℝ) (hc : 0 < c) (hb : 0 < b)
    (hsep : ∀ i, c ≤ ‖(y : ℂ) - (z i : ℂ)‖)
    (hnear : ‖(x : ℂ) - (z l : ℂ)‖ ≤ b) :
    2 * (c / 2) ^ (n - 1) * ‖cardinal (fun i => (z i : ℂ)) k (x : ℂ)‖ ≤
      b * ‖cardinal (fun i => (z i : ℂ)) k (y : ℂ)‖ := by
  let Z : Fin n → ℂ := fun i => (z i : ℂ)
  let K : ℝ := 2 * (c / 2) ^ (n - 1)
  have hK : 0 ≤ K := mul_nonneg (by norm_num)
    (pow_nonneg (div_nonneg hc.le (by norm_num)) _)
  have hy := circle_cardinal_numerator_lower z k y c hc.le hsep
  have hx := circle_cardinal_numerator_upper_of_near_node z k l hkl x b hb.le hnear
  have hnum : K * cardinalNormNumerator Z k (x : ℂ) ≤
      b * cardinalNormNumerator Z k (y : ℂ) := by
    calc
      K * cardinalNormNumerator Z k (x : ℂ) ≤ K * (b * 2 ^ (n - 2)) :=
        mul_le_mul_of_nonneg_left hx hK
      _ = b * c ^ (n - 1) := by
        rw [show K * (b * 2 ^ (n - 2)) =
          b * (K * 2 ^ (n - 2)) by ring]
        rw [cardinal_comparison_factor_mul_pow hsize]
      _ ≤ b * cardinalNormNumerator Z k (y : ℂ) :=
        mul_le_mul_of_nonneg_left hy hb.le
  have hden : 0 < cardinalNormDenominator Z k :=
    cardinalNormDenominator_pos Z (Circle.coe_injective.comp hinj) k
  change K * ‖cardinal Z k (x : ℂ)‖ ≤ b * ‖cardinal Z k (y : ℂ)‖
  rw [norm_cardinal_eq_numerator_div_denominator, norm_cardinal_eq_numerator_div_denominator,
    ← mul_div_assoc, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hnum hden.le

/-- Each actual cardinal is controlled when some other node is close to the second point.
@isnad1 id=le.6h7v.s9.5bfc5003ec9e from=translated src=- shape=095f786e vocab=f3e059f1
-/
lemma circle_cardinal_comparison (hsize : 2 ≤ n)
    (z : Fin n → Circle) (hinj : Function.Injective z) (y x : Circle) (c b : ℝ)
    (hc : 0 < c) (hb : 0 < b) (hsep : ∀ i, c ≤ ‖(y : ℂ) - (z i : ℂ)‖)
    (hnear : ∀ k, ∃ l, l ≠ k ∧ ‖(x : ℂ) - (z l : ℂ)‖ ≤ b) :
    ∀ k, 2 * (c / 2) ^ (n - 1) * ‖cardinal (fun i => (z i : ℂ)) k (x : ℂ)‖ ≤
      b * ‖cardinal (fun i => (z i : ℂ)) k (y : ℂ)‖ := by
  intro k
  obtain ⟨l, hkl, hl⟩ := hnear k
  exact circle_cardinal_comparison_of_near_node hsize z hinj k l hkl y x c b hc hb hsep hl

/-- Summing the pointwise estimates compares the literal Lebesgue functions.
@isnad1 id=le.6h6v.s9.fb6929031e07 from=translated src=- shape=a9e75d28 vocab=1c041e6d
-/
lemma circle_lebesgue_comparison (hsize : 2 ≤ n)
    (z : Fin n → Circle) (hinj : Function.Injective z) (y x : Circle) (c b : ℝ)
    (hc : 0 < c) (hb : 0 < b) (hsep : ∀ i, c ≤ ‖(y : ℂ) - (z i : ℂ)‖)
    (hnear : ∀ k, ∃ l, l ≠ k ∧ ‖(x : ℂ) - (z l : ℂ)‖ ≤ b) :
    2 * (c / 2) ^ (n - 1) * lebesgueFunction (fun i => (z i : ℂ)) (x : ℂ) ≤
      b * lebesgueFunction (fun i => (z i : ℂ)) (y : ℂ) := by
  unfold lebesgueFunction
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ =>
    circle_cardinal_comparison hsize z hinj y x c b hc hb hsep hnear k)

/-- Evaluating at a literal node supplies a nonzero comparison value without any peak theorem.
@isnad1 id=le.7h7v.s9.4b94b77ded87 from=translated src=- shape=6f1c4a8e vocab=1c041e6d
-/
lemma circle_lebesgue_lower_of_close_pair (hsize : 2 ≤ n)
    (z : Fin n → Circle) (hinj : Function.Injective z) (k l : Fin n) (hkl : l ≠ k)
    (y : Circle) (c b : ℝ) (hc : 0 < c) (hb : 0 < b)
    (hsep : ∀ i, c ≤ ‖(y : ℂ) - (z i : ℂ)‖)
    (hnear : ‖(z k : ℂ) - (z l : ℂ)‖ ≤ b) :
    2 * (c / 2) ^ (n - 1) ≤
      b * lebesgueFunction (fun i => (z i : ℂ)) (y : ℂ) := by
  have hother : ∀ j, ∃ i, i ≠ j ∧ ‖(z k : ℂ) - (z i : ℂ)‖ ≤ b := by
    intro j
    by_cases hj : j = k
    · subst j
      exact ⟨l, hkl, hnear⟩
    · exact ⟨k, Ne.symm hj, by simpa only [sub_self, norm_zero] using hb.le⟩
  have h := circle_lebesgue_comparison hsize z hinj y (z k) c b hc hb hsep hother
  rw [lebesgueFunction_at_node (fun i => (z i : ℂ))
    (Circle.coe_injective.comp hinj) k, mul_one] at h
  exact h

/-- A separated evaluation point and a close node pair give a literal amplification estimate.
@isnad1 id=le.6h7v.s7.c7375b24a693 from=translated src=- shape=68b04052 vocab=99f6f8fa
-/
lemma amplification_lower_of_separated_point_close_pair (hsize : 2 ≤ n)
    (nodes : NodeFamily n) (k l : Fin n) (hkl : l ≠ k) (y : Circle) (c b : ℝ)
    (hc : 0 < c) (hb : 0 < b)
    (hsep : ∀ i, c ≤ ‖(y : ℂ) - nodes.coordinates i‖)
    (hnear : ‖nodes.coordinates k - nodes.coordinates l‖ ≤ b) :
    2 * (c / 2) ^ (n - 1) / b ≤ amplification nodes := by
  apply (div_le_iff₀ hb).mpr
  have h := circle_lebesgue_lower_of_close_pair hsize nodes.point nodes.injective
    k l hkl y c b hc hb hsep hnear
  exact h.trans (by
    have heval := mul_le_mul_of_nonneg_left (le_amplification nodes y) hb.le
    change b * lebesgueFunction (fun i => (nodes.point i : ℂ)) (y : ℂ) ≤
      b * amplification nodes at heval
    simpa only [mul_comm] using heval)

end

end UnitCircleInterpolation
