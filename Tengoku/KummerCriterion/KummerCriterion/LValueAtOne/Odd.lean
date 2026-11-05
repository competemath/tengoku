module

import Tengoku.KummerCriterion.KummerCriterion.LValueAtOne.Sine
public import Tengoku.Seed.NumberTheory.LSeries.DirichletContinuation
public import Tengoku.KummerCriterion.KummerCriterion.KummerCongruence.BernoulliGeneralized

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic `L(1, χ)` definitions

This file packages the canonical odd/even right-hand sides together with the
functional-equation reduction for the odd formula.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace KummerCriterion

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- right-hand side: the value predicted for `L(1, χ)` when `χ` is odd
primitive modulo `p`.-/
noncomputable def oddLValueRhs (χ : DirichletCharacter ℂ p) : ℂ :=
  ((((Real.pi : ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N := p)) / (p : ℂ)) *
    BernoulliGen χ⁻¹ 1

/-- The logarithmic sum appearing in the corrected even-character formula at
`s = 1`.-/
noncomputable def evenLValueLogSum (χ : DirichletCharacter ℂ p) : ℂ :=
  ∑ a : ZMod p, χ⁻¹ a * ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ)

/-- right-hand side: the value predicted for `L(1, χ)` when `χ` is even
primitive modulo `p`.-/
noncomputable def evenLValueRhs (χ : DirichletCharacter ℂ p) : ℂ :=
  -(gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ * evenLValueLogSum p χ

/-- Functional-equation reduction of the odd `L(1, χ)` formula to the special
value formula for `L(0, χ⁻¹)`.
@isnad1 id=eq.3h2v.s7.1c905f5f65aa from=translated src=- shape=00bcaca8 vocab=e9b12044
-/
theorem odd_LFunction_one_eq_oddLValueRhs_of_LFunction_inv_zero
    {χ : DirichletCharacter ℂ p} (hχ_prim : χ.IsPrimitive) (hχ_odd : χ.Odd)
    (hχ0 : DirichletCharacter.LFunction χ⁻¹ 0 = -BernoulliGen χ⁻¹ 1) :
    DirichletCharacter.LFunction χ 1 = oddLValueRhs p χ := by
  have hp_ne_one : p ≠ 1 := hp.out.ne_one
  have hp_ne_zero : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  have hχinv_odd : (χ⁻¹).Odd := by
    rw [DirichletCharacter.Odd] at hχ_odd ⊢
    rw [MulChar.inv_apply_eq_inv', hχ_odd]
    norm_num
  have hL1 : DirichletCharacter.LFunction χ 1 =
      ((Real.pi : ℝ) : ℂ) * DirichletCharacter.completedLFunction χ 1 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ) (s := 1)
        (Or.inl one_ne_zero), hχ_odd.gammaFactor_def]
    simp [Complex.Gammaℝ_def, Complex.Gamma_one, Complex.cpow_neg_one, mul_comm]
  have hL0 : DirichletCharacter.completedLFunction χ⁻¹ 0 =
      DirichletCharacter.LFunction χ⁻¹ 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ⁻¹) (s := 0)
        (Or.inr hp_ne_one), hχinv_odd.gammaFactor_def]
    simp
  have hfe :=
    DirichletCharacter.IsPrimitive.completedLFunction_one_sub (χ := χ) hχ_prim (0 : ℂ)
  rw [DirichletCharacter.rootNumber, ite_eq_right hχ_odd.not_even, pow_one,
    ← mul_comm_div, ← mul_comm_div, ← Complex.cpow_sub _ _ hp_ne_zero, sub_sub, add_halves,
    hL0, hχ0] at hfe
  have hfe' : DirichletCharacter.completedLFunction χ 1 =
      (p : ℂ) ^ (-1 : ℂ) * Complex.I * gaussSum χ (ZMod.stdAddChar (N := p)) *
        BernoulliGen χ⁻¹ 1 := by
    simpa using hfe
  calc
    DirichletCharacter.LFunction χ 1
        = ((Real.pi : ℝ) : ℂ) * DirichletCharacter.completedLFunction χ 1 := hL1
    _ = ((Real.pi : ℝ) : ℂ) *
          (((p : ℂ) ^ (-1 : ℂ)) * Complex.I * gaussSum χ (ZMod.stdAddChar (N := p)) *
            BernoulliGen χ⁻¹ 1) := by rw [hfe']
    _ = ((((Real.pi : ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N := p)) /
            (p : ℂ)) * BernoulliGen χ⁻¹ 1 := by
      simp [Complex.cpow_neg_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = oddLValueRhs p χ := rfl

end LValueAtOne

end KummerCriterion

/-!
# Odd-character `L(1, χ)` formulas

This file packages the odd `L(0, χ)` and `L(1, χ)` evaluations
sine-side boundary-value identities.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace KummerCriterion

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- Rewrite `L(0, χ)` for an odd character as a finite sum of the values
`sinZeta (a / p) 1`.
@isnad1 id=eq.1h2v.s7.50023efcabb7 from=translated src=- shape=d539a0e3 vocab=dc91376c
-/
theorem odd_LFunction_zero_eq_pi_inv_mul_sum_sinZeta_one
    {χ : DirichletCharacter ℂ p} (hχ_odd : χ.Odd) :
    DirichletCharacter.LFunction χ 0 =
      (((Real.pi : ℝ) : ℂ)⁻¹) *
        ∑ a : ZMod p, χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 := by
  have hs : ∀ n : ℕ, (1 : ℂ) ≠ -n := by
    intro n h
    have hre : (1 : ℝ) = -(n : ℝ) := by
      simpa using congrArg Complex.re h
    nlinarith
  have hχ_odd_fun : Function.Odd (fun a : ZMod p => χ a) :=
    fun a => DirichletCharacter.Odd.eval_neg (ψ := χ) a hχ_odd
  rw [DirichletCharacter.LFunction, ZMod.LFunction_def_odd hχ_odd_fun]
  simp only [neg_zero, Complex.cpow_zero, one_mul]
  calc
    ∑ a : ZMod p, χ a * HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle a) 0
        = ∑ a : ZMod p,
            χ a *
              ((((Real.pi : ℝ) : ℂ)⁻¹) * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              have hvalue := HurwitzZeta.hurwitzZetaOdd_one_sub
                (s := (1 : ℂ)) (a := ZMod.toAddCircle a) hs
              have hsin : Complex.sin (((Real.pi : ℝ) : ℂ) * (2⁻¹ : ℂ)) = 1 := by
                simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
                  using Complex.sin_pi_div_two
              simpa [Complex.Gamma_one, Complex.cpow_neg_one, hsin, mul_assoc, mul_left_comm,
                mul_comm, div_eq_mul_inv] using congrArg (fun z : ℂ => χ a * z) hvalue
    _ = ∑ a : ZMod p,
          (((Real.pi : ℝ) : ℂ)⁻¹) * (χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) := by
            refine Finset.sum_congr rfl fun a _ => by ring
    _ = (((Real.pi : ℝ) : ℂ)⁻¹) *
          ∑ a : ZMod p, χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 := by
            rw [Finset.mul_sum]

/-- The odd special value `L(0, χ) = -B_{1,χ}` follows from the classical
boundary-value formula `sinZeta (a / p) 1 = π (1 / 2 - a / p)`
nonzero residues `a`.
@isnad1 id=eq.3h2v.s8.b0f2ac013973 from=translated src=- shape=e0424e1c vocab=8f2184c1
-/
theorem odd_LFunction_zero_eq_neg_BernoulliGen_one_of_sinZeta_one_formula
    {χ : DirichletCharacter ℂ p} (hχ_odd : χ.Odd) (hχ_ne_one : χ ≠ 1)
    (hsin : ∀ a : ZMod p, a ≠ 0 →
      HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 =
        (((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ)))) :
    DirichletCharacter.LFunction χ 0 = -BernoulliGen χ 1 := by
  have hp_ne_one : p ≠ 1 := hp.out.ne_one
  have hp_ne_zero : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  have hχ_zero : χ 0 = 0 := χ.map_zero' hp_ne_one
  have hsum_zero : ∑ a : ZMod p, χ a = 0 := MulChar.sum_eq_zero_of_ne_one hχ_ne_one
  have hpi : (((Real.pi : ℝ) : ℂ)⁻¹) * (((Real.pi : ℝ) : ℂ)) = 1 := by
    field_simp [Real.pi_ne_zero]
  calc
    DirichletCharacter.LFunction χ 0
        = (((Real.pi : ℝ) : ℂ)⁻¹) *
            ∑ a : ZMod p, χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 :=
          odd_LFunction_zero_eq_pi_inv_mul_sum_sinZeta_one (p := p) hχ_odd
    _ = (((Real.pi : ℝ) : ℂ)⁻¹) *
          ∑ a : ZMod p,
            χ a *
              ((((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ)))) := by
            refine congrArg (fun z : ℂ => (((Real.pi : ℝ) : ℂ)⁻¹) * z) ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            rcases eq_or_ne a 0 with rfl | ha
            · simp [hχ_zero]
            · rw [hsin a ha]
    _ = ∑ a : ZMod p, χ a * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          calc
            (((Real.pi : ℝ) : ℂ)⁻¹) *
                (χ a * (((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ))))
                = ((((Real.pi : ℝ) : ℂ)⁻¹) * (((Real.pi : ℝ) : ℂ))) *
                    (χ a * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ))) := by
                      ring
            _ = χ a * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ)) := by
                  rw [hpi, one_mul]
    _ = -∑ a : ZMod p, χ a * ((a.val : ℂ) / (p : ℂ)) := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
          have hconst : ∑ a : ZMod p, χ a * (1 / 2 : ℂ) = 0 := by
            calc
              ∑ a : ZMod p, χ a * (1 / 2 : ℂ) = (1 / 2 : ℂ) * ∑ a : ZMod p, χ a := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _ => by rw [mul_comm]
              _ = 0 := by rw [hsum_zero, mul_zero]
          rw [hconst, zero_sub]
    _ = -BernoulliGen χ 1 := by
          congr 1
          rw [BernoulliGen_one_of_ne_one (R := ℂ) (N := p) (χ := χ) hχ_ne_one]
          refine Finset.sum_congr rfl fun a _ => ?_
          congr 1
          change (a.val : ℂ) / (p : ℂ) = ((((a.val : ℚ) / p : ℚ)) : ℂ)
          rw [Rat.cast_div]
          push_cast
          rfl

/-- Odd special value `L(0, χ) = -BernoulliGen χ 1`
odd nontrivial Dirichlet characters modulo `p`, packaged independently of the
endpoint layer by feeding the endpoint identity
`sinZeta_toAddCircle_one_eq_boundary` into the generic reduction lemma.
@isnad1 id=eq.2h2v.s6.44714f52bf2e from=translated src=- shape=e72a4a97 vocab=4e982d66
-/
theorem odd_LFunction_zero_eq_neg_BernoulliGen_one
    {χ : DirichletCharacter ℂ p} (hχ_odd : χ.Odd) (hχ_ne_one : χ ≠ 1) :
    DirichletCharacter.LFunction χ 0 = -BernoulliGen χ 1 :=
  odd_LFunction_zero_eq_neg_BernoulliGen_one_of_sinZeta_one_formula (p := p)
    hχ_odd hχ_ne_one
    (fun _ ha => sinZeta_toAddCircle_one_eq_boundary (p := p) ha)

/-- `L(1, χ)` for odd primitive characters
modulo `p`. Closes the full odd-side formula by applying the functional-equation
reduction `odd_LFunction_one_eq_oddLValueRhs_of_LFunction_inv_zero` to the
packaged odd special-value theorem at `χ⁻¹`.
@isnad1 id=eq.3h2v.s6.a4e2f49e36a7 from=translated src=- shape=434b3ae2 vocab=6c0217b7
-/
theorem odd_LFunction_one_eq_oddLValueRhs
    {χ : DirichletCharacter ℂ p} (hχ_prim : χ.IsPrimitive) (hχ_odd : χ.Odd)
    (hχ_ne_one : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 = oddLValueRhs p χ := by
  have hχinv_odd : (χ⁻¹).Odd := by
    rw [DirichletCharacter.Odd] at hχ_odd ⊢
    rw [MulChar.inv_apply_eq_inv', hχ_odd]
    norm_num
  have hχinv_ne_one : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ_ne_one
    calc χ = χ⁻¹⁻¹ := (inv_inv χ).symm
      _ = (1 : DirichletCharacter ℂ p)⁻¹ := by rw [h]
      _ = 1 := inv_one
  exact odd_LFunction_one_eq_oddLValueRhs_of_LFunction_inv_zero (p := p) hχ_prim hχ_odd
    (odd_LFunction_zero_eq_neg_BernoulliGen_one (p := p) hχinv_odd hχinv_ne_one)

end LValueAtOne

end KummerCriterion
