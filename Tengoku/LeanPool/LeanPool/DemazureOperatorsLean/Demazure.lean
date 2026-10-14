/-
Copyright (c) 2026 Óscar Álvarez Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Óscar Álvarez Sánchez
-/
module

public import Tengoku

/-!
# LeanPool.DemazureOperatorsLean.Demazure
-/

@[expose] public section

noncomputable section
open MvPolynomial

namespace Demazure

variable {n : ℕ} (n_pos : n > 0) (n_gt_1 : n > 1)

/- In this file we define the Demazure operator directly as a function
  in the ring of multivariate polynomials -/

/- Prerequisites  -/

/-- The polynomial obtained by swapping the variables indexed by `i` and `j`. -/
def SwapVariablesFun (i j : Fin n) (p : MvPolynomial (Fin n) ℂ) : (MvPolynomial (Fin n) ℂ) :=
  (renameEquiv ℂ (Equiv.swap i j)) p

/--
@isnad1 id=eq.0h3v.s6.2ff578f4fcba from=translated src=- shape=0c5202f7 vocab=29193ece
-/
@[simp]
lemma swap_variables_map_zero (i j : Fin n) : SwapVariablesFun i j 0 = 0 := by
  rw[SwapVariablesFun]
  have : (0 : MvPolynomial (Fin n) ℂ) = C 0 := by
    refine C_0.symm
  rw[this]
  exact rename_C (Equiv.swap i j) 0

/--
@isnad1 id=eq.0h3v.s6.a088aa9b10b5 from=translated src=- shape=0c5202f7 vocab=29193ece
-/
@[simp]
lemma swap_variables_map_one {i j : Fin n} : SwapVariablesFun i j 1 = 1 := by
  simp[SwapVariablesFun]

/--
@isnad1 id=eq.0h5v.s7.eb4dcd69c7cc from=translated src=- shape=3ca08dc4 vocab=beadca11
-/
@[simp]
lemma swap_variables_add {i j : Fin n} : ∀p q :
    MvPolynomial (Fin n) ℂ,
    SwapVariablesFun i j (p + q) = SwapVariablesFun i j p + SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

/--
@isnad1 id=eq.0h5v.s7.2aec51970f38 from=translated src=- shape=3ca08dc4 vocab=1202d032
-/
@[simp]
lemma swap_variables_sub {i j : Fin n} : ∀p q :
    MvPolynomial (Fin n) ℂ,
    SwapVariablesFun i j (p - q) = SwapVariablesFun i j p - SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

/--
@isnad1 id=eq.0h5v.s6.02c6775af623 from=translated src=- shape=3ca08dc4 vocab=dc86614f
-/
@[simp]
lemma swap_variables_mul {i j : Fin n} : ∀p q :
    MvPolynomial (Fin n) ℂ,
    SwapVariablesFun i j (p * q) = SwapVariablesFun i j p * SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

/--
@isnad1 id=eq.0h5v.s6.02c6775af623 from=translated src=- shape=3ca08dc4 vocab=dc86614f
-/
lemma swap_variables_mul' (i j : Fin n) : ∀p q :
    MvPolynomial (Fin n) ℂ,
    SwapVariablesFun i j (p * q) = SwapVariablesFun i j p * SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

/--
@isnad1 id=eq.0h5v.s6.02c6775af623 from=translated src=- shape=3ca08dc4 vocab=dc86614f
-/
lemma swap_variables_mul'' {i j : Fin n} {p q : MvPolynomial (Fin n) ℂ} :
 SwapVariablesFun i j (p * q) = SwapVariablesFun i j p * SwapVariablesFun i j q := by
  simp[SwapVariablesFun]

/--
@isnad1 id=eq.0h5v.s7.eb4dcd69c7cc from=translated src=- shape=3ca08dc4 vocab=beadca11
-/
lemma swap_variables_add'' {i j : Fin n} {p q : MvPolynomial (Fin n) ℂ} :
 SwapVariablesFun i j (p + q) = SwapVariablesFun i j p + SwapVariablesFun i j q := by
  simp[SwapVariablesFun]

/--
@isnad1 id=eq.0h4v.s7.3756009855d8 from=translated src=- shape=b636e10c vocab=0f9873e8
-/
@[simp]
lemma swap_variables_commutes {i j : Fin n} : ∀r : ℂ, SwapVariablesFun i j (C r) = C r := by
  intro r
  simp[SwapVariablesFun]

/--
@isnad1 id=eq.0h4v.s4.6d1def70585a from=translated src=- shape=0cb906ec vocab=b5b552ac
-/
@[simp]
lemma swap_variables_order_two {i j : Fin n} {p : MvPolynomial (Fin n) ℂ} :
  SwapVariablesFun i j (SwapVariablesFun i j p) = p := by
  rw [SwapVariablesFun, SwapVariablesFun, renameEquiv_apply, renameEquiv_apply, rename_rename]
  convert rename_id_apply (R := ℂ) p
  funext k
  simp

/-- The algebra equivalence swapping the variables indexed by `i` and `j`. -/
def SwapVariables (i : Fin n) (j : Fin n) :
    AlgEquiv ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) :=
  renameEquiv ℂ (Equiv.swap i j)

/--
@isnad1 id=eq.0h4v.s7.e6ddfe704e86 from=translated src=- shape=e931536f vocab=25807898
-/
@[simp]
lemma swap_variables_apply (i j : Fin n) (p : MvPolynomial (Fin n) ℂ) :
    SwapVariables i j p = SwapVariablesFun i j p := rfl

/-- The polynomial equation of the unit circle in two variables. -/
def circleEquation : MvPolynomial (Fin 2) ℂ := X 0 ^ 2 + X 1 ^ 2 - C 1

/- some more properties of swap_variables and others -/

/--
@isnad1 id=ne.1h4v.s9.98fa1b474930 from=translated src=- shape=146f1f10 vocab=9edd8ad3
-/
lemma swap_variables_ne_zero (i j : Fin (n + 1)) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ, p ≠ 0 → SwapVariables i j p ≠ 0 := by
  intro p hp h
  apply hp
  rw[← map_zero (SwapVariables i j)] at h
  apply AlgEquiv.injective (SwapVariables i j)
  exact h

/--
@isnad1 id=eq.0h3v.s6.f7373f92c477 from=translated src=- shape=c8007fb2 vocab=03587218
-/
@[simp]
lemma swap_variables_first {i j : Fin (n + 1)} : SwapVariablesFun i j (X i) = X j := by
  simp [SwapVariablesFun]

/--
@isnad1 id=eq.0h4v.s6.83f254fe2e86 from=translated src=- shape=12bf7bef vocab=9e254c59
-/
lemma swap_variables_symmetrical {i j : Fin (n + 1)} {p : MvPolynomial (Fin (n + 1)) ℂ} :
  SwapVariablesFun i j p = SwapVariablesFun j i p := by
  simp [SwapVariablesFun, Equiv.swap_comm]

/--
@isnad1 id=eq.0h3v.s6.2d248ebd2a43 from=translated src=- shape=922832b6 vocab=03587218
-/
@[simp]
lemma swap_variables_second {i j : Fin (n + 1)} : SwapVariablesFun i j (X j) = X i := by
  simp [SwapVariablesFun]

/--
@isnad1 id=eq.2h4v.s7.60256aff5ca8 from=translated src=- shape=ebc4f32f vocab=03587218
-/
@[simp]
lemma swap_variables_none {i j k : Fin (n + 1)} (h1 : k ≠ i) (h2 : k ≠ j) :
SwapVariablesFun i j (X k) = X k := by
  simp [SwapVariablesFun, h1, h2, Equiv.swap_apply_of_ne_of_ne]

/--
@isnad1 id=eq.2h4v.s7.60256aff5ca8 from=translated src=- shape=ebc4f32f vocab=03587218
-/
lemma swap_variables_none' {i j k : Fin (n + 1)} {h1 : k ≠ i} {h2 : k ≠ j} :
SwapVariablesFun i j (X k) = X k := by
  simp [SwapVariablesFun, h1, h2, Equiv.swap_apply_of_ne_of_ne]

/- Some really specific and technical lemmas-/
/--
@isnad1 id=ne.0h2v.s4.72fa7c8fa28d from=translated src=- shape=af1341c4 vocab=ba3db020
-/
lemma fin_succ_ne_fin_castSucc (i : Fin n) : Fin.succ i ≠ Fin.castSucc i := by
  apply Fin.val_ne_iff.mp
  simp [Fin.val_succ, Fin.val_castSucc]

/--
@isnad1 id=iff.2h3v.s5.e605bd586386 from=translated src=- shape=191bfb67 vocab=286518db
-/
lemma wario_number_one {n : ℕ} {a : ℕ} {h : a < n} {a' : ℕ} {h' : a' < n} :
({ val := a, isLt := h } : Fin n) ≠ { val := a', isLt := h' } ↔ a ≠ a' := by
  constructor
  · intro h_ne haa
    exact h_ne (Fin.ext haa)
  · intro haa h_eq
    exact haa (congrArg Fin.val h_eq)

/--
@isnad1 id=ne.2h2v.s6.1cf2c9beae41 from=translated src=- shape=eb32c7f6 vocab=b608ed9c
-/
lemma i_ne_i_plus_1 {i : ℕ} {h : i < n + 1} {h' : i + 1 < n + 1} :
 ({ val := i, isLt := h } : Fin (n + 1)) ≠ { val := i + 1, isLt := h' } := by
  rw [wario_number_one]
  omega

/--
@isnad1 id=ne.0h2v.s8.c5741b7fb921 from=translated src=- shape=344ae3a8 vocab=75298cea
-/
lemma demazure_denominator_not_null (i : Fin n) :
    (X (Fin.castSucc i) : MvPolynomial (Fin (n + 1)) ℂ) - X (Fin.succ i) ≠ 0 := by
  apply MvPolynomial.ne_zero_iff.mpr
  use Finsupp.single (Fin.succ i) 1
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X, MvPolynomial.coeff_X]
  have h : Finsupp.single (Fin.castSucc i) 1 ≠ Finsupp.single (Fin.succ i) 1 := by
    apply Finsupp.ne_iff.mpr
    use Fin.succ i
    simp [fin_succ_ne_fin_castSucc]
  rw [ite_eq_right h]
  simp

/- Now we can use these to define the demazure numerator. We distinguish the variable x_i
 to perform division by (x_i - x_(i+1)) later (only univariable division is supported) -/

/-- The numerator used to define the Demazure operator in one distinguished variable. -/
def DemazureNumerator (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ) :
    Polynomial (MvPolynomial (Fin n) ℂ) :=
  let i' : Fin (n + 1) := Fin.castSucc i
  let i'_plus_1 : Fin (n + 1) := Fin.succ i
  let numerator := p - SwapVariables i' i'_plus_1 p
  let numerator_X_i_at_start : MvPolynomial (Fin (n + 1)) ℂ := SwapVariables i' 0 numerator
  (finSuccEquiv ℂ n) numerator_X_i_at_start

/--
@isnad1 id=eq.0h4v.s8.481ffef91617 from=translated src=- shape=90eadf7d vocab=46335712
-/
lemma demazure_numerator_add (i : Fin n) : ∀ p q : MvPolynomial (Fin (n + 1)) ℂ,
  DemazureNumerator i (p + q) = DemazureNumerator i p + DemazureNumerator i q := by
  intro p q
  simp [DemazureNumerator, SwapVariables, map_add, sub_eq_add_neg]
  abel

/--
@isnad1 id=eq.0h4v.s9.819a31c69904 from=translated src=- shape=8eae55e8 vocab=11a9c589
-/
lemma demazure_numerator_C_mul (i : Fin n) : ∀ (p : MvPolynomial (Fin (n + 1)) ℂ) (r : ℂ),
 DemazureNumerator i (C r * p) = Polynomial.C (C r) * DemazureNumerator i p := by
  intro p r
  simp only [DemazureNumerator, SwapVariables, map_mul, renameEquiv_apply, algHom_C,
    algebraMap_eq, sub_eq_add_neg, map_add, map_neg, rename_rename]
  rw [show (MvPolynomial.finSuccEquiv ℂ n) (C r : MvPolynomial (Fin (n + 1)) ℂ) =
    Polynomial.C (C r) by simp [MvPolynomial.finSuccEquiv_apply]]
  ring

-- Now we also define the denominator taking the variable x_i as the variable to divide by
/-- The monic denominator `X - X_i` used in the Demazure division step. -/
def DemazureDenominator (i : Fin n) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  let X_i : MvPolynomial (Fin n) ℂ := MvPolynomial.X i
  let denominator_X : Polynomial (MvPolynomial (Fin n) ℂ) := (Polynomial.X - Polynomial.C X_i)
  denominator_X

/--
@isnad1 id=ne.0h2v.s6.aaf5ebb56924 from=translated src=- shape=49b05ef3 vocab=903dff05
-/
lemma demazure_denominator_ne_zero : ∀ i : Fin n, DemazureDenominator i ≠ 0 := by
  intro i
  simpa [DemazureDenominator] using Polynomial.X_sub_C_ne_zero (X i)

/--
@isnad1 id=monic.0h2v.s4.dfdb0fa148ea from=translated src=- shape=14b0ff91 vocab=bbfc2556
-/
lemma demazure_denominator_monic : ∀ i : Fin n, Polynomial.Monic (DemazureDenominator i) := by
  intro i
  simpa [DemazureDenominator] using Polynomial.monic_X_sub_C (X i)

/- the division is exact so the demazure operator is well defined
(division by polynomials returns just the quotient) -/
/--
@isnad1 id=eq.0h3v.s7.8b9457738e0f from=translated src=- shape=ace07ec0 vocab=97b552ea
-/
lemma demazure_division_exact : ∀(i : Fin n), ∀(p : MvPolynomial (Fin (n + 1)) ℂ),
  (DemazureNumerator i p).modByMonic (DemazureDenominator i) = 0 := by
    intro i p
    simp only [DemazureNumerator, SwapVariables, renameEquiv_apply, map_sub,
      rename_rename, finSuccEquiv_apply, coe_eval₂Hom, DemazureDenominator,
      Polynomial.modByMonic_X_sub_C_eq_C_eval, Polynomial.eval_sub, polynomial_eval_eval₂]
    apply sub_eq_zero.mpr
    apply congr_arg Polynomial.C
    repeat
      rw[MvPolynomial.eval₂_rename]
    apply MvPolynomial.eval₂_congr
    intro j c _ _
    simp[Equiv.swap_apply_def]
    by_cases h1 : j = Fin.castSucc i
    · simp[h1, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]
    by_cases h2 : j = Fin.succ i
    · simp[h2, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]
    by_cases h3 : j = 0
    · subst h3
      simp[h1, h2]
    simp[h1, h2, h3]

/-- The Demazure operator as a function on multivariate polynomials. -/
def DemazureFun (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ) : MvPolynomial (Fin (n + 1)) ℂ  :=
  let numerator := DemazureNumerator i p
  let denominator := DemazureDenominator i
  let division := numerator.divByMonic denominator
  let division_mv : MvPolynomial (Fin (n + 1)) ℂ := (AlgEquiv.symm (finSuccEquiv ℂ n)) division
  let i' : Fin (n + 1) := Fin.castSucc i
  SwapVariables i' 0 division_mv

/- Some auxiliary lemmas for the multivariate polynomial ring -/
/--
@isnad1 id=iff.1h4v.s8.c8b2ce7a664c from=translated src=- shape=0910f1d2 vocab=b5e2dec9
-/
lemma poly_mul_cancel {p q r : Polynomial (MvPolynomial (Fin n) ℂ)} (hr : r ≠ 0) :
    p = q ↔ (r * p) = (r * q) := by
  constructor
  · intro h
    exact congrArg (HMul.hMul r) h
  · intro h
    exact mul_left_cancel₀ hr h

/--
@isnad1 id=eq.2h4v.s7.6da3547eafdf from=translated src=- shape=f7b654fa vocab=28168880
-/
lemma poly_cancel_left {p q r : MvPolynomial (Fin n) ℂ} (hr : r ≠ 0) :
    (r * p) = (r * q) → p = q := by
  intro h
  exact mul_left_cancel₀ hr h

/--
@isnad1 id=iff.3h4v.s8.6fc901452d77 from=translated src=- shape=2745fe25 vocab=935372fd
-/
lemma poly_div_cancel {p q r : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hr : Polynomial.Monic r) (hp : p %ₘ r = 0) (hq : q %ₘ r = 0) :
    p = q ↔ (p /ₘ r) = (q /ₘ r) := by
  constructor
  · intro h
    exact congrArg (· /ₘ r) h
  · intro h
    have div_p := Polynomial.modByMonic_add_div p r
    have div_q := Polynomial.modByMonic_add_div q r
    rw [hp, zero_add] at div_p
    rw [hq, zero_add] at div_q
    rw [← div_p, ← div_q]
    exact (poly_mul_cancel (Polynomial.Monic.ne_zero hr)).mp h

/--
@isnad1 id=eq.2h3v.s8.2f9c24de49fe from=translated src=- shape=94ffbcc6 vocab=4b03de8f
-/
lemma poly_exact_div_mul_cancel {p q : Polynomial (MvPolynomial (Fin n) ℂ)}
 (_q_monic : Polynomial.Monic q) (exact_div : p %ₘ q = 0) : q * (p /ₘ q) = p := by
  have := Polynomial.modByMonic_add_div p q
  rw [exact_div, zero_add] at this
  exact this

-- since the division is exact, the quotient perfectly divides the numerator
/--
@isnad1 id=eq.0h3v.s7.a82daecbe26d from=translated src=- shape=2f4c1364 vocab=c5790102
-/
lemma demazure_division_exact' : ∀(i : Fin n), ∀(p : MvPolynomial (Fin (n + 1)) ℂ),
    DemazureDenominator i * ((DemazureNumerator i p) /ₘ (DemazureDenominator i)) =
      DemazureNumerator i p := by
  intro i p
  apply poly_exact_div_mul_cancel (demazure_denominator_monic i) (demazure_division_exact i p)

/- Now we prove that the Demazure operator is a linear map directly with the definition.
  This requires a lot of work to disentangle it -/

/--
@isnad1 id=eq.0h4v.s8.141f2c221700 from=translated src=- shape=5995a5c4 vocab=bbb52def
-/
lemma demazure_map_add (i : Fin n) : ∀p q : MvPolynomial (Fin (n + 1)) ℂ,
  DemazureFun i (p + q) = DemazureFun i p + DemazureFun i q := by
  intro p q
  simp only [DemazureFun, SwapVariables, renameEquiv_apply]
  rw[← map_add]
  apply congr_arg
  rw[← map_add (AlgEquiv.symm (MvPolynomial.finSuccEquiv ℂ n))
    (DemazureNumerator i p /ₘ DemazureDenominator i)
    (DemazureNumerator i q /ₘ DemazureDenominator i)]
  apply congr_arg
  apply (poly_mul_cancel (demazure_denominator_ne_zero i)).mpr
  simp only [mul_add]
  simp only [demazure_division_exact']
  exact demazure_numerator_add i p q

/--
@isnad1 id=eq.0h4v.s8.661008442f0d from=translated src=- shape=a8a08777 vocab=5a786abf
-/
lemma demazure_map_smul (i : Fin n) : ∀ (r : ℂ) (p : MvPolynomial (Fin (n + 1)) ℂ),
  DemazureFun i (r • p) = r • DemazureFun i p := by
  intro r p
  simp only [DemazureFun, SwapVariables, smul_eq_C_mul, renameEquiv_apply]
  nth_rewrite 2 [← rename_C (Equiv.swap (Fin.castSucc i) 0) r]
  rw[← map_mul]
  apply congr_arg
  nth_rewrite 2 [← MvPolynomial.finSuccEquiv_comp_C_eq_C]
  simp only [RingHom.comp, Nat.succ_eq_add_one, RingHom.coe_coe, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw[← map_mul (AlgEquiv.symm (MvPolynomial.finSuccEquiv ℂ n))]
  apply congr_arg
  apply (poly_mul_cancel (demazure_denominator_ne_zero i)).mpr
  rw[← mul_assoc]
  rw [mul_comm (DemazureDenominator i) (Polynomial.C (C r))]
  simp only [demazure_division_exact']
  rw[mul_assoc]
  rw[demazure_division_exact' i p]
  exact demazure_numerator_C_mul i p r

/-- The Demazure operator as a complex-linear map. -/
def DemazureLinear (i : Fin n) :
    LinearMap (RingHom.id ℂ) (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (n + 1)) ℂ) where
  toFun := DemazureFun i
  map_add' := demazure_map_add i
  map_smul' := demazure_map_smul i

/--
@isnad1 id=eq.1h2v.s7.f2611754c2dc from=translated src=- shape=c80e9de6 vocab=a2e3a261
-/
lemma one_of_div_by_monic_self : ∀ (p : Polynomial (MvPolynomial (Fin n) ℂ))
    (_h : Polynomial.Monic p), p /ₘ p = 1 := by
  intro p hp
  have hmod : p %ₘ p = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hp).mpr (dvd_refl p)
  have h := Polynomial.modByMonic_add_div p p
  rw [hmod, zero_add] at h
  exact mul_left_cancel₀ hp.ne_zero (by simpa using h)

-- Example showing that the demazure operator doesn't respect the multiplication
/--
@isnad1 id=ex.0h2v.s10.df4939581451 from=translated src=- shape=281396a2 vocab=dea42618
-/
lemma demazure_not_multiplicative : ∀ (i : Fin n), ∃(p q : MvPolynomial (Fin (n+1)) ℂ),
  DemazureLinear i (p * q) ≠ DemazureLinear i p * DemazureLinear i q := by
  intro i
  use (X (Fin.castSucc i))
  use C 1
  simp only [DemazureLinear, mul_one, LinearMap.coe_mk, AddHom.coe_mk, DemazureFun,
    SwapVariables, DemazureNumerator, renameEquiv_apply, rename_X, Equiv.swap_apply_left,
    map_sub, Equiv.swap_apply_def, fin_succ_ne_fin_castSucc, ↓reduceIte, Fin.succ_ne_zero,
    DemazureDenominator, map_one, sub_self, map_zero,
    Polynomial.zero_divByMonic, mul_zero, ne_eq]
  rw [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
  rw[one_of_div_by_monic_self]
  · simp
  · exact Polynomial.monic_X_sub_C (X i)

/- Doing anything with the definition, even simple things, requires a lot of work given
the complexity of the definition. That's why in DemazureAux.lean we introduce an alternative
definition that will be the one we actually use for computations -/

end Demazure

end
