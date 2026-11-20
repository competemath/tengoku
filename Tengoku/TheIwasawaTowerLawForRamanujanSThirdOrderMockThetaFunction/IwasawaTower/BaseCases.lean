import Tengoku.TheIwasawaTowerLawForRamanujanSThirdOrderMockThetaFunction.IwasawaTower.Series

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kernel-checked characteristic-three base cases

Author: Joesph D. Burke III.
-/

noncomputable section

open scoped BigOperators

namespace IwasawaTower.Series

open Finset PowerSeries

namespace FinitePolynomial

abbrev P := Polynomial 𝔽₃

local instance : CharP P 3 := charP_of_injective_algebraMap' 𝔽₃ 3

private theorem cast_mod_three (k : ℕ) :
    ((k : ℕ) : P) = Polynomial.C ((k % 3 : ℕ) : 𝔽₃) := by
  rw [CharP.cast_eq_mod (R := P) 3]
  rfl

private theorem C_two_eq_neg_one : Polynomial.C (2 : 𝔽₃) = (-1 : P) := by
  simpa using congrArg (Polynomial.C : 𝔽₃ →+* P) (show (2 : 𝔽₃) = -1 by decide)

def y : P := Polynomial.X

def x : P := 1 - y

def a (r : ℕ) : P :=
  ∏ j ∈ Finset.range r, (1 + x ^ (j + 1))

def aExcept (r j : ℕ) : P :=
  ∏ l ∈ Finset.range r, if l = j then 1 else (1 + x ^ (l + 1))

def w (N : ℕ) : P :=
  ∑ r ∈ Finset.range N,
    (x ^ (r + 1) * a r ^ 2 -
      ∑ j ∈ Finset.range r,
        x ^ (r + 1) * x ^ (j + 1) * (1 + x ^ (j + 1)) * aExcept r j ^ 2)

/--
@isnad1 id=eq.0h3v.s6.d9055a5d3432 from=translated src=- shape=452036d1 vocab=53808064
-/
@[simp] theorem coe_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → P) :
    ((∑ i ∈ s, f i : P) : PS) = ∑ i ∈ s, ((f i : P) : PS) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, Polynomial.coe_add]

/--
@isnad1 id=eq.0h3v.s6.4180b7e9d99a from=translated src=- shape=452036d1 vocab=8a09b83e
-/
@[simp] theorem coe_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → P) :
    ((∏ i ∈ s, f i : P) : PS) = ∏ i ∈ s, ((f i : P) : PS) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, Polynomial.coe_mul]

private theorem prod_ite_one_eq_prod_erase {ι M : Type*} [DecidableEq ι]
    [CommMonoid M] (s : Finset ι) (j : ι) (f : ι → M) :
    (∏ l ∈ s, if l = j then 1 else f l) = ∏ l ∈ s.erase j, f l := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      by_cases hij : i = j
      · subst i
        rw [Finset.prod_insert hi, ite_eq_left rfl, one_mul, ih,
          Finset.erase_insert hi, Finset.erase_eq_of_notMem hi]
      · rw [Finset.prod_insert hi, ite_eq_right hij, ih,
          Finset.erase_insert_of_ne hij, Finset.prod_insert (by simp [hi])]

/--
@isnad1 id=eq.0h0v.s4.1db35063a90c from=translated src=- shape=93ea8593 vocab=d0bf3908
-/
@[simp] theorem coe_y : ((y : P) : PS) = Y := by
  simp [y, Y]

/--
@isnad1 id=eq.0h0v.s4.34233acb082a from=translated src=- shape=93ea8593 vocab=d3910b0e
-/
@[simp] theorem coe_x : ((x : P) : PS) = X := by
  simp [x, X]

/--
@isnad1 id=eq.0h1v.s4.a9365e91b8fa from=translated src=- shape=d709d7a6 vocab=7340aeac
-/
@[simp] theorem coe_a (r : ℕ) : ((a r : P) : PS) = A r := by
  simp [a, A]

/--
@isnad1 id=eq.0h2v.s4.d409efc06abb from=translated src=- shape=88033774 vocab=73db6129
-/
@[simp] theorem coe_aExcept (r j : ℕ) : ((aExcept r j : P) : PS) = AExcept r j := by
  simp [aExcept, AExcept, prod_ite_one_eq_prod_erase]

/--
@isnad1 id=eq.0h1v.s4.41f8368e31c1 from=translated src=- shape=d709d7a6 vocab=e4695b21
-/
theorem coe_w (N : ℕ) : ((w N : P) : PS) = WPolynomial N := by
  simp [w, WPolynomial]

private theorem w_three_exact :
    w 3 = y ^ 2 + y ^ 5 + y ^ 6 - y ^ 8 + y ^ 9 := by
  norm_num [w, a, aExcept, x, y, Finset.sum_range_succ, Finset.prod_range_succ]
  ring_nf
  simp only [← Nat.cast_ofNat (R := P), cast_mod_three]
  norm_num
  rw [C_two_eq_neg_one]
  ring

/-- The quotient after removing the leading `y^5` and a factor `y^6` from
`w 9`.  Its explicit form is a certificate, not an assumption.-/
private def qNine : P :=
  1 + y + y ^ 2 + y ^ 4 + y ^ 5 + 2 * y ^ 6 + 2 * y ^ 7 + 2 * y ^ 8 +
  2 * y ^ 10 + 2 * y ^ 11 + y ^ 12 + y ^ 14 + 2 * y ^ 15 + 2 * y ^ 16 +
  2 * y ^ 18 + y ^ 19 + y ^ 20 + y ^ 22 + y ^ 25 + y ^ 26 + 2 * y ^ 27 +
  y ^ 29 + 2 * y ^ 30 + y ^ 31 + y ^ 32 + 2 * y ^ 34 + y ^ 35 + y ^ 36 +
  y ^ 37 + 2 * y ^ 38 + 2 * y ^ 40 + 2 * y ^ 41 + y ^ 42 + y ^ 44 +
  y ^ 45 + y ^ 46 + y ^ 48 + y ^ 49 + y ^ 51 + 2 * y ^ 52 + 2 * y ^ 53 +
  y ^ 54 + 2 * y ^ 55 + 2 * y ^ 56 + y ^ 58 + y ^ 59 + y ^ 60 + y ^ 62 +
  2 * y ^ 67 + y ^ 70 + 2 * y ^ 71 + 2 * y ^ 74 + y ^ 75

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
private theorem w_nine_exact : w 9 = y ^ 5 + y ^ 6 * qNine := by
  norm_num [w, a, aExcept, x, y, qNine, Finset.sum_range_succ,
    Finset.prod_range_succ]
  ring_nf
  simp only [← Nat.cast_ofNat (R := P), cast_mod_three]
  norm_num
  rw [C_two_eq_neg_one]
  ring

end FinitePolynomial

/--
@isnad1 id=mody.1h3v.s8.b69b67825b2f from=translated src=- shape=b5f267ae vocab=2a0db324
-/
theorem modY_of_coe_trunc_eq {n : ℕ} {f g : PS}
    (h : (PowerSeries.trunc n f : PS) = g) : ModY n f g := by
  refine ⟨PowerSeries.mk (fun i ↦ PowerSeries.coeff (i + n) f), ?_⟩
  rw [sub_eq_iff_eq_add, ← h]
  simpa [Y] using PowerSeries.eq_X_pow_mul_shift_add_trunc n f

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem trunc_W_three :
    (PowerSeries.trunc 3 (W 3) : PS) = Y ^ 2 := by
  rw [W_eq_WPolynomial, ← FinitePolynomial.coe_w, FinitePolynomial.w_three_exact]
  ext i
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hi : i < 3
  · rw [ite_eq_left hi]
    interval_cases i <;>
      norm_num [FinitePolynomial.y, Y, PowerSeries.coeff_X_pow]
  · have hi2 : i ≠ 2 := by omega
    simp [hi, hi2, FinitePolynomial.y, Y, PowerSeries.coeff_X_pow]

/-- The exceptional base level has exact order two and leading coefficient one.
@isnad1 id=hasleadi.0h0v.s5.01752748622e from=translated src=- shape=fa5f2107 vocab=1d43aa1e
-/
theorem W_three_hasLeading : HasLeading 2 1 (W 3) := by
  simpa [HasLeading, one_mul] using modY_of_coe_trunc_eq trunc_W_three

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
private theorem trunc_W_nine :
    (PowerSeries.trunc 6 (W 9) : PS) = Y ^ 5 := by
  rw [W_eq_WPolynomial, ← FinitePolynomial.coe_w, FinitePolynomial.w_nine_exact]
  ext i
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hi : i < 6
  · simp only [ite_eq_left hi, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X,
      Polynomial.coe_mul, FinitePolynomial.y, Y]
    rw [map_add, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul']
    have hn : ¬6 ≤ i := by omega
    simp [hn]
  · have hi5 : i ≠ 5 := by omega
    simp [hi, hi5, FinitePolynomial.y, Y, PowerSeries.coeff_X_pow]

/-- The first nonexceptional strong base has order five and coefficient one.
@isnad1 id=hasleadi.0h0v.s5.b397dfe738b4 from=translated src=- shape=fa5f2107 vocab=1d43aa1e
-/
theorem W_nine_hasLeading : HasLeading 5 1 (W 9) := by
  simpa [HasLeading, one_mul] using modY_of_coe_trunc_eq trunc_W_nine

end IwasawaTower.Series
