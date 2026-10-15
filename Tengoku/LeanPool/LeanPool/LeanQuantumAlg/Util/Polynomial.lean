/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku
import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Util.Complex

/-!
# Polynomial helper lemmas (quantum-free)

Generic `ℂ[X]` lemmas used by the QSP development, factored out so they carry
no dependency on the quantum framework:

- `conjP` — coefficient-conjugate of a polynomial (the `P*` of the QSP
  literature) and its ring/eval lemmas;
- `HasParity` — the predicate "all nonzero coefficients sit in degrees of a
  fixed parity" and its closure lemmas;
- total coefficient formulas (`coeff_X_mul'`, `coeff_X_sq_mul`) and bounded
  product-coefficient lemmas;
- `Polynomial.reflect` coefficient/evaluation lemmas;
- `eq_of_circle_eval_eq` — two polynomials agreeing on the unit circle are equal.

These are upstream candidates for Mathlib; nothing here mentions `Gate`/`PureState`.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

/-! ### Coefficient-conjugate polynomials -/

/-- `conjP P` conjugates every coefficient of `P : ℂ[X]`; this is the `P*` of
the QSP literature (for real `x`, `(conjP P).eval x = conj (P.eval x)`). -/
noncomputable def conjP (P : ℂ[X]) : ℂ[X] := P.map (starRingEnd ℂ)

/--
@isnad1 id=eq.0h2v.s5.53f5a7ba13cd from=translated src=- shape=70b7541d vocab=2fa86305
-/
@[simp]
theorem conjP_coeff (P : ℂ[X]) (k : ℕ) :
    (conjP P).coeff k = starRingEnd ℂ (P.coeff k) :=
  Polynomial.coeff_map _ _

/--
@isnad1 id=eq.0h0v.s4.60c2450db709 from=translated src=- shape=e467432f vocab=e6a6bc54
-/
@[simp] theorem conjP_zero : conjP 0 = 0 := Polynomial.map_zero _

/--
@isnad1 id=eq.0h0v.s4.c20888057910 from=translated src=- shape=e467432f vocab=e6a6bc54
-/
@[simp] theorem conjP_one : conjP 1 = 1 := Polynomial.map_one _

/--
@isnad1 id=eq.0h0v.s3.38afbe23dbdb from=translated src=- shape=9b1c3ca8 vocab=0d94f11a
-/
@[simp] theorem conjP_X : conjP X = X := Polynomial.map_X _

/--
@isnad1 id=eq.0h1v.s6.c56a4ff28baa from=translated src=- shape=97dbf19d vocab=b7eb5e52
-/
@[simp]
theorem conjP_C (c : ℂ) : conjP (C c) = C (starRingEnd ℂ c) :=
  Polynomial.map_C _

/--
@isnad1 id=eq.0h2v.s5.34485ce443ca from=translated src=- shape=5de3d10d vocab=ed0d688b
-/
theorem conjP_add (P Q : ℂ[X]) : conjP (P + Q) = conjP P + conjP Q :=
  Polynomial.map_add _

/--
@isnad1 id=eq.0h2v.s5.662dd2e4fa36 from=translated src=- shape=5de3d10d vocab=e81fb49b
-/
theorem conjP_sub (P Q : ℂ[X]) : conjP (P - Q) = conjP P - conjP Q :=
  Polynomial.map_sub _

/--
@isnad1 id=eq.0h2v.s5.0325a409ba2b from=translated src=- shape=5de3d10d vocab=40ab89f1
-/
theorem conjP_mul (P Q : ℂ[X]) : conjP (P * Q) = conjP P * conjP Q :=
  Polynomial.map_mul _

/--
@isnad1 id=eq.0h2v.s6.a57ba2a19057 from=translated src=- shape=82fd8ab5 vocab=34cb8f73
-/
theorem conjP_pow (P : ℂ[X]) (n : ℕ) : conjP (P ^ n) = conjP P ^ n :=
  Polynomial.map_pow _ _

/--
@isnad1 id=eq.0h1v.s3.ef891fb15d1c from=translated src=- shape=e9e6e124 vocab=e6a6bc54
-/
@[simp]
theorem conjP_conjP (P : ℂ[X]) : conjP (conjP P) = P := by
  ext k
  simp

/-- Evaluating the coefficient-conjugate at a real point conjugates the value.
@isnad1 id=eq.0h2v.s5.cf5e598e07cf from=translated src=- shape=52e3817d vocab=ada4bf70
-/
theorem conjP_eval_ofReal (P : ℂ[X]) (x : ℝ) :
    (conjP P).eval (x : ℂ) = starRingEnd ℂ (P.eval (x : ℂ)) := by
  have h : ((x : ℂ)) = starRingEnd ℂ (x : ℂ) := (Complex.conj_ofReal x).symm
  rw [conjP, Polynomial.eval_map]
  conv_lhs => rw [h]
  rw [Polynomial.eval₂_hom]

/-! ### Parity of polynomials

`HasParity P p` says every nonzero coefficient of `P` sits in a degree
congruent to `p` modulo `2` ("`P` has parity `p mod 2`" in
[Lin22, hermfunc.tex:1132]). The zero polynomial has every parity. -/

/-- All nonzero coefficients of `P` are in degrees `≡ p (mod 2)`. -/
def HasParity (P : ℂ[X]) (p : ℕ) : Prop :=
  ∀ k, P.coeff k ≠ 0 → k % 2 = p % 2

/--
@isnad1 id=eq.2h3v.s5.93410511416e from=translated src=- shape=fdddd2a1 vocab=91c257c3
-/
theorem HasParity.coeff_eq_zero {P : ℂ[X]} {p : ℕ} (h : HasParity P p) {k : ℕ}
    (hk : k % 2 ≠ p % 2) : P.coeff k = 0 :=
  by_contra fun hne => hk (h k hne)

/--
@isnad1 id=hasparit.0h1v.s4.d527483bc083 from=translated src=- shape=97ba0dd3 vocab=0fd297cf
-/
theorem hasParity_zero (p : ℕ) : HasParity 0 p := fun k hk => by simp at hk

/--
@isnad1 id=hasparit.1h2v.s6.e4db60f226ab from=translated src=- shape=7a594ec0 vocab=810b5ba2
-/
theorem hasParity_C (c : ℂ) {p : ℕ} (hp : p % 2 = 0) : HasParity (C c) p := by
  intro k hk
  rw [Polynomial.coeff_C] at hk
  simp_all

/--
@isnad1 id=hasparit.2h3v.s5.117c46669c0e from=translated src=- shape=82bf8ec9 vocab=f83290cd
-/
theorem HasParity.add {P Q : ℂ[X]} {p : ℕ} (hP : HasParity P p)
    (hQ : HasParity Q p) : HasParity (P + Q) p := by
  intro k hk
  rw [Polynomial.coeff_add] at hk
  by_cases h : P.coeff k = 0
  · exact hQ k (by simpa [h] using hk)
  · exact hP k h

/--
@isnad1 id=hasparit.1h2v.s4.68d74255a09f from=translated src=- shape=bcf1421e vocab=2799769a
-/
theorem HasParity.neg {P : ℂ[X]} {p : ℕ} (hP : HasParity P p) :
    HasParity (-P) p := by
  intro k hk
  rw [Polynomial.coeff_neg, neg_ne_zero] at hk
  exact hP k hk

/--
@isnad1 id=hasparit.2h3v.s5.27ae2704ca79 from=translated src=- shape=82bf8ec9 vocab=0d4aad3b
-/
theorem HasParity.sub {P Q : ℂ[X]} {p : ℕ} (hP : HasParity P p)
    (hQ : HasParity Q p) : HasParity (P - Q) p := by
  rw [sub_eq_add_neg]
  exact hP.add hQ.neg

/--
@isnad1 id=hasparit.1h3v.s6.c68f108b27bb from=translated src=- shape=4137c727 vocab=1c63830c
-/
theorem HasParity.C_mul {P : ℂ[X]} {p : ℕ} (c : ℂ) (hP : HasParity P p) :
    HasParity (C c * P) p := by
  intro k hk
  rw [Polynomial.coeff_C_mul] at hk
  exact hP k (right_ne_zero_of_mul hk)

/-- Parity only depends on `p` modulo `2`.
@isnad1 id=hasparit.2h3v.s5.c2385ab24c1e from=translated src=- shape=d12df094 vocab=f480f1fa
-/
theorem HasParity.congr {P : ℂ[X]} {p q : ℕ} (hP : HasParity P p)
    (hpq : p % 2 = q % 2) : HasParity P q := by
  intro k hk
  rw [hP k hk, hpq]

/-- Total coefficient formula for `X * P`.
@isnad1 id=eq.0h2v.s6.1aba1ac2c473 from=translated src=- shape=a59c1bb3 vocab=0d014a4b
-/
theorem coeff_X_mul' (P : ℂ[X]) (n : ℕ) :
    (X * P).coeff n = if n = 0 then 0 else P.coeff (n - 1) := by
  cases n with
  | zero => simp [Polynomial.mul_coeff_zero]
  | succ m => simp [Polynomial.coeff_X_mul]

/-- Total coefficient formula for `X^2 * P`.
@isnad1 id=eq.0h2v.s6.eb78530210c3 from=translated src=- shape=1c526ea3 vocab=0ddbfb8b
-/
theorem coeff_X_sq_mul (P : ℂ[X]) (n : ℕ) :
    (X ^ 2 * P).coeff n = if n < 2 then 0 else P.coeff (n - 2) := by
  have h : (X ^ 2 * P : ℂ[X]) = X * (X * P) := by ring
  rw [h, coeff_X_mul' (X * P) n]
  rcases n with - | m
  · simp
  · rw [ite_eq_right (Nat.succ_ne_zero m), Nat.succ_sub_one, coeff_X_mul' P m]
    simp_all

/--
@isnad1 id=hasparit.1h2v.s5.1b8a768cf575 from=translated src=- shape=e72b28df vocab=da1768a2
-/
theorem HasParity.X_mul {P : ℂ[X]} {p : ℕ} (hP : HasParity P p) :
    HasParity (X * P) (p + 1) := by
  intro k hk
  rw [coeff_X_mul'] at hk
  by_cases hk0 : k = 0
  · simp [hk0] at hk
  · rw [ite_eq_right hk0] at hk
    have := hP _ hk
    omega

/--
@isnad1 id=hasparit.1h2v.s6.f1ae44ce28a1 from=translated src=- shape=9c34f6f4 vocab=bb8b59c0
-/
theorem HasParity.one_sub_X_sq_mul {P : ℂ[X]} {p : ℕ} (hP : HasParity P p) :
    HasParity ((1 - X ^ 2) * P) p := by
  have h : ((1 - X ^ 2) * P : ℂ[X]) = P - X ^ 2 * P := by ring
  rw [h]
  refine hP.sub ?_
  intro k hk
  rw [coeff_X_sq_mul] at hk
  by_cases hk2 : k < 2
  · simp [hk2] at hk
  · rw [ite_eq_right hk2] at hk
    have := hP _ hk
    omega

/-! ### Bounded product coefficients -/

/-! ### Reflection of coefficients -/

/--
@isnad1 id=eq.1h3v.s5.b98358b876ec from=translated src=- shape=3d629efb vocab=968ee86a
-/
theorem coeff_reflect_of_le {F : ℂ[X]} {N m : ℕ} (hm : m ≤ N) :
    (F.reflect N).coeff m = F.coeff (N - m) := by
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hm]

/--
@isnad1 id=eq.2h3v.s5.8acbe787b14a from=translated src=- shape=e6a2b189 vocab=74424c2e
-/
theorem coeff_reflect_eq_zero {F : ℂ[X]} {N m : ℕ} (hF : F.natDegree ≤ N)
    (hm : N < m) : (F.reflect N).coeff m = 0 := by
  rw [Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hm]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hF hm)

/--
@isnad1 id=eq.0h3v.s6.cf716f8944fc from=translated src=- shape=a620512d vocab=d79e5774
-/
theorem reflect_sub (F G : ℂ[X]) (N : ℕ) :
    (F - G).reflect N = F.reflect N - G.reflect N := by
  simp_all

/--
@isnad1 id=eq.0h3v.s6.d3a72074c4b5 from=translated src=- shape=a620512d vocab=c5ea1900
-/
theorem reflect_add' (F G : ℂ[X]) (N : ℕ) :
    (F + G).reflect N = F.reflect N + G.reflect N := by
  simp_all

/-- `reflect (L+1) F = X · reflect L F` for `natDegree F ≤ L`.
@isnad1 id=eq.1h2v.s5.96e5f3eb77c4 from=translated src=- shape=13e49ecf vocab=7b664e55
-/
theorem reflect_succ {F : ℂ[X]} {L : ℕ} (hF : F.natDegree ≤ L) :
    F.reflect (L + 1) = X * F.reflect L := by
  ext k
  rw [Polynomial.coeff_reflect, coeff_X_mul']
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [ite_eq_left rfl, Polynomial.revAt_le (Nat.zero_le _)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · rw [ite_eq_right (by omega)]
    rcases Nat.lt_or_ge k (L + 2) with hk2 | hk2
    · rw [Polynomial.revAt_le (by omega), Polynomial.coeff_reflect,
        Polynomial.revAt_le (by omega)]
      congr 1
      omega
    · rw [Polynomial.revAt_eq_self_of_lt (by omega), Polynomial.coeff_reflect,
        Polynomial.revAt_eq_self_of_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- `reflect (L+1) (X·F) = reflect L F` for `natDegree F ≤ L`.
@isnad1 id=eq.1h2v.s5.d40c3d5f42ed from=translated src=- shape=f7d36d77 vocab=7b664e55
-/
theorem reflect_X_mul {F : ℂ[X]} {L : ℕ} (hF : F.natDegree ≤ L) :
    (X * F).reflect (L + 1) = F.reflect L := by
  ext k
  rw [Polynomial.coeff_reflect, Polynomial.coeff_reflect]
  rcases Nat.lt_or_ge k (L + 1) with hk | hk
  · rw [Polynomial.revAt_le (by omega), Polynomial.revAt_le (by omega),
      coeff_X_mul', ite_eq_right (by omega)]
    congr 1
    omega
  · rcases Nat.lt_or_ge k (L + 2) with hk2 | hk2
    · have hkeq : k = L + 1 := by omega
      subst hkeq
      rw [Polynomial.revAt_le le_rfl, Polynomial.revAt_eq_self_of_lt (by omega),
        Nat.sub_self, coeff_X_mul', ite_eq_left rfl,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    · rw [Polynomial.revAt_eq_self_of_lt (by omega),
        Polynomial.revAt_eq_self_of_lt (by omega), coeff_X_mul',
        ite_eq_right (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- Evaluation of a reflection: `(reflect L F)(z) = z^L · F(z⁻¹)`.
@isnad1 id=eq.2h3v.s6.a79a1762f136 from=translated src=- shape=fc8225d5 vocab=ad1e6d67
-/
theorem eval_reflect {F : ℂ[X]} {L : ℕ} (hF : F.natDegree ≤ L) {z : ℂ}
    (hz : z ≠ 0) : (F.reflect L).eval z = z ^ L * F.eval z⁻¹ := by
  have h1 : (F.reflect L).natDegree ≤ L :=
    Polynomial.natDegree_le_iff_degree_le.mpr <|
      (Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm =>
        coeff_reflect_eq_zero hF (by exact_mod_cast hm)
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h1),
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hF), Finset.mul_sum,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [coeff_reflect_of_le (by omega), show L - (L + 1 - 1 - k) = k by omega,
    show z ^ L = z ^ (L + 1 - 1 - k) * z ^ k by rw [← pow_add]; congr 1; omega,
    inv_pow]
  field_simp

/--
@isnad1 id=eq.0h1v.s6.a36338aa8b42 from=translated src=- shape=c99b262d vocab=5935d279
-/
theorem reflect_zero_C (r : ℂ) : (C r).reflect 0 = C r := by
  simp_all

/-! ### Evaluation on the unit circle -/

/-- Two polynomials agreeing on the unit circle are equal (the circle is an
infinite evaluation set). -/
theorem eq_of_circle_eval_eq {F G : ℂ[X]}
    (h : ∀ x : ℝ, F.eval (Complex.exp ((x : ℂ) * Complex.I))
      = G.eval (Complex.exp ((x : ℂ) * Complex.I))) : F = G := by
  refine Polynomial.eq_of_infinite_eval_eq F G ?_
  refine ((Set.Ioo_infinite Real.pi_pos).image exp_I_injOn_Ioo).mono ?_
  simp_all

end QuantumAlg
