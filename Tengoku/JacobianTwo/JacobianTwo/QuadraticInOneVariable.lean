/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.Seed.Algebra.Polynomial.Derivative
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Plane Keller maps quadratic in one variable

This module studies maps

`(x, y) ↦ (a(x)y² + b(x)y + c(x), e(x)y + f(x))`.

The coefficients of its Jacobian determinant, as a polynomial in `y`, give
three one-variable differential identities.  We prove directly from those
identities that the first coordinate is a quadratic polynomial in the second,
up to an affine function of `x`.  A nonzero constant Jacobian therefore gives
an explicit inverse.
-/

noncomputable section

open scoped Polynomial

namespace JacobianTwo.QuadraticInOneVariable

open Polynomial

variable {K : Type*} [Field K]

private theorem eq_C_mul_pow_of_differential_eq [CharZero K] {p e : K[X]} {n : ℕ}
    (he : e ≠ 0) (hn : n ≠ 0)
    (h : derivative p * e = C (n : K) * p * derivative e) :
    ∃ lam : K, p = C lam * e ^ n := by
  by_cases he' : derivative e = 0
  · let eps := e.coeff 0
    let alpha := p.coeff 0
    have heC : e = C eps := by
      dsimp [eps]
      exact eq_C_of_derivative_eq_zero he'
    have he0 : eps ≠ 0 := by
      intro hzero
      apply he
      calc
        e = C eps := heC
        _ = 0 := by simp [hzero]
    have hp' : derivative p = 0 := by
      rw [heC] at h
      simpa [he0] using h
    have hpC : p = C alpha := by
      dsimp [alpha]
      exact eq_C_of_derivative_eq_zero hp'
    refine ⟨alpha / eps ^ n, ?_⟩
    rw [hpC, heC, ← C_pow, ← C_mul]
    congr 1
    field_simp
  · by_cases hp : p = 0
    · exact ⟨0, by simp [hp]⟩
    · have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
      have hlcp : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
      have hlce : e.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr he
      have natDegree_relation : ∀ {r : K[X]}, r ≠ 0 →
          derivative r * e = C (n : K) * r * derivative e →
          r.natDegree = n * e.natDegree := by
        intro r hr hrdiff
        have hdr : derivative r ≠ 0 := by
          intro hzero
          have hright : C (n : K) * r * derivative e ≠ 0 :=
            mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hnK) hr) he'
          apply hright
          simpa [hzero] using hrdiff.symm
        have hlc := congrArg leadingCoeff hrdiff
        simp only [leadingCoeff_mul, leadingCoeff_derivative, leadingCoeff_C] at hlc
        have hlcr : r.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hr
        have hdeg_cast : (r.natDegree : K) = (n : K) * (e.natDegree : K) := by
          field_simp at hlc ⊢
          exact hlc
        exact_mod_cast hdeg_cast
      have hdeg : p.natDegree = n * e.natDegree := natDegree_relation hp h
      let lam : K := p.leadingCoeff / e.leadingCoeff ^ n
      let q : K[X] := p - C lam * e ^ n
      have hpow_ne : e ^ n ≠ 0 := pow_ne_zero n he
      have hlam : lam ≠ 0 := by
        dsimp [lam]
        exact div_ne_zero hlcp (pow_ne_zero n hlce)
      have hmodel_ne : C lam * e ^ n ≠ 0 :=
        mul_ne_zero (C_ne_zero.mpr hlam) hpow_ne
      have hmodel_degree : (C lam * e ^ n).degree = p.degree := by
        rw [degree_eq_natDegree hmodel_ne, degree_eq_natDegree hp]
        simp [natDegree_mul, hlam, he, hdeg]
      have hmodel_lc : (C lam * e ^ n).leadingCoeff = p.leadingCoeff := by
        simp [lam, leadingCoeff_mul, hlce]
      have hq_degree : q.degree < p.degree := by
        dsimp [q]
        exact degree_sub_lt_left hmodel_degree.symm hp hmodel_lc.symm
      have hq_diff : derivative q * e = C (n : K) * q * derivative e := by
        dsimp [q]
        have hpow : e * e ^ (n - 1) = e ^ n := by
          rw [← pow_succ']
          congr 1
          omega
        rw [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add,
          derivative_pow]
        calc
          (derivative p - C lam * (C (n : K) * e ^ (n - 1) * derivative e)) * e =
              derivative p * e - C lam * C (n : K) *
                (e * e ^ (n - 1)) * derivative e := by ring
          _ = derivative p * e - C lam * C (n : K) * e ^ n * derivative e := by
            rw [hpow]
          _ = C (n : K) * (p - C lam * e ^ n) * derivative e := by
            rw [h]
            ring
      by_cases hq : q = 0
      · refine ⟨lam, ?_⟩
        exact sub_eq_zero.mp hq
      · have hqdeg : q.natDegree = n * e.natDegree := by
          exact natDegree_relation hq hq_diff
        have hqnat_lt : q.natDegree < p.natDegree := by
          rw [degree_eq_natDegree hp] at hq_degree
          exact (natDegree_lt_iff_degree_lt hq).mpr hq_degree
        rw [hqdeg, hdeg] at hqnat_lt
        exact (Nat.lt_irrefl _ hqnat_lt).elim

/-- A plane polynomial map whose first coordinate is quadratic in `y` and
whose second coordinate is affine in `y`.-/
def quadraticInYMap (a b c e f : K[X]) (p : K × K) : K × K :=
  (a.eval p.1 * p.2 ^ 2 + b.eval p.1 * p.2 + c.eval p.1,
    e.eval p.1 * p.2 + f.eval p.1)

/-- The normal form forced by the constant-Jacobian coefficient equations.-/
def normalFormMap (lam mu alpha beta eps : K) (f : K[X]) (p : K × K) : K × K :=
  let r := eps * p.2 + f.eval p.1
  (lam * r ^ 2 + mu * r + alpha * p.1 + beta, r)

/-- The polynomial inverse of `normalFormMap`.-/
def normalFormInverse (lam mu alpha beta eps : K) (f : K[X]) (p : K × K) : K × K :=
  let x := (p.1 - lam * p.2 ^ 2 - mu * p.2 - beta) / alpha
  (x, (p.2 - f.eval x) / eps)

/-- The triangular normal form in the complementary chart `e = 0`.-/
def zeroSlopeNormalFormMap (eta delta gamma : K) (c : K[X]) (p : K × K) : K × K :=
  (eta * p.2 + c.eval p.1, delta * p.1 + gamma)

/-- The explicit polynomial inverse in the complementary chart `e = 0`.-/
def zeroSlopeNormalFormInverse (eta delta gamma : K) (c : K[X])
    (p : K × K) : K × K :=
  let x := (p.2 - gamma) / delta
  (x, (p.1 - c.eval x) / eta)

/-- Substituting the coefficient normal form turns the original presentation
of the map into `normalFormMap`.
@isnad1 id=eq.4h11v.s10.2b36cf54e80d from=translated src=- shape=4e09a3f9 vocab=b7e42108
-/
theorem quadraticInYMap_eq_normalFormMap {a b c e f : K[X]}
    {lam mu alpha beta eps : K}
    (he : e = C eps)
    (ha : a = C lam * e ^ 2)
    (hb : b = e * (C (2 * lam) * f + C mu))
    (hc : c = C lam * f ^ 2 + C mu * f + C alpha * X + C beta) :
    quadraticInYMap a b c e f = normalFormMap lam mu alpha beta eps f := by
  funext p
  rcases p with ⟨x, y⟩
  simp only [quadraticInYMap, normalFormMap, ha, hb, hc, he, eval_add, eval_mul,
    eval_pow, eval_C, eval_X]
  apply Prod.ext <;> simp only
  ring

/-- The displayed inverse is a left inverse whenever the two triangular
slopes are nonzero.
@isnad1 id=leftinve.2h7v.s6.918f88e454b7 from=translated src=- shape=99c6ae8b vocab=ae55e2f4
-/
theorem normalFormInverse_left {lam mu alpha beta eps : K} {f : K[X]}
    (halpha : alpha ≠ 0) (heps : eps ≠ 0) :
    Function.LeftInverse (normalFormInverse lam mu alpha beta eps f)
      (normalFormMap lam mu alpha beta eps f) := by
  rintro ⟨x, y⟩
  let r := eps * y + f.eval x
  let x' := (lam * r ^ 2 + mu * r + alpha * x + beta - lam * r ^ 2 - mu * r - beta) /
    alpha
  change (x', (r - f.eval x') / eps) = (x, y)
  have hx : x' = x := by
    dsimp [x']
    field_simp
    ring
  apply Prod.ext
  · exact hx
  · simp only [hx]
    dsimp [r]
    field_simp
    ring

/-- The displayed inverse is also a right inverse.
@isnad1 id=rightinv.2h7v.s6.4017cdc70259 from=translated src=- shape=99c6ae8b vocab=d2cfc24b
-/
theorem normalFormInverse_right {lam mu alpha beta eps : K} {f : K[X]}
    (halpha : alpha ≠ 0) (heps : eps ≠ 0) :
    Function.RightInverse (normalFormInverse lam mu alpha beta eps f)
      (normalFormMap lam mu alpha beta eps f) := by
  rintro ⟨u, v⟩
  let x := (u - lam * v ^ 2 - mu * v - beta) / alpha
  let y := (v - f.eval x) / eps
  have hr : eps * y + f.eval x = v := by
    dsimp [y]
    field_simp
    ring
  change (let r := eps * y + f.eval x
    (lam * r ^ 2 + mu * r + alpha * x + beta, r)) = (u, v)
  simp only [hr]
  apply Prod.ext
  · dsimp [x]
    field_simp
    ring
  · rfl

/-- Substituting the `e = 0` coefficient normal form gives the complementary
triangular map.
@isnad1 id=eq.4h9v.s9.bd72033a4749 from=translated src=- shape=0f21685a vocab=129fb831
-/
theorem quadraticInYMap_eq_zeroSlopeNormalFormMap {a b c e f : K[X]}
    {eta delta gamma : K}
    (ha : a = 0) (hb : b = C eta) (he : e = 0)
    (hf : f = C delta * X + C gamma) :
    quadraticInYMap a b c e f = zeroSlopeNormalFormMap eta delta gamma c := by
  funext p
  rcases p with ⟨x, y⟩
  simp only [quadraticInYMap, zeroSlopeNormalFormMap, ha, hb, he, hf, eval_add,
    eval_mul, eval_C, eval_X, eval_zero, zero_mul, zero_add]

/-- The displayed complementary-chart inverse is a left inverse.
@isnad1 id=leftinve.2h5v.s6.ebb93f5ec7b6 from=translated src=- shape=efb0300c vocab=e7d07cae
-/
theorem zeroSlopeNormalFormInverse_left {eta delta gamma : K} {c : K[X]}
    (heta : eta ≠ 0) (hdelta : delta ≠ 0) :
    Function.LeftInverse (zeroSlopeNormalFormInverse eta delta gamma c)
      (zeroSlopeNormalFormMap eta delta gamma c) := by
  rintro ⟨x, y⟩
  let x' := (delta * x + gamma - gamma) / delta
  change (x', (eta * y + c.eval x - c.eval x') / eta) = (x, y)
  have hx : x' = x := by
    dsimp [x']
    field_simp
    ring
  apply Prod.ext
  · exact hx
  · simp only [hx]
    field_simp
    ring

/-- The displayed complementary-chart inverse is a right inverse.
@isnad1 id=rightinv.2h5v.s6.42bed309e4c6 from=translated src=- shape=efb0300c vocab=b0ae2704
-/
theorem zeroSlopeNormalFormInverse_right {eta delta gamma : K} {c : K[X]}
    (heta : eta ≠ 0) (hdelta : delta ≠ 0) :
    Function.RightInverse (zeroSlopeNormalFormInverse eta delta gamma c)
      (zeroSlopeNormalFormMap eta delta gamma c) := by
  rintro ⟨u, v⟩
  let x := (v - gamma) / delta
  let y := (u - c.eval x) / eta
  have hx : delta * x + gamma = v := by
    dsimp [x]
    field_simp
    ring
  change (eta * y + c.eval x, delta * x + gamma) = (u, v)
  apply Prod.ext
  · dsimp [y]
    field_simp
    ring
  · exact hx

/-- The coefficient equations for a nonzero constant Jacobian force the
quadratic-in-`y` map into a triangular normal form.  The conclusion records
all five scalar parameters explicitly; in particular `alpha * eps = k`.

The hypotheses are exactly the coefficients of `y²`, `y`, and `1` in the
Jacobian determinant, together with `k ≠ 0` and the choice of the target chart
in which `e ≠ 0`.  The complementary chart `e = 0` is handled separately in
`quadraticInY_bijective_full`.
@isnad1 id=ex.5h7v.s12.48db5792b166 from=translated src=- shape=b301397e vocab=7f34478b
-/
theorem quadraticInY_normal_form [CharZero K] {a b c e f : K[X]} {k : K}
    (hk : k ≠ 0) (he : e ≠ 0)
    (hquad : derivative a * e - C (2 : K) * a * derivative e = 0)
    (hlinear : derivative b * e - b * derivative e =
      C (2 : K) * a * derivative f)
    (hconstant : derivative c * e - b * derivative f = C k) :
    ∃ lam mu alpha beta eps : K,
      eps ≠ 0 ∧ alpha * eps = k ∧ e = C eps ∧
      a = C lam * e ^ 2 ∧
      b = e * (C (2 * lam) * f + C mu) ∧
      c = C lam * f ^ 2 + C mu * f + C alpha * X + C beta := by
  have hquad' : derivative a * e = C (2 : K) * a * derivative e :=
    sub_eq_zero.mp hquad
  obtain ⟨lam, ha⟩ :=
    eq_C_mul_pow_of_differential_eq (p := a) (e := e) (n := 2) he (by omega) hquad'
  let q : K[X] := b - C (2 : K) * C lam * e * f
  have hq_diff : derivative q * e = q * derivative e := by
    dsimp [q]
    simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add]
    rw [ha] at hlinear
    linear_combination hlinear
  obtain ⟨mu, hq⟩ :=
    eq_C_mul_pow_of_differential_eq (p := q) (e := e) (n := 1) he (by omega) (by
      simpa using hq_diff)
  have hb : b = e * (C (2 * lam) * f + C mu) := by
    dsimp [q] at hq
    simp only [pow_one] at hq
    have hC : C (2 * lam) = C (2 : K) * C lam := by rw [← C_mul]
    rw [hC]
    linear_combination hq
  let g : K[X] := c - C lam * f ^ 2 - C mu * f
  have hg_derivative_mul : derivative g * e = C k := by
    dsimp [g]
    simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_pow, Nat.reduceSubDiff, pow_one]
    rw [hb] at hconstant
    have hC : C (2 * lam) = C (2 : K) * C lam := by rw [← C_mul]
    rw [hC] at hconstant
    linear_combination hconstant
  have hg_derivative_ne : derivative g ≠ 0 := by
    intro hgzero
    have : (0 : K[X]) = C k := by simpa [hgzero] using hg_derivative_mul
    have hkC : C k ≠ 0 := C_ne_zero.mpr hk
    exact hkC this.symm
  have hdegrees : (derivative g).natDegree + e.natDegree = 0 := by
    rw [← natDegree_mul hg_derivative_ne he, hg_derivative_mul]
    simp
  obtain ⟨hg_degree, he_degree⟩ := Nat.add_eq_zero_iff.mp hdegrees
  let eps := e.coeff 0
  let alpha := (derivative g).coeff 0
  have heC : e = C eps := by
    dsimp [eps]
    exact eq_C_of_natDegree_eq_zero he_degree
  have heps : eps ≠ 0 := by
    intro hepszero
    apply he
    calc
      e = C eps := heC
      _ = 0 := by simp [hepszero]
  have hg_derivative_C : derivative g = C alpha := by
    dsimp [alpha]
    exact eq_C_of_natDegree_eq_zero hg_degree
  have halpha_eps : alpha * eps = k := by
    rw [hg_derivative_C, heC, ← C_mul] at hg_derivative_mul
    exact C_injective hg_derivative_mul
  let beta := (g - C alpha * X).coeff 0
  have hg_affine : g = C alpha * X + C beta := by
    have hconst : g - C alpha * X = C beta := by
      dsimp [beta]
      apply eq_C_of_derivative_eq_zero
      rw [derivative_sub, hg_derivative_C, derivative_C_mul_X, sub_self]
    linear_combination hconst
  have hc : c = C lam * f ^ 2 + C mu * f + C alpha * X + C beta := by
    dsimp [g] at hg_affine
    linear_combination hg_affine
  exact ⟨lam, mu, alpha, beta, eps, heps, halpha_eps, heC, ha, hb, hc⟩

/-- In the complementary chart `e = 0`, the coefficient equations force the
map into the triangular form `(eta * y + c(x), delta * x + gamma)`, with both
slopes nonzero.
@isnad1 id=ex.4h7v.s11.569eba5f0ee6 from=translated src=- shape=1b396477 vocab=391891cc
-/
theorem quadraticInY_zeroSlope_normal_form [CharZero K]
    {a b c e f : K[X]} {k : K}
    (hk : k ≠ 0) (he : e = 0)
    (hlinear : derivative b * e - b * derivative e =
      C (2 : K) * a * derivative f)
    (hconstant : derivative c * e - b * derivative f = C k) :
    ∃ eta delta gamma : K,
      eta ≠ 0 ∧ delta ≠ 0 ∧ -(eta * delta) = k ∧
      a = 0 ∧ b = C eta ∧ e = 0 ∧ f = C delta * X + C gamma := by
  have hc : -(b * derivative f) = C k := by
    simpa [he] using hconstant
  have hb : b ≠ 0 := by
    intro hbzero
    have hkzero : C k = 0 := by
      simpa [hbzero] using hc.symm
    exact (C_ne_zero.mpr hk) hkzero
  have hf' : derivative f ≠ 0 := by
    intro hfzero
    have hkzero : C k = 0 := by
      simpa [hfzero] using hc.symm
    exact (C_ne_zero.mpr hk) hkzero
  have ha : a = 0 := by
    have hprod : C (2 : K) * a * derivative f = 0 := by
      simpa [he] using hlinear.symm
    by_contra hane
    exact (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr (by norm_num)) hane) hf') hprod
  have hprod : b * derivative f = C (-k) := by
    calc
      b * derivative f = -C k := neg_eq_iff_eq_neg.mp hc
      _ = C (-k) := by simp
  have hdegrees : b.natDegree + (derivative f).natDegree = 0 := by
    rw [← natDegree_mul hb hf', hprod]
    simp
  obtain ⟨hb_degree, hf_degree⟩ := Nat.add_eq_zero_iff.mp hdegrees
  let eta := b.coeff 0
  let delta := (derivative f).coeff 0
  have hbC : b = C eta := by
    dsimp [eta]
    exact eq_C_of_natDegree_eq_zero hb_degree
  have hfC : derivative f = C delta := by
    dsimp [delta]
    exact eq_C_of_natDegree_eq_zero hf_degree
  have heta : eta ≠ 0 := by
    intro hetazero
    apply hb
    calc
      b = C eta := hbC
      _ = 0 := by simp [hetazero]
  have hdelta : delta ≠ 0 := by
    intro hdeltazero
    apply hf'
    calc
      derivative f = C delta := hfC
      _ = 0 := by simp [hdeltazero]
  have heta_delta : -(eta * delta) = k := by
    rw [hbC, hfC, ← C_mul] at hprod
    have hscalar : eta * delta = -k := C_injective hprod
    rw [hscalar]
    simp
  let gamma := (f - C delta * X).coeff 0
  have hf_affine : f = C delta * X + C gamma := by
    have hconst : f - C delta * X = C gamma := by
      dsimp [gamma]
      apply eq_C_of_derivative_eq_zero
      rw [derivative_sub, hfC, derivative_C_mul_X, sub_self]
    linear_combination hconst
  exact ⟨eta, delta, gamma, heta, hdelta, heta_delta, ha, hbC, he, hf_affine⟩

/-- In the target chart `e ≠ 0`, a quadratic-in-one-variable plane map
satisfying the three nonzero constant-Jacobian coefficient identities is
bijective, with the explicit polynomial inverse `normalFormInverse` after
normalization.
@isnad1 id=bijectiv.5h7v.s11.0ab5bfbdb8dd from=translated src=- shape=5b87750d vocab=7753eeff
-/
theorem quadraticInY_bijective [CharZero K] {a b c e f : K[X]} {k : K}
    (hk : k ≠ 0) (he : e ≠ 0)
    (hquad : derivative a * e - C (2 : K) * a * derivative e = 0)
    (hlinear : derivative b * e - b * derivative e =
      C (2 : K) * a * derivative f)
    (hconstant : derivative c * e - b * derivative f = C k) :
    Function.Bijective (quadraticInYMap a b c e f) := by
  obtain ⟨lam, mu, alpha, beta, eps, heps, halpha_eps, heC, ha, hb, hc⟩ :=
    quadraticInY_normal_form hk he hquad hlinear hconstant
  have halpha : alpha ≠ 0 := by
    intro halpha_zero
    apply hk
    rw [← halpha_eps, halpha_zero, zero_mul]
  rw [quadraticInYMap_eq_normalFormMap heC ha hb hc]
  exact ⟨(normalFormInverse_left halpha heps).injective,
    (normalFormInverse_right halpha heps).surjective⟩

/-- Every quadratic-in-one-variable plane map satisfying the three nonzero
constant-Jacobian coefficient identities is bijective.  The proof covers both
target charts and supplies an explicit polynomial inverse in each chart.
@isnad1 id=bijectiv.4h7v.s11.b2d1bb592663 from=translated src=- shape=daeccccc vocab=7753eeff
-/
theorem quadraticInY_bijective_full [CharZero K] {a b c e f : K[X]} {k : K}
    (hk : k ≠ 0)
    (hquad : derivative a * e - C (2 : K) * a * derivative e = 0)
    (hlinear : derivative b * e - b * derivative e =
      C (2 : K) * a * derivative f)
    (hconstant : derivative c * e - b * derivative f = C k) :
    Function.Bijective (quadraticInYMap a b c e f) := by
  by_cases he : e = 0
  · obtain ⟨eta, delta, gamma, heta, hdelta, _heta_delta, ha, hb, he, hf⟩ :=
      quadraticInY_zeroSlope_normal_form hk he hlinear hconstant
    rw [quadraticInYMap_eq_zeroSlopeNormalFormMap ha hb he hf]
    exact ⟨(zeroSlopeNormalFormInverse_left heta hdelta).injective,
      (zeroSlopeNormalFormInverse_right heta hdelta).surjective⟩
  · exact quadraticInY_bijective hk he hquad hlinear hconstant

/-- No noninjective Keller map occurs in the full quadratic-in-one-variable
ansatz.  Both target charts have explicit normal forms and two-sided inverses
in `quadraticInY_bijective_full`.
@isnad1 id=injectiv.4h7v.s11.adebe42a9707 from=translated src=- shape=daeccccc vocab=93495be4
-/
theorem quadraticInY_injective [CharZero K] {a b c e f : K[X]} {k : K}
    (hk : k ≠ 0)
    (hquad : derivative a * e - C (2 : K) * a * derivative e = 0)
    (hlinear : derivative b * e - b * derivative e =
      C (2 : K) * a * derivative f)
    (hconstant : derivative c * e - b * derivative f = C k) :
    Function.Injective (quadraticInYMap a b c e f) :=
  (quadraticInY_bijective_full hk hquad hlinear hconstant).1

end JacobianTwo.QuadraticInOneVariable
