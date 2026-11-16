/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.Seed.Algebra.Polynomial.Bivariate
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Keller maps with one affine coordinate

This module treats a plane polynomial map whose second coordinate is affine in
`y`, without any degree bound on its first coordinate.  Both partial
derivatives are represented as bundled derivations of `K[X][Y]`, so the
hypothesis is an equality for the actual formal Jacobian polynomial.
-/

noncomputable section

open scoped Polynomial Polynomial.Bivariate

namespace JacobianTwo.AffineCoordinate

open Polynomial

variable {K : Type*} [Field K]

/-- Formal differentiation of a bivariate polynomial with respect to `x`.-/
def xDerivative : Derivation K K[X][Y] K[X][Y] :=
  PolynomialModule.equivPolynomialSelf.compDer
    (Polynomial.derivative' (R := K)).mapCoeffs

/-- Formal differentiation of a bivariate polynomial with respect to `y`.-/
def yDerivative : Derivation K K[X][Y] K[X][Y] :=
  (Polynomial.derivative' (R := K[X])).restrictScalars K

/-- The formal Jacobian determinant `P_x Q_y - P_y Q_x`.-/
def jacobian (P Q : K[X][Y]) : K[X][Y] :=
  xDerivative P * yDerivative Q - yDerivative P * xDerivative Q

/-- The Jacobian with a fixed second coordinate, bundled as a derivation in
the first coordinate.-/
def jacobianDerivation (Q : K[X][Y]) : Derivation K K[X][Y] K[X][Y] :=
  (yDerivative Q) • xDerivative - (xDerivative Q) • yDerivative

/-- A second coordinate affine in `y`.-/
def affineCoordinate (e f : K[X]) : K[X][Y] := C e * Y + C f

@[simp]
theorem coeff_xDerivative (P : K[X][Y]) (n : ℕ) :
    (xDerivative P).coeff n = derivative (P.coeff n) := by
  rfl

@[simp]
theorem yDerivative_apply (P : K[X][Y]) : yDerivative P = derivative P := by
  rfl

@[simp]
theorem xDerivative_C (p : K[X]) : xDerivative (C p) = C (derivative p) := by
  apply Polynomial.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · simp [coeff_xDerivative, coeff_C, hn]

@[simp]
theorem xDerivative_Y : xDerivative (Y : K[X][Y]) = 0 := by
  apply Polynomial.ext
  intro n
  by_cases hn : n = 1
  · subst n
    simp
  · simp [coeff_xDerivative, coeff_X, Ne.symm hn]

@[simp]
theorem xDerivative_CC (a : K) : xDerivative (CC a : K[X][Y]) = 0 := by
  simp

@[simp]
theorem xDerivative_affineCoordinate (e f : K[X]) :
    xDerivative (affineCoordinate e f) = C (derivative e) * Y + C (derivative f) := by
  simp [affineCoordinate, Derivation.leibniz]

@[simp]
theorem yDerivative_affineCoordinate (e f : K[X]) :
    yDerivative (affineCoordinate e f) = C e := by
  simp [affineCoordinate]

theorem natDegree_affineCoordinate {e f : K[X]} (he : e ≠ 0) :
    (affineCoordinate e f).natDegree = 1 := by
  exact natDegree_linear he

theorem leadingCoeff_affineCoordinate {e f : K[X]} (he : e ≠ 0) :
    (affineCoordinate e f).leadingCoeff = e := by
  exact leadingCoeff_linear he

@[simp]
theorem jacobianDerivation_apply (P Q : K[X][Y]) :
    jacobianDerivation Q P = jacobian P Q := by
  simp only [jacobianDerivation, Derivation.sub_apply, Derivation.smul_apply,
    yDerivative_apply, jacobian]
  ring

@[simp]
theorem jacobian_self (Q : K[X][Y]) : jacobian Q Q = 0 := by
  simp [jacobian]
  ring

@[simp]
theorem jacobian_pow_left (Q : K[X][Y]) (n : ℕ) : jacobian (Q ^ n) Q = 0 := by
  rw [← jacobianDerivation_apply]
  simp

@[simp]
theorem jacobian_CC_left (a : K) (Q : K[X][Y]) : jacobian (CC a) Q = 0 := by
  simp [jacobian]

theorem jacobian_sub_left (P R Q : K[X][Y]) :
    jacobian (P - R) Q = jacobian P Q - jacobian R Q := by
  rw [← jacobianDerivation_apply, ← jacobianDerivation_apply,
    ← jacobianDerivation_apply]
  exact map_sub (jacobianDerivation Q) P R

theorem jacobian_add_left (P R Q : K[X][Y]) :
    jacobian (P + R) Q = jacobian P Q + jacobian R Q := by
  rw [← jacobianDerivation_apply, ← jacobianDerivation_apply,
    ← jacobianDerivation_apply]
  exact map_add (jacobianDerivation Q) P R

@[simp]
theorem jacobian_CC_mul_pow_left (a : K) (Q : K[X][Y]) (n : ℕ) :
    jacobian (CC a * Q ^ n) Q = 0 := by
  rw [← jacobianDerivation_apply]
  simp

theorem jacobian_C_left (h : K[X]) (e f : K[X]) :
    jacobian (C h) (affineCoordinate e f) = C (derivative h * e) := by
  rw [jacobian, xDerivative_C, yDerivative_affineCoordinate, yDerivative_apply,
    derivative_C, zero_mul, sub_zero, ← C_mul]

/-- The leading `y`-coefficient of the Jacobian with an affine second
coordinate.  This is the differential equation used by degree descent.-/
theorem coeff_natDegree_jacobian_affineCoordinate (P : K[X][Y]) (e f : K[X])
    (hn : P.natDegree ≠ 0) :
    (jacobian P (affineCoordinate e f)).coeff P.natDegree =
      derivative P.leadingCoeff * e -
        C (P.natDegree : K) * P.leadingCoeff * derivative e := by
  obtain ⟨n, hnP⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [hnP]
  rw [jacobian, xDerivative_affineCoordinate, yDerivative_affineCoordinate,
    yDerivative_apply, coeff_sub, coeff_mul_C]
  rw [mul_add, ← mul_assoc, coeff_add, coeff_mul_X, coeff_mul_C, coeff_mul_C,
    coeff_derivative, coeff_derivative, coeff_xDerivative]
  rw [show P.coeff (n + 1) = P.leadingCoeff by simpa [hnP] using P.coeff_natDegree]
  rw [show P.coeff (n + 1 + 1) = 0 by simpa [hnP] using P.coeff_natDegree_succ_eq_zero]
  simp only [zero_mul]
  simp only [← C_eq_natCast]
  push_cast
  rw [map_add]
  simp only [map_one]
  ring_nf

/-- Polynomial solutions of `p' e = n p e'` over a characteristic-zero
field are scalar multiples of `e ^ n`.-/
theorem eq_C_mul_pow_of_differential_eq [CharZero K] {p e : K[X]} {n : ℕ}
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
      · have hqdeg : q.natDegree = n * e.natDegree :=
          natDegree_relation hq hq_diff
        have hqnat_lt : q.natDegree < p.natDegree := by
          rw [degree_eq_natDegree hp] at hq_degree
          exact (natDegree_lt_iff_degree_lt hq).mpr hq_degree
        rw [hqdeg, hdeg] at hqnat_lt
        exact (Nat.lt_irrefl _ hqnat_lt).elim

/-- Degree descent for an arbitrary first coordinate.  A constant Jacobian
against `e(x)y + f(x)` with `e ≠ 0` writes the first coordinate as a scalar
polynomial in the second coordinate, plus a polynomial in `x` alone.-/
theorem exists_comp_add_C_of_jacobian_eq [CharZero K]
    {P : K[X][Y]} {e f : K[X]} {k : K}
    (he : e ≠ 0)
    (hjac : jacobian P (affineCoordinate e f) = CC k) :
    ∃ G h : K[X],
      P = (G.map C).comp (affineCoordinate e f) + C h ∧
      derivative h * e = C k := by
  let Q := affineCoordinate e f
  have descend : ∀ n : ℕ, ∀ R : K[X][Y], R.natDegree = n →
      jacobian R Q = CC k →
      ∃ G h : K[X], R = (G.map C).comp Q + C h ∧ derivative h * e = C k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro R hdegree hRjac
        by_cases hn : n = 0
        · have hRconstant : R = C (R.coeff 0) := by
            apply eq_C_of_natDegree_eq_zero
            rw [hdegree, hn]
          refine ⟨0, R.coeff 0, ?_, ?_⟩
          · rw [hRconstant]
            simp
          · have h := hRjac
            rw [hRconstant, jacobian_C_left] at h
            exact C_injective h
        · have hRdegree_ne : R.natDegree ≠ 0 := by simpa [hdegree] using hn
          have hcoeff :
              derivative R.leadingCoeff * e -
                  C (R.natDegree : K) * R.leadingCoeff * derivative e = 0 := by
            rw [← coeff_natDegree_jacobian_affineCoordinate R e f hRdegree_ne]
            rw [hRjac]
            exact coeff_C_of_ne_zero hRdegree_ne
          have hdiff : derivative R.leadingCoeff * e =
              C (R.natDegree : K) * R.leadingCoeff * derivative e :=
            sub_eq_zero.mp hcoeff
          obtain ⟨lam, hlamodel⟩ :=
            eq_C_mul_pow_of_differential_eq he hRdegree_ne hdiff
          have hRne : R ≠ 0 := by
            intro hzero
            rw [hzero, natDegree_zero] at hRdegree_ne
            exact hRdegree_ne rfl
          have hlam : lam ≠ 0 := by
            intro hlamzero
            have hleadzero : R.leadingCoeff = 0 := by simp [hlamodel, hlamzero]
            exact (leadingCoeff_ne_zero.mpr hRne) hleadzero
          let model : K[X][Y] := CC lam * Q ^ R.natDegree
          let tail : K[X][Y] := R - model
          have hQne : Q ≠ 0 := by
            intro hzero
            have := natDegree_affineCoordinate (f := f) he
            rw [← show Q = affineCoordinate e f by rfl, hzero, natDegree_zero] at this
            omega
          have hmodel_ne : model ≠ 0 := by
            dsimp [model]
            exact mul_ne_zero (C_ne_zero.mpr (C_ne_zero.mpr hlam))
              (pow_ne_zero _ hQne)
          have hmodel_natDegree : model.natDegree = R.natDegree := by
            dsimp [model]
            rw [natDegree_mul (C_ne_zero.mpr (C_ne_zero.mpr hlam))
                (pow_ne_zero _ hQne), natDegree_C, zero_add, natDegree_pow,
              show Q.natDegree = 1 by exact natDegree_affineCoordinate (f := f) he,
              mul_one]
          have hmodel_leadingCoeff : model.leadingCoeff = R.leadingCoeff := by
            dsimp [model]
            rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow,
              show Q.leadingCoeff = e by exact leadingCoeff_affineCoordinate (f := f) he]
            exact hlamodel.symm
          have hmodel_degree : model.degree = R.degree := by
            rw [degree_eq_natDegree hmodel_ne, degree_eq_natDegree hRne,
              hmodel_natDegree]
          have htail_degree : tail.degree < R.degree := by
            dsimp [tail]
            exact degree_sub_lt_left hmodel_degree.symm hRne hmodel_leadingCoeff.symm
          have htail_natDegree : tail.natDegree < n := by
            by_cases htail : tail = 0
            · simp [htail, Nat.pos_of_ne_zero hn]
            · apply (natDegree_lt_iff_degree_lt htail).mpr
              rw [degree_eq_natDegree hRne, hdegree] at htail_degree
              exact htail_degree
          have htail_jac : jacobian tail Q = CC k := by
            dsimp [tail, model]
            rw [jacobian_sub_left, jacobian_CC_mul_pow_left, sub_zero]
            exact hRjac
          obtain ⟨G, h, htail_repr, hh⟩ :=
            ih tail.natDegree htail_natDegree tail rfl htail_jac
          refine ⟨G + monomial R.natDegree lam, h, ?_, hh⟩
          calc
            R = tail + model := by simp [tail]
            _ = ((G.map C).comp Q + C h) + CC lam * Q ^ R.natDegree := by
              rw [htail_repr]
            _ = (((G + monomial R.natDegree lam).map C).comp Q) + C h := by
              rw [Polynomial.map_add, add_comp, map_monomial, monomial_comp]
              ring
  exact descend P.natDegree P rfl hjac

/-- With nonzero affine `y`-slope and nonzero constant Jacobian, the degree
descent normal form has constant `y`-slope and an affine residual in `x`.-/
theorem nonzeroSlope_normal_form [CharZero K]
    {P : K[X][Y]} {e f : K[X]} {k : K}
    (hk : k ≠ 0) (he : e ≠ 0)
    (hjac : jacobian P (affineCoordinate e f) = CC k) :
    ∃ G : K[X], ∃ alpha beta eps : K,
      eps ≠ 0 ∧ alpha ≠ 0 ∧ alpha * eps = k ∧ e = C eps ∧
      P = (G.map C).comp (affineCoordinate e f) +
        C (C alpha * X + C beta) := by
  obtain ⟨G, h, hP, hh⟩ := exists_comp_add_C_of_jacobian_eq he hjac
  have hhderiv : derivative h ≠ 0 := by
    intro hzero
    have hkzero : C k = 0 := by simpa [hzero] using hh.symm
    exact (C_ne_zero.mpr hk) hkzero
  have hdegrees : (derivative h).natDegree + e.natDegree = 0 := by
    rw [← natDegree_mul hhderiv he, hh]
    simp
  obtain ⟨hhdegree, hedegree⟩ := Nat.add_eq_zero_iff.mp hdegrees
  let eps := e.coeff 0
  let alpha := (derivative h).coeff 0
  have heC : e = C eps := by
    dsimp [eps]
    exact eq_C_of_natDegree_eq_zero hedegree
  have hhC : derivative h = C alpha := by
    dsimp [alpha]
    exact eq_C_of_natDegree_eq_zero hhdegree
  have heps : eps ≠ 0 := by
    intro hzero
    apply he
    rw [heC, hzero, C_0]
  have halpha : alpha ≠ 0 := by
    intro hzero
    apply hhderiv
    rw [hhC, hzero, C_0]
  have halphaeps : alpha * eps = k := by
    rw [hhC, heC, ← C_mul] at hh
    exact C_injective hh
  let beta := (h - C alpha * X).coeff 0
  have hh_affine : h = C alpha * X + C beta := by
    have hconstant : h - C alpha * X = C beta := by
      dsimp [beta]
      apply eq_C_of_derivative_eq_zero
      rw [derivative_sub, hhC, derivative_C_mul_X, sub_self]
    linear_combination hconstant
  refine ⟨G, alpha, beta, eps, heps, halpha, halphaeps, heC, ?_⟩
  rw [hP, hh_affine]

/-- Evaluation of a bivariate first coordinate together with an affine second
coordinate.-/
def affineCoordinateMap (P : K[X][Y]) (e f : K[X]) (p : K × K) : K × K :=
  (P.evalEval p.1 p.2, (affineCoordinate e f).evalEval p.1 p.2)

/-- The triangular normal form in the chart where the affine `y`-slope is
nonzero.-/
def nonzeroSlopeNormalFormMap (G : K[X]) (alpha beta eps : K) (f : K[X])
    (p : K × K) : K × K :=
  let q := eps * p.2 + f.eval p.1
  (G.eval q + alpha * p.1 + beta, q)

/-- Explicit inverse to `nonzeroSlopeNormalFormMap`.-/
def nonzeroSlopeNormalFormInverse (G : K[X]) (alpha beta eps : K) (f : K[X])
    (p : K × K) : K × K :=
  let x := (p.1 - G.eval p.2 - beta) / alpha
  (x, (p.2 - f.eval x) / eps)

theorem affineCoordinateMap_eq_nonzeroSlopeNormalFormMap
    {P : K[X][Y]} {e f G : K[X]} {alpha beta eps : K}
    (he : e = C eps)
    (hP : P = (G.map C).comp (affineCoordinate e f) +
      C (C alpha * X + C beta)) :
    affineCoordinateMap P e f = nonzeroSlopeNormalFormMap G alpha beta eps f := by
  funext p
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · simp [affineCoordinateMap, nonzeroSlopeNormalFormMap, hP, affineCoordinate,
      he, evalEval, eval_comp, eval_map]
    change (evalRingHom x) (eval₂ C (C eps * C y + f) G) + (alpha * x + beta) =
      G.eval (eps * y + f.eval x) + alpha * x + beta
    rw [hom_eval₂ G C (evalRingHom x)]
    have hcomp : (evalRingHom x).comp C = RingHom.id K :=
      eval₂RingHom_comp_C (RingHom.id K) x
    rw [hcomp, eval₂_id]
    have harg : (evalRingHom x) (C eps * C y + f) = eps * y + f.eval x := by
      simp
    rw [harg]
    ring
  · simp [affineCoordinateMap, nonzeroSlopeNormalFormMap, affineCoordinate, he,
      evalEval]

theorem nonzeroSlopeNormalFormInverse_left
    {G : K[X]} {alpha beta eps : K} {f : K[X]}
    (halpha : alpha ≠ 0) (heps : eps ≠ 0) :
    Function.LeftInverse (nonzeroSlopeNormalFormInverse G alpha beta eps f)
      (nonzeroSlopeNormalFormMap G alpha beta eps f) := by
  rintro ⟨x, y⟩
  let q := eps * y + f.eval x
  let x' := (G.eval q + alpha * x + beta - G.eval q - beta) / alpha
  change (x', (q - f.eval x') / eps) = (x, y)
  have hx : x' = x := by
    dsimp [x']
    field_simp
    ring
  apply Prod.ext
  · exact hx
  · simp only [hx]
    dsimp [q]
    field_simp
    ring

theorem nonzeroSlopeNormalFormInverse_right
    {G : K[X]} {alpha beta eps : K} {f : K[X]}
    (halpha : alpha ≠ 0) (heps : eps ≠ 0) :
    Function.RightInverse (nonzeroSlopeNormalFormInverse G alpha beta eps f)
      (nonzeroSlopeNormalFormMap G alpha beta eps f) := by
  rintro ⟨u, v⟩
  let x := (u - G.eval v - beta) / alpha
  let y := (v - f.eval x) / eps
  have hq : eps * y + f.eval x = v := by
    dsimp [y]
    field_simp
    ring
  change (let q := eps * y + f.eval x
    (G.eval q + alpha * x + beta, q)) = (u, v)
  simp only [hq]
  apply Prod.ext
  · dsimp [x]
    field_simp
    ring
  · rfl

/-- Arbitrary-degree Keller maps with a nonzero affine second-coordinate
slope are bijective, with an explicit polynomial inverse after normalization.-/
theorem nonzeroSlope_bijective [CharZero K]
    {P : K[X][Y]} {e f : K[X]} {k : K}
    (hk : k ≠ 0) (he : e ≠ 0)
    (hjac : jacobian P (affineCoordinate e f) = CC k) :
    Function.Bijective (affineCoordinateMap P e f) := by
  obtain ⟨G, alpha, beta, eps, heps, halpha, _halphaeps, heC, hP⟩ :=
    nonzeroSlope_normal_form hk he hjac
  rw [affineCoordinateMap_eq_nonzeroSlopeNormalFormMap heC hP]
  exact ⟨(nonzeroSlopeNormalFormInverse_left halpha heps).injective,
    (nonzeroSlopeNormalFormInverse_right halpha heps).surjective⟩

theorem jacobian_zeroSlope (P : K[X][Y]) (f : K[X]) :
    jacobian P (affineCoordinate 0 f) = -(derivative P * C (derivative f)) := by
  simp [jacobian, affineCoordinate]

/-- In the complementary chart, the actual Jacobian equality forces a
triangular map: the first coordinate is affine in `y` and the second is affine
in `x`.-/
theorem zeroSlope_normal_form [CharZero K]
    {P : K[X][Y]} {f : K[X]} {k : K}
    (hk : k ≠ 0)
    (hjac : jacobian P (affineCoordinate 0 f) = CC k) :
    ∃ c : K[X], ∃ eta delta gamma : K,
      eta ≠ 0 ∧ delta ≠ 0 ∧ -(eta * delta) = k ∧
      P = CC eta * Y + C c ∧
      f = C delta * X + C gamma := by
  have hprod : derivative P * C (derivative f) = CC (-k) := by
    have h := hjac
    rw [jacobian_zeroSlope] at h
    have hneg := congrArg Neg.neg h
    calc
      derivative P * C (derivative f) = -CC k := by simpa using hneg
      _ = CC (-k) := by
        change -(C (C k)) = C (C (-k))
        rw [C_neg, C_neg]
  have hconstant_ne : CC (-k) ≠ (0 : K[X][Y]) :=
    C_ne_zero.mpr (C_ne_zero.mpr (neg_ne_zero.mpr hk))
  have hPderiv_ne : derivative P ≠ 0 := by
    intro hzero
    apply hconstant_ne
    rw [← hprod, hzero, zero_mul]
  have hfderiv_ne : derivative f ≠ 0 := by
    intro hzero
    apply hconstant_ne
    rw [← hprod, hzero, C_0, mul_zero]
  have hPderiv_degree : (derivative P).natDegree = 0 := by
    have hdegrees : (derivative P).natDegree + (C (derivative f)).natDegree = 0 := by
      rw [← natDegree_mul hPderiv_ne (C_ne_zero.mpr hfderiv_ne), hprod]
      simp
    exact (Nat.add_eq_zero_iff.mp hdegrees).1
  let b : K[X] := (derivative P).coeff 0
  have hPderiv_C : derivative P = C b := by
    dsimp [b]
    exact eq_C_of_natDegree_eq_zero hPderiv_degree
  have hbprod : b * derivative f = C (-k) := by
    rw [hPderiv_C, ← C_mul] at hprod
    exact C_injective hprod
  have hb_ne : b ≠ 0 := by
    intro hzero
    have : C (-k) = 0 := by simpa [hzero] using hbprod.symm
    exact (C_ne_zero.mpr (neg_ne_zero.mpr hk)) this
  have hinner_degrees : b.natDegree + (derivative f).natDegree = 0 := by
    rw [← natDegree_mul hb_ne hfderiv_ne, hbprod]
    simp
  obtain ⟨hbdegree, hfdegree⟩ := Nat.add_eq_zero_iff.mp hinner_degrees
  let eta := b.coeff 0
  let delta := (derivative f).coeff 0
  have hbC : b = C eta := by
    dsimp [eta]
    exact eq_C_of_natDegree_eq_zero hbdegree
  have hfC : derivative f = C delta := by
    dsimp [delta]
    exact eq_C_of_natDegree_eq_zero hfdegree
  have heta : eta ≠ 0 := by
    intro hzero
    apply hb_ne
    rw [hbC, hzero, C_0]
  have hdelta : delta ≠ 0 := by
    intro hzero
    apply hfderiv_ne
    rw [hfC, hzero, C_0]
  have heta_delta : -(eta * delta) = k := by
    rw [hbC, hfC, ← C_mul] at hbprod
    have hscalar : eta * delta = -k := C_injective hbprod
    rw [hscalar]
    simp
  let c : K[X] := (P - CC eta * Y).coeff 0
  have hPform : P = CC eta * Y + C c := by
    have hconstant : P - CC eta * Y = C c := by
      dsimp [c]
      apply eq_C_of_derivative_eq_zero
      rw [derivative_sub, derivative_C_mul_X]
      rw [hPderiv_C, hbC, sub_self]
    linear_combination hconstant
  let gamma := (f - C delta * X).coeff 0
  have hfform : f = C delta * X + C gamma := by
    have hconstant : f - C delta * X = C gamma := by
      dsimp [gamma]
      apply eq_C_of_derivative_eq_zero
      rw [derivative_sub, hfC, derivative_C_mul_X, sub_self]
    linear_combination hconstant
  exact ⟨c, eta, delta, gamma, heta, hdelta, heta_delta, hPform, hfform⟩

/-- The triangular normal form in the zero-slope chart.-/
def zeroSlopeNormalFormMap (eta delta gamma : K) (c : K[X])
    (p : K × K) : K × K :=
  (eta * p.2 + c.eval p.1, delta * p.1 + gamma)

/-- Explicit inverse to `zeroSlopeNormalFormMap`.-/
def zeroSlopeNormalFormInverse (eta delta gamma : K) (c : K[X])
    (p : K × K) : K × K :=
  let x := (p.2 - gamma) / delta
  (x, (p.1 - c.eval x) / eta)

theorem affineCoordinateMap_eq_zeroSlopeNormalFormMap
    {P : K[X][Y]} {f c : K[X]} {eta delta gamma : K}
    (hP : P = CC eta * Y + C c)
    (hf : f = C delta * X + C gamma) :
    affineCoordinateMap P 0 f = zeroSlopeNormalFormMap eta delta gamma c := by
  funext p
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · simp [affineCoordinateMap, zeroSlopeNormalFormMap, hP, evalEval]
  · simp [affineCoordinateMap, zeroSlopeNormalFormMap, affineCoordinate, hf,
      evalEval]

theorem zeroSlopeNormalFormInverse_left
    {eta delta gamma : K} {c : K[X]}
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

theorem zeroSlopeNormalFormInverse_right
    {eta delta gamma : K} {c : K[X]}
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

/-- Every plane map whose second coordinate is affine in `y` and whose actual
formal Jacobian is a nonzero constant is bijective, with no degree bound on
the first coordinate.-/
theorem affineCoordinate_bijective [CharZero K]
    {P : K[X][Y]} {e f : K[X]} {k : K}
    (hk : k ≠ 0)
    (hjac : jacobian P (affineCoordinate e f) = CC k) :
    Function.Bijective (affineCoordinateMap P e f) := by
  by_cases he : e = 0
  · subst e
    obtain ⟨c, eta, delta, gamma, heta, hdelta, _heta_delta, hP, hf⟩ :=
      zeroSlope_normal_form hk hjac
    rw [affineCoordinateMap_eq_zeroSlopeNormalFormMap hP hf]
    exact ⟨(zeroSlopeNormalFormInverse_left heta hdelta).injective,
      (zeroSlopeNormalFormInverse_right heta hdelta).surjective⟩
  · exact nonzeroSlope_bijective hk he hjac

theorem affineCoordinate_injective [CharZero K]
    {P : K[X][Y]} {e f : K[X]} {k : K}
    (hk : k ≠ 0)
    (hjac : jacobian P (affineCoordinate e f) = CC k) :
    Function.Injective (affineCoordinateMap P e f) :=
  (affineCoordinate_bijective hk hjac).1

end JacobianTwo.AffineCoordinate
