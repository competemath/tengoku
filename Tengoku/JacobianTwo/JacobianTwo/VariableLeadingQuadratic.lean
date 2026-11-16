/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.AffineCoordinate
import Tengoku.Seed.RingTheory.UniqueFactorizationDomain.Multiplicity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Keller maps with a variable-leading quadratic coordinate

This module begins the coefficient descent for a plane polynomial map whose
second coordinate has the form

`a(x) * y^2 + g(x) * y + f(x)`.

The coefficient immediately above the `y`-degree of the first coordinate is
independent of `g` and `f`.  Its vanishing gives the differential equation

`2 * a * p_n' - n * a' * p_n = 0`

for the leading `y`-coefficient `p_n` of the first coordinate.
-/

noncomputable section

open scoped Polynomial Polynomial.Bivariate

namespace JacobianTwo.VariableLeadingQuadratic

open Polynomial
open JacobianTwo.AffineCoordinate

variable {K : Type*} [Field K]

@[simp]
theorem C_natCast_inner (n : ℕ) : C (n : K[X]) = (n : K[X][Y]) := by
  rw [map_natCast]

@[simp]
theorem C_ofNat_inner (n : ℕ) [n.AtLeastTwo] :
    C (ofNat(n) : K[X]) = (ofNat(n) : K[X][Y]) := by
  rw [C_ofNat]

@[simp]
theorem CC_ofNat_scalar (n : ℕ) [n.AtLeastTwo] :
    C (C (ofNat(n) : K)) = (ofNat(n) : K[X][Y]) := by
  rw [C_ofNat, C_ofNat]

/-- A polynomial that is quadratic in `y`, allowing its leading coefficient
to vary with `x`.-/
def variableQuadraticCoordinate (a g f : K[X]) : K[X][Y] :=
  C a * Y ^ 2 + C g * Y + C f

/-- The exact UFD square-shape conclusion needed after the odd-degree
leading-coefficient identity.  Establishing this predicate from that identity
is a separate factorization step.-/
def IsNonzeroScalarTimesSquare (a : K[X]) : Prop :=
  ∃ eps : K, ∃ h : K[X], eps ≠ 0 ∧ a = C eps * h ^ 2

/-- In `K[x]`, if a square is a nonzero scalar times an odd power, then the
base is a nonzero scalar times a square.  The same square root also describes
the original square root up to a nonzero scalar.-/
theorem scalar_times_square_and_odd_root_of_sq_eq_scalar_mul_pow
    {p a : K[X]} {c : K} {n : ℕ}
    (hc : c ≠ 0) (ha : a ≠ 0) (hodd : Odd n)
    (hsq : p ^ 2 = C c * a ^ n) :
    ∃ eps : K, ∃ h : K[X], ∃ lam : K,
      eps ≠ 0 ∧ lam ≠ 0 ∧
      a = C eps * h ^ 2 ∧ p = C lam * h ^ n := by
  rcases hodd with ⟨m, hn⟩
  have hpowDvd : (a ^ m) ^ 2 ∣ p ^ 2 := by
    rw [hsq]
    refine ⟨C c * a, ?_⟩
    rw [hn, show 2 * m + 1 = m + m + 1 by omega, pow_succ, pow_add,
      pow_two]
    ring
  have hdvd : a ^ m ∣ p :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by omega : 2 ≠ 0)).mp
      hpowDvd
  obtain ⟨h, hpresentation⟩ := hdvd
  have hpresentation' : p = a ^ m * h := hpresentation
  have hcancel :
      a ^ (m + m) * h ^ 2 = a ^ (m + m) * (C c * a) := by
    calc
      a ^ (m + m) * h ^ 2 = (a ^ m * h) ^ 2 := by
        rw [pow_add, pow_two, pow_two]
        ring
      _ = p ^ 2 := by rw [← hpresentation']
      _ = C c * a ^ n := hsq
      _ = a ^ (m + m) * (C c * a) := by
        rw [hn, pow_succ, pow_add]
        ring
  have hahpow : a ^ (m + m) ≠ 0 := pow_ne_zero _ ha
  have hhsq : h ^ 2 = C c * a := mul_left_cancel₀ hahpow hcancel
  let eps : K := c⁻¹
  let lam : K := c⁻¹ ^ m
  have heps : eps ≠ 0 := by
    dsimp [eps]
    exact inv_ne_zero hc
  have hlam : lam ≠ 0 := by
    dsimp [lam]
    exact pow_ne_zero _ (inv_ne_zero hc)
  have haSquare : a = C eps * h ^ 2 := by
    rw [hhsq]
    symm
    calc
      C eps * (C c * a) = (C eps * C c) * a := by ring
      _ = C (eps * c) * a := by rw [C_mul]
      _ = a := by
        dsimp [eps]
        rw [inv_mul_cancel₀ hc, C_1, one_mul]
  have hpRoot : p = C lam * h ^ n := by
    rw [hpresentation', haSquare, hn]
    dsimp [lam, eps]
    rw [mul_pow, ← C_pow, pow_succ, pow_add]
    ring
  exact ⟨eps, h, lam, heps, hlam, haSquare, hpRoot⟩

/-- The square-shape projection of
`scalar_times_square_and_odd_root_of_sq_eq_scalar_mul_pow`.-/
theorem isNonzeroScalarTimesSquare_of_sq_eq_scalar_mul_odd_pow
    {p a : K[X]} {c : K} {n : ℕ}
    (hc : c ≠ 0) (ha : a ≠ 0) (hodd : Odd n)
    (hsq : p ^ 2 = C c * a ^ n) :
    IsNonzeroScalarTimesSquare a := by
  obtain ⟨eps, h, _lam, heps, _hlam, haSquare, _hpRoot⟩ :=
    scalar_times_square_and_odd_root_of_sq_eq_scalar_mul_pow hc ha hodd hsq
  exact ⟨eps, h, heps, haSquare⟩

section ParityDecomposition

variable {L : Type*} [Field L]

/-- The quadratic generator used for even/odd decomposition.-/
def parityQuadratic (eps F : L) : L[X] :=
  C eps * X ^ 2 + C F

theorem natDegree_parityQuadratic {eps F : L} (heps : eps ≠ 0) :
    (parityQuadratic eps F).natDegree = 2 := by
  simpa [parityQuadratic] using
    (natDegree_quadratic (b := (0 : L)) (c := F) heps)

theorem leadingCoeff_parityQuadratic {eps F : L} (heps : eps ≠ 0) :
    (parityQuadratic eps F).leadingCoeff = eps := by
  simpa [parityQuadratic] using
    (leadingCoeff_quadratic (b := (0 : L)) (c := F) heps)

/-- Every polynomial is the sum of a polynomial in `eps*X^2+F` and `X`
times another polynomial in that quadratic.-/
theorem exists_comp_parityQuadratic_add_X_mul_comp
    (R : L[X]) {eps F : L} (heps : eps ≠ 0) :
    ∃ H B : L[X],
      R = H.comp (parityQuadratic eps F) +
        X * (B.comp (parityQuadratic eps F)) := by
  let q := parityQuadratic eps F
  have hqdegree : q.natDegree = 2 := natDegree_parityQuadratic heps
  have hqlead : q.leadingCoeff = eps := leadingCoeff_parityQuadratic heps
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hqdegree
    omega
  have descend : ∀ n : ℕ, ∀ S : L[X], S.natDegree = n →
      ∃ H B : L[X], S = H.comp q + X * (B.comp q) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hdegree
        by_cases hn : n = 0
        · have hSconstant : S = C (S.coeff 0) := by
            apply eq_C_of_natDegree_eq_zero
            rw [hdegree, hn]
          refine ⟨C (S.coeff 0), 0, ?_⟩
          rw [hSconstant]
          simp
        · have hSne : S ≠ 0 := by
            intro hzero
            rw [hzero, natDegree_zero] at hdegree
            exact hn hdegree.symm
          obtain heven | hodd := Nat.even_or_odd n
          · rcases heven with ⟨m, hneven⟩
            let mu : L := S.leadingCoeff / eps ^ m
            have hmu : mu ≠ 0 := by
              dsimp [mu]
              exact div_ne_zero (leadingCoeff_ne_zero.mpr hSne)
                (pow_ne_zero _ heps)
            let model : L[X] := C mu * q ^ m
            let tail : L[X] := S - model
            have hmodel_ne : model ≠ 0 := by
              dsimp [model]
              exact mul_ne_zero (C_ne_zero.mpr hmu) (pow_ne_zero _ hqne)
            have hmodel_natDegree : model.natDegree = S.natDegree := by
              dsimp [model]
              rw [natDegree_mul (C_ne_zero.mpr hmu) (pow_ne_zero _ hqne),
                natDegree_C, zero_add, natDegree_pow, hqdegree, hdegree,
                hneven]
              omega
            have hmodel_leadingCoeff : model.leadingCoeff = S.leadingCoeff := by
              dsimp [model, mu]
              rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow, hqlead]
              field_simp
            have hmodel_degree : model.degree = S.degree := by
              rw [degree_eq_natDegree hmodel_ne, degree_eq_natDegree hSne,
                hmodel_natDegree]
            have htail_degree : tail.degree < S.degree := by
              dsimp [tail]
              exact degree_sub_lt_left hmodel_degree.symm hSne
                hmodel_leadingCoeff.symm
            have htail_natDegree : tail.natDegree < n := by
              by_cases htail : tail = 0
              · simp [htail, Nat.pos_of_ne_zero hn]
              · apply (natDegree_lt_iff_degree_lt htail).mpr
                rw [degree_eq_natDegree hSne, hdegree] at htail_degree
                exact htail_degree
            obtain ⟨H, B, htail_repr⟩ :=
              ih tail.natDegree htail_natDegree tail rfl
            refine ⟨H + monomial m mu, B, ?_⟩
            calc
              S = tail + model := by simp [tail]
              _ = (H.comp q + X * (B.comp q)) + C mu * q ^ m := by
                rw [htail_repr]
              _ = (H + monomial m mu).comp q + X * (B.comp q) := by
                rw [add_comp, monomial_comp]
                ring
          · rcases hodd with ⟨m, hnodd⟩
            let mu : L := S.leadingCoeff / eps ^ m
            have hmu : mu ≠ 0 := by
              dsimp [mu]
              exact div_ne_zero (leadingCoeff_ne_zero.mpr hSne)
                (pow_ne_zero _ heps)
            let core : L[X] := C mu * q ^ m
            let model : L[X] := X * core
            let tail : L[X] := S - model
            have hcore_ne : core ≠ 0 := by
              dsimp [core]
              exact mul_ne_zero (C_ne_zero.mpr hmu) (pow_ne_zero _ hqne)
            have hmodel_ne : model ≠ 0 := by
              dsimp [model]
              exact mul_ne_zero X_ne_zero hcore_ne
            have hcore_natDegree : core.natDegree = 2 * m := by
              dsimp [core]
              rw [natDegree_mul (C_ne_zero.mpr hmu) (pow_ne_zero _ hqne),
                natDegree_C, zero_add, natDegree_pow, hqdegree]
              omega
            have hmodel_natDegree : model.natDegree = S.natDegree := by
              dsimp [model]
              rw [natDegree_X_mul hcore_ne, hcore_natDegree, hdegree, hnodd]
            have hcore_leadingCoeff : core.leadingCoeff = S.leadingCoeff := by
              dsimp [core, mu]
              rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow, hqlead]
              field_simp
            have hmodel_leadingCoeff : model.leadingCoeff = S.leadingCoeff := by
              dsimp [model]
              rw [leadingCoeff_mul, leadingCoeff_X, one_mul,
                hcore_leadingCoeff]
            have hmodel_degree : model.degree = S.degree := by
              rw [degree_eq_natDegree hmodel_ne, degree_eq_natDegree hSne,
                hmodel_natDegree]
            have htail_degree : tail.degree < S.degree := by
              dsimp [tail]
              exact degree_sub_lt_left hmodel_degree.symm hSne
                hmodel_leadingCoeff.symm
            have htail_natDegree : tail.natDegree < n := by
              by_cases htail : tail = 0
              · simp [htail, Nat.pos_of_ne_zero hn]
              · apply (natDegree_lt_iff_degree_lt htail).mpr
                rw [degree_eq_natDegree hSne, hdegree] at htail_degree
                exact htail_degree
            obtain ⟨H, B, htail_repr⟩ :=
              ih tail.natDegree htail_natDegree tail rfl
            refine ⟨H, B + monomial m mu, ?_⟩
            calc
              S = tail + model := by simp [tail]
              _ = (H.comp q + X * (B.comp q)) + X * (C mu * q ^ m) := by
                rw [htail_repr]
              _ = H.comp q + X * ((B + monomial m mu).comp q) := by
                rw [add_comp, monomial_comp]
                ring
  simpa only [q] using descend R.natDegree R rfl

/-- In any parity decomposition of a polynomial of odd degree `2*m+1`, the
odd coefficient has degree `m`; its leading coefficient is determined by the
leading coefficient of the original polynomial.-/
theorem odd_degree_parityDecomposition_control
    {R H B : L[X]} {eps F lam : L} {m : ℕ}
    (heps : eps ≠ 0)
    (hrepr : R = H.comp (parityQuadratic eps F) +
      X * (B.comp (parityQuadratic eps F)))
    (hdegree : R.natDegree = 2 * m + 1)
    (hlead : R.leadingCoeff = lam) :
    B.natDegree = m ∧ B.leadingCoeff = lam / eps ^ m := by
  let q := parityQuadratic eps F
  let evenPart := H.comp q
  let oddPart := X * (B.comp q)
  have hrepr' : R = evenPart + oddPart := by
    simpa only [q, evenPart, oddPart] using hrepr
  have hqdegree : q.natDegree = 2 := natDegree_parityQuadratic heps
  have hqlead : q.leadingCoeff = eps := leadingCoeff_parityQuadratic heps
  have hqdegree_ne : q.natDegree ≠ 0 := by omega
  have hBne : B ≠ 0 := by
    intro hzero
    have hRdegreeEven : R.natDegree = H.natDegree * 2 := by
      rw [hrepr, hzero]
      simp [natDegree_comp, natDegree_parityQuadratic heps]
    rw [hdegree] at hRdegreeEven
    omega
  have hBcompne : B.comp q ≠ 0 := by
    intro hzero
    rcases comp_eq_zero_iff.mp hzero with hBzero | ⟨_, hqconstant⟩
    · exact hBne hBzero
    · have hdegrees := congrArg natDegree hqconstant
      rw [hqdegree] at hdegrees
      simp at hdegrees
  have hevenDegree : evenPart.natDegree = H.natDegree * 2 := by
    dsimp [evenPart]
    rw [natDegree_comp, hqdegree]
  have hoddDegree : oddPart.natDegree = B.natDegree * 2 + 1 := by
    dsimp [oddPart]
    rw [natDegree_X_mul hBcompne, natDegree_comp, hqdegree]
  have hdegrees_ne : evenPart.natDegree ≠ oddPart.natDegree := by
    rw [hevenDegree, hoddDegree]
    omega
  obtain heven_lt_odd | hodd_lt_even := lt_or_gt_of_ne hdegrees_ne
  · have hRdegreeOdd : R.natDegree = oddPart.natDegree := by
      rw [hrepr']
      exact natDegree_add_eq_right_of_natDegree_lt heven_lt_odd
    have hBdegree : B.natDegree = m := by
      rw [hdegree, hoddDegree] at hRdegreeOdd
      omega
    have hRleadOdd : R.leadingCoeff = oddPart.leadingCoeff := by
      rw [hrepr']
      exact leadingCoeff_add_of_degree_lt (degree_lt_degree heven_lt_odd)
    have hoddLead :
        oddPart.leadingCoeff = B.leadingCoeff * eps ^ B.natDegree := by
      dsimp [oddPart]
      rw [leadingCoeff_mul, leadingCoeff_X, one_mul,
        leadingCoeff_comp hqdegree_ne, hqlead]
    have hmul : B.leadingCoeff * eps ^ m = lam := by
      calc
        B.leadingCoeff * eps ^ m = oddPart.leadingCoeff := by
          rw [hoddLead, hBdegree]
        _ = R.leadingCoeff := hRleadOdd.symm
        _ = lam := hlead
    exact ⟨hBdegree, (eq_div_iff (pow_ne_zero _ heps)).2 hmul⟩
  · have hRdegreeEven : R.natDegree = evenPart.natDegree := by
      rw [hrepr']
      exact natDegree_add_eq_left_of_natDegree_lt hodd_lt_even
    rw [hdegree, hevenDegree] at hRdegreeEven
    omega

/-- Existence together with the exact odd-part degree and leading
coefficient for an input of degree `2*m+1`.-/
theorem exists_comp_parityQuadratic_add_X_mul_comp_of_odd_degree
    (R : L[X]) {eps F lam : L} {m : ℕ}
    (heps : eps ≠ 0)
    (hdegree : R.natDegree = 2 * m + 1)
    (hlead : R.leadingCoeff = lam) :
    ∃ H B : L[X],
      R = H.comp (parityQuadratic eps F) +
        X * (B.comp (parityQuadratic eps F)) ∧
      B.natDegree = m ∧ B.leadingCoeff = lam / eps ^ m := by
  obtain ⟨H, B, hrepr⟩ :=
    exists_comp_parityQuadratic_add_X_mul_comp R heps
  obtain ⟨hBdegree, hBlead⟩ :=
    odd_degree_parityDecomposition_control heps hrepr hdegree hlead
  exact ⟨H, B, hrepr, hBdegree, hBlead⟩

/-- The even/odd decomposition relative to `eps*X^2+F` is unique.-/
theorem parityDecomposition_unique
    {H B H' B' : L[X]} {eps F : L} (heps : eps ≠ 0)
    (heq : H.comp (parityQuadratic eps F) +
        X * (B.comp (parityQuadratic eps F)) =
      H'.comp (parityQuadratic eps F) +
        X * (B'.comp (parityQuadratic eps F))) :
    H = H' ∧ B = B' := by
  let q := parityQuadratic eps F
  let A := H - H'
  let D := B - B'
  have hqdegree : q.natDegree = 2 := natDegree_parityQuadratic heps
  have hqnotconstant : q ≠ C (q.coeff 0) := by
    intro hconstant
    have hdegrees := congrArg natDegree hconstant
    rw [hqdegree] at hdegrees
    simp at hdegrees
  have comp_ne_zero : ∀ {T : L[X]}, T ≠ 0 → T.comp q ≠ 0 := by
    intro T hT hcomp
    rcases comp_eq_zero_iff.mp hcomp with hzero | ⟨_, hconstant⟩
    · exact hT hzero
    · exact hqnotconstant hconstant
  have hzero : A.comp q + X * (D.comp q) = 0 := by
    calc
      A.comp q + X * (D.comp q) =
          (H.comp q + X * (B.comp q)) -
            (H'.comp q + X * (B'.comp q)) := by
              dsimp [A, D]
              rw [sub_comp, sub_comp]
              ring
      _ = 0 := by
        apply sub_eq_zero.mpr
        simpa only [q] using heq
  have hA : A = 0 := by
    by_contra hAne
    have hAcompne := comp_ne_zero hAne
    by_cases hD : D = 0
    · apply hAcompne
      simpa [hD] using hzero
    · have hDcompne := comp_ne_zero hD
      have hequal : A.comp q = -(X * (D.comp q)) := by
        linear_combination hzero
      have hdegrees := congrArg natDegree hequal
      rw [natDegree_comp, hqdegree, natDegree_neg,
        natDegree_X_mul hDcompne, natDegree_comp, hqdegree] at hdegrees
      omega
  have hD : D = 0 := by
    have hproduct : X * (D.comp q) = 0 := by
      simpa [hA] using hzero
    have hcomp : D.comp q = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left X_ne_zero
    by_contra hDne
    exact (comp_ne_zero hDne) hcomp
  exact ⟨sub_eq_zero.mp hA, sub_eq_zero.mp hD⟩

end ParityDecomposition

section FractionFieldCentering

variable {L : Type*} [Field L]

/-- The center that removes the linear term after scaling the variable by
`h`.-/
def quadraticCenter (eps h g : L) : L :=
  g / (2 * eps * h)

/-- The inverse affine substitution `y = (U-rho)/h`.-/
def centeredAffineSubstitution (h rho : L) : L[X] :=
  C h⁻¹ * (X - C rho)

theorem natDegree_centeredAffineSubstitution
    {h rho : L} (hh : h ≠ 0) :
    (centeredAffineSubstitution h rho).natDegree = 1 := by
  have hnormal : centeredAffineSubstitution h rho =
      C h⁻¹ * X + C (-h⁻¹ * rho) := by
    simp [centeredAffineSubstitution]
    ring
  rw [hnormal]
  exact natDegree_linear (inv_ne_zero hh)

theorem leadingCoeff_centeredAffineSubstitution
    {h rho : L} (hh : h ≠ 0) :
    (centeredAffineSubstitution h rho).leadingCoeff = h⁻¹ := by
  have hnormal : centeredAffineSubstitution h rho =
      C h⁻¹ * X + C (-h⁻¹ * rho) := by
    simp [centeredAffineSubstitution]
    ring
  rw [hnormal]
  exact leadingCoeff_linear (inv_ne_zero hh)

/-- The constant term left after completing the square.-/
def quadraticCenteredResidual (eps rho f : L) : L :=
  f - eps * rho ^ 2

@[simp]
theorem derivative_centeredAffineSubstitution (h rho : L) :
    derivative (centeredAffineSubstitution h rho) = C h⁻¹ := by
  simp [centeredAffineSubstitution]

/-- Chain rule for the inverse affine substitution.-/
theorem derivative_comp_centeredAffineSubstitution
    (R : L[X]) (h rho : L) :
    derivative (R.comp (centeredAffineSubstitution h rho)) =
      C h⁻¹ * (derivative R).comp (centeredAffineSubstitution h rho) := by
  rw [derivative_comp, derivative_centeredAffineSubstitution]

/-- Completion of the square after the invertible affine substitution
`y = (U-rho)/h`.-/
theorem quadratic_comp_centeredAffineSubstitution
    {eps h : L} (g f : L) (htwo : (2 : L) ≠ 0)
    (heps : eps ≠ 0) (hh : h ≠ 0) :
    (C (eps * h ^ 2) * X ^ 2 + C g * X + C f).comp
        (centeredAffineSubstitution h (quadraticCenter eps h g)) =
      parityQuadratic eps
        (quadraticCenteredResidual eps (quadraticCenter eps h g) f) := by
  let rho := quadraticCenter eps h g
  let z := centeredAffineSubstitution h rho
  have hcenter : 2 * eps * h * rho = g := by
    dsimp [rho, quadraticCenter]
    field_simp
  have hz : C h * z = X - C rho := by
    dsimp [z, centeredAffineSubstitution]
    calc
      C h * (C h⁻¹ * (X - C rho)) = C (h * h⁻¹) * (X - C rho) := by
        rw [C_mul]
        ring
      _ = X - C rho := by rw [mul_inv_cancel₀ hh, C_1, one_mul]
  have hquadratic : C (eps * h ^ 2) * z ^ 2 =
      C eps * (C h * z) ^ 2 := by
    rw [C_mul, C_pow]
    ring
  have hlinear : C g * z = C (2 * eps * rho) * (C h * z) := by
    rw [← hcenter]
    simp only [map_mul]
    ring
  change (C (eps * h ^ 2) * X ^ 2 + C g * X + C f).comp z =
    parityQuadratic eps (quadraticCenteredResidual eps rho f)
  simp only [add_comp, mul_comp, pow_comp, C_comp, X_comp]
  rw [hquadratic, hlinear, hz]
  simp only [parityQuadratic, quadraticCenteredResidual]
  have hClinear : C (2 * eps * rho) = 2 * C eps * C rho := by
    rw [C_mul, C_mul, C_ofNat]
  have hCresidual : C (f - eps * rho ^ 2) =
      C f - C eps * C rho ^ 2 := by
    simp [map_sub, map_mul, map_pow]
  rw [hClinear, hCresidual]
  ring

end FractionFieldCentering

section FractionRingTransport

/-- Embed a polynomial in `K[x]` into its fraction field.-/
def toPolynomialFractionField (p : K[X]) : FractionRing K[X] :=
  algebraMap K[X] (FractionRing K[X]) p

/-- Map the coefficients of a polynomial in `K[x][y]` into `Frac(K[x])`.-/
def mapToPolynomialFractionField (P : K[X][Y]) :
    (FractionRing K[X])[X] :=
  P.map (algebraMap K[X] (FractionRing K[X]))

/-- The center `g/(2*eps*h)` in `Frac(K[x])`.-/
def fractionQuadraticCenter (eps : K) (h g : K[X]) : FractionRing K[X] :=
  quadraticCenter
    (toPolynomialFractionField (C eps))
    (toPolynomialFractionField h)
    (toPolynomialFractionField g)

/-- The inverse source substitution over `Frac(K[x])`.-/
def fractionCenteredAffineSubstitution (eps : K) (h g : K[X]) :
    (FractionRing K[X])[X] :=
  centeredAffineSubstitution
    (toPolynomialFractionField h)
    (fractionQuadraticCenter eps h g)

/-- The centered residual in `Frac(K[x])`.-/
def fractionQuadraticCenteredResidual
    (eps : K) (h g f : K[X]) : FractionRing K[X] :=
  quadraticCenteredResidual
    (toPolynomialFractionField (C eps))
    (fractionQuadraticCenter eps h g)
    (toPolynomialFractionField f)

/-- Map coefficients into `Frac(K[x])` and then apply the inverse affine
source substitution.-/
def fractionAffineTransport
    (eps : K) (h g : K[X]) (P : K[X][Y]) : (FractionRing K[X])[X] :=
  (mapToPolynomialFractionField P).comp
    (fractionCenteredAffineSubstitution eps h g)

/-- After mapping coefficients into `Frac(K[x])` and applying
`y = (U-rho)/h`, a quadratic with leading coefficient `eps*h^2` becomes
`eps*U^2+F`.-/
theorem map_variableQuadraticCoordinate_comp_fractionCenteredAffineSubstitution
    [CharZero K] {eps : K} {h g f : K[X]}
    (heps : eps ≠ 0) (hh : h ≠ 0) :
    fractionAffineTransport eps h g
        (variableQuadraticCoordinate (C eps * h ^ 2) g f) =
      parityQuadratic (toPolynomialFractionField (C eps))
        (fractionQuadraticCenteredResidual eps h g f) := by
  have hepsFraction : toPolynomialFractionField (C eps) ≠ 0 := by
    simpa [toPolynomialFractionField] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne
        (C_ne_zero.mpr heps)
  have hhFraction : toPolynomialFractionField h ≠ 0 := by
    simpa [toPolynomialFractionField] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne hh
  have htwoPolynomial : (2 : K[X]) ≠ 0 := by norm_num
  have htwoFraction : (2 : FractionRing K[X]) ≠ 0 := by
    intro hzero
    apply htwoPolynomial
    apply IsFractionRing.injective K[X] (FractionRing K[X])
    rw [map_ofNat, map_zero]
    exact hzero
  simpa [fractionAffineTransport, mapToPolynomialFractionField,
    variableQuadraticCoordinate,
    fractionCenteredAffineSubstitution, fractionQuadraticCenter,
    fractionQuadraticCenteredResidual, toPolynomialFractionField,
    map_mul, map_pow] using
    (quadratic_comp_centeredAffineSubstitution
      (L := FractionRing K[X])
      (toPolynomialFractionField g) (toPolynomialFractionField f)
      htwoFraction hepsFraction hhFraction)

/-- The parity decomposition instantiated over `Frac(K[x])` for the affine
transport of an arbitrary first coordinate.-/
theorem exists_fractionAffineTransport_parityDecomposition
    [CharZero K] {eps : K} {h g f : K[X]}
    (P : K[X][Y]) (heps : eps ≠ 0) :
    ∃ H B : (FractionRing K[X])[X],
      fractionAffineTransport eps h g P =
        H.comp
            (parityQuadratic (toPolynomialFractionField (C eps))
              (fractionQuadraticCenteredResidual eps h g f)) +
          X *
            (B.comp
              (parityQuadratic (toPolynomialFractionField (C eps))
                (fractionQuadraticCenteredResidual eps h g f))) := by
  have hepsFraction : toPolynomialFractionField (C eps) ≠ 0 := by
    simpa [toPolynomialFractionField] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne
        (C_ne_zero.mpr heps)
  exact exists_comp_parityQuadratic_add_X_mul_comp
    (fractionAffineTransport eps h g P) hepsFraction

/-- Re-express the parity decomposition using the transported quadratic
coordinate itself as the generator.-/
theorem exists_fractionAffineTransport_comp_transformedQuadratic
    [CharZero K] {eps : K} {h g f : K[X]}
    (P : K[X][Y]) (heps : eps ≠ 0) (hh : h ≠ 0) :
    ∃ H B : (FractionRing K[X])[X],
      fractionAffineTransport eps h g P =
        H.comp
            (fractionAffineTransport eps h g
              (variableQuadraticCoordinate (C eps * h ^ 2) g f)) +
          X *
            (B.comp
              (fractionAffineTransport eps h g
                (variableQuadraticCoordinate (C eps * h ^ 2) g f))) := by
  obtain ⟨H, B, hrepr⟩ :=
    exists_fractionAffineTransport_parityDecomposition
      (f := f) P heps
  refine ⟨H, B, ?_⟩
  rw [map_variableQuadraticCoordinate_comp_fractionCenteredAffineSubstitution
    heps hh]
  exact hrepr

/-- Transport of formal differentiation in the source variable.  This is the
`U`-derivative part of the transformed Jacobian; differentiating the
`Frac(K[x])` coefficients with respect to `x` is a separate derivation.-/
theorem derivative_fractionAffineTransport
    (eps : K) (h g : K[X]) (P : K[X][Y]) :
    derivative (fractionAffineTransport eps h g P) =
      C (toPolynomialFractionField h)⁻¹ *
        (mapToPolynomialFractionField (yDerivative P)).comp
          (fractionCenteredAffineSubstitution eps h g) := by
  rw [fractionAffineTransport, derivative_comp,
    fractionCenteredAffineSubstitution,
    derivative_centeredAffineSubstitution]
  rw [yDerivative_apply, mapToPolynomialFractionField, derivative_map]
  rfl

/-- The invertible affine source substitution preserves `y`-degree after
passing to `Frac(K[x])`.-/
theorem natDegree_fractionAffineTransport
    (eps : K) {h g : K[X]} (P : K[X][Y]) (hh : h ≠ 0) :
    (fractionAffineTransport eps h g P).natDegree = P.natDegree := by
  have hinjective := IsFractionRing.injective K[X] (FractionRing K[X])
  rw [fractionAffineTransport, natDegree_comp,
    mapToPolynomialFractionField,
    natDegree_map_eq_of_injective hinjective,
    fractionCenteredAffineSubstitution,
    natDegree_centeredAffineSubstitution]
  · simp
  · simpa [toPolynomialFractionField] using hh

/-- Exact leading-coefficient scaling under the inverse affine source
substitution.-/
theorem leadingCoeff_fractionAffineTransport
    (eps : K) {h g : K[X]} (P : K[X][Y]) (hh : h ≠ 0) :
    (fractionAffineTransport eps h g P).leadingCoeff =
      toPolynomialFractionField P.leadingCoeff *
        (toPolynomialFractionField h)⁻¹ ^ P.natDegree := by
  have hinjective := IsFractionRing.injective K[X] (FractionRing K[X])
  have hhFraction : toPolynomialFractionField h ≠ 0 := by
    simpa [toPolynomialFractionField] using hinjective.ne hh
  rw [fractionAffineTransport,
    leadingCoeff_comp (by
      rw [fractionCenteredAffineSubstitution,
        natDegree_centeredAffineSubstitution hhFraction]
      omega),
    mapToPolynomialFractionField,
    leadingCoeff_map_of_injective hinjective,
    fractionCenteredAffineSubstitution,
    leadingCoeff_centeredAffineSubstitution hhFraction,
    natDegree_map_eq_of_injective hinjective]
  rfl

/-- A leading coefficient of the form `lam*h^n` becomes the scalar `lam`
after the inverse affine substitution.-/
theorem leadingCoeff_fractionAffineTransport_of_shape
    (eps : K) {h g : K[X]} (P : K[X][Y]) {lam : K}
    (hh : h ≠ 0)
    (hlead : P.leadingCoeff = C lam * h ^ P.natDegree) :
    (fractionAffineTransport eps h g P).leadingCoeff =
      toPolynomialFractionField (C lam) := by
  rw [leadingCoeff_fractionAffineTransport eps P hh, hlead]
  simp only [toPolynomialFractionField, map_mul, map_pow]
  have hhFraction :
      algebraMap K[X] (FractionRing K[X]) h ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne hh
  calc
    (algebraMap K[X] (FractionRing K[X]) (C lam) *
          algebraMap K[X] (FractionRing K[X]) h ^ P.natDegree) *
        (algebraMap K[X] (FractionRing K[X]) h)⁻¹ ^ P.natDegree =
      algebraMap K[X] (FractionRing K[X]) (C lam) *
        ((algebraMap K[X] (FractionRing K[X]) h) ^ P.natDegree *
          (algebraMap K[X] (FractionRing K[X]) h)⁻¹ ^ P.natDegree) := by
            ring
    _ = algebraMap K[X] (FractionRing K[X]) (C lam) := by
      rw [← mul_pow, mul_inv_cancel₀ hhFraction, one_pow, mul_one]

end FractionRingTransport

@[simp]
theorem yDerivative_variableQuadraticCoordinate (a g f : K[X]) :
    yDerivative (variableQuadraticCoordinate a g f) =
      C (C (2 : K) * a) * Y + C g := by
  simp [variableQuadraticCoordinate, yDerivative_apply, derivative_pow]
  ring

@[simp]
theorem xDerivative_variableQuadraticCoordinate (a g f : K[X]) :
    xDerivative (variableQuadraticCoordinate a g f) =
      C (derivative a) * Y ^ 2 + C (derivative g) * Y + C (derivative f) := by
  simp [variableQuadraticCoordinate, Derivation.leibniz]

theorem natDegree_variableQuadraticCoordinate {a g f : K[X]} (ha : a ≠ 0) :
    (variableQuadraticCoordinate a g f).natDegree = 2 := by
  exact natDegree_quadratic ha

theorem leadingCoeff_variableQuadraticCoordinate {a g f : K[X]} (ha : a ≠ 0) :
    (variableQuadraticCoordinate a g f).leadingCoeff = a := by
  exact leadingCoeff_quadratic ha

/-- The coefficient of the Jacobian one step above the `y`-degree of `P`.
Only the leading coefficient of `P` and the quadratic coefficient `a` occur.-/
theorem coeff_natDegree_succ_jacobian_variableQuadraticCoordinate
    (P : K[X][Y]) (a g f : K[X]) :
    (jacobian P (variableQuadraticCoordinate a g f)).coeff
        (P.natDegree + 1) =
      C (2 : K) * derivative P.leadingCoeff * a -
        C (P.natDegree : K) * P.leadingCoeff * derivative a := by
  by_cases hn : P.natDegree = 0
  · rw [hn]
    simp only [Nat.zero_add, Nat.cast_zero, C_0, zero_mul]
    rw [jacobian, xDerivative_variableQuadraticCoordinate,
      yDerivative_variableQuadraticCoordinate, coeff_sub]
    simp only [mul_add, coeff_add, ← mul_assoc, coeff_mul_X, coeff_mul_C,
      coeff_xDerivative, yDerivative_apply, coeff_derivative]
    have hP1 : P.coeff 1 = 0 := by
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    have hP2 : P.coeff 2 = 0 := by
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hP1, hP2]
    simp only [map_zero, zero_mul, Nat.cast_one, add_zero]
    rw [show P.coeff 0 = P.leadingCoeff by simpa [hn] using P.coeff_natDegree]
    have hquadraticTerm :
        (derivative P * C (derivative a) * Y ^ 2).coeff 1 = 0 := by
      rw [pow_two, ← mul_assoc, coeff_mul_X, coeff_mul_X_zero]
    rw [hquadraticTerm]
    ring
  · obtain ⟨n, hnP⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hnP]
    rw [jacobian, xDerivative_variableQuadraticCoordinate,
      yDerivative_variableQuadraticCoordinate, coeff_sub]
    simp only [mul_add, coeff_add, ← mul_assoc, pow_two, coeff_mul_X,
      coeff_mul_C, coeff_xDerivative, yDerivative_apply, coeff_derivative]
    have hlead : P.coeff (n + 1) = P.leadingCoeff := by
      simpa [hnP] using P.coeff_natDegree
    have hnext : P.coeff (n + 1 + 1) = 0 := by
      simpa [hnP] using P.coeff_natDegree_succ_eq_zero
    have hnext2 : P.coeff (n + 1 + 1 + 1) = 0 := by
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hlead, hnext, hnext2]
    simp only [map_zero, zero_mul, add_zero]
    push_cast
    rw [map_add]
    simp only [map_one, map_natCast]
    ring

/-- A constant Jacobian makes the top coefficient identity vanish.-/
theorem leadingCoeff_differential_eq_of_constant_jacobian
    (P : K[X][Y]) (a g f : K[X]) (k : K)
    (hjac : jacobian P (variableQuadraticCoordinate a g f) = CC k) :
    C (2 : K) * derivative P.leadingCoeff * a =
      C (P.natDegree : K) * P.leadingCoeff * derivative a := by
  have hcoeff := congrArg
    (fun R : K[X][Y] => R.coeff (P.natDegree + 1)) hjac
  rw [coeff_natDegree_succ_jacobian_variableQuadraticCoordinate] at hcoeff
  have hrhs : (CC k).coeff (P.natDegree + 1) = 0 := by
    simp
  exact sub_eq_zero.mp (hcoeff.trans hrhs)

/-- If the `y`-degree of `P` is a positive even number `2*r`, its leading
coefficient is a scalar multiple of `a^r`.  This is the algebraic input for
subtracting a scalar multiple of `Q^r` in the even-degree descent.-/
theorem leadingCoeff_eq_C_mul_pow_of_even_natDegree [CharZero K]
    {P : K[X][Y]} {a g f : K[X]} {k : K} {r : ℕ}
    (ha : a ≠ 0) (hr : r ≠ 0)
    (hdegree : P.natDegree = 2 * r)
    (hjac : jacobian P (variableQuadraticCoordinate a g f) = CC k) :
    ∃ lam : K, P.leadingCoeff = C lam * a ^ r := by
  have htop :=
    leadingCoeff_differential_eq_of_constant_jacobian P a g f k hjac
  rw [hdegree] at htop
  have htwo : (2 : K) ≠ 0 := by norm_num
  have htwoC : C (2 : K) ≠ (0 : K[X]) := C_ne_zero.mpr htwo
  have hscaled :
      C (2 : K) * (derivative P.leadingCoeff * a) =
        C (2 : K) *
          (C (r : K) * P.leadingCoeff * derivative a) := by
    calc
      C (2 : K) * (derivative P.leadingCoeff * a) =
          C ((2 * r : ℕ) : K) * P.leadingCoeff * derivative a := by
            simpa only [mul_assoc] using htop
      _ = C (2 : K) *
          (C (r : K) * P.leadingCoeff * derivative a) := by
            push_cast
            rw [map_mul]
            ring
  have hreduced : derivative P.leadingCoeff * a =
      C (r : K) * P.leadingCoeff * derivative a := by
    exact mul_left_cancel₀ htwoC hscaled
  exact eq_C_mul_pow_of_differential_eq ha hr hreduced

/-- At odd `y`-degree, the square of the leading coefficient is a nonzero
scalar multiple of the corresponding power of the quadratic coefficient.
This is the differential identity whose UFD factorization should imply
`IsNonzeroScalarTimesSquare a`.-/
theorem leadingCoeff_sq_eq_C_mul_pow_of_odd_natDegree [CharZero K]
    {P : K[X][Y]} {a g f : K[X]} {k : K}
    (ha : a ≠ 0) (hodd : Odd P.natDegree)
    (hjac : jacobian P (variableQuadraticCoordinate a g f) = CC k) :
    ∃ c : K, c ≠ 0 ∧
      P.leadingCoeff ^ 2 = C c * a ^ P.natDegree := by
  have hn : P.natDegree ≠ 0 := Nat.ne_of_gt hodd.pos
  have htop :=
    leadingCoeff_differential_eq_of_constant_jacobian P a g f k hjac
  have hsquareDifferential :
      derivative (P.leadingCoeff ^ 2) * a =
        C (P.natDegree : K) * P.leadingCoeff ^ 2 * derivative a := by
    rw [derivative_pow]
    simp only [Nat.reduceSubDiff, pow_one]
    calc
      C (2 : K) * P.leadingCoeff * derivative P.leadingCoeff * a =
          P.leadingCoeff *
            (C (2 : K) * derivative P.leadingCoeff * a) := by ring
      _ = P.leadingCoeff *
          (C (P.natDegree : K) * P.leadingCoeff * derivative a) := by
            rw [htop]
      _ = C (P.natDegree : K) * P.leadingCoeff ^ 2 * derivative a := by
            ring
  obtain ⟨c, hc⟩ :=
    eq_C_mul_pow_of_differential_eq ha hn hsquareDifferential
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hn
    exact hn rfl
  have hlead : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hPne
  have hcne : c ≠ 0 := by
    intro hzero
    have hsquareZero : P.leadingCoeff ^ 2 = 0 := by
      simpa [hzero] using hc
    exact (pow_ne_zero 2 hlead) hsquareZero
  exact ⟨c, hcne, hc⟩

/-- The UFD consequence of the odd-degree leading-coefficient identity.  The
quadratic coefficient is a nonzero scalar times a square, and the leading
coefficient of `P` is a nonzero scalar times the matching odd power of the
same square root.-/
theorem odd_natDegree_quadraticCoeff_and_leadingCoeff_shape [CharZero K]
    {P : K[X][Y]} {a g f : K[X]} {k : K}
    (ha : a ≠ 0) (hodd : Odd P.natDegree)
    (hjac : jacobian P (variableQuadraticCoordinate a g f) = CC k) :
    ∃ eps : K, ∃ h : K[X], ∃ lam : K,
      eps ≠ 0 ∧ lam ≠ 0 ∧
      a = C eps * h ^ 2 ∧
      P.leadingCoeff = C lam * h ^ P.natDegree := by
  obtain ⟨c, hc, hsq⟩ :=
    leadingCoeff_sq_eq_C_mul_pow_of_odd_natDegree ha hodd hjac
  exact scalar_times_square_and_odd_root_of_sq_eq_scalar_mul_pow
    hc ha hodd hsq

/-- Repeated target shears remove every positive even `y`-degree from the
first coordinate.  A nonzero constant Jacobian excludes degree zero, so the
terminal residual has odd `y`-degree.-/
theorem exists_target_shear_add_odd_residual [CharZero K]
    {P : K[X][Y]} {a g f : K[X]} {k : K}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hjac : jacobian P (variableQuadraticCoordinate a g f) = CC k) :
    ∃ H : K[X], ∃ R : K[X][Y],
      P = (H.map C).comp (variableQuadraticCoordinate a g f) + R ∧
      jacobian R (variableQuadraticCoordinate a g f) = CC k ∧
      Odd R.natDegree := by
  let Q := variableQuadraticCoordinate a g f
  have descend : ∀ n : ℕ, ∀ R : K[X][Y], R.natDegree = n →
      jacobian R Q = CC k →
      ∃ H : K[X], ∃ S : K[X][Y],
        R = (H.map C).comp Q + S ∧ jacobian S Q = CC k ∧
        Odd S.natDegree := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro R hdegree hRjac
        by_cases hn : n = 0
        · have hRconstant : R = C (R.coeff 0) := by
            apply eq_C_of_natDegree_eq_zero
            rw [hdegree, hn]
          have htop :=
            leadingCoeff_differential_eq_of_constant_jacobian R a g f k (by
              simpa only [Q] using hRjac)
          have htopzero :
              C (2 : K) * derivative R.leadingCoeff * a = 0 := by
            simpa [hdegree, hn] using htop
          have htwo : (2 : K) ≠ 0 := by norm_num
          have htwoC : C (2 : K) ≠ (0 : K[X]) := C_ne_zero.mpr htwo
          have hderivative : derivative R.leadingCoeff = 0 := by
            rcases mul_eq_zero.mp htopzero with hleft | haright
            · exact (mul_eq_zero.mp hleft).resolve_left htwoC
            · exact (ha haright).elim
          have hcoeff : R.coeff 0 = R.leadingCoeff := by
            simpa [hdegree, hn] using R.coeff_natDegree
          have hRjaczero : jacobian R Q = 0 := by
            rw [hRconstant]
            have hcoeffDerivative : derivative (R.coeff 0) = 0 := by
              rw [hcoeff]
              exact hderivative
            simp [jacobian, hcoeffDerivative]
          have hkCC : CC k ≠ (0 : K[X][Y]) :=
            C_ne_zero.mpr (C_ne_zero.mpr hk)
          exact (hkCC (hRjac.symm.trans hRjaczero)).elim
        · obtain heven | hodd := Nat.even_or_odd n
          · rcases heven with ⟨r, hneven⟩
            have hr : r ≠ 0 := by
              intro hrzero
              subst r
              simp at hneven
              exact hn hneven
            have hdegreeEven : R.natDegree = 2 * r := by
              rw [hdegree, hneven]
              omega
            obtain ⟨lam, hlamodel⟩ :=
              leadingCoeff_eq_C_mul_pow_of_even_natDegree ha hr hdegreeEven (by
                simpa only [Q] using hRjac)
            have hRne : R ≠ 0 := by
              intro hzero
              rw [hzero, natDegree_zero] at hdegree
              exact hn hdegree.symm
            have hlam : lam ≠ 0 := by
              intro hlamzero
              have hleadzero : R.leadingCoeff = 0 := by
                simp [hlamodel, hlamzero]
              exact (leadingCoeff_ne_zero.mpr hRne) hleadzero
            let model : K[X][Y] := CC lam * Q ^ r
            let tail : K[X][Y] := R - model
            have hQdegree : Q.natDegree = 2 := by
              exact natDegree_variableQuadraticCoordinate ha
            have hQne : Q ≠ 0 := by
              intro hzero
              rw [hzero, natDegree_zero] at hQdegree
              omega
            have hmodel_ne : model ≠ 0 := by
              dsimp [model]
              exact mul_ne_zero (C_ne_zero.mpr (C_ne_zero.mpr hlam))
                (pow_ne_zero _ hQne)
            have hmodel_natDegree : model.natDegree = R.natDegree := by
              dsimp [model]
              rw [natDegree_mul (C_ne_zero.mpr (C_ne_zero.mpr hlam))
                  (pow_ne_zero _ hQne), natDegree_C, zero_add, natDegree_pow,
                hQdegree, hdegreeEven]
              omega
            have hmodel_leadingCoeff : model.leadingCoeff = R.leadingCoeff := by
              dsimp [model]
              rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow,
                show Q.leadingCoeff = a by
                  exact leadingCoeff_variableQuadraticCoordinate ha]
              exact hlamodel.symm
            have hmodel_degree : model.degree = R.degree := by
              rw [degree_eq_natDegree hmodel_ne, degree_eq_natDegree hRne,
                hmodel_natDegree]
            have htail_degree : tail.degree < R.degree := by
              dsimp [tail]
              exact degree_sub_lt_left hmodel_degree.symm hRne
                hmodel_leadingCoeff.symm
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
            obtain ⟨H, S, htail_repr, hSjac, hSodd⟩ :=
              ih tail.natDegree htail_natDegree tail rfl htail_jac
            refine ⟨H + monomial r lam, S, ?_, hSjac, hSodd⟩
            calc
              R = tail + model := by simp [tail]
              _ = ((H.map C).comp Q + S) + CC lam * Q ^ r := by
                rw [htail_repr]
              _ = (((H + monomial r lam).map C).comp Q) + S := by
                rw [Polynomial.map_add, add_comp, map_monomial, monomial_comp]
                ring
          · refine ⟨0, R, ?_, hRjac, ?_⟩
            · simp
            · rw [hdegree]
              exact hodd
  exact descend P.natDegree P rfl hjac

end JacobianTwo.VariableLeadingQuadratic
