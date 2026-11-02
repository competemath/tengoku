/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.RelativeRiemannRoch.ExamplesLCIAlgebra
import Tengoku.Seed.RingTheory.Polynomial.UniqueFactorization
import Tengoku.Seed.Algebra.MvPolynomial.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# G2E4P algebra: the three affine charts of the projective nodal cubic

`F = y²z − x³ − x²z ∈ k[x, y, z]` (`x = X₀`, `y = X₁`, `z = X₂`).  On the standard chart
`D₊(X_a)` the coordinate ring is the polynomial ring on `{j : Fin 3 // j ≠ a}` and `F`
dehomogenises to `fpoly a`:

* `a = 2` (`z = 1`): `y² − x³ − x²`, identified with `ExamplesLCI.nodal` (`fpoly_two_eq`);
* `a = 1` (`y = 1`): `(1 − x²)·z − x³`;
* `a = 0` (`x = 1`): `(y² − 1)·z − 1`.

All three are prime (`fpoly_prime`): the first by G2E4 (Eisenstein), the other two because they
are of degree one in `z` with coprime coefficients over `k[x]` (resp. `k[y]`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace ExamplesLCIProjective

open Polynomial

variable (k : Type u) [Field k]

/-- The variables of the `a`-th standard chart.-/
abbrev Chart (a : Fin 3) : Type := {j : Fin 3 // j ≠ a}

/-- The ratio `X_j / X_a` in the chart ring: `1` if `j = a`, else the variable `x_j`.-/
def rp (a j : Fin 3) : MvPolynomial (Chart a) k :=
  if h : j = a then 1 else MvPolynomial.X ⟨j, h⟩

/-- The dehomogenisation of `F = y²z − x³ − x²z` on the `a`-th chart.-/
def fpoly (a : Fin 3) : MvPolynomial (Chart a) k :=
  rp k a 1 * rp k a 1 * rp k a 2 - rp k a 0 * rp k a 0 * rp k a 0 - rp k a 0 * rp k a 0 * rp k a 2

/-! ## A two-variable chart ring is `k[u][v]` -/

/-- `u ↦ C X` (inner variable), every other variable `↦ X` (outer variable).-/
def toPP (a : Fin 3) (u : Chart a) : MvPolynomial (Chart a) k →+* Polynomial (Polynomial k) :=
  MvPolynomial.eval₂Hom (C.comp C) (fun j => if j = u then C X else X)

/-- The inverse map, `C X ↦ x_u`, `X ↦ x_v`.-/
def ofPP (a : Fin 3) (u v : Chart a) : Polynomial (Polynomial k) →+* MvPolynomial (Chart a) k :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X u))
    (MvPolynomial.X v)

/-- The chart ring `k[x_u, x_v] ≃ k[u][v]`.-/
def ppEquiv (a : Fin 3) (u v : Chart a) (huv : u ≠ v) (hc : ∀ j, j = u ∨ j = v) :
    MvPolynomial (Chart a) k ≃+* Polynomial (Polynomial k) :=
  RingEquiv.ofRingHom (toPP k a u) (ofPP k a u v)
    (by
      have inner : (toPP k a u).comp ((ofPP k a u v).comp Polynomial.C) = Polynomial.C := by
        apply Polynomial.ringHom_ext
        · intro c
          simp [toPP, ofPP]
        · simp [toPP, ofPP]
      apply Polynomial.ringHom_ext
      · intro p
        exact RingHom.congr_fun inner p
      · simp [toPP, ofPP, huv.symm])
    (by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [toPP, ofPP]
      · intro j
        rcases hc j with rfl | rfl
        · simp [toPP, ofPP]
        · simp [toPP, ofPP, huv.symm])

theorem ppEquiv_apply (a : Fin 3) (u v : Chart a) (huv : u ≠ v) (hc : ∀ j, j = u ∨ j = v)
    (p : MvPolynomial (Chart a) k) : ppEquiv k a u v huv hc p = toPP k a u p := rfl

/-! ## The three charts -/

/-- Chart variables.-/
def cv (a j : Fin 3) (h : j ≠ a) : Chart a := ⟨j, h⟩

theorem cover (a : Fin 3) (u v : Fin 3) (hu : u ≠ a) (hv : v ≠ a)
    (hall : ∀ j : Fin 3, j = a ∨ j = u ∨ j = v) :
    ∀ j : Chart a, j = cv a u hu ∨ j = cv a v hv := by
  rintro ⟨j, hj⟩
  rcases hall j with h | h | h
  · exact absurd h hj
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h

/-- `k[x, y] ≃ k[x][y]` on the chart `z = 1`.-/
def e2 : MvPolynomial (Chart 2) k ≃+* Polynomial (Polynomial k) :=
  ppEquiv k 2 (cv 2 0 (by decide)) (cv 2 1 (by decide)) (by decide)
    (cover 2 0 1 (by decide) (by decide) (by decide))

/-- `k[x, z] ≃ k[x][z]` on the chart `y = 1`.-/
def e1 : MvPolynomial (Chart 1) k ≃+* Polynomial (Polynomial k) :=
  ppEquiv k 1 (cv 1 0 (by decide)) (cv 1 2 (by decide)) (by decide)
    (cover 1 0 2 (by decide) (by decide) (by decide))

/-- `k[y, z] ≃ k[y][z]` on the chart `x = 1`.-/
def e0 : MvPolynomial (Chart 0) k ≃+* Polynomial (Polynomial k) :=
  ppEquiv k 0 (cv 0 1 (by decide)) (cv 0 2 (by decide)) (by decide)
    (cover 0 1 2 (by decide) (by decide) (by decide))

theorem e2_fpoly : e2 k (fpoly k 2) = ExamplesLCI.nodal k := by
  simp [e2, ppEquiv_apply, fpoly, rp, toPP, cv, ExamplesLCI.nodal]
  ring

theorem e1_fpoly : e1 k (fpoly k 1) = C (1 - X ^ 2) * X + C (-X ^ 3) := by
  simp [e1, ppEquiv_apply, fpoly, rp, toPP, cv]
  ring

theorem e0_fpoly : e0 k (fpoly k 0) = C (X ^ 2 - 1) * X + C (-1) := by
  simp [e0, ppEquiv_apply, fpoly, rp, toPP, cv]
  ring

/-! ## Primality -/

theorem prime_linear (a b : Polynomial k) (ha : a ≠ 0) (hab : IsCoprime a b) :
    Prime (C a * X + C b : Polynomial (Polynomial k)) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_C_mul_X_add_C ha hab.isRelPrime)

theorem fpoly_prime_two : Prime (fpoly k 2) :=
  (MulEquiv.prime_iff (e2 k)).mp (by rw [e2_fpoly]; exact ExamplesLCI.nodal_prime k)

theorem fpoly_prime_one : Prime (fpoly k 1) := by
  refine (MulEquiv.prime_iff (e1 k)).mp ?_
  rw [e1_fpoly]
  refine prime_linear k _ _ ?_ ⟨1 + X ^ 2, -X, by ring⟩
  intro h
  have := congrArg (eval 0) h
  simp at this

theorem fpoly_prime_zero : Prime (fpoly k 0) := by
  refine (MulEquiv.prime_iff (e0 k)).mp ?_
  rw [e0_fpoly]
  refine prime_linear k _ _ ?_ ⟨0, -1, by ring⟩
  intro h
  have := congrArg (eval 0) h
  simp at this

theorem fpoly_prime (a : Fin 3) : Prime (fpoly k a) := by
  fin_cases a
  · exact fpoly_prime_zero k
  · exact fpoly_prime_one k
  · exact fpoly_prime_two k

theorem fpoly_ne_zero (a : Fin 3) : fpoly k a ≠ 0 := (fpoly_prime k a).ne_zero

/-! ## The chart `z ≠ 0` meets the other charts -/

theorem not_dvd_X (α β : Polynomial k) (hβ : β ≠ 0) (hf : ¬ IsUnit (C α * X + C β)) :
    ¬ (C α * X + C β : Polynomial (Polynomial k)) ∣ X := by
  rintro ⟨q, hq⟩
  have h0 := congrArg (fun p => Polynomial.coeff p 0) hq
  simp only [coeff_X_zero, mul_coeff_zero, coeff_add, mul_zero, coeff_C_zero, zero_add] at h0
  have hq0 : q.coeff 0 = 0 := by
    rcases mul_eq_zero.mp h0.symm with h | h
    · exact absurd h hβ
    · exact h
  obtain ⟨q', rfl⟩ := X_dvd_iff.mpr hq0
  apply hf
  have h1 : (X : Polynomial (Polynomial k)) * ((C α * X + C β) * q') = X * 1 := by
    rw [mul_one]
    conv_rhs => rw [hq]
    ring
  have h2 := mul_left_cancel₀ X_ne_zero h1
  exact ⟨⟨_, q', h2, by rw [mul_comm]; exact h2⟩, rfl⟩

theorem rp_two_not_mem_one : rp k 1 2 ∉ Ideal.span {fpoly k 1} := by
  rw [Ideal.mem_span_singleton, ← map_dvd_iff (e1 k), e1_fpoly]
  have hx : e1 k (rp k 1 2) = X := by simp [e1, ppEquiv_apply, rp, toPP, cv]
  rw [hx]
  refine not_dvd_X k _ _ (by simp) ?_
  rw [← e1_fpoly]
  exact fun h => (fpoly_prime_one k).not_isUnit ((MulEquiv.isUnit_map (e1 k)).mp h)

theorem rp_two_not_mem_zero : rp k 0 2 ∉ Ideal.span {fpoly k 0} := by
  rw [Ideal.mem_span_singleton, ← map_dvd_iff (e0 k), e0_fpoly]
  have hx : e0 k (rp k 0 2) = X := by simp [e0, ppEquiv_apply, rp, toPP, cv]
  rw [hx]
  refine not_dvd_X k _ _ (by simp) ?_
  rw [← e0_fpoly]
  exact fun h => (fpoly_prime_zero k).not_isUnit ((MulEquiv.isUnit_map (e0 k)).mp h)

end ExamplesLCIProjective
