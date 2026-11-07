/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/
module

public import Tengoku

public import Tengoku.Seed.Algebra.Polynomial.BigOperators
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# ArkLib-Specific Bivariate Polynomial Extensions

The core bivariate polynomial definitions and degree/eval/multiplicity theory are provided
by CompPoly (`CompPoly.ToMathlib.Polynomial.BivariateDegree`, `BivariateWeightedDegree`,
`BivariateMultiplicity`). This file contains only ArkLib-specific extensions:

- Finset-level coefficient and evaluation helpers (`coeffs`, `evalSetX`, `evalSetY`)
- Quotient (divisibility) predicates and degree bounds
- Linear-map monomial constructors (`monomialY`, `monomialXY`) and their algebra
-/

@[expose] public section

open Polynomial
open Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type} [Semiring F]

/-- The set of coefficients of a bivariate polynomial.-/
def coeffs [DecidableEq F] (f : F[X][Y]) : Finset F[X] := f.support.image f.coeff

/-- A bivariate polynomial is non-zero if and only if its coefficient function is non-zero.-/
@[grind =_]
lemma ne_zero_iff_coeffs_ne_zero (f : F[X][Y]) : f ≠ 0 ↔ f.coeff ≠ 0 :=
  ⟨
    fun hf ↦ by have f_finsupp : f.toFinsupp ≠ 0 := by aesop
                simpa [Polynomial.coeff],
    fun f_coeffs ↦ by intro h; exact f_coeffs (by subst h; ext; simp)
  ⟩

/-- The set of `Y`-degrees is non-empty.-/
lemma degreesY_nonempty {f : F[X][Y]} (hf : f ≠ 0) : (f.toFinsupp.coeff.support).Nonempty := by
  rw [Polynomial.support_toFinsupp]
  exact Polynomial.support_nonempty.mpr hf

variable {f : F[X][Y]}

attribute [local grind] Finsupp.support_nonempty_iff natDegree_mul_le degree_eq_bot
                        WithBot.bot_lt_coe isMaxOn_iff sup_eq_of_isMaxOn monomial_eq_monomial_iff
attribute [local grind ←] toFinsupp_eq_zero
attribute [local grind _=_] Finsupp.mem_support_iff toFinsupp_apply smul_monomial
attribute [local grind =] natDegree_mul natDegree_add_eq_right_of_degree_lt
                          natDegree_zero

theorem natDegree_sum_lt_of_forall_lt {F : Type} [Semiring F]
    {α : Type} {s : Finset α} {g : α → F[X]} {deg : ℕ} :
  0 < deg → (∀ x ∈ s, (g x).natDegree < deg) → (∑ x ∈ s, g x).natDegree < deg := by
  intro deg_pos h
  have hle : (∑ x ∈ s, g x).natDegree ≤ Nat.pred deg := by
    refine Polynomial.natDegree_sum_le_of_forall_le (s := s) (f := g) (n := Nat.pred deg) ?_
    intro x hx
    exact Nat.le_pred_of_lt (h x hx)
  exact lt_of_le_of_lt hle (Nat.pred_lt_self deg_pos)

theorem natDeg_sum_eq_of_unique {α : Type} {s : Finset α} {f : α → F[X]} {deg : ℕ}
    (mx : α) (h : mx ∈ s) :
    (f mx).natDegree = deg →
    (∀ y ∈ s, y ≠ mx → (f y).natDegree < deg ∨ f y = 0) →
    (∑ x ∈ s, f x).natDegree = deg := by
  classical
  intro hmxdeg others
  by_cases hdeg0 : deg = 0
  · have hothers0 : ∀ y ∈ s, y ≠ mx → f y = 0 := by
      intro y hy hne
      have h' := others y hy hne
      rcases h' with hlt | hy0
      · simp [hdeg0] at hlt
      · exact hy0
    have hsum : (∑ x ∈ s, f x) = f mx := by
      classical
      refine Finset.sum_eq_single_of_mem mx h ?_?
      intro y hy hne
      exact hothers0 y hy hne
    calc
      (∑ x ∈ s, f x).natDegree = (f mx).natDegree := by simp [hsum]
      _ = deg := hmxdeg
  · have deg_pos : 0 < deg := Nat.pos_of_ne_zero hdeg0
    have hlt_sum : (∑ x ∈ s \ {mx}, f x).natDegree < deg := by
      refine natDegree_sum_lt_of_forall_lt (s := s \ {mx}) (g := f) (deg := deg) deg_pos ?_
      intro y hy
      have hy_s : y ∈ s := (Finset.mem_sdiff.mp hy).1
      have hy_not : y ∉ ({mx} : Finset α) := (Finset.mem_sdiff.mp hy).2
      have hy_ne : y ≠ mx := by
        simpa [Finset.mem_singleton] using hy_not
      have h' := others y hy_s hy_ne
      rcases h' with hlt | hy0
      · exact hlt
      · simpa [hy0] using deg_pos
    have hlt_mx : (∑ x ∈ s \ {mx}, f x).natDegree < (f mx).natDegree := by
      simpa [hmxdeg] using hlt_sum
    have hsum_decomp : (∑ x ∈ s, f x) = (∑ x ∈ s \ {mx}, f x) + f mx := by
      classical
      simpa using (Finset.sum_eq_sum_sdiff_singleton_add (f := f) h)
    calc
      (∑ x ∈ s, f x).natDegree = ((∑ x ∈ s \ {mx}, f x) + f mx).natDegree := by
        simp [hsum_decomp]
      _ = (f mx).natDegree := by
        exact Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt_mx
      _ = deg := hmxdeg

/-- If some element `x ∈ s` maps to `y` under `f`, and every element of `s` maps to a value
less than or equal to `y`, then the supremum of `f` over `s` is exactly `y`.-/
lemma sup_eq_of_le_of_reach {α β : Type} [SemilatticeSup β] [OrderBot β] {s : Finset α} {f : α → β}
    (x : α) {y : β} (h : x ∈ s) :
    f x = y →
    (∀ x ∈ s, f x ≤ y) →
    s.sup f = y := by
  grind

/-- The bivariate quotient polynomial.-/
def quotient (f g : F[X][Y]) : Prop := ∃ q : F[X][Y], g = q * f

/-- The quotient of two non-zero bivariate polynomials is non-zero.-/
@[grind .]
lemma quotient_nezero {f q : F[X][Y]} (hg : q * f ≠ 0) : q ≠ 0 := by by_contra h; apply hg; simp [h]

/-- If a non-zero bivariate polynomial `f` divides a non-zero bivariate polynomial `g`, then
all the coefficients of the quoetient are non-zero.-/
@[grind .]
lemma coeff_ne_zero {f q : F[X][Y]} (hg : q * f ≠ 0) : q.coeff ≠ 0 :=
  (ne_zero_iff_coeffs_ne_zero q).1 (quotient_nezero hg)

/-
If `q * f ≠ 0`, then the `X`-degree of `q` is bounded above by the difference of the
`X`-degrees: `degreeX q ≤ degreeX (q * f) - degreeX f`.
-/

/-
If `q * f ≠ 0`, then the `Y`-degree of `q` is bounded above by the difference of the
`Y`-degrees: `natDegreeY q ≤ natDegreeY (q * f) - natDegreeY f`.
-/

/-- Definition of a monomial when the bivariate polynomial is considered as a univariate
polynomial in `Y`.-/
def monomialY (n : ℕ) : F[X] →ₗ[F[X]] F[X][Y] where
  toFun t := Polynomial.monomial n t
  map_add' x y := by simp
  map_smul' r x := by simp only [RingHom.id_apply, Polynomial.smul_monomial]

/-- Definition of the bivariate monomial `X^n * Y^m`-/
def monomialXY (n m : ℕ) : F →ₗ[F] F[X][Y] where
  toFun t := Polynomial.monomial m (Polynomial.monomial n t)
  map_add' x y := by simp
  map_smul' x y := by simp only [RingHom.id_apply, Polynomial.smul_monomial]

/-- The bivariate monomial is well-defined.-/
@[grind _=_]
theorem monomialXY_def {n m : ℕ} {a : F} :
    monomialXY n m a = Polynomial.monomial m (Polynomial.monomial n a) := by
  rfl

/-- Adding bivariate monomials works as expected.
In particular, `(a + b) * X^n * Y^m = a * X^n * Y^m + b * X^n * Y^m`.-/
@[simp, grind =]
theorem monomialXY_add {n m : ℕ} {a b : F} :
    monomialXY n m (a + b) = monomialXY n m a + monomialXY n m b :=
  (monomialXY n m).map_add _ _

/-- Multiplying bivariate monomials works as expected.
In particular, `(a * X^n * Y^m) * (b * X^p * Y^q) = (a * b) * X^(n+p) * Y^(m+q)`.-/
@[grind _=_]
theorem monomialXY_mul_monomialXY {n m p q : ℕ} {a b : F} :
    monomialXY n m a * monomialXY p q b = monomialXY (n + p) (m + q) (a * b) :=
  by simp only [monomialXY_def, Polynomial.monomial_mul_monomial]

/-- Taking a bivariate monomial to a power works as expected.
In particular, ` (a * X^n * Y^m)^k = (a^k) * X^(n * k) * Y^(m * k)`.-/
@[simp, grind _=_]
theorem monomialXY_pow {n m k : ℕ} {a : F} :
    monomialXY n m a ^ k = monomialXY (n * k) (m * k) (a ^ k) := by
  simp [monomialXY]

/-- Multiplying a bivariate monomial by a scalar works as expected.
In particular, ` b * a * X^n * Y^m = b * (a * X^n * Y^m)`.-/
@[simp, grind _=_]
theorem smul_monomialXY {n m : ℕ} {a : F} {S} [SMulZeroClass S F] {b : S} :
    monomialXY n m (b • a) = b • monomialXY n m a := by
  grind [monomialXY]

/-- A bivariate monimial `a * X^n * Y^m` is equal to zero if and only if `a = 0`.-/
@[simp, grind =]
theorem monomialXY_eq_zero_iff {n m : ℕ} {a : F} : monomialXY n m a = 0 ↔ a = 0 := by
  simp [monomialXY]

/-- Two bivariate monomials `a * X^n * Y^m` and `b * X^p * Y^q` are equal if and only if `a = b`
`n = p` and `m = q` or if both are zero, i.e., `a = b = 0`.-/
@[grind =]
theorem monomialXY_eq_monomialXY_iff {n m p q : ℕ} {a b : F} :
    monomialXY n m a = monomialXY p q b ↔ n = p ∧ m = q ∧ a = b ∨ a = 0 ∧ b = 0 := by
  aesop (add simp [monomialXY, Polynomial.monomial_eq_monomial_iff])

end

end Polynomial.Bivariate
