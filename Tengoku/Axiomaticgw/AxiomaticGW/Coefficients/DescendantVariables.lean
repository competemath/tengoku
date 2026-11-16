/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Coefficients.Novikov
public import Tengoku.Seed.RingTheory.MvPowerSeries.Basic
public import Tengoku.Seed.Tactic.Ring

import Tengoku.Seed.Algebra.MvPolynomial.PDeriv
import Tengoku.Seed.RingTheory.MvPowerSeries.Trunc

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descendant variables

The variable `(k, alpha)` records the insertion `tau_k(phi_alpha)`. Formal
partial differentiation is defined coefficientwise on multivariable power
series.
-/

@[expose] public section

namespace AxiomaticGW

/-- Index of a descendant variable: cotangent power and state-space basis
label.-/
abbrev DescendantVariable (BasisIndex : Type*) := ℕ × BasisIndex

/-- A Novikov-valued formal potential in a chosen variable type.-/
abbrev FormalPotential {B : Type*} [AddCancelCommMonoid B]
    (D : EffectiveCurveMonoid B) (Vars R : Type*) :=
  MvPowerSeries Vars (NovikovSeries D R)

namespace MvPowerSeries

variable {Vars R : Type*} [CommRing R]

/-- Formal partial derivative with respect to one multivariable-series
variable.-/
noncomputable def pderiv (v : Vars) :
    MvPowerSeries Vars R →ₗ[R] MvPowerSeries Vars R where
  toFun f n := (n v + 1) • f (n + Finsupp.single v 1)
  map_add' f g := by
    ext n
    change (n v + 1) •
        (f (n + Finsupp.single v 1) + g (n + Finsupp.single v 1)) =
      (n v + 1) • f (n + Finsupp.single v 1) +
        (n v + 1) • g (n + Finsupp.single v 1)
    exact nsmul_add _ _ _
  map_smul' r f := by
    ext n
    change (n v + 1) • (r * f (n + Finsupp.single v 1)) =
      r * ((n v + 1) • f (n + Finsupp.single v 1))
    simp only [nsmul_eq_mul]
    ring

@[simp]
theorem pderiv_apply (v : Vars) (f : MvPowerSeries Vars R)
    (n : Vars →₀ ℕ) :
    pderiv v f n = (n v + 1) • f (n + Finsupp.single v 1) := rfl

@[simp]
theorem pderiv_zero (v : Vars) : pderiv v (0 : MvPowerSeries Vars R) = 0 :=
  map_zero (pderiv v)

@[simp]
theorem pderiv_add (v : Vars) (f g : MvPowerSeries Vars R) :
    pderiv v (f + g) = pderiv v f + pderiv v g :=
  map_add (pderiv v) f g

section PDerivMul

/-- Local decidable equality used only by finite polynomial truncations.-/
private noncomputable local instance pderivDecidableEq : DecidableEq Vars :=
  Classical.decEq Vars

private theorem coeff_pderiv_trunc' (v : Vars)
    (f : MvPowerSeries Vars R) (n N : Vars →₀ ℕ)
    (hN : n + Finsupp.single v 1 ≤ N) :
    (MvPolynomial.pderiv v (MvPowerSeries.trunc' R N f)).coeff n =
      pderiv v f n := by
  classical
  rw [MvPolynomial.coeff_pderiv, MvPowerSeries.coeff_trunc', ite_eq_left hN]
  simp only [MvPowerSeries.coeff_apply, pderiv_apply, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_comm]

private theorem coeff_pderiv_mul_trunc' (v : Vars)
    (f g : MvPowerSeries Vars R) (n : Vars →₀ ℕ) :
    (MvPolynomial.pderiv v
        (MvPowerSeries.trunc' R (n + Finsupp.single v 1) f *
          MvPowerSeries.trunc' R (n + Finsupp.single v 1) g)).coeff n =
      pderiv v (f * g) n := by
  classical
  rw [MvPolynomial.coeff_pderiv,
    MvPowerSeries.coeff_trunc'_mul_trunc'_eq_coeff_mul
      (n + Finsupp.single v 1) f g le_rfl]
  simp only [MvPowerSeries.coeff_apply, pderiv_apply, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_comm]

private theorem coeff_pderiv_trunc'_mul (v : Vars)
    (f g : MvPowerSeries Vars R) (n : Vars →₀ ℕ) :
    (MvPolynomial.pderiv v
        (MvPowerSeries.trunc' R (n + Finsupp.single v 1) f) *
      MvPowerSeries.trunc' R (n + Finsupp.single v 1) g).coeff n =
      MvPowerSeries.coeff n (pderiv v f * g) := by
  classical
  rw [MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
  have hleft : x.1 + Finsupp.single v 1 ≤
      n + Finsupp.single v 1 := by
    rw [← hsum]
    intro i
    simp only [Finsupp.add_apply]
    omega
  have hright : x.2 ≤ n + Finsupp.single v 1 := by
    rw [← hsum]
    intro i
    simp only [Finsupp.add_apply]
    omega
  rw [coeff_pderiv_trunc' v f x.1 _ hleft,
    MvPowerSeries.coeff_trunc', ite_eq_left hright]
  simp only [MvPowerSeries.coeff_apply]

private theorem coeff_mul_pderiv_trunc' (v : Vars)
    (f g : MvPowerSeries Vars R) (n : Vars →₀ ℕ) :
    (MvPowerSeries.trunc' R (n + Finsupp.single v 1) f *
      MvPolynomial.pderiv v
        (MvPowerSeries.trunc' R (n + Finsupp.single v 1) g)).coeff n =
      MvPowerSeries.coeff n (f * pderiv v g) := by
  classical
  rw [MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
  have hleft : x.1 ≤ n + Finsupp.single v 1 := by
    rw [← hsum]
    intro i
    simp only [Finsupp.add_apply]
    omega
  have hright : x.2 + Finsupp.single v 1 ≤
      n + Finsupp.single v 1 := by
    rw [← hsum]
    intro i
    simp only [Finsupp.add_apply]
    omega
  rw [MvPowerSeries.coeff_trunc', ite_eq_left hleft,
    coeff_pderiv_trunc' v g x.2 _ hright]
  simp only [MvPowerSeries.coeff_apply]

/-- Formal partial differentiation satisfies the Leibniz rule.-/
theorem pderiv_mul (v : Vars) (f g : MvPowerSeries Vars R) :
    pderiv v (f * g) = pderiv v f * g + f * pderiv v g := by
  classical
  ext n
  change pderiv v (f * g) n =
    (pderiv v f * g + f * pderiv v g) n
  rw [← coeff_pderiv_mul_trunc' v f g n, MvPolynomial.pderiv_mul,
    MvPolynomial.coeff_add, coeff_pderiv_trunc'_mul v f g n,
    coeff_mul_pderiv_trunc' v f g n]
  rfl

end PDerivMul

/-- Partial derivatives in distinct formal variables commute.-/
theorem pderiv_comm {v w : Vars} (h : v ≠ w)
    (f : MvPowerSeries Vars R) :
    pderiv v (pderiv w f) = pderiv w (pderiv v f) := by
  apply funext
  intro n
  change (n v + 1) •
      ((n + (Finsupp.single v 1 : Vars →₀ ℕ)) w + 1) •
        f (n + Finsupp.single v 1 + Finsupp.single w 1) =
    (n w + 1) •
      ((n + (Finsupp.single w 1 : Vars →₀ ℕ)) v + 1) •
        f (n + Finsupp.single w 1 + Finsupp.single v 1)
  have hindex : n + (Finsupp.single v 1 : Vars →₀ ℕ) + Finsupp.single w 1 =
      n + Finsupp.single w 1 + Finsupp.single v 1 := by
    ac_rfl
  rw [hindex]
  simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne h,
    Finsupp.single_eq_of_ne (Ne.symm h), add_zero, nsmul_eq_mul]
  ring

/-- Formal partial derivatives commute for all pairs of variables.-/
theorem pderiv_commute (v w : Vars) (f : MvPowerSeries Vars R) :
    pderiv v (pderiv w f) = pderiv w (pderiv v f) := by
  by_cases h : v = w
  · subst w
    rfl
  · exact pderiv_comm h f

/-- Apply formal partial derivatives in the order listed.-/
noncomputable def iteratedPDeriv :
    List Vars → MvPowerSeries Vars R →ₗ[R] MvPowerSeries Vars R
  | [] => LinearMap.id
  | v :: derivatives => (pderiv v).comp (iteratedPDeriv derivatives)

@[simp]
theorem iteratedPDeriv_nil (f : MvPowerSeries Vars R) :
    iteratedPDeriv ([] : List Vars) f = f := rfl

@[simp]
theorem iteratedPDeriv_cons (v : Vars) (derivatives : List Vars)
    (f : MvPowerSeries Vars R) :
    iteratedPDeriv (v :: derivatives) f =
      pderiv v (iteratedPDeriv derivatives f) := rfl

/-- Adjacent formal derivatives may be exchanged.-/
theorem iteratedPDeriv_swap (v w : Vars) (derivatives : List Vars)
    (f : MvPowerSeries Vars R) :
    iteratedPDeriv (v :: w :: derivatives) f =
      iteratedPDeriv (w :: v :: derivatives) f :=
  pderiv_commute v w (iteratedPDeriv derivatives f)

end MvPowerSeries

end AxiomaticGW
