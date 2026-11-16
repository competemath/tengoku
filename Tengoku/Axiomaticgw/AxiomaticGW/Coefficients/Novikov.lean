/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Coefficients.EffectiveCurveClass
public import Tengoku.Seed.Algebra.MonoidAlgebra.Basic
public import Tengoku.Seed.LinearAlgebra.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Novikov series

For a positive locally finite effective monoid, every coefficient function is
a valid Novikov series. Multiplication is convolution over the finite set of
additive splittings of a fixed curve class.
-/

@[expose] public section

namespace AxiomaticGW

/-- The beta-preserving completed monoid ring attached to `D`.-/
def NovikovSeries {B : Type*} [AddCancelCommMonoid B]
    (_D : EffectiveCurveMonoid B) (R : Type*) :=
  B → R

namespace NovikovSeries

variable {B R : Type*} [AddCancelCommMonoid B]
  (D : EffectiveCurveMonoid B)

instance [Inhabited R] : Inhabited (NovikovSeries D R) :=
  inferInstanceAs (Inhabited (B → R))

instance [Zero R] : Zero (NovikovSeries D R) :=
  inferInstanceAs (Zero (B → R))

instance [AddMonoid R] : AddMonoid (NovikovSeries D R) :=
  inferInstanceAs (AddMonoid (B → R))

instance [AddCommMonoid R] : AddCommMonoid (NovikovSeries D R) :=
  inferInstanceAs (AddCommMonoid (B → R))

instance [AddGroup R] : AddGroup (NovikovSeries D R) :=
  inferInstanceAs (AddGroup (B → R))

instance [AddCommGroup R] : AddCommGroup (NovikovSeries D R) :=
  inferInstanceAs (AddCommGroup (B → R))

instance {K : Type*} [Semiring K] [AddCommMonoid R] [Module K R] :
    Module K (NovikovSeries D R) :=
  inferInstanceAs (Module K (B → R))

section Semiring

variable [Semiring R]

/-- Extract the coefficient of a fixed curve class.-/
def coeff (beta : B) : NovikovSeries D R →ₗ[R] R :=
  LinearMap.proj beta

/--
@isnad1 id=eq.0h5v.s7.0f3a01773e66 from=translated src=- shape=8c9a368c vocab=817926c7
-/
@[simp]
theorem coeff_apply (f : NovikovSeries D R) (beta : B) :
    coeff D beta f = f beta := rfl

/--
@isnad1 id=eq.1h5v.s7.5411e2166c0a from=translated src=- shape=b4f4660c vocab=817926c7
-/
@[ext]
theorem ext {f g : NovikovSeries D R}
    (h : ∀ beta : B, coeff D beta f = coeff D beta g) : f = g :=
  funext h

/-- A single Novikov monomial `a Q^beta`.-/
noncomputable def monomial (beta : B) : R →ₗ[R] NovikovSeries D R :=
  by
    classical
    exact LinearMap.single R (fun _ ↦ R) beta

/--
@isnad1 id=eq.0h5v.s6.bc345b28a3f5 from=translated src=- shape=d0d4a559 vocab=6e34ff3b
-/
@[simp]
theorem coeff_monomial_same (beta : B) (a : R) :
    monomial D beta a beta = a := by
  classical
  change (Pi.single beta a : B → R) beta = a
  exact Pi.single_eq_same (M := fun _ : B ↦ R) beta a

/--
@isnad1 id=eq.1h6v.s7.ae90ffa80dac from=translated src=- shape=dd69b13c vocab=2b268d63
-/
theorem coeff_monomial_ne {beta gamma : B} (h : beta ≠ gamma) (a : R) :
    coeff D beta (monomial D gamma a) = 0 := by
  classical
  change (Pi.single gamma a : B → R) beta = 0
  exact Pi.single_eq_of_ne (M := fun _ : B ↦ R) h a

noncomputable instance : One (NovikovSeries D R) :=
  ⟨monomial D 0 1⟩

noncomputable instance : AddMonoidWithOne (NovikovSeries D R) where
  natCast n := monomial D 0 n
  natCast_zero := by
    simpa only [Nat.cast_zero] using map_zero (monomial D 0)
  natCast_succ n := by
    rw [Nat.cast_succ]
    exact map_add (monomial D 0) (n : R) 1

noncomputable instance : Mul (NovikovSeries D R) :=
  ⟨fun f g beta ↦ ∑ split ∈ D.splittings beta,
    coeff D split.1 f * coeff D split.2 g⟩

/--
@isnad1 id=eq.0h6v.s8.9d4d977acaa3 from=translated src=- shape=c39f45dc vocab=8bbb3afe
-/
theorem coeff_mul (f g : NovikovSeries D R) (beta : B) :
    coeff D beta (f * g) = ∑ split ∈ D.splittings beta,
      coeff D split.1 f * coeff D split.2 g := rfl

/--
@isnad1 id=eq.0h4v.s6.05cf241540df from=translated src=- shape=ace27d1d vocab=560295d7
-/
protected theorem zero_mul (f : NovikovSeries D R) : 0 * f = 0 := by
  apply NovikovSeries.ext D
  intro beta
  rw [coeff_mul]
  change (∑ x ∈ D.splittings beta, (0 : R) * f x.2) = 0
  simp only [zero_mul, Finset.sum_const_zero]

/--
@isnad1 id=eq.0h4v.s6.8cb180c64c8d from=translated src=- shape=95ae0965 vocab=560295d7
-/
protected theorem mul_zero (f : NovikovSeries D R) : f * 0 = 0 := by
  apply NovikovSeries.ext D
  intro beta
  rw [coeff_mul]
  change (∑ x ∈ D.splittings beta, f x.1 * (0 : R)) = 0
  simp only [mul_zero, Finset.sum_const_zero]

/--
@isnad1 id=eq.0h6v.s8.e0be2009bb0b from=translated src=- shape=ec62ff32 vocab=c57133c0
-/
theorem coeff_monomial_zero_mul (a : R) (f : NovikovSeries D R) (beta : B) :
    coeff D beta (monomial D 0 a * f) = a * coeff D beta f := by
  classical
  rw [coeff_mul]
  calc
    _ = coeff D 0 (monomial D 0 a) * coeff D beta f := by
      apply Finset.sum_eq_single (0, beta)
      · intro split hsplit hne
        have hfirst : split.1 ≠ 0 := by
          intro hzero
          apply hne
          apply Prod.ext hzero
          simpa only [hzero, zero_add]
            using (D.mem_splittings split.1 split.2 beta).mp hsplit
        simp only [coeff_monomial_ne D hfirst, coeff_apply, zero_mul]
      · simp only [D.mem_splittings, zero_add, not_true_eq_false,
          coeff_apply, coeff_monomial_same, IsEmpty.forall_iff]
    _ = _ := by simp only [coeff_apply, coeff_monomial_same]

/--
@isnad1 id=eq.0h6v.s8.db19770633f6 from=translated src=- shape=33cb3ab9 vocab=c57133c0
-/
theorem coeff_mul_monomial_zero (f : NovikovSeries D R) (a : R) (beta : B) :
    coeff D beta (f * monomial D 0 a) = coeff D beta f * a := by
  classical
  rw [coeff_mul]
  calc
    _ = coeff D beta f * coeff D 0 (monomial D 0 a) := by
      apply Finset.sum_eq_single (beta, 0)
      · intro split hsplit hne
        have hsecond : split.2 ≠ 0 := by
          intro hzero
          apply hne
          apply Prod.ext
          · simpa only [hzero, add_zero]
              using (D.mem_splittings split.1 split.2 beta).mp hsplit
          · exact hzero
        simp only [coeff_apply, coeff_monomial_ne D hsecond, mul_zero]
      · simp only [D.mem_splittings, add_zero, not_true_eq_false,
          coeff_apply, coeff_monomial_same, IsEmpty.forall_iff]
    _ = _ := by simp only [coeff_apply, coeff_monomial_same]

/--
@isnad1 id=eq.0h4v.s6.35110b85bc8d from=translated src=- shape=3be19cff vocab=560295d7
-/
protected theorem one_mul (f : NovikovSeries D R) : 1 * f = f := by
  apply NovikovSeries.ext D
  intro beta
  exact coeff_monomial_zero_mul D 1 f beta |>.trans (one_mul _)

/--
@isnad1 id=eq.0h4v.s6.ac20423ef460 from=translated src=- shape=385c0cef vocab=560295d7
-/
protected theorem mul_one (f : NovikovSeries D R) : f * 1 = f := by
  apply NovikovSeries.ext D
  intro beta
  exact coeff_mul_monomial_zero D f 1 beta |>.trans (mul_one _)

/--
@isnad1 id=eq.0h6v.s7.6d4afdefd284 from=translated src=- shape=c9f9188f vocab=f6a3ab86
-/
protected theorem mul_add (f g h : NovikovSeries D R) :
    f * (g + h) = f * g + f * h := by
  apply NovikovSeries.ext D
  intro beta
  change (∑ x ∈ D.splittings beta, f x.1 * (g x.2 + h x.2)) =
    (∑ x ∈ D.splittings beta, f x.1 * g x.2) +
      ∑ x ∈ D.splittings beta, f x.1 * h x.2
  simp only [mul_add, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h6v.s7.ae07424747be from=translated src=- shape=d3c40d76 vocab=f6a3ab86
-/
protected theorem add_mul (f g h : NovikovSeries D R) :
    (f + g) * h = f * h + g * h := by
  apply NovikovSeries.ext D
  intro beta
  change (∑ x ∈ D.splittings beta, (f x.1 + g x.1) * h x.2) =
    (∑ x ∈ D.splittings beta, f x.1 * h x.2) +
      ∑ x ∈ D.splittings beta, g x.1 * h x.2
  simp only [add_mul, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h6v.s7.60a0c7ab6522 from=translated src=- shape=5f8a4544 vocab=560295d7
-/
protected theorem mul_assoc (f g h : NovikovSeries D R) :
    f * g * h = f * (g * h) := by
  apply NovikovSeries.ext D
  intro beta
  classical
  simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  apply Finset.sum_nbij'
      (fun ⟨⟨_ , j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
      (fun ⟨⟨i, _⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩)
  · intro a ha
    simp only [Finset.mem_sigma, D.mem_splittings] at ha ⊢
    rcases ha with ⟨houter, hinner⟩
    refine ⟨?_, trivial⟩
    calc
      a.2.1 + (a.2.2 + a.1.2) = (a.2.1 + a.2.2) + a.1.2 :=
        (add_assoc _ _ _).symm
      _ = a.1.1 + a.1.2 := congrArg (· + a.1.2) hinner
      _ = beta := houter
  · intro a ha
    simp only [Finset.mem_sigma, D.mem_splittings] at ha ⊢
    rcases ha with ⟨houter, hinner⟩
    refine ⟨?_, trivial⟩
    calc
      (a.1.1 + a.2.1) + a.2.2 = a.1.1 + (a.2.1 + a.2.2) :=
        add_assoc _ _ _
      _ = a.1.1 + a.1.2 := congrArg (a.1.1 + ·) hinner
      _ = beta := houter
  · intro a ha
    simp_all only [Finset.mem_sigma, D.mem_splittings, Prod.mk.eta, Sigma.eta]
  · intro a ha
    simp_all only [Finset.mem_sigma, D.mem_splittings, Prod.mk.eta, Sigma.eta]
  · intro a ha
    simp_all only [Finset.mem_sigma, D.mem_splittings, coeff_apply, mul_assoc]

noncomputable instance : Semiring (NovikovSeries D R) where
  zero_mul := NovikovSeries.zero_mul D
  mul_zero := NovikovSeries.mul_zero D
  one_mul := NovikovSeries.one_mul D
  mul_one := NovikovSeries.mul_one D
  mul_assoc := NovikovSeries.mul_assoc D
  left_distrib := NovikovSeries.mul_add D
  right_distrib := NovikovSeries.add_mul D

end Semiring

noncomputable instance [CommSemiring R] : CommSemiring (NovikovSeries D R) where
  mul_comm f g := by
    apply NovikovSeries.ext D
    intro beta
    classical
    rw [coeff_mul, coeff_mul]
    apply Finset.sum_equiv (Equiv.prodComm B B)
    · intro split
      simp only [D.mem_splittings, Equiv.prodComm_apply, Prod.fst_swap,
        Prod.snd_swap, add_comm]
    · intro split hsplit
      simp only [coeff_apply, Equiv.prodComm_apply, Prod.fst_swap,
        Prod.snd_swap, mul_comm]

noncomputable instance [Ring R] : Ring (NovikovSeries D R) where

noncomputable instance [CommRing R] : CommRing (NovikovSeries D R) where

section CommSemiring

variable [CommSemiring R]

/-- Constant series embedding.-/
noncomputable def C : R →+* NovikovSeries D R where
  toFun := monomial D 0
  map_zero' := map_zero _
  map_one' := rfl
  map_add' := map_add _
  map_mul' a b := by
    apply NovikovSeries.ext D
    intro beta
    classical
    by_cases hbeta : beta = 0
    · subst beta
      rw [coeff_monomial_zero_mul]
      simp only [coeff_apply, coeff_monomial_same]
    · rw [coeff_monomial_ne D hbeta, coeff_monomial_zero_mul,
        coeff_monomial_ne D hbeta, mul_zero]

noncomputable instance : Algebra R (NovikovSeries D R) :=
  (C D).toAlgebra

/--
@isnad1 id=eq.0h4v.s6.8d4125babe15 from=translated src=- shape=d07c51c4 vocab=d2eeff1e
-/
@[simp]
theorem coeff_C_zero (a : R) : C D a 0 = a := by
  exact coeff_monomial_same D 0 a

/--
@isnad1 id=eq.1h5v.s8.464fd9229e25 from=translated src=- shape=43a74a92 vocab=14fc16fd
-/
theorem coeff_C_ne {beta : B} (hbeta : beta ≠ 0) (a : R) :
    coeff D beta (C D a) = 0 :=
  coeff_monomial_ne D hbeta a

/--
@isnad1 id=eq.0h7v.s8.b7b86089460c from=translated src=- shape=f917c1cc vocab=05a13d52
-/
@[simp]
theorem monomial_mul_monomial (beta gamma : B) (a b : R) :
    monomial D beta a * monomial D gamma b =
      monomial D (beta + gamma) (a * b) := by
  apply NovikovSeries.ext D
  intro delta
  classical
  rw [coeff_mul]
  by_cases hdelta : delta = beta + gamma
  · subst delta
    calc
      _ = coeff D beta (monomial D beta a) *
          coeff D gamma (monomial D gamma b) := by
        apply Finset.sum_eq_single (beta, gamma)
        · intro split hsplit hne
          by_cases hfirst : split.1 = beta
          · have hsecond : split.2 ≠ gamma := by
              intro hs
              exact hne (Prod.ext hfirst hs)
            simp only [hfirst, coeff_apply, coeff_monomial_same,
              coeff_monomial_ne D hsecond, mul_zero]
          · simp only [coeff_monomial_ne D hfirst, coeff_apply, zero_mul]
        · simp only [D.mem_splittings, not_true_eq_false, coeff_apply,
            coeff_monomial_same, IsEmpty.forall_iff]
      _ = _ := by
        simp only [coeff_apply, coeff_monomial_same]
  · have hnone : (beta, gamma) ∉ D.splittings delta := by
      simpa only [D.mem_splittings] using Ne.symm hdelta
    rw [coeff_monomial_ne D hdelta]
    apply Finset.sum_eq_zero
    intro split hsplit
    by_cases hfirst : split.1 = beta
    · have hsecond : split.2 ≠ gamma := by
        intro hs
        apply hnone
        exact (D.mem_splittings beta gamma delta).mpr (by
          simpa only [hfirst, hs] using
            (D.mem_splittings split.1 split.2 delta).mp hsplit)
      simp only [hfirst, coeff_apply, coeff_monomial_same,
        coeff_monomial_ne D hsecond, mul_zero]
    · simp only [coeff_monomial_ne D hfirst, coeff_apply, zero_mul]

end CommSemiring

end NovikovSeries

end AxiomaticGW
