/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos-Fernández
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Algebra.Defs
public import Tengoku.Seed.Algebra.SkewMonoidAlgebra.Single
public import Tengoku.Seed.Algebra.SkewMonoidAlgebra.Support
/-!
# Univariate skew polynomials

Given a ring `R` and an endomorphism `φ` on `R` the skew polynomials over `R`
are polynomials
$$\sum_{i= 0}^n a_iX^n, n\geq 0, a_i\in R$$
where the addition is the usual addition of polynomials
$$\sum_{i= 0}^n a_iX^n + \sum_{i= 0}^n b_iX^n= \sum_{i= 0}^n (a_i + b_i)X^n.$$
The multiplication, however, is determined by
$$Xa = \varphi (a)X$$
by extending it to all polynomials in the obvious way.

Skew polynomials are represented as `SkewMonoidAlgebra R (Multiplicative ℕ)`,
where `R` is usually at least a Semiring. In this file, we define `SkewPolynomial`
and provide basic instances.

**Note**: To register the endomorphism `φ` see notation below.

## Notation

The endomorphism `φ` is implemented using some action of `Multiplicative ℕ` on `R`.
From this action, `φ` is an `abbrev` denoting $(\text{ofAdd } 1) \cdot a := \varphi(a)$.

Users that want to work with a specific map `φ` should introduce an action of
`Multiplicative ℕ` on `R`. Specifying that this action is a `MulSemiringAction` amounts
to saying that `φ` is an endomorphism.

Furthermore, with this notation `φ^[n](a) = (ofAdd n) • a`, see `φ_iterate_apply`.

## Main definitions

* `SkewPolynomial.monomial n a` is the skew polynomial `a X ^ n`. Note that
  `SkewPolynomial.monomial n` is defined as an `R`-linear map.
* `SkewPolynomial.C a` is the constant skew polynomial `a`. Note that `C` is defined as an additive
  homomorphism.
* `SkewPolynomial.CRingHom a` is the constant skew polynomial `a`, as a ring homomorphism. This
  requires to assume `[MulSemiringAction (Multiplicative ℕ) R]`.
* `SkewPolynomial.X` is the skew polynomial `X`, i.e., `SkewPolynomial.monomial 1 1`.
* `p.sum f` is `∑ n ∈ p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`.
* `SkewPolynomial.coeff p n` is the coefficient of `X ^ n` in `p`.
* `SkewPolynomial.erase p n` is the skew polynomial `p` in which one removes the monomial in
  degree `n`.
* `SkewPolynomial.update p n a` is the skew polynomial obtained by replacing the coefficient of
  degree `n` by a given value `a : R`.  If `a = 0`, this is equal to `p.erase n` If
  `p.natDegree < n` and `a ≠ 0`, this increases the degree of `p` to `n`.

## Implementation notes

The implementation uses `Multiplicative ℕ` instead of `ℕ`, since Mathlib does not contain an
additive version of `SkewMonoidAlgebra`.

This decision was made because we use the type class `MulSemiringAction` to specify the properties
the action needs to respect for associativity. There is no version of this in Mathlib that
uses an acting `AddMonoid M` and so we need to use `Multiplicative ℕ` for the action.

For associativity to hold, there should be an instance of
`MulSemiringAction (Multiplicative ℕ) R` present in the context.
For example, in the context of $\mathbb{F}_q$-linear polynomials, this can be the
$q$-th Frobenius endomorphism - so $\varphi(a) = a^q$.

## Reference

The definition is inspired by Chapter 3 of [Papikian2023].

## Tags

Skew Polynomials, Twisted Polynomials.

Note that [ore33] proposes a more general definition of skew polynomial ring, where the
multiplication is determined by  $Xa = \varphi (a)X + δ (a)$, where `φ` is as above and
`δ` is a derivation.

-/

@[expose] public section

noncomputable section

open Function Multiplicative SkewMonoidAlgebra

/-- The skew polynomials over `R` is the type of univariate polynomials over `R`
endowed with a skewed convolution product. -/
abbrev SkewPolynomial (R : Type*) [AddCommMonoid R] := SkewMonoidAlgebra R (Multiplicative ℕ)

namespace SkewPolynomial

variable {R : Type*} {m n : ℕ}

section Semiring

variable [Semiring R] {p q : SkewPolynomial R}


/--
@isnad1 id=eq.0h1v.s6.13ced824a908 from=seed src=0 shape=70b2b2ba vocab=6ae22f4b
-/
lemma zero_def : (0 : SkewPolynomial R) = (0 : SkewMonoidAlgebra R (Multiplicative ℕ)) := rfl

variable {S : Type*}

/--
The set of all `n` such that `X^n` has a non-zero coefficient.
-/
def support (p : SkewPolynomial R) : Finset ℕ :=
  Finset.map ⟨toAdd, toAdd.injective⟩ (SkewMonoidAlgebra.support p)

/-- Though `SkewPolynomial.support` is not definiyionally equal to `SkewMonoidAlgebra.support` we
  can relate them using the following lemma.
@isnad1 id=eq.0h2v.s5.c1549776e1bb from=seed src=0 shape=0f0a64e5 vocab=623dcdcd
-/
lemma support_eq_skewMonoidAlgebra_support (p : SkewPolynomial R) :
    p.support = Finset.map (Multiplicative.toAdd (α := ℕ)) (SkewMonoidAlgebra.support p) := by
  simp only [support]

/--
@isnad1 id=eq.0h1v.s5.75b99bd5ca5a from=seed src=0 shape=e023bc36 vocab=9fbf202c
-/
@[simp] lemma support_zero : (0 : SkewPolynomial R).support = ∅ := rfl

/--
@isnad1 id=iff.0h2v.s5.772aef5f2890 from=seed src=0 shape=463e5f66 vocab=9fbf202c
-/
@[simp] lemma support_eq_empty : p.support = ∅ ↔ p = 0 := by simp [support]

/--
@isnad1 id=iff.0h2v.s5.c975ff92a56e from=seed src=0 shape=4fd6f0f4 vocab=5c272a5c
-/
lemma card_support_eq_zero : p.support.card = 0 ↔ p = 0 := by simp

/--
@isnad1 id=le.0h3v.s6.3efaca564855 from=seed src=0 shape=5ac31341 vocab=147263f2
-/
lemma support_add : (p + q).support ⊆ p.support ∪ q.support := by
  simpa [support, ← Finset.map_union, Finset.map_subset_map] using SkewMonoidAlgebra.support_add

/-- `coeff p n` is the coefficient of `X ^ n` in `p`. -/
def coeff (p : SkewPolynomial R) : ℕ → R := fun n ↦ (SkewMonoidAlgebra.coeff p (ofAdd n))

/--
@isnad1 id=iff.0h3v.s5.03c27e2ae94e from=seed src=0 shape=b0ab6824 vocab=e78f2719
-/
@[simp]
lemma mem_support_iff : n ∈ p.support ↔ p.coeff n ≠ 0 := by
  simp [support, coeff]

/--
@isnad1 id=iff.0h3v.s5.14cfb3671956 from=seed src=0 shape=932a0875 vocab=e78f2719
-/
lemma notMem_support_iff : n ∉ p.support ↔ p.coeff n = 0 := by simp

/-- `p.sum f` is `∑ n ∈ p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`. -/
def sum {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : ℕ → R → S) : S :=
  SkewMonoidAlgebra.sum p (fun n r ↦ f (toAdd n : ℕ) r)

/-- For a skew polynomial `p`, `p.sum f` can be written in terms of `SkewMonoidAlgebra.sum p`.
@isnad1 id=eq.0h4v.s6.88413bdf77b2 from=seed src=0 shape=359ba4f1 vocab=004ab6a0
-/
lemma sum_def' {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : ℕ → R → S) :
    p.sum f = SkewMonoidAlgebra.sum p (fun n r ↦ f (toAdd n : ℕ) r) := rfl

/--
@isnad1 id=eq.0h4v.s5.0a03cbea0b8e from=seed src=0 shape=f488ee6b vocab=d37f6499
-/
lemma sum_def {S : Type*} [AddCommMonoid S] (p : SkewPolynomial R) (f : ℕ → R → S) :
    p.sum f = ∑ n ∈ p.support, f n (p.coeff n) := by
  simp only [sum_def', SkewMonoidAlgebra.sum_def, Finsupp.sum]
  apply Finset.sum_of_injOn (toAdd) (Injective.injOn fun ⦃a₁ a₂⦄ a ↦ a) (fun _ ↦ ?_) <;>
  simp +contextual [coeff]

/--
@isnad1 id=eq.2h6v.s7.59fb58a8868d from=seed src=0 shape=8c9acd45 vocab=60f6deba
-/
lemma sum_sum_index {R' P : Type*} [AddCommMonoid P] [Semiring R']
    {f : SkewPolynomial R} {g : ℕ → R → SkewPolynomial R'} {h : ℕ → R' → P}
    (h_zero : ∀ (a : ℕ), h a 0 = 0)
    (h_add : ∀ (a : ℕ) (b₁ b₂ : R'), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    sum (sum f g) h = sum f fun (a : ℕ) (b : R) ↦ sum (g a b) h := by
  simp only [sum_def', SkewMonoidAlgebra.sum_sum_index (fun a ↦ h_zero (toAdd a))
    (fun a ↦ h_add (toAdd a))]

/--
@isnad1 id=eq.0h3v.s5.3e8a3d5b1936 from=seed src=0 shape=5186a096 vocab=00465a18
-/
@[simp]
lemma sum_zero {N : Type*} [AddCommMonoid N] {f : SkewPolynomial R} :
    (f.sum fun (_ : ℕ) _ ↦ (0 : N)) = 0 :=
  SkewMonoidAlgebra.sum_zero

section Monomial

variable (n)

/-- `monomial s a` is the monomial `a * X ^ s`. -/
def monomial : R →ₗ[R] SkewPolynomial R := lsingle R (ofAdd n)

/--
@isnad1 id=eq.0h2v.s7.4483dfbd95de from=seed src=0 shape=a54770a1 vocab=c713d881
-/
lemma monomial_zero_right : monomial n (0 : R) = 0 := single_zero _

/--
@isnad1 id=eq.0h1v.s7.b289b4e60c78 from=seed src=0 shape=408062fb vocab=c713d881
-/
lemma monomial_zero_one : monomial 0 (1 : R) = 1 := rfl

/--
@isnad1 id=eq.0h3v.s7.f67584d03c3d from=seed src=0 shape=f12bcd26 vocab=18d9b522
-/
lemma monomial_def (a : R) : monomial n a = single (ofAdd n) a := rfl

/--
@isnad1 id=eq.0h4v.s8.7b9bc651adca from=seed src=0 shape=41e45037 vocab=97620994
-/
lemma monomial_add (r s : R) : monomial n (r + s) = monomial n r + monomial n s :=
  single_add ..

/--
@isnad1 id=eq.0h5v.s8.7ac2ac5440c6 from=seed src=0 shape=9da2b67e vocab=7766dbef
-/
lemma smul_monomial {S} [Semiring S] [Module S R] (a : S) (b : R) :
    a • monomial n b = monomial n (a • b) :=
  smul_single ..

/--
@isnad1 id=eq.0h2v.s7.accafb756af3 from=seed src=0 shape=f664d327 vocab=d0f5a709
-/
@[simp]
lemma sum_monomial (f : SkewPolynomial R) : f.sum (fun (a : ℕ) ↦ monomial a) = f :=
  SkewMonoidAlgebra.sum_single _

/--
@isnad1 id=eq.1h5v.s7.e8c23e8687e6 from=seed src=0 shape=40508cdf vocab=55c5539b
-/
@[simp]
lemma sum_monomial_index {N} [AddCommMonoid N] {n : ℕ} {b : R} {h : ℕ → R → N}
    (h_zero : h n 0 = 0) : (monomial n b).sum h = h n b :=
  SkewMonoidAlgebra.sum_single_index h_zero

/--
@isnad1 id=injectiv.0h2v.s6.7b299ed4255e from=seed src=0 shape=cc3a6b26 vocab=3a0ba534
-/
lemma monomial_injective : Function.Injective (monomial n : R → SkewPolynomial R) :=
  single_injective (ofAdd n)

/--
@isnad1 id=iff.0h3v.s7.eb17168f0745 from=seed src=0 shape=17b96c1d vocab=c713d881
-/
@[simp]
lemma monomial_eq_zero_iff (t : R) : monomial n t = 0 ↔ t = 0 :=
  LinearMap.map_eq_zero_iff _ (SkewPolynomial.monomial_injective n)

/--
@isnad1 id=iff.0h5v.s7.b4509e99f302 from=seed src=0 shape=c3dceb46 vocab=c713d881
-/
lemma monomial_eq_monomial_iff {m n : ℕ} {a b : R} :
    monomial m a = monomial n b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0 := by
  rw [← Finsupp.single_eq_single_iff m n a b]
  simp only [monomial_def, ← coeff_single, coeff_inj]
  simp only [← ofCoeff_single, SkewMonoidAlgebra.ofCoeff_inj, Finsupp.single_eq_single_iff,
    EmbeddingLike.apply_eq_iff_eq]

/--
@isnad1 id=var.0h5v.s7.d8eb4280ffd8 from=seed src=0 shape=7b5e3c96 vocab=e9d2e166
-/
lemma induction {motive : SkewPolynomial R → Prop} (p : SkewPolynomial R) (h0 : motive 0)
  (ha : ∀ (n : ℕ) (r : R) (q : SkewPolynomial R), n ∉ q.support → r ≠ 0 → motive q →
    motive (SkewPolynomial.monomial n r + q)) : motive p := by
  apply SkewMonoidAlgebra.induction <;> aesop

end Monomial
section phi

variable [MulSemiringAction (Multiplicative ℕ) R]

/-- Ring homomorphism associated to the twist of the skew polynomial ring.
The multiplication in a skew polynomial ring is given by `xr = φ(r)x`. -/
abbrev φ := MulSemiringAction.toRingHom (Multiplicative ℕ) R (ofAdd 1)

/--
@isnad1 id=eq.0h1v.s6.64ccc7efeda4 from=seed src=0 shape=78088c4d vocab=f8ff5461
-/
theorem φ_def : φ = MulSemiringAction.toRingHom (Multiplicative ℕ) R (ofAdd 1) := rfl

/--
@isnad1 id=eq.0h3v.s7.a7aa853caa89 from=seed src=0 shape=9dbff5b4 vocab=9d92cfdd
-/
lemma φ_iterate_apply (n : ℕ) (a : R) : (φ^[n] a) = ((ofAdd n) • a) := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp_all [MulSemiringAction.toRingHom_apply, Function.iterate_succ', -Function.iterate_succ,
      ← mul_smul, mul_comm]

end phi

/--
@isnad1 id=eq.0h5v.s8.d5b218152fbc from=seed src=0 shape=f79a6b97 vocab=ff33ec6b
-/
lemma monomial_mul_monomial [MulSemiringAction (Multiplicative ℕ) R] (n m : ℕ) (r s : R) :
    monomial n r * monomial m s = monomial (n + m) (r * (φ^[n] s)) := by
  rw [φ_iterate_apply]
  exact SkewMonoidAlgebra.single_mul_single

/--
@isnad1 id=eq.0h3v.s8.5845eac9b2be from=seed src=0 shape=921dfa4b vocab=3755a7a1
-/
lemma mul_def {f g : SkewPolynomial R} [MulSemiringAction (Multiplicative ℕ) R] : f * g =
    f.sum fun (a₁ : ℕ) b₁ ↦ g.sum fun (a₂ : ℕ) b₂ ↦ monomial (a₁ + a₂) (b₁ * φ^[a₁] b₂) := by
  ext
  simp [φ_iterate_apply, sum_def', coeff_mul, monomial, lsingle_apply, SkewMonoidAlgebra.coeff_sum']
  simp [SkewMonoidAlgebra.sum, Finsupp.single_apply]

section Constant

/-- `C a` is the constant SkewPolynomial `a`. `C` is provided as an additive homomorphism. -/
def C : R →+ SkewPolynomial R := SkewMonoidAlgebra.singleAddHom 1

variable {a b : R}

/--
@isnad1 id=eq.0h2v.s7.22ee2e5bc5c1 from=seed src=0 shape=6f930351 vocab=20a5cf43
-/
@[simp] lemma monomial_zero_left ⦃a : R⦄ : monomial 0 a = C a := rfl

/--
@isnad1 id=eq.0h1v.s7.1bb696322242 from=seed src=0 shape=759a5eb9 vocab=3a344abe
-/
lemma C_0 : C (0 : R) = 0 := single_zero _

/--
@isnad1 id=eq.0h3v.s8.13067ffa1d49 from=seed src=0 shape=048cfcd0 vocab=bea63b28
-/
lemma C_add : C (a + b) = C a + C b := C.map_add a b

/--
@isnad1 id=eq.0h1v.s7.e3427133651f from=seed src=0 shape=759a5eb9 vocab=3a344abe
-/
lemma C_1 : C (1 : R) = 1 := rfl

/--
@isnad1 id=eq.1h4v.s7.bda72ec5ab52 from=seed src=0 shape=05bb12f1 vocab=9a0903d8
-/
@[simp]
lemma sum_C_index {β} [AddCommMonoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
  (C a).sum f = f 0 a := sum_single_index h

section RingHom

variable [MulSemiringAction (Multiplicative ℕ) R]

/-- `CRingHom a` is the constant SkewPolynomial `a`, as a ring homomorphism. This requires
`[MulSemiringAction (Multiplicative ℕ) R]`. -/
def CRingHom : R →+* SkewPolynomial R := SkewMonoidAlgebra.singleOneRingHom

/--
@isnad1 id=eq.0h2v.s7.1b4b1f799cdd from=seed src=0 shape=62916e5f vocab=59f63e96
-/
lemma CRingHom_eq_C : CRingHom a = C a := rfl

/--
@isnad1 id=eq.0h3v.s8.b68377a20736 from=seed src=0 shape=7beae42c vocab=87c541dc
-/
lemma C_mul : C (a * b) = C a * C b := CRingHom.map_mul a b

/--
@isnad1 id=eq.0h3v.s8.8df63e5f5e7e from=seed src=0 shape=5974b071 vocab=a4cb48e7
-/
lemma C_pow : C (a ^ n) = C a ^ n := CRingHom.map_pow a n

/--
@isnad1 id=eq.0h2v.s7.0a7ca865393e from=seed src=0 shape=a2bca38e vocab=74efeb79
-/
lemma C_eq_natCast (n : ℕ) : C (n : R) = (n : SkewPolynomial R) := map_natCast CRingHom n

/--
@isnad1 id=eq.0h4v.s8.3e9baf30910d from=seed src=0 shape=ed06ead3 vocab=8c9d6192
-/
@[simp]
lemma C_mul_monomial : C a * monomial n b = monomial n (a * b) := by
  simp [← monomial_zero_left, monomial_mul_monomial, zero_add]

/--
@isnad1 id=eq.0h4v.s8.824f4c543d38 from=seed src=0 shape=f5b82389 vocab=e9f87ca5
-/
@[simp]
lemma monomial_mul_C : monomial n a * C b = monomial n (a * φ^[n] b) := by
  simp [← monomial_zero_left, monomial_mul_monomial, add_zero]

end RingHom

end Constant

section Variable

/-- `X` is the SkewPolynomial variable (aka indeterminate). -/
def X : SkewPolynomial R := monomial 1 1

/--
@isnad1 id=eq.0h1v.s6.30b9666d17df from=seed src=0 shape=24594b81 vocab=4e81450b
-/
lemma monomial_one_one_eq_X : monomial 1 (1 : R) = X := rfl

variable [MulSemiringAction (Multiplicative ℕ) R]

/--
@isnad1 id=eq.0h2v.s7.08a903237018 from=seed src=0 shape=7474931a vocab=c7ae9d45
-/
lemma monomial_one_right_eq_X_pow (n : ℕ) : monomial n (1 : R) = X ^ n := by
  induction n with
  | zero      => simp only [monomial_zero_left, ← CRingHom_eq_C, map_one, pow_zero]
  | succ n ih =>
    rw [pow_succ', ← ih, ← monomial_one_one_eq_X, monomial_mul_monomial]
    simp [add_comm]

/--
@isnad1 id=eq.0h2v.s8.fbe86341620f from=seed src=0 shape=2fe8416f vocab=8eb48abe
-/
lemma X_mul : X * p = sum p (fun a b ↦ monomial a (φ b)) * X := by
  simp only [X, mul_def]
  rw [sum_monomial_index (by simp), sum_sum_index (by simp) (by simp)]
  simp [add_comm]

/--
@isnad1 id=eq.0h3v.s8.bc8ddf553ba9 from=seed src=0 shape=2054dff2 vocab=124dffad
-/
lemma X_pow_mul {n : ℕ} : X ^ n * p = sum p (fun (a : ℕ) b ↦ monomial a (φ^[n] b)) * X ^ n := by
  induction n generalizing p with
  | zero      => simp only [pow_zero, one_mul, Function.iterate_zero, id_eq, sum_monomial, mul_one]
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc, X_mul, ← mul_assoc, ih, mul_assoc, ← pow_succ, sum_sum_index (by simp) (by simp)]
    simp

/--
@isnad1 id=eq.0h3v.s8.49239bb1b46f from=seed src=0 shape=7566d4b8 vocab=23cedf77
-/
@[simp]
lemma monomial_mul_X (n : ℕ) (r : R) : monomial n r * X = monomial (n + 1) r := by
  rw [← monomial_one_one_eq_X, monomial_mul_monomial, iterate_map_one, mul_one]

/--
@isnad1 id=eq.0h4v.s8.204ede598773 from=seed src=0 shape=c8664610 vocab=b52400dd
-/
@[simp]
lemma monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) : monomial n r * X ^ k = monomial (n+k) r := by
  induction k with
  | zero      => simp
  | succ n ih => simp [pow_succ, ← mul_assoc, ih, add_assoc]

/--
@isnad1 id=eq.0h3v.s8.83663237f048 from=seed src=0 shape=3d1e0325 vocab=ac15caf4
-/
@[simp]
lemma X_mul_monomial (n : ℕ) (r : R) : X * monomial n r = monomial (n+1) (φ r) := by
  simp [X_mul]

/--
@isnad1 id=eq.0h4v.s8.67527e1b9b71 from=seed src=0 shape=dd7eca1c vocab=098b1c4a
-/
@[simp]
lemma X_pow_mul_monomial (k n : ℕ) (r : R) : X ^ k * monomial n r = monomial (n + k) (φ^[k] r) := by
  simp [X_pow_mul]

end Variable

section Coefficient

variable {a b : R}

/--
@isnad1 id=eq.0h4v.s7.3d71f67624c4 from=seed src=0 shape=3de3bde1 vocab=878ff319
-/
lemma coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 :=
  SkewMonoidAlgebra.coeff_single_apply

/--
@isnad1 id=eq.0h2v.s5.cf32df43a3f9 from=seed src=0 shape=242dd53f vocab=cc587eb3
-/
@[simp] lemma coeff_zero (n : ℕ) : coeff (0 : SkewPolynomial R) n = 0 := rfl

/--
@isnad1 id=eq.0h1v.s5.1868ee08f9a7 from=seed src=0 shape=61888708 vocab=cc587eb3
-/
@[simp] lemma coeff_one_zero : coeff (1 : SkewPolynomial R) 0 = 1 := coeff_monomial

/--
@isnad1 id=eq.0h2v.s6.c3848d33a86c from=seed src=0 shape=720edede vocab=ff92fbe6
-/
lemma coeff_one [MulSemiringAction (Multiplicative ℕ) R] (n : ℕ) :
    coeff (1 : SkewPolynomial R) n = if 0 = n then 1 else 0 := by
  have : (1 : SkewPolynomial R) = monomial 0 1 := by simp [← CRingHom_eq_C]
  rw [this, coeff_monomial]

/--
@isnad1 id=eq.0h1v.s5.1598e703cd8f from=seed src=0 shape=e6ec5b5c vocab=982b827e
-/
@[simp] lemma coeff_X_one : coeff (X : SkewPolynomial R) 1 = 1 := coeff_monomial

/--
@isnad1 id=eq.0h1v.s4.19aa11d2eabe from=seed src=0 shape=e6ec5b5c vocab=982b827e
-/
@[simp] lemma coeff_X_zero : coeff (X : SkewPolynomial R) 0 = 0 := coeff_monomial

/--
@isnad1 id=eq.0h3v.s7.7dbaa39a39e4 from=seed src=0 shape=74d8cb52 vocab=cecac52a
-/
@[simp] lemma coeff_monomial_succ : coeff (monomial (n + 1) a) 0 = 0 := by simp [coeff_monomial]

/--
@isnad1 id=eq.0h2v.s5.8e47d498378a from=seed src=0 shape=fe8509e3 vocab=a61c4719
-/
lemma coeff_X : coeff (X : SkewPolynomial R) n = if 1 = n then 1 else 0 := coeff_monomial

/--
@isnad1 id=eq.1h2v.s5.b6edb4f20b80 from=seed src=0 shape=e148f3f0 vocab=982b827e
-/
lemma coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : SkewPolynomial R) n = 0 := by
  rw [coeff_X, ite_eq_right hn.symm]

/--
@isnad1 id=eq.0h3v.s7.0897ca9e7e45 from=seed src=0 shape=d18c800c vocab=2b8e338e
-/
lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 := by
  convert! coeff_monomial using 2; simp [eq_comm]

/--
@isnad1 id=eq.0h2v.s6.816bfafa25de from=seed src=0 shape=39f0848f vocab=dec7bb06
-/
@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := coeff_monomial

/--
@isnad1 id=eq.1h3v.s7.e4f4e9546c27 from=seed src=0 shape=07d72a37 vocab=dec7bb06
-/
lemma coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 := by rw [coeff_C, ite_eq_right h]

/--
@isnad1 id=eq.0h3v.s7.f3d7e7ac585b from=seed src=0 shape=a02b44a2 vocab=8ecf7dc8
-/
@[simp]
lemma coeff_C_succ {r : R} {n : ℕ} : coeff (C r) (n + 1) = 0 := by simp [coeff_C]

/--
@isnad1 id=eq.0h3v.s6.92160485ecdb from=seed src=0 shape=b3c91104 vocab=c315ebf8
-/
@[simp]
lemma coeff_natCast_ite [MulSemiringAction (Multiplicative ℕ) R] :
    (Nat.cast m : SkewPolynomial R).coeff n = ite (n = 0) m 0 := by
  simp [← C_eq_natCast, coeff_C]

/--
@isnad1 id=eq.0h2v.s6.f0fe6d70c227 from=seed src=0 shape=0dc0efc8 vocab=9ac2047e
-/
@[simp]
lemma coeff_ofNat_zero [MulSemiringAction (Multiplicative ℕ) R] (a : ℕ) [a.AtLeastTwo] :
    coeff (ofNat(a) : SkewPolynomial R) 0 = ofNat(a) := by simp [OfNat.ofNat]

/--
@isnad1 id=eq.0h3v.s6.f60b013abe2c from=seed src=0 shape=6be0e48f vocab=01b3774a
-/
@[simp]
lemma coeff_ofNat_succ [MulSemiringAction (Multiplicative ℕ) R] (a n : ℕ) [h : a.AtLeastTwo] :
    coeff (ofNat(a) : SkewPolynomial R) (n + 1) = 0 := by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]

/--
@isnad1 id=eq.0h3v.s8.2abd79511a03 from=seed src=0 shape=57ef6e32 vocab=feac11d4
-/
lemma C_mul_X_pow_eq_monomial [MulSemiringAction (Multiplicative ℕ) R] :
    ∀ ⦃n : ℕ⦄, C a * X ^ n = monomial n a
  | 0 => mul_one _
  | n + 1 => by
    rw [pow_succ, ← mul_assoc, C_mul_X_pow_eq_monomial, X, monomial_mul_monomial,
      iterate_map_one, mul_one]

/--
@isnad1 id=eq.0h2v.s8.175a12d20845 from=seed src=0 shape=ea4c44cd vocab=8bc35d8d
-/
lemma C_mul_X_eq_monomial [MulSemiringAction (Multiplicative ℕ) R] : C a * X = monomial 1 a := by
  rw [← C_mul_X_pow_eq_monomial, pow_one]

/--
@isnad1 id=injectiv.0h1v.s6.2565fc824aec from=seed src=0 shape=d6139fd5 vocab=a57ba252
-/
lemma C_injective : Injective (C : R → SkewPolynomial R) := monomial_injective 0

/--
@isnad1 id=iff.0h3v.s7.1406ae6d28dd from=seed src=0 shape=d2c36b7a vocab=3a344abe
-/
@[simp] lemma C_inj : C a = C b ↔ a = b :=
  ⟨fun h ↦ coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩

/--
@isnad1 id=iff.0h2v.s7.7ad4ebb71df0 from=seed src=0 shape=6a647082 vocab=3a344abe
-/
@[simp] lemma C_eq_zero : C a = 0 ↔ a = 0 :=
  calc C a = 0 ↔ C a = C 0 := by rw [C_0]
    _ ↔ a = 0 := C_inj

end Coefficient

/--
@isnad1 id=nontrivi.1h3v.s5.c6c0bf54ea0a from=seed src=0 shape=e90e5ea7 vocab=0ade62a9
-/
lemma Nontrivial.of_polynomial_ne [MulSemiringAction (Multiplicative ℕ) R] (h : p ≠ q) :
    Nontrivial R :=
  ⟨⟨0, 1, fun h01 : 0 = 1 ↦ h <|
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] ⟩⟩

/--
@isnad1 id=iff.0h3v.s5.8a45df630f8c from=seed src=0 shape=004abbdd vocab=538deff8
-/
lemma ext_iff {p q : SkewPolynomial R} : p = q ↔ ∀ n, coeff p n = coeff q n :=
  SkewMonoidAlgebra.ext_iff

/--
@isnad1 id=eq.1h3v.s5.c17bcd048075 from=seed src=0 shape=48e4affc vocab=538deff8
-/
@[ext] lemma ext {p q : SkewPolynomial R} : (∀ n, coeff p n = coeff q n) → p = q :=
  SkewMonoidAlgebra.ext

/--
@isnad1 id=eq.1h4v.s8.25d499657dd8 from=seed src=0 shape=4cc65f56 vocab=2b7d4326
-/
@[ext] lemma addHom_ext' {M : Type*} [AddMonoid M] {f g : SkewPolynomial R →+ M}
    (h : ∀ n, f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddMonoidHom) : f = g :=
  SkewMonoidAlgebra.addHom_ext' h

/--
@isnad1 id=eq.1h4v.s8.22ccc1eedf4b from=seed src=0 shape=3b097a22 vocab=5b7dac4f
-/
@[ext] lemma addHom_ext {M : Type*} [AddMonoid M] {f g : SkewPolynomial R →+ M}
    (h : ∀ n a, f (monomial n a) = g (monomial n a)) : f = g :=
  SkewMonoidAlgebra.addHom_ext h

/--
@isnad1 id=eq.1h4v.s8.6295d4f1dc76 from=seed src=0 shape=17d1f377 vocab=2a1254d9
-/
@[ext] lemma linearMap_ext' {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : SkewPolynomial R →ₗ[R] M} (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) :
    f = g :=
  SkewMonoidAlgebra.lhom_ext' h

lemma eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : SkewPolynomial R) : p = 0 := by
  rw [← one_smul R p, ← h, zero_smul]

section Support

/--
@isnad1 id=eq.1h3v.s7.71dcd74ef065 from=seed src=0 shape=fb3c8e08 vocab=06e0f1a3
-/
@[simp] lemma support_monomial (n) {a : R} (h : a ≠ 0) : (monomial n a).support = singleton n := by
  ext m
  simp [monomial_def, support_eq_skewMonoidAlgebra_support, h]

/--
@isnad1 id=le.0h3v.s6.92b0e10d9338 from=seed src=0 shape=f75b0aa8 vocab=c6f77fc5
-/
lemma support_monomial_subset (n) {a : R} : (monomial n a).support ⊆ singleton n := by
  simp only [monomial_def, support_eq_skewMonoidAlgebra_support]
  refine Finset.subset_map_symm.mp SkewMonoidAlgebra.support_single_subset

/--
@isnad1 id=eq.1h2v.s7.46da23beaa5f from=seed src=0 shape=f6a3ccdc vocab=7540cc58
-/
@[simp] lemma support_C {a : R} (h : a ≠ 0) : (C a).support = singleton 0 := support_monomial 0 h

/--
@isnad1 id=le.0h2v.s7.20c752b0bf64 from=seed src=0 shape=63b0cf1a vocab=ee174345
-/
lemma support_C_subset (a : R) : (C a).support ⊆ singleton 0 := support_monomial_subset 0

/--
@isnad1 id=eq.1h2v.s7.5d401b933b2d from=seed src=0 shape=515bd590 vocab=ff01d685
-/
@[simp] lemma support_C_mul_X [MulSemiringAction (Multiplicative ℕ) R] {c : R} (h : c ≠ 0) :
    support (C c * X) = singleton 1 := by
  rw [C_mul_X_eq_monomial, support_monomial 1 h]

/--
@isnad1 id=le.0h2v.s7.24dca8a64e0a from=seed src=0 shape=7486e682 vocab=5200fa81
-/
lemma support_C_mul_X_subset [MulSemiringAction (Multiplicative ℕ) R] (c : R) :
    support (C c * X) ⊆ singleton 1 := by
  simpa [C_mul_X_eq_monomial] using support_monomial_subset 1

/--
@isnad1 id=eq.1h3v.s8.0136b7613875 from=seed src=0 shape=ab3ba318 vocab=32661e38
-/
@[simp]
lemma support_C_mul_X_pow [MulSemiringAction (Multiplicative ℕ) R] (n : ℕ) {c : R} (h : c ≠ 0) :
    support (C c * X ^ n) = singleton n := by
  rw [C_mul_X_pow_eq_monomial, support_monomial n h]

/--
@isnad1 id=le.0h3v.s8.8127c5faab9c from=seed src=0 shape=95a8a49d vocab=2a41a94f
-/
lemma support_C_mul_X_pow_subset [MulSemiringAction (Multiplicative ℕ) R] (n : ℕ) (c : R) :
    support (C c * X ^ n) ⊆ singleton n := by
  simpa [C_mul_X_pow_eq_monomial] using support_monomial_subset n

open Finset
/--
@isnad1 id=le.0h5v.s9.d83bb3d83eca from=seed src=0 shape=6af84588 vocab=957e067d
-/
lemma support_binomial_subset [MulSemiringAction (Multiplicative ℕ) R] (k m : ℕ) (x y : R) :
    support (C x * X ^ k + C y * X ^ m) ⊆ {k, m} :=
  support_add.trans
    (union_subset
      ((support_C_mul_X_pow_subset k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow_subset m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

/--
@isnad1 id=le.0h7v.s9.c8b38f28479f from=seed src=0 shape=e63d8461 vocab=957e067d
-/
lemma support_trinomial_subset [MulSemiringAction (Multiplicative ℕ) R] (k m n : ℕ) (x y z : R) :
    support (C x * X ^ k + C y * X ^ m + C z * X ^ n) ⊆ {k, m, n} :=
  support_add.trans
    (union_subset
      (support_add.trans
        (union_subset
          ((support_C_mul_X_pow_subset k x).trans
            (singleton_subset_iff.mpr (mem_insert_self k {m, n})))
          ((support_C_mul_X_pow_subset m y).trans
            (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_self m {n}))))))
      ((support_C_mul_X_pow_subset n z).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n))))))

end Support

variable {a b : R}

/--
@isnad1 id=eq.0h2v.s7.3652e46059dc from=seed src=0 shape=f8798979 vocab=c7ae9d45
-/
lemma X_pow_eq_monomial (n) [MulSemiringAction (Multiplicative ℕ) R] :
    X ^ n = monomial n (1 : R) := by
  induction n with
  | zero      => simp only [pow_zero, monomial_zero_left, ← CRingHom_eq_C, map_one]
  | succ n hn =>
    rw [pow_succ', hn, X, monomial_mul_monomial]
    simp [add_comm]

/--
@isnad1 id=eq.0h3v.s7.f70e48596d12 from=seed src=0 shape=47accb60 vocab=e621e0b6
-/
lemma smul_X_eq_monomial {n} [MulSemiringAction (Multiplicative ℕ) R] :
    a • X ^ n = monomial n (a : R) := by
  rw [eq_comm]
  calc monomial n a = monomial n (a * 1) := by simp only [mul_one]
    _ = monomial n (a • 1) := by simp [mul_one, smul_eq_mul]
    _ = a • monomial n 1 := (SkewMonoidAlgebra.smul_single _ _ _).symm
    _ = a • X ^ n  := by rw [X_pow_eq_monomial]

/--
@isnad1 id=eq.0h2v.s6.03b78aadd342 from=seed src=0 shape=8447075c vocab=8bc226c5
-/
@[simp]
lemma support_X_pow [Nontrivial R] (n : ℕ) [MulSemiringAction (Multiplicative ℕ) R] :
    (X ^ n : SkewPolynomial R).support = singleton n := by
  convert support_monomial n (NeZero.out (n := (1 : R)))
  exact X_pow_eq_monomial n

/--
@isnad1 id=eq.1h1v.s5.741687644d4b from=seed src=0 shape=fd60e6a1 vocab=9b822381
-/
lemma support_X_empty (H : (1 : R) = 0) : (X : SkewPolynomial R).support = ∅ := by
  rw [X, H, monomial_zero_right, support_zero]

/--
@isnad1 id=eq.0h1v.s5.0251e167fb0d from=seed src=0 shape=673cd2de vocab=8c09723d
-/
@[simp]
lemma support_X [Nontrivial R] [MulSemiringAction (Multiplicative ℕ) R] :
    (X : SkewPolynomial R).support = singleton 1 := by
  rw [← pow_one X, support_X_pow 1]

/--
@isnad1 id=iff.1h4v.s7.3cea05baed87 from=seed src=0 shape=fdbc3ce1 vocab=c713d881
-/
lemma monomial_left_inj {R : Type*} [Semiring R] {a : R} (ha : a ≠ 0) {i j : ℕ} :
    (monomial i a) = (monomial j a) ↔ i = j :=
  SkewMonoidAlgebra.single_left_inj ha

/--
@isnad1 id=eq.0h3v.s7.7b0c4b32b84a from=seed src=0 shape=9c395c93 vocab=ee697084
-/
lemma nat_cast_mul {R : Type*} [Semiring R] (n : ℕ) (p : SkewPolynomial R)
    [MulSemiringAction (Multiplicative ℕ) R] : (n : SkewPolynomial R) * p = n • p :=
  (nsmul_eq_mul _ _).symm
section Sum

variable {S : Type*} [AddCommMonoid S]

/--
@isnad1 id=eq.2h5v.s6.9e11a60adfea from=seed src=0 shape=602f4267 vocab=8ae087eb
-/
lemma sum_eq_of_subset {p : SkewPolynomial R} (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) {s : Finset ℕ}
    (hs : p.support ⊆ s) : p.sum f = ∑ n ∈ s, f n (p.coeff n) := by
  rw [sum_def , Finset.sum_subset hs]
  intro _ _ hx
  simp only [mem_support_iff, ne_eq, not_not] at hx
  simp [hx, hf]

/--
@isnad1 id=eq.0h3v.s6.77708ccc0d40 from=seed src=0 shape=c01a9eed vocab=0ec0a806
-/
@[simp]
lemma sum_zero_index (f : ℕ → R → S) : (0 : SkewPolynomial R).sum f = 0 := by
  simp [sum_def', zero_def]

/--
@isnad1 id=eq.1h3v.s6.7678bed823ec from=seed src=0 shape=899389f1 vocab=d8d552ab
-/
@[simp]
lemma sum_X_index {f : ℕ → R → S} (hf : f 1 0 = 0) : (X : SkewPolynomial R).sum f = f 1 1 :=
  sum_monomial_index hf

/--
@isnad1 id=eq.2h5v.s7.d3e64b02cab6 from=seed src=0 shape=5d2da4f6 vocab=60f6deba
-/
lemma sum_add_index (p q : SkewPolynomial R) (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0)
    (h_add : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
    (p + q).sum f = p.sum f + q.sum f := by
  simp only [sum_def']
  exact SkewMonoidAlgebra.sum_add_index (fun n _ ↦ hf (toAdd n)) (fun n _ ↦ h_add (toAdd n))

/-- See also `SkewPolynomial.sum_add`.
@isnad1 id=eq.0h5v.s6.dd0af24fcac9 from=seed src=0 shape=30f83620 vocab=f7d83d6f
-/
@[simp]
lemma sum_add' (p : SkewPolynomial R) (f g : ℕ → R → S) : p.sum (f + g) = p.sum f + p.sum g := by
  simp [sum_def, Finset.sum_add_distrib]

/-- See also `SkewPolynomial.sum_add'`.
@isnad1 id=eq.0h5v.s6.40b141b6d50d from=seed src=0 shape=5148c640 vocab=f7d83d6f
-/
@[simp]
lemma sum_add (p : SkewPolynomial R) (f g : ℕ → R → S) :
    (p.sum fun n x ↦ f n x + g n x) = p.sum f + p.sum g :=
  sum_add' _ _ _

/-- See also `SkewPolynomial.sum_smul_index'` for a version using `smul` on the RHS.
@isnad1 id=eq.1h5v.s7.974969f81ea3 from=seed src=0 shape=36d6d2ac vocab=55d41f16
-/
lemma sum_smul_index (p : SkewPolynomial R) (b : R) (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) :
    (b • p).sum f = p.sum fun n a ↦ f n (b * a) :=
  Finsupp.sum_smul_index hf

/-- See also `SkewPolynomial.sum_smul_index` for a version using multiplication on the RHS.
@isnad1 id=eq.1h6v.s7.2a6211561e10 from=seed src=0 shape=20c90625 vocab=d2cbb610
-/
lemma sum_smul_index' {T : Type*} [DistribSMul T R] (p : SkewPolynomial R) (b : T) (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum fun n a ↦ f n (b • a) :=
  Finsupp.sum_smul_index' hf

/--
@isnad1 id=eq.0h6v.s6.7581db81339e from=seed src=0 shape=d59f6e07 vocab=04377cf7
-/
protected lemma smul_sum {T : Type*} [DistribSMul T S] (p : SkewPolynomial R) (b : T)
    (f : ℕ → R → S) : b • p.sum f = p.sum fun n a ↦ b • f n a :=
  Finsupp.smul_sum

end Sum

/--
@isnad1 id=eq.0h4v.s6.7d6ddb20f9cf from=seed src=0 shape=58dae8f8 vocab=a1c7119e
-/
@[simp]
lemma coeff_add (p q : SkewPolynomial R) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n := by
  simp [coeff]

end Semiring

section Ring

variable [Ring R] {a b : R}

/--
@isnad1 id=eq.0h4v.s6.3d1d2a8f9f1e from=seed src=0 shape=1461cf8f vocab=71b6afb1
-/
@[simp] lemma sum_neg {S : Type*} [Ring S] (p : SkewPolynomial R) (f : ℕ → R → S) :
    (p.sum fun n x ↦ - f n x) = - p.sum f := by
  simp [sum_def, Finset.sum_neg_distrib]

/--
@isnad1 id=eq.0h5v.s6.2e65eb1532b2 from=seed src=0 shape=e0565fff vocab=b0a78961
-/
@[simp] lemma sum_sub {S : Type*} [Ring S] (p : SkewPolynomial R) (f g : ℕ → R → S) :
    (p.sum fun n x ↦ f n x - g n x) = p.sum f - p.sum g := by
  simp only [sub_eq_add_neg, sum_add, sum_neg]

instance instRing [MulSemiringAction (Multiplicative ℕ) R] : Ring (SkewPolynomial R) :=
  SkewMonoidAlgebra.instRing

/--
@isnad1 id=eq.0h3v.s5.bd85d70892c8 from=seed src=0 shape=81d4d1ad vocab=a4f72994
-/
@[simp]
lemma coeff_neg (p : SkewPolynomial R) (n : ℕ) : coeff (-p) n = -coeff p n := by
  simp [← add_eq_zero_iff_eq_neg, ← coeff_add, neg_add_cancel p]

/--
@isnad1 id=eq.0h4v.s6.b51670b81e94 from=seed src=0 shape=58dae8f8 vocab=e4ebd3f5
-/
@[simp]
lemma coeff_sub (p q : SkewPolynomial R) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := by
  simp_rw [sub_eq_add_neg, ← coeff_neg, SkewPolynomial.coeff_add]

/--
@isnad1 id=eq.0h3v.s8.0253e0d48bb1 from=seed src=0 shape=19fc4c97 vocab=aa65184a
-/
@[simp] lemma monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -(monomial n a) := by
  rw [eq_neg_iff_add_eq_zero, ← monomial_add, neg_add_cancel, monomial_zero_right]

/--
@isnad1 id=eq.0h2v.s5.7c195a50466a from=seed src=0 shape=44c3e8dc vocab=a39023e9
-/
@[simp] lemma support_neg {p : SkewPolynomial R} : (-p).support = p.support := by
  simpa [support_eq_skewMonoidAlgebra_support] using SkewMonoidAlgebra.support_neg p

/--
@isnad1 id=eq.0h4v.s8.5d40ba95e4c5 from=seed src=0 shape=f345475f vocab=ee5da724
-/
lemma monomial_sub (n : ℕ) : monomial n (a - b) = monomial n a - monomial n b := by
  rw [sub_eq_add_neg, monomial_add, monomial_neg, sub_eq_add_neg]

variable [MulSemiringAction (Multiplicative ℕ) R]

/--
@isnad1 id=eq.0h2v.s7.413a7aedc845 from=seed src=0 shape=eefbedfc vocab=693b5133
-/
lemma C_eq_intCast (n : ℤ) : C (n : R) = n := by simp [← CRingHom_eq_C]

/--
@isnad1 id=eq.0h2v.s8.b886387c83c1 from=seed src=0 shape=d3e3b700 vocab=34c3bc98
-/
lemma C_neg : C (-a) = -C a := RingHom.map_neg CRingHom a

/--
@isnad1 id=eq.0h3v.s8.14e12ab8708f from=seed src=0 shape=7beae42c vocab=1a36fa74
-/
lemma C_sub : C (a - b) = C a - C b := RingHom.map_sub CRingHom a b

end Ring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R]

/--
@isnad1 id=nontrivi.0h1v.s3.49a791c80f97 from=seed src=0 shape=d96e9922 vocab=cb0f1829
-/
instance instNontrivial : Nontrivial (SkewPolynomial R) :=
  SkewMonoidAlgebra.instNontrivialOfNonempty

/--
@isnad1 id=ne.0h1v.s5.48dee2b263a9 from=seed src=0 shape=37fa0090 vocab=4c7db18e
-/
lemma X_ne_zero : (X : SkewPolynomial R) ≠ 0 := mt (congr_arg (fun p ↦ coeff p 1)) (by simp)

end NontrivialSemiring

section erase

variable [Semiring R]

/-- `erase p n` is the polynomial `p` in which the `X ^ n` term has been erased. -/
def erase (n : ℕ) (p : SkewPolynomial R) : SkewPolynomial R :=
  SkewMonoidAlgebra.erase (ofAdd n) p

/--
@isnad1 id=eq.0h3v.s5.78a3df1fa837 from=seed src=0 shape=36306b34 vocab=7c278c21
-/
@[simp]
lemma support_erase {p : SkewPolynomial R} (n : ℕ) :
    support (p.erase n) = (support p).erase n := by
  simp [support_eq_skewMonoidAlgebra_support, erase]

/--
@isnad1 id=eq.0h3v.s7.d09ccfc0fc83 from=seed src=0 shape=fb020d01 vocab=bd6260ad
-/
lemma monomial_add_erase (p : SkewPolynomial R) (n : ℕ) :
    monomial n (coeff p n) + p.erase n = p := by
  simp [coeff, monomial_def, erase, SkewMonoidAlgebra.single_add_erase]

/--
@isnad1 id=eq.0h4v.s5.e83274dd32c2 from=seed src=0 shape=50155e48 vocab=529ab221
-/
@[simp]
lemma coeff_erase (p : SkewPolynomial R) (n i : ℕ) :
    (p.erase n).coeff i = if i = n then 0 else p.coeff i := by
  exact ite_congr rfl (fun _ ↦ rfl) (fun _ ↦ rfl)

/--
@isnad1 id=eq.0h2v.s6.38baccceee5c from=seed src=0 shape=0836f219 vocab=a8b55a23
-/
@[simp]
lemma erase_zero (n : ℕ) : (0 : SkewPolynomial R).erase n = 0 := by
  simp [erase, zero_def]

/--
@isnad1 id=eq.0h3v.s7.9785cacdf564 from=seed src=0 shape=3ad069cc vocab=50be22ab
-/
@[simp]
lemma erase_monomial {n : ℕ} {a : R} : erase n (monomial n a) = 0 := by
  simp [erase, monomial_def, zero_def]

/--
@isnad1 id=eq.0h3v.s5.1110c01ffd57 from=seed src=0 shape=2a6f9e87 vocab=7a6bc33b
-/
@[deprecated coeff_erase (since := "2026-07-06")]
lemma erase_same (p : SkewPolynomial R) (n : ℕ) : coeff (p.erase n) n = 0 := by
    simp [coeff_erase]

/--
@isnad1 id=eq.1h4v.s5.5e654ceea7ef from=seed src=0 shape=e8b67d6c vocab=7a6bc33b
-/
@[deprecated coeff_erase (since := "2026-07-06")]
lemma erase_ne (p : SkewPolynomial R) {n i : ℕ} (h : i ≠ n) :
    coeff (p.erase n) i = coeff p i := by
  simp [coeff_erase, h]

end erase

section update

variable [Semiring R]

/-- Replace the coefficient of a `p : SkewPolynomial R` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.natDegree < n` and `a ≠ 0`, this increases the degree to `n`. -/
def update (p : SkewPolynomial R) (n : ℕ) (a : R) : SkewPolynomial R :=
  SkewMonoidAlgebra.update p (ofAdd n) a

/--
@isnad1 id=eq.0h4v.s5.64e88fb70ddf from=seed src=0 shape=c0b07798 vocab=56c36e7c
-/
lemma update_def (p : SkewPolynomial R) (n : ℕ) (a : R) :
    p.update n a = SkewMonoidAlgebra.update p (ofAdd n) a := rfl

/--
@isnad1 id=eq.0h4v.s5.29514826c86a from=seed src=0 shape=f9b2ce32 vocab=65c1bfa4
-/
@[simp]
lemma coeff_update (p : SkewPolynomial R) (n : ℕ) (a : R) :
    (p.update n a).coeff = Function.update p.coeff n a := by
  ext; simp [coeff, update]; rfl

/--
@isnad1 id=eq.0h5v.s5.2681d12b3eaf from=seed src=0 shape=c8802920 vocab=34fef36d
-/
@[deprecated coeff_update (since := "2026-07-06")]
lemma coeff_update_apply (p : SkewPolynomial R) (n : ℕ) (a : R) (i : ℕ) :
    (p.update n a).coeff i = if i = n then a else p.coeff i :=
  SkewMonoidAlgebra.coeff_update_apply _ _ _ _

/--
@isnad1 id=eq.0h4v.s4.14af498bd6cf from=seed src=0 shape=fa66da58 vocab=925ffcc1
-/
@[deprecated coeff_update (since := "2026-07-06")]
lemma coeff_update_same (p : SkewPolynomial R) (n : ℕ) (a : R) : (p.update n a).coeff n = a := by
  rw [p.coeff_update_apply, ite_eq_left rfl]

/--
@isnad1 id=eq.1h5v.s5.65463ace8e5b from=seed src=0 shape=1d493529 vocab=925ffcc1
-/
@[deprecated coeff_update (since := "2026-07-06")]
lemma coeff_update_ne (p : SkewPolynomial R) {n i : ℕ} (a : R) (h : i ≠ n) :
    (p.update n a).coeff i = p.coeff i := by rw [p.coeff_update_apply, ite_eq_right h]

/--
@isnad1 id=eq.0h3v.s5.02cfbb049242 from=seed src=0 shape=97f390e8 vocab=9afb3f53
-/
@[simp]
lemma update_zero_eq_erase (p : SkewPolynomial R) (n : ℕ) : p.update n 0 = p.erase n := by
  ext; simp [Function.update_apply]

/--
@isnad1 id=eq.0h4v.s6.b80e96c991a3 from=seed src=0 shape=a09136f7 vocab=73362ac0
-/
lemma support_update (p : SkewPolynomial R) (n : ℕ) (a : R) [DecidableEq R] :
    support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support := by
  simp only [update_def, support_eq_skewMonoidAlgebra_support, SkewMonoidAlgebra.support_update]
  split_ifs <;> simp

/--
@isnad1 id=eq.0h3v.s5.798d1cb094dd from=seed src=0 shape=7eeb6dec vocab=4af6e9b6
-/
lemma support_update_zero (p : SkewPolynomial R) (n : ℕ) :
    support (p.update n 0) = p.support.erase n := by
  simp

/--
@isnad1 id=eq.1h4v.s5.13eb04205e74 from=seed src=0 shape=589c88db vocab=a4036b80
-/
lemma support_update_ne_zero (p : SkewPolynomial R) (n : ℕ) {a : R} (ha : a ≠ 0) :
    support (p.update n a) = insert n p.support := by classical rw [support_update, ite_eq_right ha]

end update

end SkewPolynomial
