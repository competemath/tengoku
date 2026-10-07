/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.Finsupp.Notation
public import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogenize a univariate polynomial

In this file we define a function `Polynomial.homogenize p n`
that takes a polynomial `p` and a natural number `n`
and returns a homogeneous bivariate polynomial of degree `n`.

If `n` is at least the degree of `p`, then `(homogenize p n).eval ![x, 1] = p.eval x`.

We use `MvPolynomial (Fin 2) R` to represent bivariate polynomials
instead of `R[X][Y]` (i.e., `Polynomial (Polynomial R)`),
because Mathlib has a theory about homogeneous multivariate polynomials,
but not about homogeneous bivariate polynomials encoded as `R[X][Y]`.
-/

@[expose] public section

open Finset

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Given a polynomial `p` and a number `n ≥ natDegree p`,
returns a homogeneous bivariate polynomial `q` of degree `n` such that `q(x, 1) = p(x)`.

It is defined as `∑ k + l = n, a_k X_0^k X_1^l`, where `a_k` is the `k`th coefficient of `p`. -/
noncomputable def homogenize (p : R[X]) (n : ℕ) : MvPolynomial (Fin 2) R :=
  ∑ kl ∈ antidiagonal n, .monomial (fun₀ | 0 => kl.1 | 1 => kl.2) (p.coeff kl.1)

/--
@isnad1 id=eq.0h2v.s6.8774d3795efb from=seed src=0 shape=dbbb88f6 vocab=e66d80ea
-/
@[simp]
lemma homogenize_zero (n : ℕ) : homogenize (0 : R[X]) n = 0 := by
  simp [homogenize]

/--
@isnad1 id=eq.0h4v.s7.d0749fc6ee46 from=seed src=0 shape=5977c48c vocab=4dc1fb75
-/
@[simp]
lemma homogenize_add (p q : R[X]) (n : ℕ) :
    homogenize (p + q) n = homogenize p n + homogenize q n := by
  simp [homogenize, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h5v.s8.ab35e159d94f from=seed src=0 shape=ba096f51 vocab=19791c1a
-/
@[simp]
lemma homogenize_smul {S : Type*} [Semiring S] [Module S R] (c : S) (p : R[X]) (n : ℕ) :
    homogenize (c • p) n = c • homogenize p n := by
  simp [homogenize, Finset.smul_sum, MvPolynomial.smul_monomial]

/-- `homogenize` as a bundled linear map. -/
@[simps]
noncomputable def homogenizeLM (n : ℕ) : R[X] →ₗ[R] MvPolynomial (Fin 2) R where
  toFun p := homogenize p n
  map_add' := (homogenize_add · · n)
  map_smul' := (homogenize_smul · · n)

/--
@isnad1 id=eq.0h5v.s6.10a260f51341 from=seed src=0 shape=e0a1cd48 vocab=3d6bb92d
-/
@[simp]
lemma homogenize_finsetSum {ι : Type*} (s : Finset ι) (p : ι → R[X]) (n : ℕ) :
    homogenize (∑ i ∈ s, p i) n = ∑ i ∈ s, homogenize (p i) n :=
  _root_.map_sum (homogenizeLM n) p s

/--
@isnad1 id=eq.0h5v.s7.64bcc2982d53 from=seed src=0 shape=05823f3e vocab=5c808aa0
-/
lemma homogenize_map {S : Type*} [CommSemiring S] (f : R →+* S) (p : R[X]) (n : ℕ) :
    homogenize (p.map f) n = MvPolynomial.map f (homogenize p n) := by
  simp [homogenize]

/--
@isnad1 id=eq.0h4v.s8.ed66983e80da from=seed src=0 shape=afcb5c7f vocab=659270f1
-/
@[simp]
lemma homogenize_C_mul (c : R) (p : R[X]) (n : ℕ) :
    homogenize (C c * p) n = .C c * homogenize p n := by
  simp only [C_mul', homogenize_smul, MvPolynomial.C_mul']

/--
@isnad1 id=eq.1h4v.s8.33faf51e6a5c from=seed src=0 shape=6656638e vocab=a9bbd9f7
-/
@[simp]
lemma homogenize_monomial {m n : ℕ} (h : m ≤ n) (r : R) :
    homogenize (monomial m r) n = .monomial (fun₀ | 0 => m | 1 => n - m) r := by
  rw [homogenize, Finset.sum_eq_single (a := (m, n - m))]
  · simp
  · aesop (add simp coeff_monomial)
  · simp [h]

/--
@isnad1 id=eq.1h4v.s7.a462d0b43634 from=seed src=0 shape=fcf42453 vocab=b133c956
-/
lemma homogenize_monomial_of_lt {m n : ℕ} (h : n < m) (r : R) :
    homogenize (monomial m r) n = 0 := by
  rw [homogenize]
  apply Finset.sum_eq_zero
  aesop (add simp coeff_monomial)

/--
@isnad1 id=eq.1h3v.s8.8fceceb84673 from=seed src=0 shape=69ea338a vocab=8736a5ec
-/
@[simp]
lemma homogenize_X_pow {m n : ℕ} (h : m ≤ n) :
    homogenize (X ^ m : R[X]) n = .X 0 ^ m * .X 1 ^ (n - m) := by
  rw [X_pow_eq_monomial, homogenize_monomial h, Finsupp.update_eq_add_single (by simp),
    MvPolynomial.monomial_single_add, ← MvPolynomial.X_pow_eq_monomial]

/--
@isnad1 id=eq.1h2v.s7.00079fcabf6b from=seed src=0 shape=8e9ce952 vocab=1bc81031
-/
@[simp]
lemma homogenize_X {n : ℕ} (hn : n ≠ 0) : homogenize (X : R[X]) n = .X 0 * .X 1 ^ (n - 1) := by
  rw [← pow_one X, homogenize_X_pow, pow_one]
  rwa [Nat.one_le_iff_ne_zero]

/--
@isnad1 id=eq.0h3v.s8.687b0e1b5c43 from=seed src=0 shape=5ed20002 vocab=c465ad85
-/
@[simp]
lemma homogenize_C (c : R) (n : ℕ) : homogenize (.C c) n = .C c * .X 1 ^ n := by
  simpa [MvPolynomial.C_mul_X_pow_eq_monomial] using homogenize_monomial (Nat.zero_le n) c

/--
@isnad1 id=eq.0h2v.s7.3acd6e129cc8 from=seed src=0 shape=42c42319 vocab=50881317
-/
@[simp]
lemma homogenize_one (n : ℕ) : homogenize (1 : R[X]) n = .X 1 ^ n := by
  simpa using homogenize_C (1 : R) n

/--
@isnad1 id=eq.0h4v.s8.b848fbfdc775 from=seed src=0 shape=0ba126ee vocab=7d13a8fa
-/
lemma coeff_homogenize (p : R[X]) (n : ℕ) (m : Fin 2 →₀ ℕ) :
    (homogenize p n).coeff m = if m 0 + m 1 = n then coeff p (m 0) else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp [*, ite_add_ite]
  | monomial k c =>
    rcases le_or_gt k n with hkn | hnk
    · rw [homogenize_monomial hkn, coeff_monomial, MvPolynomial.coeff_monomial]
      have : (fun₀ | 0 => m 0 | 1 => m 1) = m := by ext i; fin_cases i <;> simp
      aesop
    · aesop (add simp homogenize_monomial_of_lt) (add simp coeff_monomial)

lemma eq_zero_of_homogenize_eq_zero {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n)
    (h : p.homogenize n = 0) :
    p = 0 := by
  ext i
  simp only [coeff_zero]
  rcases le_or_gt i p.natDegree with H | H
  · have : p.coeff i = (p.homogenize n).coeff fun₀ | 0 => i | 1 => n - i := by
      simp [coeff_homogenize, Nat.add_sub_of_le (H.trans hn)]
    simp [this, h]
  · exact coeff_eq_zero_of_natDegree_lt H

/--
@isnad1 id=iff.1h3v.s7.8f2bf0970a37 from=seed src=0 shape=116042fe vocab=6d5433b4
-/
lemma homogenize_eq_zero_iff {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    p.homogenize n = 0 ↔ p = 0 :=
  ⟨eq_zero_of_homogenize_eq_zero hn, by simp +contextual⟩

/--
@isnad1 id=eq.2h6v.s7.e75b243034da from=seed src=0 shape=eaf240a6 vocab=f4f0ca8b
-/
lemma eval₂_homogenize_of_eq_one {S : Type*} [CommSemiring S] {p : R[X]} {n : ℕ}
    (hn : natDegree p ≤ n) (f : R →+* S) (g : Fin 2 → S) (hg : g 1 = 1) :
    MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0) := by
  apply Polynomial.induction_with_natDegree_le
    (fun p ↦ MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0)) (N := n)
  · simp
  · simp +contextual [hg]
  · simp +contextual
  · assumption

/--
@isnad1 id=eq.2h5v.s8.b41ade676cf1 from=seed src=0 shape=de68a5f3 vocab=8ff156ab
-/
lemma aeval_homogenize_of_eq_one {A : Type*} [CommSemiring A] [Algebra R A] {p : R[X]} {n : ℕ}
    (hn : natDegree p ≤ n) (g : Fin 2 → A) (hg : g 1 = 1) :
    MvPolynomial.aeval g (p.homogenize n) = aeval (g 0) p := by
  apply eval₂_homogenize_of_eq_one <;> assumption

/-- If `deg p ≤ n`, then `homogenize p n (x, 1) = p x`.
@isnad1 id=eq.1h3v.s8.4f5dfc34d7ab from=seed src=0 shape=6ef6d917 vocab=72b08c95
-/
@[simp]
lemma aeval_homogenize_X_one (p : R[X]) {n : ℕ} (hn : natDegree p ≤ n) :
    MvPolynomial.aeval ![X, 1] (p.homogenize n) = p := by
  rw [aeval_homogenize_of_eq_one] <;> simp [*]

/--
@isnad1 id=ishomoge.0h3v.s4.5dc6121b8b46 from=seed src=0 shape=219bebe8 vocab=2db0f486
-/
@[simp]
lemma isHomogeneous_homogenize {n : ℕ} (p : R[X]) : (p.homogenize n).IsHomogeneous n := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
  simp only [Prod.forall, mem_antidiagonal]
  rintro a b rfl
  apply MvPolynomial.isHomogeneous_monomial
  simp [Finsupp.update_eq_add_single]

/--
@isnad1 id=eq.2h4v.s8.c12be643003a from=seed src=0 shape=1418289e vocab=2a4efac8
-/
lemma homogenize_eq_of_isHomogeneous {p : R[X]} {n : ℕ} {q : MvPolynomial (Fin 2) R}
    (hq : q.IsHomogeneous n) (hpq : MvPolynomial.aeval ![X, 1] q = p) :
    p.homogenize n = q := by
  subst p
  rw [q.as_sum]
  simp only [MvPolynomial.aeval_sum, MvPolynomial.aeval_monomial, ← C_eq_algebraMap,
    homogenize_finsetSum, homogenize_C_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [MvPolynomial.monomial_eq]
  congr 1
  obtain rfl : m.weight 1 = n := hq <| by simpa using hm
  simp [Finsupp.prod_fintype, Finsupp.weight_apply, Finsupp.sum_fintype, Fin.prod_univ_two,
    Fin.sum_univ_two]

/--
@isnad1 id=eq.2h5v.s7.e9c8364d5e81 from=seed src=0 shape=16b4d280 vocab=9ce5f291
-/
lemma homogenize_mul (p q : R[X]) {m n : ℕ} (hm : natDegree p ≤ m) (hn : natDegree q ≤ n) :
    homogenize (p * q) (m + n) = homogenize p m * homogenize q n := by
  apply homogenize_eq_of_isHomogeneous
  · apply_rules [MvPolynomial.IsHomogeneous.mul, isHomogeneous_homogenize]
  · simp [*]

/--
@isnad1 id=eq.1h5v.s7.9df170299ae4 from=seed src=0 shape=caf9ed5b vocab=8bbd7310
-/
lemma homogenize_finsetProd {ι : Type*} {s : Finset ι} {p : ι → R[X]} {n : ι → ℕ}
    (h : ∀ i ∈ s, (p i).natDegree ≤ n i) :
    homogenize (∏ i ∈ s, p i) (∑ i ∈ s, n i) = ∏ i ∈ s, homogenize (p i) (n i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ihs =>
    simp only [prod_cons, sum_cons, forall_mem_cons] at *
    rw [homogenize_mul _ _ h.1, ihs h.2]
    exact (natDegree_prod_le _ _).trans (sum_le_sum h.2)

/--
@isnad1 id=dvd.1h3v.s7.358ffe57ed9e from=seed src=0 shape=be6f965c vocab=a58d783f
-/
lemma homogenize_dvd [NoZeroDivisors R] {p q : R[X]} (h : p ∣ q) :
    homogenize p p.natDegree ∣ homogenize q q.natDegree := by
  rcases h with ⟨r, rfl⟩
  obtain rfl | rfl | ⟨hp₀, hr₀⟩ : p = 0 ∨ r = 0 ∨ p ≠ 0 ∧ r ≠ 0 := by tauto
  · simp
  · simp
  · rw [natDegree_mul hp₀ hr₀, homogenize_mul _ _ le_rfl le_rfl]
    apply dvd_mul_right

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/--
@isnad1 id=eq.0h3v.s7.0f7e990f68e5 from=seed src=0 shape=e4007f29 vocab=84f80790
-/
@[simp]
lemma homogenize_neg (p : R[X]) (n : ℕ) : (-p).homogenize n = -p.homogenize n :=
  map_neg (homogenizeLM n) p

/--
@isnad1 id=eq.0h4v.s7.52f396e7db9d from=seed src=0 shape=5977c48c vocab=89530682
-/
@[simp]
lemma homogenize_sub (p q : R[X]) (n : ℕ) :
    (p - q).homogenize n = p.homogenize n - q.homogenize n :=
  map_sub (homogenizeLM n) p q

end CommRing

section Semifield

variable {K : Type*} [Semifield K]

/--
@isnad1 id=eq.2h4v.s8.583d030938b4 from=seed src=0 shape=a1867298 vocab=5d3c513d
-/
lemma eval_homogenize {p : K[X]} {n : ℕ} (hn : p.natDegree ≤ n) (x : Fin 2 → K) (hx : x 1 ≠ 0) :
    MvPolynomial.eval x (p.homogenize n) = p.eval (x 0 / x 1) * x 1 ^ n := by
  simp only [homogenize, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hn),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single, Finsupp.prod_add_index',
    Finsupp.prod_single_index, Finsupp.prod_single_index, pow_sub₀]
  · ring
  all_goals simp_all [pow_add]

end Semifield

section projectivize

variable {R : Type*} [CommSemiring R]

/-- Given a polynomial `p : R[X]`, this is the vector `![p₀, p₁]` of homogeneous bivariate
polynomials of degree `p.natDegree` such that `p(x) = p₀(x,1)/p₁(x,1)` and `p₁` is a monomial. -/
noncomputable
def toTupleMvPolynomial (p : R[X]) : Fin 2 → MvPolynomial (Fin 2) R :=
  ![p.homogenize p.natDegree, (MvPolynomial.X 1) ^ p.natDegree]

/--
@isnad1 id=eq.0h2v.s5.dcf1e10ad6a2 from=seed src=0 shape=1073d073 vocab=afce76e5
-/
lemma toTupleMvPolynomial_zero_eq (p : R[X]) :
    p.toTupleMvPolynomial 0 = p.homogenize p.natDegree :=
  rfl

/--
@isnad1 id=eq.0h2v.s7.ef4e23927e7a from=seed src=0 shape=97ff9ebe vocab=0474c9df
-/
lemma toTupleMvPolynomial_one_eq (p : R[X]) :
    p.toTupleMvPolynomial 1 = (MvPolynomial.X 1) ^ p.natDegree :=
  rfl

/--
@isnad1 id=ishomoge.0h3v.s5.7491799f6ffd from=seed src=0 shape=72c02929 vocab=77056453
-/
lemma isHomogeneous_toTupleMvPolynomial (p : R[X]) (i : Fin 2) :
    (p.toTupleMvPolynomial i).IsHomogeneous p.natDegree := by
  fin_cases i
  · simp [toTupleMvPolynomial]
  · simpa [toTupleMvPolynomial] using MvPolynomial.isHomogeneous_X_pow 1 p.natDegree

/--
@isnad1 id=ishomoge.0h3v.s5.7491799f6ffd from=seed src=0 shape=72c02929 vocab=77056453
-/
@[deprecated (since := "2026-04-06")]
alias isHomogenous_toTupleMvPolynomial := isHomogeneous_toTupleMvPolynomial

/--
@isnad1 id=eq.0h2v.s9.375e9255b763 from=seed src=0 shape=651d395d vocab=2b4f751e
-/
lemma eval_X_toTupleMvPolynomial_zero_eq (p : R[X]) :
    MvPolynomial.aeval ![X, 1] (p.toTupleMvPolynomial 0) =
      p * MvPolynomial.aeval ![X, 1] (p.toTupleMvPolynomial 1) := by
  simp [toTupleMvPolynomial]

/--
@isnad1 id=eq.0h3v.s8.166c1ec5f6b8 from=seed src=0 shape=6adb1758 vocab=d13d538a
-/
lemma eval_eq_div_eval_toTupleMvPolynomial {R : Type*} [Field R] (p : R[X]) (x : R) :
    p.eval x =
      (p.toTupleMvPolynomial 0).eval ![x, 1] / (p.toTupleMvPolynomial 1).eval ![x, 1] := by
  simp [toTupleMvPolynomial, eval_homogenize]

/--
@isnad1 id=eq.1h3v.s7.a3306a8b8144 from=seed src=0 shape=9f284730 vocab=f40c319d
-/
lemma sum_eq_natDegree_of_mem_support_homogenize (p : R[X]) {s : Fin 2 →₀ ℕ}
    (hs : s ∈ (p.homogenize p.natDegree).support) :
    s 0 + s 1 = p.natDegree := by
  simp [(isHomogeneous_homogenize p).degree_eq_sum_deg_support hs, ← Finsupp.degree_apply,
        Finsupp.degree_eq_sum]

/-- Summing a function over the coefficients of the homogenization of a polynomial `p`
(of degree `p.natDegree`) gives the same result as summing over the coefficients of `p`.
@isnad1 id=eq.0h4v.s6.5e1ee644cb49 from=seed src=0 shape=6c0d6871 vocab=eb4e8493
-/
lemma finsuppSum_homogenize_eq {M : Type*} [AddCommMonoid M] (p : R[X]) {f : R → M} :
    (AddMonoidAlgebra.coeff <| p.homogenize p.natDegree).sum (fun _ c ↦ f c) =
      p.sum fun _ c ↦ f c := by
  rw [MvPolynomial.sum_def, sum_def p]
  -- We set up a bijection between the sets indexing the terms on both sides
  -- and show that it maps the terms in the one sum to those in the other.
  refine Finset.sum_nbij' (fun s ↦ s 0) (fun n ↦ fun₀ | 0 => n | 1 => p.natDegree - n)
    (fun s hs ↦ ?_) (fun n hn ↦ ?_) (fun s hs ↦ ?_) (fun n hn ↦ by simp)
    fun s hs ↦ ?_
  · simpa [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs] using hs
  · simpa [coeff_homogenize, mem_support_iff.mp hn]
      using Nat.add_sub_of_le <| le_natDegree_of_mem_supp n hn
  · -- speeds up `grind` quite a bit
    grind only [= Finsupp.update_apply, = Finsupp.single_apply,
      sum_eq_natDegree_of_mem_support_homogenize p hs]
  · simp [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs]

end projectivize

end Polynomial
