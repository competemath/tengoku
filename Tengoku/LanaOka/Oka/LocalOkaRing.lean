/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Algebra.MvPolynomial.Funext
import Tengoku.Seed.Analysis.Analytic.Uniqueness
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension
import Tengoku.Seed.LinearAlgebra.Complex.FiniteDimensional
import Tengoku.Seed.RingTheory.MvPowerSeries.Inverse
import Tengoku.Seed.RingTheory.MvPowerSeries.Rename
-- `Mathlib.RingTheory.Polynomial.DegreeLT` is not used in this file, but it supplies the
-- `R[X]_d` notation that `Oka/OkaLemma.lean` relies on transitively; without it the
-- statements there fail to parse.
import Tengoku.Seed.RingTheory.Polynomial.DegreeLT
import Tengoku.Seed.RingTheory.PowerSeries.Order
import Tengoku.LanaOka.Oka.StructureSheaf

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The local ring of convergent power series

We introduce the ring `LocalOkaRing ι` of formal power series in the variables `ι` over `ℂ`
which converge absolutely on a neighbourhood of the origin, i.e. the ring of germs at `0` of
holomorphic functions on `ℂ^ι`.

## Main definitions

- `MvPowerSeries.evalMonomial`, `MvPowerSeries.term` and `MvPowerSeries.eval`: the terms of a
  power series evaluated at a point, and its sum.
- `MvPowerSeries.SummableAt` and `MvPowerSeries.LocallyConvergent`: absolute convergence at a
  point, resp. on a neighbourhood of the origin.
- `MvPowerSeries.Represents`: `P` sums to the function `f` near the origin.
- `LocalOkaRing`: the ring of locally convergent power series; it is a local ring with maximal
  ideal the series with vanishing constant term.
- `OkaRing.toLocalOkaRingHom`: the `ℂ`-algebra map sending a holomorphic function defined on an
  open set `U ∋ 0` to its Taylor series at the origin.
- `MvPowerSeries.fromPolynomial` and `MvPowerSeries.fromPolynomial'`: a polynomial in one
  distinguished variable over the power series in the remaining variables, viewed as a power
  series in all variables.
- `MvPowerSeries.partialEval`: the restriction `P ↦ P(0, ..., z_i, ..., 0)` of a power series
  to the `i`-th coordinate axis.

## Main results

- `LocalOkaRing.isUnit_iff`: a locally convergent power series is a unit if and only if its
  constant term is nonzero; hence `LocalOkaRing ι` is a local ring.
- `LocalOkaRing.exists_okaRing`: every locally convergent power series is the Taylor series of
  a holomorphic function on some open neighbourhood of the origin.
- `MvPowerSeries.order_partialEval_eq_one_iff`: **a simple zero along the `i`-th axis is the pair
  of coefficient conditions** `constantCoeff P = 0` and `coeff (Finsupp.single i 1) P ≠ 0`.

## The analytic dictionary

The section `AnalyticDictionary` translates between `MvPowerSeries ι ℂ` and
`FormalMultilinearSeries ℂ (ι → ℂ) ℂ`, which is what relates the two notions of holomorphy
used here. In one direction, `MvPowerSeries.toFPS` groups the monomials of a power series by
total degree, giving `MvPowerSeries.LocallyConvergent.analyticAt`; in the other,
`MvPowerSeries.ofFPS` reads off the coefficients by expanding the multilinear maps over the
standard basis of `ι → ℂ`, giving `MvPowerSeries.exists_represents`. Restricting to complex
lines and using the one variable identity theorem yields `MvPowerSeries.Represents.unique`.
-/
namespace Tengoku.LanaOka end Tengoku.LanaOka open Tengoku.LanaOka
open Filter Topology TopologicalSpace

universe u

variable {ι : Type u}

namespace MvPowerSeries

section Eval

/-- The monomial function `x ↦ ∏ i, (x i) ^ (d i)` attached to `d : ι →₀ ℕ`. -/
noncomputable def evalMonomial (d : ι →₀ ℕ) (x : ι → ℂ) : ℂ :=
  d.prod fun i k ↦ x i ^ k

/--
@isnad1 id=eq.0h2v.s5.b83fa29c3661 from=translated src=- shape=705a9773 vocab=ae871651
-/
@[simp]
lemma evalMonomial_zero (x : ι → ℂ) : evalMonomial (0 : ι →₀ ℕ) x = 1 :=
  Finsupp.prod_zero_index

/--
@isnad1 id=eq.0h4v.s6.898e4f94f393 from=translated src=- shape=335c264f vocab=cd91c815
-/
lemma evalMonomial_add (d e : ι →₀ ℕ) (x : ι → ℂ) :
    evalMonomial (d + e) x = evalMonomial d x * evalMonomial e x :=
  Finsupp.prod_add_index' (by simp) (by simp [pow_add])

/-- The `d`-th term of the power series `P` evaluated at `x`. -/
noncomputable def term (P : MvPowerSeries ι ℂ) (x : ι → ℂ) (d : ι →₀ ℕ) : ℂ :=
  coeff d P * evalMonomial d x

/--
@isnad1 id=eq.0h3v.s5.5977badbf73d from=translated src=- shape=3c60507c vocab=1ab39ca8
-/
@[simp]
lemma term_zero (x : ι → ℂ) (d : ι →₀ ℕ) : (0 : MvPowerSeries ι ℂ).term x d = 0 := by
  simp [term]

/--
@isnad1 id=eq.0h5v.s6.27edc745baa9 from=translated src=- shape=c5133ab8 vocab=599af6bd
-/
@[simp]
lemma term_add (P Q : MvPowerSeries ι ℂ) (x : ι → ℂ) (d : ι →₀ ℕ) :
    (P + Q).term x d = P.term x d + Q.term x d := by
  simp [term, add_mul]

/--
@isnad1 id=eq.0h3v.s6.0fd58a6627b9 from=translated src=- shape=3840c748 vocab=2da60f73
-/
@[simp]
lemma term_algebraMap_zero (c : ℂ) (x : ι → ℂ) :
    (algebraMap ℂ (MvPowerSeries ι ℂ) c).term x 0 = c := by
  classical
  rw [term, algebraMap_apply, coeff_C, ite_eq_left rfl, evalMonomial_zero, mul_one]
  simp

/--
@isnad1 id=eq.1h4v.s6.d318d52845b5 from=translated src=- shape=af3b313b vocab=2da60f73
-/
lemma term_algebraMap_of_ne_zero (c : ℂ) (x : ι → ℂ) {d : ι →₀ ℕ} (hd : d ≠ 0) :
    (algebraMap ℂ (MvPowerSeries ι ℂ) c).term x d = 0 := by
  classical
  rw [term, algebraMap_apply, coeff_C, ite_eq_right hd, zero_mul]

/--
@isnad1 id=eq.0h5v.s7.7c4ed4c34e87 from=translated src=- shape=657bc9fc vocab=832c782b
-/
lemma term_mul [DecidableEq ι] (P Q : MvPowerSeries ι ℂ) (x : ι → ℂ) (d : ι →₀ ℕ) :
    (P * Q).term x d =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal d, P.term x p.1 * Q.term x p.2 := by
  rw [term, coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [term, term, ← hp, evalMonomial_add]
  ring

/-- The sum of the power series `P` at `x`. This is only meaningful if `P` converges at `x`,
see `MvPowerSeries.SummableAt.hasSum`. -/
noncomputable def eval (P : MvPowerSeries ι ℂ) (x : ι → ℂ) : ℂ :=
  ∑' d, P.term x d

/--
@isnad1 id=eq.1h2v.s6.468dd1ceeadb from=translated src=- shape=a411f583 vocab=ae871651
-/
lemma evalMonomial_eq_zero {d : ι →₀ ℕ} (hd : d ≠ 0) : evalMonomial d 0 = 0 := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
  refine Finset.prod_eq_zero hi ?_
  exact zero_pow (Finsupp.mem_support_iff.mp hi)

/--
@isnad1 id=eq.0h2v.s6.d548a5475062 from=translated src=- shape=4ae0c325 vocab=4e9be08f
-/
@[simp]
lemma eval_zero (P : MvPowerSeries ι ℂ) : P.eval 0 = constantCoeff P := by
  rw [eval, tsum_eq_single 0 fun d hd ↦ by rw [term, evalMonomial_eq_zero hd, mul_zero], term,
    evalMonomial_zero, mul_one, coeff_zero_eq_constantCoeff]

/-- A power series converges absolutely at `x` if the family of its terms at `x` is absolutely
summable. -/
def SummableAt (P : MvPowerSeries ι ℂ) (x : ι → ℂ) : Prop :=
  Summable fun d ↦ ‖P.term x d‖

/--
@isnad1 id=summable.1h3v.s5.890d95c616e1 from=translated src=- shape=4903b1dc vocab=a831b3d2
-/
lemma SummableAt.summable {P : MvPowerSeries ι ℂ} {x : ι → ℂ} (h : P.SummableAt x) :
    Summable (P.term x) :=
  Summable.of_norm h

/--
@isnad1 id=hassum.1h3v.s5.12ffbac613f2 from=translated src=- shape=c452dcb7 vocab=affd682e
-/
lemma SummableAt.hasSum {P : MvPowerSeries ι ℂ} {x : ι → ℂ} (h : P.SummableAt x) :
    HasSum (P.term x) (P.eval x) :=
  h.summable.hasSum

/--
@isnad1 id=summable.0h3v.s6.aaa16012992a from=translated src=- shape=319ac1cc vocab=466d97c8
-/
lemma summableAt_algebraMap (c : ℂ) (x : ι → ℂ) :
    (algebraMap ℂ (MvPowerSeries ι ℂ) c).SummableAt x := by
  classical
  refine summable_of_ne_finset_zero (s := {0}) fun d hd ↦ ?_
  rw [term_algebraMap_of_ne_zero c x (by simpa using hd), norm_zero]

/--
@isnad1 id=summable.2h4v.s5.5c569f1441a6 from=translated src=- shape=c9856741 vocab=03f599bf
-/
lemma SummableAt.add {P Q : MvPowerSeries ι ℂ} {x : ι → ℂ} (hP : P.SummableAt x)
    (hQ : Q.SummableAt x) : (P + Q).SummableAt x := by
  refine Summable.of_nonneg_of_le (fun d ↦ norm_nonneg _) (fun d ↦ ?_) (Summable.add hP hQ)
  rw [term_add]
  exact norm_add_le _ _

variable (ι) in
/-- The pairs of exponents summing to a given exponent are, altogether, all pairs of
exponents. -/
noncomputable def antidiagonalSigmaEquiv [DecidableEq ι] :
    (Σ d : ι →₀ ℕ, {p : (ι →₀ ℕ) × (ι →₀ ℕ) //
      p ∈ Finset.HasAntidiagonal.antidiagonal d}) ≃ ((ι →₀ ℕ) × (ι →₀ ℕ)) where
  toFun x := x.2.1
  invFun p := ⟨p.1 + p.2, p, Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  left_inv := by
    rintro ⟨d, p, hp⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    subst hp
    rfl

/-- The Cauchy product of two absolutely convergent power series converges absolutely.
@isnad1 id=summable.2h4v.s5.5c294ff71805 from=translated src=- shape=c9856741 vocab=759f40f3
-/
lemma SummableAt.mul {P Q : MvPowerSeries ι ℂ} {x : ι → ℂ} (hP : P.SummableAt x)
    (hQ : Q.SummableAt x) : (P * Q).SummableAt x := by
  classical
  have hF : Summable fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ ‖P.term x p.1‖ * ‖Q.term x p.2‖ :=
    Summable.mul_of_nonneg hP hQ (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hkey : Summable fun d : ι →₀ ℕ ↦
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal d, ‖P.term x p.1‖ * ‖Q.term x p.2‖ := by
    refine Summable.congr (((antidiagonalSigmaEquiv ι).summable_iff.mpr hF).sigma) fun d ↦ ?_
    rw [← Finset.tsum_subtype]
    rfl
  refine Summable.of_nonneg_of_le (fun d ↦ norm_nonneg _) (fun d ↦ ?_) hkey
  rw [term_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦ ?_)
  rw [norm_mul]

end Eval

section LocallyConvergent

/-- A formal power series is locally convergent if it converges absolutely on a neighbourhood
of the origin. -/
def LocallyConvergent (P : MvPowerSeries ι ℂ) : Prop :=
  ∀ᶠ x in 𝓝 (0 : ι → ℂ), P.SummableAt x

/--
@isnad1 id=locallyc.0h2v.s6.2fc6f92ac3c2 from=translated src=- shape=73552dd3 vocab=5ff7abc3
-/
lemma locallyConvergent_algebraMap (c : ℂ) :
    (algebraMap ℂ (MvPowerSeries ι ℂ) c).LocallyConvergent :=
  .of_forall fun x ↦ summableAt_algebraMap c x

/--
@isnad1 id=locallyc.0h1v.s4.b36626c65fe7 from=translated src=- shape=eb105b30 vocab=577a7938
-/
lemma locallyConvergent_zero : (0 : MvPowerSeries ι ℂ).LocallyConvergent := by
  simpa using locallyConvergent_algebraMap (ι := ι) 0

/--
@isnad1 id=locallyc.0h1v.s4.0dd3f2020d5b from=translated src=- shape=eb105b30 vocab=577a7938
-/
lemma locallyConvergent_one : (1 : MvPowerSeries ι ℂ).LocallyConvergent := by
  simpa using locallyConvergent_algebraMap (ι := ι) 1

/--
@isnad1 id=locallyc.2h3v.s5.02c7dfed9f2c from=translated src=- shape=42c9f699 vocab=edada018
-/
lemma LocallyConvergent.add {P Q : MvPowerSeries ι ℂ} (hP : P.LocallyConvergent)
    (hQ : Q.LocallyConvergent) : (P + Q).LocallyConvergent := by
  filter_upwards [hP, hQ] with x hx hx' using hx.add hx'

/--
@isnad1 id=locallyc.2h3v.s5.fffbc2682cab from=translated src=- shape=42c9f699 vocab=55960b4d
-/
lemma LocallyConvergent.mul {P Q : MvPowerSeries ι ℂ} (hP : P.LocallyConvergent)
    (hQ : Q.LocallyConvergent) : (P * Q).LocallyConvergent := by
  filter_upwards [hP, hQ] with x hx hx' using hx.mul hx'

end LocallyConvergent

section Represents

/-- A power series `P` represents the function `f` if it sums to `f` on a neighbourhood of the
origin. -/
def Represents (P : MvPowerSeries ι ℂ) (f : (ι → ℂ) → ℂ) : Prop :=
  ∀ᶠ x in 𝓝 (0 : ι → ℂ), HasSum (P.term x) (f x)

/--
@isnad1 id=represen.2h4v.s6.943686952d62 from=translated src=- shape=c4fad234 vocab=7a8f4387
-/
lemma Represents.congr {P : MvPowerSeries ι ℂ} {f g : (ι → ℂ) → ℂ} (hP : P.Represents f)
    (h : f =ᶠ[𝓝 (0 : ι → ℂ)] g) : P.Represents g := by
  filter_upwards [hP, h] with x hx hx' using hx' ▸ hx

/-- Two functions summed to by the same power series agree near the origin.
@isnad1 id=eventual.2h4v.s6.95dad5ce4a3f from=translated src=- shape=be2d6114 vocab=7a8f4387
-/
lemma Represents.eventuallyEq {P : MvPowerSeries ι ℂ} {f g : (ι → ℂ) → ℂ}
    (hf : P.Represents f) (hg : P.Represents g) : f =ᶠ[𝓝 (0 : ι → ℂ)] g := by
  filter_upwards [hf, hg] with x hx hx' using hx.unique hx'

/--
@isnad1 id=represen.1h2v.s4.206173b34390 from=translated src=- shape=089affe3 vocab=abe9e9a2
-/
lemma LocallyConvergent.represents_eval {P : MvPowerSeries ι ℂ} (hP : P.LocallyConvergent) :
    P.Represents P.eval := by
  filter_upwards [hP] with x hx using hx.hasSum

/--
@isnad1 id=represen.2h5v.s6.c9d5278e139d from=translated src=- shape=45b92ee7 vocab=ce0ac628
-/
lemma Represents.add {P Q : MvPowerSeries ι ℂ} {f g : (ι → ℂ) → ℂ} (hP : P.Represents f)
    (hQ : Q.Represents g) : (P + Q).Represents (f + g) := by
  filter_upwards [hP, hQ] with x hx hx'
  have h : (P + Q).term x = fun d ↦ P.term x d + Q.term x d := funext (term_add P Q x)
  rw [h, Pi.add_apply]
  exact hx.add hx'

/--
@isnad1 id=represen.0h2v.s6.173bbd50b4a3 from=translated src=- shape=b4b72558 vocab=ced50dee
-/
lemma represents_algebraMap (c : ℂ) :
    (algebraMap ℂ (MvPowerSeries ι ℂ) c).Represents (Function.const (ι → ℂ) c) := by
  refine .of_forall fun x ↦ ?_
  simpa using hasSum_single (f := (algebraMap ℂ (MvPowerSeries ι ℂ) c).term x) 0
    (fun d hd ↦ term_algebraMap_of_ne_zero c x hd)

/--
@isnad1 id=represen.0h1v.s4.4fb2d2515a72 from=translated src=- shape=8debde6e vocab=4c5b9dda
-/
lemma represents_zero : (0 : MvPowerSeries ι ℂ).Represents (Function.const (ι → ℂ) 0) := by
  simpa using represents_algebraMap (ι := ι) 0

/--
@isnad1 id=represen.0h1v.s4.0d2c38e812e3 from=translated src=- shape=8debde6e vocab=4c5b9dda
-/
lemma represents_one : (1 : MvPowerSeries ι ℂ).Represents (Function.const (ι → ℂ) 1) := by
  simpa using represents_algebraMap (ι := ι) 1

/-- Power series representing functions multiply to power series representing the product:
the Cauchy product formula.
@isnad1 id=represen.4h5v.s6.81e4443ac753 from=translated src=- shape=00bd97bc vocab=3cce707a
-/
lemma Represents.mul {P Q : MvPowerSeries ι ℂ} {f g : (ι → ℂ) → ℂ}
    (hPc : P.LocallyConvergent) (hQc : Q.LocallyConvergent)
    (hP : P.Represents f) (hQ : Q.Represents g) : (P * Q).Represents (f * g) := by
  classical
  filter_upwards [hPc, hQc, hP, hQ] with x hPx hQx hPf hQg
  rw [Pi.mul_apply]
  -- the family of all products of terms is summable, with sum `f x * g x`
  have hprod : HasSum (fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ P.term x p.1 * Q.term x p.2)
      (f x * g x) :=
    hPf.mul hQg (summable_mul_of_summable_norm hPx hQx)
  -- regroup it along the fibres of `(d, e) ↦ d + e`
  refine ((antidiagonalSigmaEquiv ι).hasSum_iff.mpr hprod).sigma fun d ↦ ?_
  have hval : ∑ p : {p : (ι →₀ ℕ) × (ι →₀ ℕ) // p ∈ Finset.HasAntidiagonal.antidiagonal d},
      P.term x p.val.1 * Q.term x p.val.2 = (P * Q).term x d := by
    rw [term_mul]
    exact Finset.sum_coe_sort _ fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ P.term x p.1 * Q.term x p.2
  rw [← hval]
  exact hasSum_fintype _

section AnalyticDictionary

/-!
### The dictionary between convergent power series and holomorphic functions

A locally convergent power series is turned into a `FormalMultilinearSeries` by grouping its
terms according to their total degree (`MvPowerSeries.toFPS`), and conversely the coefficients
of a `FormalMultilinearSeries` are read off by expanding its terms over the standard basis
(`MvPowerSeries.ofFPS`).
-/

variable {P Q : MvPowerSeries ι ℂ} {x y : ι → ℂ}

section Basic

variable [Fintype ι]

/--
@isnad1 id=eq.0h3v.s6.0067b9361403 from=translated src=- shape=ad8b8b18 vocab=d807c5c3
-/
lemma evalMonomial_eq_prod (d : ι →₀ ℕ) (x : ι → ℂ) : evalMonomial d x = ∏ i, x i ^ d i :=
  Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _

/--
@isnad1 id=eq.0h3v.s6.7ac7dc95a593 from=translated src=- shape=3ac80af0 vocab=85a1881b
-/
lemma norm_evalMonomial (d : ι →₀ ℕ) (x : ι → ℂ) :
    ‖evalMonomial d x‖ = ∏ i, ‖x i‖ ^ d i := by
  rw [evalMonomial_eq_prod, norm_prod]
  exact Finset.prod_congr rfl fun i _ ↦ norm_pow _ _

omit [Fintype ι] in
/--
@isnad1 id=le.1h4v.s5.fd925b8e5a65 from=translated src=- shape=995de134 vocab=5cf70d34
-/
lemma norm_evalMonomial_le (h : ∀ i, ‖x i‖ ≤ ‖y i‖) (d : ι →₀ ℕ) :
    ‖evalMonomial d x‖ ≤ ‖evalMonomial d y‖ := by
  simp only [evalMonomial, Finsupp.prod, norm_prod, norm_pow]
  exact Finset.prod_le_prod (fun i _ ↦ by positivity)
    fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (h i) _

omit [Fintype ι] in
/--
@isnad1 id=le.1h5v.s5.6365d1692093 from=translated src=- shape=bbbadf3b vocab=6cdaeeb2
-/
lemma norm_term_le (h : ∀ i, ‖x i‖ ≤ ‖y i‖) (d : ι →₀ ℕ) :
    ‖P.term x d‖ ≤ ‖P.term y d‖ := by
  rw [term, term, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_evalMonomial_le h d) (norm_nonneg _)

omit [Fintype ι] in
/-- Absolute convergence at a point implies absolute convergence at every point which is
smaller in each coordinate.
@isnad1 id=summable.2h4v.s5.1cf3230d040e from=translated src=- shape=15b0aae0 vocab=33dbe837
-/
lemma SummableAt.mono (hy : P.SummableAt y) (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : P.SummableAt x :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun d ↦ norm_term_le h d) hy

omit [Fintype ι] in
/-- Absolute convergence on a neighbourhood of the origin gives absolute convergence on a
polydisc around the origin.
@isnad1 id=ex.1h2v.s5.d958e3cfd8a7 from=translated src=- shape=9843e251 vocab=0ad3ad98
-/
lemma LocallyConvergent.exists_summableAt_const [Finite ι] (hP : P.LocallyConvergent) :
    ∃ ρ : ℝ, 0 < ρ ∧ P.SummableAt (fun _ ↦ (ρ : ℂ)) := by
  have := Fintype.ofFinite ι
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hP
  refine ⟨ε / 2, by positivity, hball ?_⟩
  rw [mem_ball_zero_iff]
  have h1 : ‖fun _ : ι ↦ ((ε / 2 : ℝ) : ℂ)‖ ≤ ε / 2 :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i ↦ by
      simp [Complex.norm_real, abs_of_nonneg hε.le]
  linarith

end Basic

section Degree

variable [Fintype ι] [DecidableEq ι]

/-- The exponents of total degree `n`. -/
noncomputable def degFinset (ι : Type u) [Fintype ι] [DecidableEq ι] (n : ℕ) :
    Finset (ι →₀ ℕ) :=
  Finset.finsuppAntidiag Finset.univ n

/--
@isnad1 id=iff.0h3v.s6.22de18bcbe8e from=translated src=- shape=4ec458dd vocab=d180df10
-/
lemma mem_degFinset {n : ℕ} {d : ι →₀ ℕ} : d ∈ degFinset ι n ↔ ∑ i, d i = n := by
  rw [degFinset, Finset.mem_finsuppAntidiag]
  exact and_iff_left (Finset.subset_univ _)

/-- Every exponent has a well-defined total degree.
@isnad1 id=mem.0h2v.s6.cb40fd7fd1fa from=translated src=- shape=eb26a6e1 vocab=d180df10
-/
lemma self_mem_degFinset (d : ι →₀ ℕ) : d ∈ degFinset ι (∑ i, d i) :=
  mem_degFinset.mpr rfl

/-- Splitting the exponents according to their total degree. -/
noncomputable def degreeSigmaEquiv :
    (Σ n : ℕ, {d : ι →₀ ℕ // d ∈ degFinset ι n}) ≃ (ι →₀ ℕ) where
  toFun x := x.2.1
  invFun d := ⟨∑ i, d i, d, self_mem_degFinset d⟩
  left_inv := by
    rintro ⟨n, d, hd⟩
    rw [mem_degFinset] at hd
    subst hd
    rfl

/-- Regrouping a summable family of exponents by total degree.
@isnad1 id=hassum.1h4v.s6.d0a2e901a516 from=translated src=- shape=829f11e5 vocab=1aa49962
-/
lemma hasSum_degFinset {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α]
    [RegularSpace α] {f : (ι →₀ ℕ) → α} {s : α} (h : HasSum f s) :
    HasSum (fun n ↦ ∑ d ∈ degFinset ι n, f d) s := by
  refine (degreeSigmaEquiv.hasSum_iff.mpr h).sigma fun n ↦ ?_
  have hval : ∑ d : {d : ι →₀ ℕ // d ∈ degFinset ι n}, f d.val = ∑ d ∈ degFinset ι n, f d :=
    Finset.sum_coe_sort _ _
  rw [← hval]
  exact hasSum_fintype _

/-- Regrouping the terms of a power series by total degree.
@isnad1 id=hassum.1h4v.s6.3f02a4425886 from=translated src=- shape=4979d5ff vocab=6abec261
-/
lemma hasSum_degree {s : ℂ} (h : HasSum (P.term x) s) :
    HasSum (fun n ↦ ∑ d ∈ degFinset ι n, P.term x d) s :=
  hasSum_degFinset h

/--
@isnad1 id=hassum.1h3v.s6.aad5048a8782 from=translated src=- shape=014e074e vocab=ad62137b
-/
lemma hasSum_degree_norm (h : P.SummableAt x) :
    HasSum (fun n ↦ ∑ d ∈ degFinset ι n, ‖P.term x d‖) (∑' d, ‖P.term x d‖) :=
  hasSum_degFinset (Summable.hasSum h)

end Degree

section Multilinear

variable [Fintype ι] [DecidableEq ι]

/-- A continuous multilinear map of degree `n` whose value on the diagonal is the monomial
attached to `d`, provided `d` has total degree `n`. -/
noncomputable def monomialCMM (d : ι →₀ ℕ) (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ (ι → ℂ)) ℂ :=
  if h : Fintype.card ((i : ι) × Fin (d i)) = n then
    (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
      fun k ↦ ContinuousLinearMap.proj ((Fintype.equivFinOfCardEq h).symm k).1
  else 0

/--
@isnad1 id=eq.1h4v.s7.cee9da6f595b from=translated src=- shape=e047f00b vocab=b91b761f
-/
lemma monomialCMM_apply_diag {d : ι →₀ ℕ} {n : ℕ} (hd : d ∈ degFinset ι n) (y : ι → ℂ) :
    monomialCMM d n (fun _ ↦ y) = evalMonomial d y := by
  have hcard : Fintype.card ((i : ι) × Fin (d i)) = n := by
    rw [Fintype.card_sigma]
    simpa using mem_degFinset.mp hd
  rw [monomialCMM, dite_eq_left hcard]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  simp only [ContinuousLinearMap.proj_apply]
  rw [Equiv.prod_comp (Fintype.equivFinOfCardEq hcard).symm fun j ↦ y j.1]
  rw [Fintype.prod_sigma]
  simp [evalMonomial_eq_prod]

omit [DecidableEq ι] in
/--
@isnad1 id=le.0h3v.s7.b79d44e4718d from=translated src=- shape=6d2e435b vocab=fcf38b78
-/
lemma norm_monomialCMM_le (d : ι →₀ ℕ) (n : ℕ) : ‖monomialCMM d n‖ ≤ 1 := by
  rw [monomialCMM]
  split
  · refine ContinuousMultilinearMap.opNorm_le_bound (by norm_num) fun v ↦ ?_
    rw [one_mul, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, norm_prod]
    simp only [ContinuousLinearMap.proj_apply]
    exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun k _ ↦ norm_le_pi_norm _ _
  · simp

variable (P) in
/-- The formal multilinear series attached to a formal power series. -/
noncomputable def toFPS : FormalMultilinearSeries ℂ (ι → ℂ) ℂ :=
  fun n ↦ ∑ d ∈ degFinset ι n, coeff d P • monomialCMM d n

/--
@isnad1 id=eq.0h4v.s7.98ed1932fe93 from=translated src=- shape=472c0fec vocab=3abed4a1
-/
lemma toFPS_apply_diag (n : ℕ) (y : ι → ℂ) :
    toFPS P n (fun _ ↦ y) = ∑ d ∈ degFinset ι n, P.term y d := by
  rw [toFPS, sum_apply]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [smul_apply, monomialCMM_apply_diag hd, term, smul_eq_mul]

/--
@isnad1 id=le.0h3v.s8.389545771666 from=translated src=- shape=0d7d6428 vocab=b767f142
-/
lemma norm_toFPS_le (n : ℕ) : ‖toFPS P n‖ ≤ ∑ d ∈ degFinset ι n, ‖coeff d P‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ ↦ ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_monomialCMM_le d n)

/--
@isnad1 id=eq.2h5v.s7.74acee8819b6 from=translated src=- shape=d37b19aa vocab=b3381fc4
-/
lemma norm_term_const {ρ : ℝ} (hρ : 0 ≤ ρ) {n : ℕ} {d : ι →₀ ℕ} (hd : d ∈ degFinset ι n) :
    ‖P.term (fun _ ↦ (ρ : ℂ)) d‖ = ‖coeff d P‖ * ρ ^ n := by
  rw [term, norm_mul, norm_evalMonomial]
  congr 1
  rw [← mem_degFinset.mp hd, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ ↦ by
    rw [Complex.norm_real, Real.norm_of_nonneg hρ]

/-- A locally convergent power series is the sum of its associated formal multilinear series
on a ball around the origin.
@isnad1 id=ex.1h2v.s6.228c403c2d47 from=translated src=- shape=fa348082 vocab=f181fe0a
-/
theorem LocallyConvergent.hasFPowerSeriesOnBall (hP : P.LocallyConvergent) :
    ∃ ρ : ℝ, 0 < ρ ∧ HasFPowerSeriesOnBall P.eval (toFPS P) 0 (ENNReal.ofReal ρ) := by
  obtain ⟨ρ, hρ, hsum⟩ := hP.exists_summableAt_const
  refine ⟨ρ, hρ, ?_, ENNReal.ofReal_pos.mpr hρ, ?_⟩
  · -- the radius of convergence is at least `ρ`
    have hbound : ∀ n : ℕ, ‖toFPS P n‖ * ((Real.toNNReal ρ : NNReal) : ℝ) ^ n ≤
        ∑' d, ‖P.term (fun _ ↦ (ρ : ℂ)) d‖ := by
      intro n
      rw [Real.coe_toNNReal ρ hρ.le]
      have h1 : ‖toFPS P n‖ * ρ ^ n ≤ (∑ d ∈ degFinset ι n, ‖coeff d P‖) * ρ ^ n :=
        mul_le_mul_of_nonneg_right (norm_toFPS_le n) (by positivity)
      have h2 : (∑ d ∈ degFinset ι n, ‖coeff d P‖) * ρ ^ n
          = ∑ d ∈ degFinset ι n, ‖P.term (fun _ ↦ (ρ : ℂ)) d‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun d hd ↦ (norm_term_const hρ.le hd).symm
      have h3 : ∑ d ∈ degFinset ι n, ‖P.term (fun _ ↦ (ρ : ℂ)) d‖ ≤
          ∑' d, ‖P.term (fun _ ↦ (ρ : ℂ)) d‖ :=
        le_hasSum (hasSum_degree_norm hsum) n fun m _ ↦
          Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
      rw [h2] at h1
      exact h1.trans h3
    exact (toFPS P).le_radius_of_bound _ hbound
  · -- and there the series sums to `P.eval`
    intro y hy
    rw [Metric.eball_ofReal, mem_ball_zero_iff] at hy
    have hle : ∀ i, ‖y i‖ ≤ ‖(fun _ ↦ (ρ : ℂ)) i‖ := fun i ↦ by
      refine (norm_le_pi_norm y i).trans ?_
      simp [Complex.norm_real, Real.norm_of_nonneg hρ.le, hy.le]
    have := hasSum_degree (P := P) (x := y) (hsum.mono hle).hasSum
    simpa only [toFPS_apply_diag, zero_add] using this

omit [DecidableEq ι] in
/-- The sum of a locally convergent power series is holomorphic near the origin.
@isnad1 id=analytic.1h2v.s6.d091d3e97b8d from=translated src=- shape=0a5580b4 vocab=8622c665
-/
theorem LocallyConvergent.analyticAt_aux (hP : P.LocallyConvergent) :
    AnalyticAt ℂ P.eval 0 := by
  classical
  obtain ⟨ρ, hρ, h⟩ := hP.hasFPowerSeriesOnBall
  exact h.analyticAt

end Multilinear

section OfFPS

variable [Fintype ι] [DecidableEq ι]

/-- The `i`-th standard basis vector of `ι → ℂ`. -/
def basisVec (i : ι) : ι → ℂ := fun j ↦ if i = j then 1 else 0

/--
@isnad1 id=le.0h2v.s5.01cded2b5886 from=translated src=- shape=257ec9fc vocab=168bacd4
-/
lemma norm_basisVec_le (i : ι) : ‖basisVec i‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j ↦ by
    rw [basisVec]; split <;> simp

/-- The multi-index attached to a tuple of variables. -/
noncomputable def tupleDeg {n : ℕ} (s : Fin n → ι) : ι →₀ ℕ := ∑ k, Finsupp.single (s k) 1

/-- The tuples of variables with a given multi-index. -/
noncomputable def tupleFinset (n : ℕ) (d : ι →₀ ℕ) : Finset (Fin n → ι) :=
  Finset.univ.filter fun s ↦ tupleDeg s = d

omit [Fintype ι] in
/--
@isnad1 id=eq.0h4v.s6.2495a24bf910 from=translated src=- shape=62ce0dda vocab=178cee62
-/
lemma tupleDeg_apply {n : ℕ} (s : Fin n → ι) (i : ι) :
    tupleDeg s i = (Finset.univ.filter fun k ↦ s k = i).card := by
  rw [tupleDeg, Finsupp.finsetSum_apply, Finset.card_filter]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [Finsupp.single_apply]

/--
@isnad1 id=mem.0h3v.s5.173ffad92daf from=translated src=- shape=53f98449 vocab=00085b26
-/
lemma tupleDeg_mem_degFinset {n : ℕ} (s : Fin n → ι) : tupleDeg s ∈ degFinset ι n := by
  rw [mem_degFinset]
  simp_rw [tupleDeg_apply]
  rw [← Finset.card_eq_sum_card_fiberwise (f := s) fun k _ ↦ Finset.mem_univ (s k)]
  simp

omit [Fintype ι] [DecidableEq ι] in
/--
@isnad1 id=eq.0h4v.s5.e3533c28ba57 from=translated src=- shape=69a370a4 vocab=74856cb4
-/
lemma prod_eq_evalMonomial [Finite ι] {n : ℕ} (s : Fin n → ι) (y : ι → ℂ) :
    ∏ k, y (s k) = evalMonomial (tupleDeg s) y := by
  classical
  have := Fintype.ofFinite ι
  rw [evalMonomial_eq_prod,
    ← Finset.prod_fiberwise_of_maps_to (fun k _ ↦ Finset.mem_univ (s k)) fun k ↦ y (s k)]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [tupleDeg_apply, ← Finset.prod_const]
  exact Finset.prod_congr rfl fun k hk ↦ by rw [(Finset.mem_filter.mp hk).2]

/-- The `d`-th coefficient extracted from the `n`-th term of a formal multilinear series. -/
noncomputable def fpsCoeff (p : FormalMultilinearSeries ℂ (ι → ℂ) ℂ) (n : ℕ) (d : ι →₀ ℕ) : ℂ :=
  ∑ s ∈ tupleFinset n d, p n fun k ↦ basisVec (s k)

/-- The power series attached to a formal multilinear series. -/
noncomputable def ofFPS (p : FormalMultilinearSeries ℂ (ι → ℂ) ℂ) : MvPowerSeries ι ℂ :=
  fun d ↦ fpsCoeff p (∑ i, d i) d

/--
@isnad1 id=eq.1h4v.s7.f6053017d541 from=translated src=- shape=0e8ca2ba vocab=12edeb39
-/
lemma coeff_ofFPS (p : FormalMultilinearSeries ℂ (ι → ℂ) ℂ) {n : ℕ} {d : ι →₀ ℕ}
    (hd : d ∈ degFinset ι n) : coeff d (ofFPS p) = fpsCoeff p n d := by
  rw [coeff_apply, ofFPS, mem_degFinset.mp hd]

/-- The value of `p n` on the diagonal is the degree `n` part of the associated power series.
@isnad1 id=eq.0h4v.s8.0bc9fcf32948 from=translated src=- shape=49d45d61 vocab=33b1ac00
-/
lemma apply_diag_eq_sum (p : FormalMultilinearSeries ℂ (ι → ℂ) ℂ) (n : ℕ) (y : ι → ℂ) :
    p n (fun _ ↦ y) = ∑ d ∈ degFinset ι n, (ofFPS p).term y d := by
  conv_lhs => rw [show (fun _ : Fin n ↦ y) = fun _ : Fin n ↦ ∑ i, y i • basisVec i from
    funext fun _ ↦ pi_eq_sum_univ y]
  rw [ContinuousMultilinearMap.map_sum]
  have hterm : ∀ s : Fin n → ι, (p n fun k ↦ y (s k) • basisVec (s k)) =
      evalMonomial (tupleDeg s) y * p n fun k ↦ basisVec (s k) := fun s ↦ by
    rw [ContinuousMultilinearMap.map_smul_univ, prod_eq_evalMonomial, smul_eq_mul]
  simp_rw [hterm]
  rw [← Finset.sum_fiberwise_of_maps_to (fun s _ ↦ tupleDeg_mem_degFinset s)
    fun s ↦ evalMonomial (tupleDeg s) y * p n fun k ↦ basisVec (s k)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [term, coeff_ofFPS p hd, fpsCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [(Finset.mem_filter.mp hs).2, mul_comm]

/--
@isnad1 id=le.0h4v.s8.e97f0b430c90 from=translated src=- shape=e3acc6cd vocab=5c320b8e
-/
lemma norm_fpsCoeff_le (p : FormalMultilinearSeries ℂ (ι → ℂ) ℂ) (n : ℕ) (d : ι →₀ ℕ) :
    ‖fpsCoeff p n d‖ ≤ (tupleFinset n d).card * ‖p n‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  refine ((p n).le_opNorm _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun k _ ↦ norm_basisVec_le _

/--
@isnad1 id=eq.0h2v.s6.f49848be4201 from=translated src=- shape=e9321890 vocab=1e7f833a
-/
lemma sum_card_fibers (n : ℕ) :
    ∑ d ∈ degFinset ι n, ((tupleFinset n d).card : ℝ) = (Fintype.card ι : ℝ) ^ n := by
  simp only [tupleFinset]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise
    (f := fun s : Fin n → ι ↦ tupleDeg s) fun s _ ↦ tupleDeg_mem_degFinset s]
  simp

/--
@isnad1 id=le.2h5v.s6.2cacb8e4cc93 from=translated src=- shape=4307dce3 vocab=7e0403a4
-/
lemma norm_evalMonomial_le_pow {ρ : ℝ} {y : ι → ℂ} (hy : ‖y‖ ≤ ρ) {n : ℕ} {d : ι →₀ ℕ}
    (hd : d ∈ degFinset ι n) : ‖evalMonomial d y‖ ≤ ρ ^ n := by
  have h1 : ∀ i, ‖y i‖ ≤ ρ := fun i ↦ (norm_le_pi_norm y i).trans hy
  rw [norm_evalMonomial, ← mem_degFinset.mp hd, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun i _ ↦ by positivity)
    fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (h1 i) _

/-- Absolute convergence can be checked after regrouping by total degree.
@isnad1 id=summable.2h2v.s6.37d95d60f4a2 from=translated src=- shape=eb1ea401 vocab=9e7145db
-/
lemma summable_of_summable_degFinset {g : (ι →₀ ℕ) → ℝ} (hg : ∀ d, 0 ≤ g d)
    (h : Summable fun n ↦ ∑ d ∈ degFinset ι n, g d) : Summable g := by
  rw [← degreeSigmaEquiv.summable_iff]
  simp only [Function.comp_def]
  rw [summable_sigma_of_nonneg fun _ ↦ hg _]
  refine ⟨fun n ↦ Summable.of_finite, h.congr fun n ↦ ?_⟩
  rw [tsum_fintype]
  exact (Finset.sum_coe_sort _ g).symm

omit [DecidableEq ι] in
/-- Every function holomorphic at the origin is the sum of a locally convergent power series.
@isnad1 id=ex.1h2v.s6.afee96a94ebe from=translated src=- shape=d19d14f7 vocab=5afdca98
-/
theorem exists_represents_aux {f : (ι → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ P : MvPowerSeries ι ℂ, P.LocallyConvergent ∧ P.Represents f := by
  classical
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨u, hu0, hur⟩ := exists_between hp.r_pos
  have hutop : u ≠ ⊤ := (hur.trans_le le_top).ne
  set v : ℝ := u.toReal with hv
  have hv0 : 0 < v := ENNReal.toReal_pos hu0.ne' hutop
  have hvu : ENNReal.ofReal v = u := ENNReal.ofReal_toReal hutop
  obtain ⟨C, hC0, hCbound⟩ := p.norm_mul_pow_le_of_lt_radius (r := u.toNNReal)
    (by rw [ENNReal.coe_toNNReal hutop]; exact hur.trans_le hp.r_le)
  set N : ℕ := Fintype.card ι with hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set ρ : ℝ := v / (2 * (N + 1)) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρv : ρ < v := by
    rw [hρdef]
    exact div_lt_self hv0 (by linarith)
  set q : ℝ := N * ρ / v with hq
  have hqval : q = (N : ℝ) / (2 * (N + 1)) := by
    rw [hq, hρdef]
    field_simp
  have hq0 : 0 ≤ q := by rw [hqval]; positivity
  have hq1 : q < 1 := by
    rw [hqval, div_lt_one (by positivity)]
    linarith
  -- the key estimate: the degree `n` part is bounded by `C * q ^ n`
  have key : ∀ y : ι → ℂ, ‖y‖ ≤ ρ →
      Summable fun n : ℕ ↦ ∑ d ∈ degFinset ι n, ‖(ofFPS p).term y d‖ := by
    intro y hy
    refine Summable.of_nonneg_of_le (fun n ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
      (fun n ↦ ?_) ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
    have h1 : ∀ d ∈ degFinset ι n, ‖(ofFPS p).term y d‖ ≤
        ((tupleFinset n d).card * ‖p n‖) * ρ ^ n := by
      intro d hd
      rw [term, norm_mul, coeff_ofFPS p hd]
      exact mul_le_mul (norm_fpsCoeff_le p n d) (norm_evalMonomial_le_pow hy hd)
        (norm_nonneg _) (by positivity)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_card_fibers]
    have hvn : (v : ℝ) ^ n ≠ 0 := pow_ne_zero _ hv0.ne'
    have hpow : (N : ℝ) ^ n * ‖p n‖ * ρ ^ n = (‖p n‖ * v ^ n) * q ^ n :=
      calc (N : ℝ) ^ n * ‖p n‖ * ρ ^ n = ‖p n‖ * ((N : ℝ) * ρ) ^ n := by rw [mul_pow]; ring
        _ = (‖p n‖ * v ^ n) * (((N : ℝ) * ρ) ^ n / v ^ n) := by field_simp
        _ = (‖p n‖ * v ^ n) * q ^ n := by rw [hq, div_pow]
    rw [hpow]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h2 := hCbound n
    rwa [show ((u.toNNReal : NNReal) : ℝ) = v from rfl] at h2
  -- the resulting power series is locally convergent
  have hconv : ∀ y : ι → ℂ, ‖y‖ ≤ ρ → (ofFPS p).SummableAt y := fun y hy ↦
    summable_of_summable_degFinset (fun _ ↦ norm_nonneg _) (key y hy)
  refine ⟨ofFPS p, ?_, ?_⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : ι → ℂ) hρ0] with y hy
    exact hconv y (mem_ball_zero_iff.mp hy).le
  · filter_upwards [Metric.ball_mem_nhds (0 : ι → ℂ) hρ0] with y hy
    rw [mem_ball_zero_iff] at hy
    -- the multilinear series sums to `f y`
    have hball : y ∈ Metric.eball (0 : ι → ℂ) r := by
      change edist y (0 : ι → ℂ) < r
      have h1 : edist y (0 : ι → ℂ) < ENNReal.ofReal v := by
        rw [edist_zero_right, ← ofReal_norm]
        exact (ENNReal.ofReal_lt_ofReal_iff hv0).mpr (hy.trans hρv)
      rw [hvu] at h1
      exact h1.trans hur
    have h1 := hp.hasSum hball
    rw [zero_add] at h1
    simp_rw [apply_diag_eq_sum] at h1
    -- and so does the regrouped power series
    have h2 := hasSum_degree (P := ofFPS p) (x := y) (hconv y hy.le).hasSum
    rw [h1.unique h2]
    exact (hconv y hy.le).hasSum

end OfFPS

section Unique

variable [Fintype ι]

omit [Fintype ι] in
/--
@isnad1 id=eq.0h5v.s6.0baf918d3c79 from=translated src=- shape=c5133ab8 vocab=8a87aed9
-/
lemma term_sub (P Q : MvPowerSeries ι ℂ) (x : ι → ℂ) (d : ι →₀ ℕ) :
    (P - Q).term x d = P.term x d - Q.term x d := by
  simp [term, sub_mul]

omit [Fintype ι] in
/--
@isnad1 id=represen.2h5v.s6.e563736eefaf from=translated src=- shape=45b92ee7 vocab=5ce3606d
-/
lemma Represents.sub {f g : (ι → ℂ) → ℂ} (hP : P.Represents f) (hQ : Q.Represents g) :
    (P - Q).Represents (f - g) := by
  filter_upwards [hP, hQ] with x hx hx'
  have h : (P - Q).term x = fun d ↦ P.term x d - Q.term x d := funext (term_sub P Q x)
  rw [h, Pi.sub_apply]
  exact hx.sub hx'

omit [Fintype ι] in
/-- A power series which converges pointwise near the origin converges absolutely there.
@isnad1 id=locallyc.1h3v.s4.351742fa026a from=translated src=- shape=afafc207 vocab=03e07003
-/
lemma Represents.locallyConvergent {f : (ι → ℂ) → ℂ} (hP : P.Represents f) :
    P.LocallyConvergent := by
  filter_upwards [hP] with x hx
  exact summable_norm_iff.mpr hx.summable

/--
@isnad1 id=eq.0h4v.s6.929bd7d5c4c8 from=translated src=- shape=cf27aec4 vocab=0ff86e52
-/
lemma evalMonomial_smul (t : ℂ) (y : ι → ℂ) (d : ι →₀ ℕ) :
    evalMonomial d (t • y) = t ^ (∑ i, d i) * evalMonomial d y := by
  rw [evalMonomial_eq_prod, evalMonomial_eq_prod, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [Pi.smul_apply, smul_eq_mul, mul_pow]

/-- The coefficients of a one variable power series which sums to zero near the origin
vanish. -/
lemma eq_zero_of_hasSum_zero {a : ℕ → ℂ} {C : ℝ} (hbound : ∀ n, ‖a n‖ ≤ C)
    (hzero : ∀ᶠ t : ℂ in 𝓝 0, HasSum (fun n ↦ a n * t ^ n) 0) (n : ℕ) : a n = 0 := by
  set p := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hnorm : ∀ m, ‖p m‖ ≤ ‖a m‖ := by
    intro m
    rw [hp, FormalMultilinearSeries.ofScalars, norm_smul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    simp
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hbound 0)
  have hrad : ((1 : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_bound C fun m ↦ ?_
    simpa using (hnorm m).trans (hbound m)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hzero
  have hfps : HasFPowerSeriesAt (0 : ℂ → ℂ) p 0 := by
    refine ⟨min (ENNReal.ofReal ε) 1, le_trans (min_le_right _ _) (by simpa using hrad),
      lt_min (ENNReal.ofReal_pos.mpr hε) one_pos, fun {y} hy ↦ ?_⟩
    have hy' : y ∈ Metric.ball (0 : ℂ) ε := by
      rw [mem_ball_zero_iff]
      have h1 : edist y (0 : ℂ) < ENNReal.ofReal ε := lt_of_lt_of_le hy (min_le_left _ _)
      rwa [edist_zero_right, ← ofReal_norm,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)] at h1
    have h2 := hball hy'
    simpa [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using h2
  have hpz : p = 0 := hfps.eq_zero
  have h0 : p n (fun _ ↦ (1 : ℂ)) = a n := by
    rw [hp, FormalMultilinearSeries.ofScalars_apply_eq]
    simp
  rw [← h0, hpz]
  simp

variable [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A power series which sums to zero near the origin is zero. -/
theorem eq_zero_of_represents_zero [Finite ι] {R : MvPowerSeries ι ℂ} (hR : R.Represents 0) :
    R = 0 := by
  classical
  have := Fintype.ofFinite ι
  have hconv : R.LocallyConvergent := hR.locallyConvergent
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hR.and hconv)
  set ρ := ε / 2 with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hmem : ∀ x : ι → ℂ, ‖x‖ ≤ ρ → HasSum (R.term x) 0 ∧ R.SummableAt x := by
    intro x hx
    refine hball ?_
    rw [mem_ball_zero_iff]
    calc ‖x‖ ≤ ρ := hx
      _ < ε := by rw [hρdef]; linarith
  -- the homogeneous parts vanish on a polydisc
  have hhom : ∀ y : ι → ℂ, ‖y‖ ≤ ρ → ∀ n : ℕ,
      ∑ d ∈ degFinset ι n, coeff d R * evalMonomial d y = 0 := by
    intro y hy n
    refine eq_zero_of_hasSum_zero (a := fun m ↦ ∑ d ∈ degFinset ι m, coeff d R * evalMonomial d y)
      (C := ∑' d, ‖R.term y d‖) (fun m ↦ ?_) ?_ n
    · calc ‖∑ d ∈ degFinset ι m, coeff d R * evalMonomial d y‖
          ≤ ∑ d ∈ degFinset ι m, ‖R.term y d‖ := by
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl fun d _ ↦ rfl
        _ ≤ ∑' d, ‖R.term y d‖ :=
            le_hasSum (hasSum_degree_norm (hmem y hy).2) m fun _ _ ↦
              Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with t ht
      rw [mem_ball_zero_iff] at ht
      have hty : ‖t • y‖ ≤ ρ := by
        rw [norm_smul]
        calc ‖t‖ * ‖y‖ ≤ 1 * ρ := by
              refine mul_le_mul ht.le hy (norm_nonneg _) zero_le_one
          _ = ρ := one_mul ρ
      have h2 := hasSum_degree (hmem (t • y) hty).1
      have hfun : (fun m ↦ ∑ d ∈ degFinset ι m, R.term (t • y) d) =
          fun m ↦ (∑ d ∈ degFinset ι m, coeff d R * evalMonomial d y) * t ^ m := by
        funext m
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        rw [term, evalMonomial_smul, mem_degFinset.mp hd]
        ring
      rwa [hfun] at h2
  -- by homogeneity they vanish identically
  have hall : ∀ (n : ℕ) (y : ι → ℂ), ∑ d ∈ degFinset ι n, coeff d R * evalMonomial d y = 0 := by
    intro n y
    set l : ℝ := ρ / (‖y‖ + 1) with hl
    have hl0 : 0 < l := by positivity
    have hly : ‖(l : ℂ) • y‖ ≤ ρ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hl0.le, hl, div_mul_eq_mul_div,
        div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg y, hρ0]
    have h1 := hhom _ hly n
    have h2 : ∑ d ∈ degFinset ι n, coeff d R * evalMonomial d ((l : ℂ) • y) =
        (l : ℂ) ^ n * ∑ d ∈ degFinset ι n, coeff d R * evalMonomial d y := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [evalMonomial_smul, mem_degFinset.mp hd]
      ring
    rw [h2] at h1
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hl0.ne'))
  -- and hence so do the coefficients, by the identity theorem for polynomials
  refine MvPowerSeries.ext fun d ↦ ?_
  have hΦ : (∑ e ∈ degFinset ι (∑ i, d i), MvPolynomial.monomial e (coeff e R) :
      MvPolynomial ι ℂ) = 0 := by
    refine MvPolynomial.funext fun y ↦ ?_
    rw [map_zero, map_sum]
    simpa [MvPolynomial.eval_monomial, evalMonomial] using hall (∑ i, d i) y
  have h3 := congrArg (MvPolynomial.coeff d) hΦ
  rw [MvPolynomial.coeff_sum] at h3
  simp only [MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero] at h3
  rw [Finset.sum_ite_eq' (degFinset ι (∑ i, d i)) d (fun e ↦ coeff e R)] at h3
  rw [ite_eq_left (self_mem_degFinset d)] at h3
  simpa using h3

omit [Fintype ι] [DecidableEq ι] in
/-- A power series is determined by the germ at the origin of the function it represents:
the identity theorem for convergent power series.
@isnad1 id=eq.2h4v.s5.5edb8044f622 from=translated src=- shape=f6c8f138 vocab=e2f01f9b
-/
theorem Represents.unique [Finite ι] {f : (ι → ℂ) → ℂ} (hP : P.Represents f)
    (hQ : Q.Represents f) : P = Q := by
  have h : (P - Q).Represents 0 := by
    have h1 := hP.sub hQ
    rwa [sub_self] at h1
  exact sub_eq_zero.mp (eq_zero_of_represents_zero h)

end Unique

end AnalyticDictionary

/-- Every function which is holomorphic near the origin is the sum of a locally convergent
power series, namely of its Taylor series at the origin.
@isnad1 id=ex.1h2v.s6.afee96a94ebe from=translated src=- shape=d19d14f7 vocab=5afdca98
-/
theorem exists_represents [Fintype ι] {f : (ι → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ P : MvPowerSeries ι ℂ, P.LocallyConvergent ∧ P.Represents f := by
  classical
  exact exists_represents_aux hf

/-- The sum of a locally convergent power series is holomorphic near the origin.
@isnad1 id=analytic.1h2v.s6.c0df826fe802 from=translated src=- shape=779bf4a0 vocab=8622c665
-/
theorem LocallyConvergent.analyticAt [Fintype ι] {P : MvPowerSeries ι ℂ}
    (hP : P.LocallyConvergent) : AnalyticAt ℂ P.eval 0 := by
  classical
  exact hP.analyticAt_aux

/-- If the constant term of a locally convergent power series does not vanish, its formal
inverse is again locally convergent: the inverse of a nonvanishing holomorphic function is
holomorphic.
@isnad1 id=locallyc.2h2v.s6.325762fa2f8c from=translated src=- shape=b14346e7 vocab=0fa37805
-/
theorem LocallyConvergent.inv [Finite ι] {P : MvPowerSeries ι ℂ} (hP : P.LocallyConvergent)
    (h : constantCoeff P ≠ 0) : P⁻¹.LocallyConvergent := by
  have := Fintype.ofFinite ι
  have hA : AnalyticAt ℂ P.eval 0 := hP.analyticAt
  have hne : P.eval 0 ≠ 0 := by rwa [eval_zero]
  -- the reciprocal of the sum of `P` is holomorphic, hence has a Taylor series `Q`
  obtain ⟨Q, hQc, hQ⟩ := exists_represents (hA.inv hne)
  -- `P * Q` represents the constant function `1`
  have h1 : (P * Q).Represents (Function.const (ι → ℂ) 1) := by
    refine (Represents.mul hP hQc hP.represents_eval hQ).congr ?_
    filter_upwards [hA.continuousAt.eventually_ne hne] with x hx
    simp [mul_inv_cancel₀ hx]
  -- hence `Q` is the formal inverse of `P`
  have hPQ : P * Q = 1 := h1.unique represents_one
  have hQP : Q = P⁻¹ := by
    calc Q = Q * (P * P⁻¹) := by rw [MvPowerSeries.mul_inv_cancel P h, mul_one]
    _ = P * Q * P⁻¹ := by ring
    _ = P⁻¹ := by rw [hPQ, one_mul]
  exact hQP ▸ hQc

end Represents

end MvPowerSeries

open MvPowerSeries

variable (ι) in
/-- The subalgebra of locally convergent power series. -/
def _root_.Tengoku.LanaOka.localOkaSubring : Subalgebra ℂ (MvPowerSeries ι ℂ) where
  carrier := { P | P.LocallyConvergent }
  mul_mem' := LocallyConvergent.mul
  add_mem' := LocallyConvergent.add
  algebraMap_mem' := locallyConvergent_algebraMap

variable (ι) in
/-- The ring of locally convergent power series, i.e. the ring of germs at the origin of
holomorphic functions on `ℂ^ι`. -/
abbrev _root_.Tengoku.LanaOka.LocalOkaRing : Type u :=
  localOkaSubring ι

namespace Tengoku.LanaOka.LocalOkaRing

noncomputable instance : CommRing (LocalOkaRing ι) :=
  inferInstanceAs <| CommRing (localOkaSubring ι)

noncomputable instance : Algebra ℂ (LocalOkaRing ι) :=
  inferInstanceAs <| Algebra ℂ (localOkaSubring ι)

/--
@isnad1 id=locallyc.0h2v.s6.40439b8af97e from=translated src=- shape=6c0c3f78 vocab=a0fa70e9
-/
@[simp]
lemma locallyConvergent (P : LocalOkaRing ι) : (P : MvPowerSeries ι ℂ).LocallyConvergent :=
  P.2

/--
@isnad1 id=eq.1h3v.s7.b477d67304e5 from=translated src=- shape=a1b0d61b vocab=3b34545a
-/
@[ext]
lemma ext {P Q : LocalOkaRing ι} (h : (P : MvPowerSeries ι ℂ) = Q) : P = Q :=
  Subtype.ext h

/-- The constant term of a locally convergent power series. -/
noncomputable def constantCoeff : LocalOkaRing ι →+* ℂ :=
  (MvPowerSeries.constantCoeff (σ := ι) (R := ℂ)).comp (localOkaSubring ι).val.toRingHom

/--
@isnad1 id=eq.0h2v.s7.b69a8c518569 from=translated src=- shape=11e576a5 vocab=87ea5d63
-/
@[simp]
lemma constantCoeff_apply (P : LocalOkaRing ι) :
    constantCoeff P = MvPowerSeries.constantCoeff (P : MvPowerSeries ι ℂ) :=
  rfl

-- Not `@[simp]`: `constantCoeff_apply` is `@[simp]` and rewrites the left-hand side to
-- `MvPowerSeries.constantCoeff ↑(algebraMap ℂ (LocalOkaRing ι) c)`, which
-- `Subalgebra.coe_algebraMap` and `MvPowerSeries.constantCoeff_C` then finish, so the attribute
-- here would never fire.
/-- A constant power series has that constant as its constant term.
@isnad1 id=eq.0h2v.s7.751c6e2aee40 from=translated src=- shape=c3155228 vocab=d9acd410
-/
lemma constantCoeff_algebraMap (c : ℂ) :
    constantCoeff (algebraMap ℂ (LocalOkaRing ι) c) = c := by
  rw [constantCoeff_apply, show ((algebraMap ℂ (LocalOkaRing ι) c : LocalOkaRing ι) :
    MvPowerSeries ι ℂ) = algebraMap ℂ (MvPowerSeries ι ℂ) c from rfl,
    MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C]
  simp

instance : Nontrivial (LocalOkaRing ι) :=
  ⟨0, 1, fun h ↦ by simpa using congrArg constantCoeff h⟩

variable [Finite ι]

/-- A locally convergent power series is invertible if and only if its constant term does not
vanish.
@isnad1 id=iff.0h2v.s6.d7b01c39f609 from=translated src=- shape=89229322 vocab=9d46135d
-/
theorem isUnit_iff {P : LocalOkaRing ι} : IsUnit P ↔ constantCoeff P ≠ 0 := by
  refine ⟨fun h ↦ (h.map constantCoeff).ne_zero, fun h ↦ ?_⟩
  exact (IsUnit.of_mul_eq_one ⟨(P : MvPowerSeries ι ℂ)⁻¹, P.2.inv h⟩
    (ext (MvPowerSeries.mul_inv_cancel _ h)))

instance : IsLocalRing (LocalOkaRing ι) := by
  refine IsLocalRing.of_nonunits_add fun P Q hP hQ ↦ ?_
  rw [mem_nonunits_iff, isUnit_iff, not_not] at hP hQ ⊢
  rw [map_add, hP, hQ, add_zero]

omit [Finite ι] in
/-- A germ in no variables is its own constant term, so it is a unit as soon as it is nonzero:
`LocalOkaRing ι` is a field for `ι` empty.
@isnad1 id=iff.0h2v.s6.e0dfa2449cfb from=translated src=- shape=2dc5266c vocab=68ea76e8
-/
theorem isUnit_iff_ne_zero [IsEmpty ι] {P : LocalOkaRing ι} : IsUnit P ↔ P ≠ 0 := by
  rw [isUnit_iff, constantCoeff_apply, ne_eq, ne_eq, not_iff_not]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; simp⟩
  refine LocalOkaRing.ext (MvPowerSeries.ext fun d ↦ ?_)
  have hd : d = 0 := by ext i; exact (IsEmpty.false i).elim
  subst hd
  simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]

end Tengoku.LanaOka.LocalOkaRing

section Germ

variable [Fintype ι] {U : Opens (ι → ℂ)}

/-- A holomorphic function on `U` is holomorphic at every point of `U`.
@isnad1 id=analytic.1h4v.s7.e375688678ab from=translated src=- shape=7b518b82 vocab=a9d80e78
-/
lemma Tengoku.LanaOka.OkaRing.analyticAt_toGlobalFun (f : OkaRing U) {x : ι → ℂ} (hx : x ∈ U) :
    AnalyticAt ℂ (f.toGlobalFun _) x :=
  (okaAnalytic_iff _).mp f.2 x hx

open Classical in
/-- The Taylor series at the origin of a holomorphic function defined on an open neighbourhood
`U` of the origin. -/
noncomputable def Tengoku.LanaOka.OkaRing.toLocalOkaRing (h0 : (0 : ι → ℂ) ∈ U) (f : OkaRing U) :
    LocalOkaRing ι :=
  ⟨(exists_represents (f.analyticAt_toGlobalFun h0)).choose,
    (exists_represents (f.analyticAt_toGlobalFun h0)).choose_spec.1⟩

/--
@isnad1 id=represen.1h3v.s7.19e2763d2ebc from=translated src=- shape=dad421bd vocab=d2f0ae96
-/
lemma Tengoku.LanaOka.OkaRing.toLocalOkaRing_represents (h0 : (0 : ι → ℂ) ∈ U) (f : OkaRing U) :
    ((f.toLocalOkaRing h0 : LocalOkaRing ι) : MvPowerSeries ι ℂ).Represents (f.toGlobalFun _) :=
  (exists_represents (f.analyticAt_toGlobalFun h0)).choose_spec.2

/-- The Taylor series is the unique locally convergent power series representing the given
function.
@isnad1 id=eq.2h4v.s7.672210dd25ce from=translated src=- shape=ba077479 vocab=b23fa821
-/
lemma Tengoku.LanaOka.OkaRing.toLocalOkaRing_eq_of_represents {h0 : (0 : ι → ℂ) ∈ U} {f : OkaRing U}
    {P : LocalOkaRing ι} (h : (P : MvPowerSeries ι ℂ).Represents (f.toGlobalFun _)) :
    f.toLocalOkaRing h0 = P :=
  LocalOkaRing.ext ((f.toLocalOkaRing_represents h0).unique h)

/-- Away from `U`, the values of `f : OkaRing U` do not matter: near the origin, the extension
by zero of `f` is any function agreeing with `f` on `U`.
@isnad1 id=eventual.2h4v.s8.0675024943c8 from=translated src=- shape=27abeb4e vocab=a7c0b3fd
-/
lemma Tengoku.LanaOka.OkaRing.toGlobalFun_eventuallyEq (h0 : (0 : ι → ℂ) ∈ U) {f : OkaRing U}
    {g : (ι → ℂ) → ℂ} (h : ∀ x : U, f.toFun _ x = g x) :
    f.toGlobalFun _ =ᶠ[𝓝 (0 : ι → ℂ)] g := by
  filter_upwards [U.isOpen.mem_nhds h0] with x hx
  rw [f.toGlobalFun_apply hx]
  exact h ⟨x, hx⟩

variable (U) in
/-- The `ℂ`-algebra map sending a holomorphic function on an open neighbourhood `U` of the
origin to its Taylor series at the origin. -/
noncomputable def Tengoku.LanaOka.OkaRing.toLocalOkaRingHom (h0 : (0 : ι → ℂ) ∈ U) :
    OkaRing U →ₐ[ℂ] LocalOkaRing ι where
  toFun f := f.toLocalOkaRing h0
  map_one' := by
    refine toLocalOkaRing_eq_of_represents (P := 1) ?_
    rw [OneMemClass.coe_one]
    exact represents_one.congr
      (toGlobalFun_eventuallyEq h0 (g := Function.const _ 1) fun _ ↦ rfl).symm
  map_mul' f g := by
    refine toLocalOkaRing_eq_of_represents ?_
    rw [MulMemClass.coe_mul]
    refine (Represents.mul (Subtype.prop _) (Subtype.prop _)
      (f.toLocalOkaRing_represents h0) (g.toLocalOkaRing_represents h0)).congr ?_
    refine (toGlobalFun_eventuallyEq h0 (g := f.toGlobalFun _ * g.toGlobalFun _) ?_).symm
    intro x
    rw [Pi.mul_apply, f.toGlobalFun_apply x.2, g.toGlobalFun_apply x.2]
    rfl
  map_zero' := by
    refine toLocalOkaRing_eq_of_represents (P := 0) ?_
    rw [ZeroMemClass.coe_zero]
    exact represents_zero.congr
      (toGlobalFun_eventuallyEq h0 (g := Function.const _ 0) fun _ ↦ rfl).symm
  map_add' f g := by
    refine toLocalOkaRing_eq_of_represents ?_
    rw [AddMemClass.coe_add]
    refine ((f.toLocalOkaRing_represents h0).add (g.toLocalOkaRing_represents h0)).congr ?_
    refine (toGlobalFun_eventuallyEq h0 (g := f.toGlobalFun _ + g.toGlobalFun _) ?_).symm
    intro x
    rw [Pi.add_apply, f.toGlobalFun_apply x.2, g.toGlobalFun_apply x.2]
    rfl
  commutes' c := by
    refine toLocalOkaRing_eq_of_represents ?_
    rw [show ((algebraMap ℂ (LocalOkaRing ι) c : LocalOkaRing ι) : MvPowerSeries ι ℂ) =
      algebraMap ℂ (MvPowerSeries ι ℂ) c from rfl]
    exact (represents_algebraMap (ι := ι) c).congr
      (toGlobalFun_eventuallyEq h0 (g := Function.const _ c) fun _ ↦ rfl).symm

/--
@isnad1 id=eq.1h3v.s8.4929647f3b61 from=translated src=- shape=392add95 vocab=333b070d
-/
@[simp]
lemma Tengoku.LanaOka.OkaRing.toLocalOkaRingHom_apply (h0 : (0 : ι → ℂ) ∈ U) (f : OkaRing U) :
    OkaRing.toLocalOkaRingHom U h0 f = f.toLocalOkaRing h0 :=
  rfl

/-- Every locally convergent power series is the Taylor series at the origin of a holomorphic
function on some open neighbourhood of the origin.
@isnad1 id=ex.0h2v.s8.3aab2cefebb6 from=translated src=- shape=718c653d vocab=440c7207
-/
theorem Tengoku.LanaOka.LocalOkaRing.exists_okaRing (P : LocalOkaRing ι) :
    ∃ (U : Opens (ι → ℂ)) (h0 : (0 : ι → ℂ) ∈ U) (f : OkaRing U),
      OkaRing.toLocalOkaRingHom U h0 f = P := by
  obtain ⟨s, hs, hsopen, h0⟩ := mem_nhds_iff.mp P.2.analyticAt.eventually_analyticAt
  refine ⟨⟨s, hsopen⟩, h0, ⟨fun x ↦ (P : MvPowerSeries ι ℂ).eval x, ?_⟩, ?_⟩
  · exact okaAnalytic_restrict fun x hx ↦ hs hx
  · refine OkaRing.toLocalOkaRing_eq_of_represents (h0 := h0) (P.2.represents_eval.congr ?_)
    exact (OkaRing.toGlobalFun_eventuallyEq h0 fun x ↦ rfl).symm

end Germ

variable {n : ℕ}

section

open Polynomial

variable {σ τ : Type*} {R : Type*} [CommRing R]

/--
@isnad1 id=tendstoc.0h2v.s3.1c772548bf75 from=translated src=- shape=650ca721 vocab=29300988
-/
instance Filter.TendstoCofinite.subtypeVal {α : Type*} {p : α → Prop} :
    TendstoCofinite (Subtype.val : Subtype p → α) :=
  tendstoCofinite_of_injective Subtype.val_injective

namespace MvPowerSeries

section Aux

variable (f : τ → σ) [TendstoCofinite f] (hf : Function.Injective f) {i : σ}
  (hi : i ∉ Set.range f)

include hf hi in
/-- Auxiliary lemma for `MvPowerSeries.coeff_fromPolynomial` and
`MvPowerSeries.coeff_fromPolynomial'`. -/
private lemma coeff_eval₂AlgHom_rename (Q : (MvPowerSeries τ R)[X]) (e : τ →₀ ℕ) (k : ℕ) :
    coeff (Finsupp.mapDomain f e + Finsupp.single i k)
      (Polynomial.eval₂AlgHom (rename f) (X i) (fun _ ↦ Commute.all _ _) Q) =
        coeff e (Q.coeff k) := by
  have hD : ∀ x : τ →₀ ℕ, Finsupp.mapDomain f x i = 0 := fun x ↦
    Finsupp.mapDomain_of_notMem_range x i hi
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial k' a =>
    rw [Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_monomial, X_pow_eq, coeff_mul_monomial]
    simp only [RingHom.coe_coe]
    -- the monomial `X i ^ k'` divides the exponent `mapDomain f e + single i k` iff `k' ≤ k`
    have hle : Finsupp.single i k' ≤ Finsupp.mapDomain f e + Finsupp.single i k ↔ k' ≤ k := by
      refine ⟨fun h ↦ by simpa [hD] using h i, fun h j ↦ ?_⟩
      rcases eq_or_ne j i with rfl | hj
      · simpa [hD] using h
      · simp [hj]
    have hsub : ∀ m : ℕ, Finsupp.mapDomain f e + Finsupp.single i k - Finsupp.single i m =
        Finsupp.mapDomain f e + Finsupp.single i (k - m) := by
      refine fun m ↦ Finsupp.ext fun j ↦ ?_
      rcases eq_or_ne j i with rfl | hj
      · simp [hD]
      · simp [hj]
    -- and the renamed coefficients only see the exponents avoiding `i`
    have hcoeff : ∀ m : ℕ, coeff (Finsupp.mapDomain f e + Finsupp.single i m) (rename f a) =
        if m = 0 then coeff e a else 0 := by
      intro m
      rcases eq_or_ne m 0 with rfl | hm
      · have h : Finsupp.mapDomain f e = Finsupp.embDomain ⟨f, hf⟩ e :=
          (Finsupp.embDomain_eq_mapDomain ⟨f, hf⟩ e).symm
        rw [ite_eq_left rfl, Finsupp.single_zero, add_zero, h]
        exact coeff_embDomain_rename ⟨f, hf⟩ a e
      · rw [ite_eq_right hm]
        refine coeff_rename_eq_zero f a ?_
        rintro ⟨x, hx⟩
        exact hm (by simpa [hD] using (congrArg (fun g ↦ g i) hx).symm)
    rw [Polynomial.coeff_monomial]
    rcases le_or_gt k' k with h | h
    · rw [ite_eq_left (hle.mpr h), hsub, hcoeff, mul_one]
      rcases eq_or_ne k' k with rfl | hk
      · simp
      · rw [ite_eq_right (by omega : ¬ k - k' = 0), ite_eq_right hk, map_zero]
    · have hlt : ¬ Finsupp.single i k' ≤ Finsupp.mapDomain f e + Finsupp.single i k := fun hc ↦
        absurd (hle.mp hc) (by omega)
      rw [ite_eq_right hlt, ite_eq_right (by omega : ¬ k' = k), map_zero]

include hf hi in
/-- Auxiliary lemma for `MvPowerSeries.fromPolynomial_injective` and
`MvPowerSeries.fromPolynomial'_injective`. -/
private lemma eval₂AlgHom_rename_injective :
    Function.Injective (Polynomial.eval₂AlgHom (R := R) (rename f) (X i)
      (fun _ ↦ Commute.all _ _)) := by
  intro P Q h
  refine Polynomial.ext fun k ↦ MvPowerSeries.ext fun e ↦ ?_
  rw [← coeff_eval₂AlgHom_rename f hf hi P e k, ← coeff_eval₂AlgHom_rename f hf hi Q e k, h]

end Aux

section FromPolynomial

variable (i : σ)

/-- The `R`-algebra map from the polynomials over the power series in the variables `j ≠ i` to
the power series in all variables, sending the polynomial variable to `X i`. -/
noncomputable def fromPolynomial :
    (MvPowerSeries { j : σ // j ≠ i } R)[X] →ₐ[R] MvPowerSeries σ R :=
  Polynomial.eval₂AlgHom (rename Subtype.val) (X i) fun _ ↦ Commute.all _ _

variable {i}

private lemma notMem_range_subtypeVal :
    i ∉ Set.range (Subtype.val : { j : σ // j ≠ i } → σ) := by
  rintro ⟨⟨j, hj⟩, hji⟩
  exact hj hji

/--
@isnad1 id=eq.0h4v.s9.972a30b91dac from=translated src=- shape=057c4034 vocab=cb676c37
-/
@[simp]
lemma fromPolynomial_C (P : MvPowerSeries { j : σ // j ≠ i } R) :
    fromPolynomial i (Polynomial.C P) = rename Subtype.val P :=
  Polynomial.eval₂_C _ _

/--
@isnad1 id=eq.0h3v.s8.6719d524030f from=translated src=- shape=5fb1b33e vocab=07feff02
-/
@[simp]
lemma fromPolynomial_X : fromPolynomial (R := R) i Polynomial.X = X i :=
  Polynomial.eval₂_X _ _

/-- The coefficients of `MvPowerSeries.fromPolynomial i Q` are the coefficients of the
coefficients of `Q`.
@isnad1 id=eq.0h6v.s9.3a2ed44bcbc5 from=translated src=- shape=e46236e8 vocab=861014d0
-/
lemma coeff_fromPolynomial (Q : (MvPowerSeries { j : σ // j ≠ i } R)[X])
    (e : { j : σ // j ≠ i } →₀ ℕ) (k : ℕ) :
    coeff (Finsupp.mapDomain Subtype.val e + Finsupp.single i k) (fromPolynomial i Q) =
      coeff e (Q.coeff k) :=
  coeff_eval₂AlgHom_rename _ Subtype.val_injective notMem_range_subtypeVal Q e k

/--
@isnad1 id=injectiv.0h3v.s8.7a0032017077 from=translated src=- shape=73bc59e3 vocab=475058c2
-/
lemma fromPolynomial_injective : Function.Injective (fromPolynomial (R := R) i) :=
  eval₂AlgHom_rename_injective _ Subtype.val_injective notMem_range_subtypeVal

end FromPolynomial

section FromPolynomial'

/-- The `R`-algebra map from the polynomials over the power series in `n` variables to the
power series in `n + 1` variables, sending the polynomial variable to the last variable. -/
noncomputable def fromPolynomial' :
    (MvPowerSeries (Fin n) R)[X] →ₐ[R] MvPowerSeries (Fin (n + 1)) R :=
  Polynomial.eval₂AlgHom (rename Fin.castSucc) (X (Fin.last n)) fun _ ↦ Commute.all _ _

private lemma last_notMem_range_castSucc :
    Fin.last n ∉ Set.range (Fin.castSucc : Fin n → Fin (n + 1)) := by
  simp

/--
@isnad1 id=eq.0h3v.s9.b531bf984f5d from=translated src=- shape=9a0feb22 vocab=a327742f
-/
@[simp]
lemma fromPolynomial'_C (P : MvPowerSeries (Fin n) R) :
    fromPolynomial' (Polynomial.C P) = rename Fin.castSucc P :=
  Polynomial.eval₂_C _ _

/--
@isnad1 id=eq.0h2v.s8.0067ecb4d9ef from=translated src=- shape=11760ce0 vocab=49f24ccb
-/
@[simp]
lemma fromPolynomial'_X : fromPolynomial' (R := R) (n := n) Polynomial.X = X (Fin.last n) :=
  Polynomial.eval₂_X _ _

/-- The coefficients of `MvPowerSeries.fromPolynomial' Q` are the coefficients of the
coefficients of `Q`.
@isnad1 id=eq.0h5v.s9.0ad37472322b from=translated src=- shape=aa855f2a vocab=6c647e71
-/
lemma coeff_fromPolynomial' (Q : (MvPowerSeries (Fin n) R)[X]) (e : Fin n →₀ ℕ) (k : ℕ) :
    coeff (Finsupp.mapDomain Fin.castSucc e + Finsupp.single (Fin.last n) k)
      (fromPolynomial' Q) = coeff e (Q.coeff k) :=
  coeff_eval₂AlgHom_rename _ (Fin.castSucc_injective n) last_notMem_range_castSucc Q e k

/--
@isnad1 id=injectiv.0h2v.s8.30dcc139c724 from=translated src=- shape=49e9f736 vocab=8a76be4a
-/
lemma fromPolynomial'_injective :
    Function.Injective (fromPolynomial' (R := R) (n := n)) :=
  eval₂AlgHom_rename_injective _ (Fin.castSucc_injective n) last_notMem_range_castSucc

end FromPolynomial'

/-- A power series is polynomial in the variable `i` if it lies in the image of
`MvPowerSeries.fromPolynomial i`. -/
def IsPolynomialIn (P : MvPowerSeries ι R) (i : ι) :
    Prop :=
  ∃ (Q : (MvPowerSeries { j : ι //  j ≠ i } R)[X]),
    MvPowerSeries.fromPolynomial i Q = P

/-- The polynomial in the variable `i` attached to a power series that is polynomial in `i`. -/
noncomputable
def IsPolyonmialIn.polynomial {P : MvPowerSeries ι R}
    {i : ι}
    (h : P.IsPolynomialIn i) :
    (MvPowerSeries { j : ι //   j ≠ i } R)[X] :=
  h.choose

section PartialEval

variable (i : σ)

/-- The map `P ↦ P(0, ..., z_i, 0, ..., 0)`, as an `R`-algebra map to the power series in one
variable. -/
noncomputable def partialEval : MvPowerSeries σ R →ₐ[R] PowerSeries R :=
  killCompl ⟨fun _ ↦ i, Function.injective_of_subsingleton _⟩

variable {i}

/--
@isnad1 id=eq.0h5v.s8.bd6c628152ff from=translated src=- shape=b2c99910 vocab=f14eb65c
-/
@[simp]
lemma coeff_partialEval (P : MvPowerSeries σ R) (k : ℕ) :
    PowerSeries.coeff k (partialEval i P) = coeff (Finsupp.single i k) P :=
  (coeff_killCompl P (Finsupp.single () k)).trans (by
    rw [Finsupp.embDomain_single]
    rfl)

/--
@isnad1 id=eq.0h4v.s8.ed662318dcb4 from=translated src=- shape=3380c3af vocab=7255d222
-/
@[simp]
lemma partialEval_C (r : R) : partialEval i (C r : MvPowerSeries σ R) = PowerSeries.C r :=
  killCompl_C r

/--
@isnad1 id=eq.0h3v.s7.f2294c261953 from=translated src=- shape=8d11aabe vocab=1e1c2135
-/
@[simp]
lemma partialEval_X_self : partialEval i (X i : MvPowerSeries σ R) = PowerSeries.X :=
  killCompl_X ()

/--
@isnad1 id=eq.1h4v.s7.568e85507c67 from=translated src=- shape=2b274fa9 vocab=2e815979
-/
@[simp]
lemma partialEval_X_of_ne {j : σ} (h : j ≠ i) : partialEval i (X j : MvPowerSeries σ R) = 0 :=
  killCompl_X_eq_zero (by simpa using h)

/--
@isnad1 id=eq.0h4v.s8.1b094da6494b from=translated src=- shape=27f6308f vocab=99624c8e
-/
@[simp]
lemma constantCoeff_partialEval (P : MvPowerSeries σ R) :
    PowerSeries.constantCoeff (partialEval i P) = constantCoeff P := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_partialEval,
    ← coeff_zero_eq_constantCoeff_apply, Finsupp.single_zero]

/-- **A simple zero along the `i`-th axis is two coefficients**: `P` restricted to that axis
vanishes to order exactly one if and only if `P` has no constant term and its `i`-linear
coefficient is nonzero.

`MvPowerSeries.partialEval` reads the `k`-th coefficient of the restriction off the exponent
`Finsupp.single i k` (`MvPowerSeries.coeff_partialEval`), so `order = 1` unfolds through
`PowerSeries.order_eq_nat` into the two exponents `0` and `Finsupp.single i 1` and no others.
**No derivative appears**, and that is the point: the linear coefficient *is* the first
derivative along the axis up to nothing at all, so a consumer that has a derivative may use it
and a consumer that does not need not acquire one.
@isnad1 id=iff.0h4v.s8.cec1630eef17 from=translated src=- shape=bd436cb0 vocab=399ef3f8
-/
lemma order_partialEval_eq_one_iff (P : MvPowerSeries σ R) :
    PowerSeries.order (partialEval i P) = 1 ↔
      constantCoeff P = 0 ∧ coeff (Finsupp.single i 1) P ≠ 0 := by
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
  simp only [coeff_partialEval]
  refine ⟨fun ⟨h1, h0⟩ ↦ ⟨by simpa using h0 0 (by norm_num), h1⟩, fun ⟨h0, h1⟩ ↦ ⟨h1, ?_⟩⟩
  intro j hj
  interval_cases j
  simpa using h0

/-- Restricting `MvPowerSeries.fromPolynomial i Q` to the `i`-th axis amounts to evaluating the
coefficients of `Q` at the origin.
@isnad1 id=eq.0h4v.s9.cc3eb4cba17f from=translated src=- shape=3d9e1def vocab=11ad22ca
-/
lemma partialEval_fromPolynomial (Q : (MvPowerSeries { j : σ // j ≠ i } R)[X]) :
    partialEval i (fromPolynomial i Q) = (Q.map constantCoeff).toPowerSeries := by
  refine PowerSeries.ext fun k ↦ ?_
  rw [coeff_partialEval, Polynomial.coeff_coe, Polynomial.coeff_map,
    ← coeff_zero_eq_constantCoeff_apply, ← coeff_fromPolynomial Q 0 k]
  simp

end PartialEval

/-- The order of vanishing of `P` along the `i`-th coordinate axis, i.e. the order of the
one variable power series `MvPowerSeries.partialEval i P`. -/
noncomputable
def orderIn (P : MvPowerSeries ι R) (i : ι) : ℕ∞ :=
  (MvPowerSeries.partialEval i P).order

/-- A power series is general in the variable `i` if it does not vanish identically on the
`i`-th coordinate axis. -/
def IsGeneralIn (P : MvPowerSeries ι R) (i : ι) :
    Prop :=
  MvPowerSeries.partialEval i P ≠ 0

/--
@isnad1 id=iff.0h4v.s5.a65573edaa3b from=translated src=- shape=614bddad vocab=a77388a5
-/
lemma isGeneralIn_iff_orderIn_ne_top
    (P : MvPowerSeries ι R) (i : ι) :
    P.IsGeneralIn i ↔ P.orderIn i < ⊤ := by
  rw [IsGeneralIn, orderIn, lt_top_iff_ne_top, ne_eq, ne_eq, PowerSeries.order_eq_top]

end MvPowerSeries

end
-- Tengoku: root names of this library moved to Tengoku.LanaOka so they do not collide with other libraries (generated)
