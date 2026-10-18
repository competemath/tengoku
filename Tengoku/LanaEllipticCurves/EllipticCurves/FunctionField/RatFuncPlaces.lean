/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.FieldTheory.RatFunc.Valuation
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.ValuationSubringDedekind

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The places of the rational function field

Stichtenoth I.2.2: **every place of `F(X)` that is trivial on `F` is either `p`-adic for a
height-one prime `p` of `F[X]`, or the place at infinity.**  Mathlib has both families of objects —
`IsDedekindDomain.HeightOneSpectrum F[X]` with its adic valuation, and `RatFunc.inftyValuation` —
but not the statement that there are no others.

```
RatFunc.valuationSubring_eq_adic_or_infty (O : ValuationSubring (RatFunc F))
    (hF : ∀ c : F, algebraMap F (RatFunc F) c ∈ O) (hO : O ≠ ⊤) :
    (∃ v, (v.valuation (RatFunc F)).valuationSubring = O)
      ∨ (RatFunc.inftyValuation F).valuationSubring = O
```

A place is formalised as a `ValuationSubring (RatFunc F)`, because a ring automorphism of `F(X)`
carries valuation subrings to valuation subrings — which is exactly what a classification of places
is for — and because it avoids quantifying over value groups.

## The proof

Case split on whether `X ∈ O`.

* If `X ∈ O` then `F[X] ⊆ O` (`algebraMap_polynomial_mem`) and the general Dedekind statement
  `IsDedekindDomain.exists_valuationSubring_eq` of
  `EllipticCurves.FunctionField.ValuationSubringDedekind` finishes it.
* If `X ∉ O` then `X⁻¹` is a *nonunit* of `O`, and the classical "expand in powers of `1/X`"
  argument shows `O` is the place at infinity.  The workhorse is
  `RatFunc.mul_inv_X_pow_mem`: for `natDegree p ≤ d`, the element `p̂ · (X⁻¹) ^ d` of `F(X)` is a
  polynomial in `X⁻¹` and hence lies in `O`.  Feeding it `p` of degree `< d` lands in the nonunits
  (`mul_inv_X_pow_mem_nonunits`), and feeding it `q` of degree exactly `d` lands *outside* the
  nonunits (`mul_inv_X_pow_notMem_nonunits`), because `q̂ · (X⁻¹) ^ d` is the leading coefficient of
  `q` plus a nonunit.  Writing `f = p / q` as `(p̂ · (X⁻¹) ^ d) · (q̂ · (X⁻¹) ^ d)⁻¹` then compares
  `f ∈ O` with `deg p ≤ deg q`, i.e. with `inftyValuation f ≤ 1`.

This is the route that avoids constructing the `X ↦ 1/X` automorphism of `F(X)`, which Mathlib does
not have.

## Main results

* **`RatFunc.valuationSubring_eq_adic_or_infty`** — the classification;
* `RatFunc.valuationSubring_eq_adic_or_infty_iff` — its hypotheses are also necessary, so the
  classification is exact;
* `RatFunc.eq_inftyValuationSubring` — the case `X ∉ O`, i.e. the place at infinity;
* `RatFunc.inftyValuationSubring_ne_valuationSubring` — the two branches are *disjoint*: `X` lies
  in every adic subring and in no infinite one.  Without it the disjunction could in principle have
  a redundant branch.

Nothing in this file mentions elliptic curves; like `ValuationSubringDedekind` it is an upstream
candidate, and sits next to `Mathlib/FieldTheory/RatFunc/Valuation.lean`.
-/

open Polynomial IsDedekindDomain

namespace RatFunc

variable {F : Type*} [Field F] {O : ValuationSubring (RatFunc F)}

/-- `X⁻¹ ^ d` clears the denominator of any polynomial of degree at most `d`: the result lies in
any subring of `F(X)` containing the constants and `X⁻¹`.  This is the statement that a polynomial
of degree `≤ d` is `X ^ d` times a polynomial in `1 / X`. -/
theorem mul_inv_X_pow_mem (hC : ∀ c : F, RatFunc.C c ∈ O) (ht : (X : RatFunc F)⁻¹ ∈ O)
    (p : F[X]) {d : ℕ} (hp : p.natDegree ≤ d) :
    algebraMap F[X] (RatFunc F) p * ((X : RatFunc F)⁻¹) ^ d ∈ O := by
  have hX0 : (X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
  rw [p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp), map_sum, Finset.sum_mul]
  refine sum_mem fun i hi => ?_
  obtain ⟨k, rfl⟩ : ∃ k, d = i + k :=
    ⟨d - i, (Nat.add_sub_cancel' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).symm⟩
  have hrw : algebraMap F[X] (RatFunc F) (Polynomial.C (p.coeff i) * Polynomial.X ^ i)
      * ((X : RatFunc F)⁻¹) ^ (i + k) = RatFunc.C (p.coeff i) * ((X : RatFunc F)⁻¹) ^ k := by
    rw [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, pow_add, ← mul_assoc,
      mul_assoc (RatFunc.C (p.coeff i)), ← mul_pow, mul_inv_cancel₀ hX0, one_pow, mul_one]
  rw [hrw]
  exact mul_mem (hC _) (pow_mem ht _)

/-- A nonzero constant is a unit of any subring of `F(X)` containing the constants. -/
theorem C_notMem_nonunits (hC : ∀ c : F, RatFunc.C c ∈ O) {c : F} (hc : c ≠ 0) :
    RatFunc.C c ∉ O.nonunits := by
  rw [O.mem_nonunits_iff_or]
  simp only [not_or, not_not]
  refine ⟨by simpa using hc, ?_⟩
  rw [← map_inv₀]
  exact hC _

/-- Strictly below the degree bound, `p̂ · X⁻¹ ^ d` is a nonunit: one factor of `X⁻¹` is left over,
and `X⁻¹` is a nonunit as soon as `X ∉ O`. -/
theorem mul_inv_X_pow_mem_nonunits (hC : ∀ c : F, RatFunc.C c ∈ O)
    (htn : (X : RatFunc F)⁻¹ ∈ O.nonunits) (p : F[X]) {d : ℕ} (hp : p.natDegree < d) :
    algebraMap F[X] (RatFunc F) p * ((X : RatFunc F)⁻¹) ^ d ∈ O.nonunits := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hmem := ValuationSubring.mul_mem_nonunits htn
    (mul_inv_X_pow_mem hC (ValuationSubring.nonunits_subset htn) p (Nat.lt_succ_iff.1 hp))
  have hrw : (X : RatFunc F)⁻¹ * (algebraMap F[X] (RatFunc F) p * ((X : RatFunc F)⁻¹) ^ e)
      = algebraMap F[X] (RatFunc F) p * ((X : RatFunc F)⁻¹) ^ (e + 1) := by ring
  rwa [hrw] at hmem

/-- Exactly at the degree bound, `q̂ · X⁻¹ ^ (natDegree q)` is a *unit*: it is the leading
coefficient plus a nonunit. -/
theorem mul_inv_X_pow_notMem_nonunits (hC : ∀ c : F, RatFunc.C c ∈ O)
    (htn : (X : RatFunc F)⁻¹ ∈ O.nonunits) {q : F[X]} (hq : q ≠ 0) :
    algebraMap F[X] (RatFunc F) q * ((X : RatFunc F)⁻¹) ^ q.natDegree ∉ O.nonunits := by
  have hX0 : (X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
  intro hmem
  refine C_notMem_nonunits hC (Polynomial.leadingCoeff_ne_zero.2 hq) ?_
  have hq' : algebraMap F[X] (RatFunc F) q
      = algebraMap F[X] (RatFunc F) q.eraseLead
        + RatFunc.C q.leadingCoeff * (X : RatFunc F) ^ q.natDegree := by
    conv_lhs => rw [← q.eraseLead_add_C_mul_X_pow]
    rw [map_add, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  have hsplit : RatFunc.C q.leadingCoeff
      = algebraMap F[X] (RatFunc F) q * ((X : RatFunc F)⁻¹) ^ q.natDegree
        - algebraMap F[X] (RatFunc F) q.eraseLead * ((X : RatFunc F)⁻¹) ^ q.natDegree := by
    rw [hq', add_mul, mul_assoc, ← mul_pow, mul_inv_cancel₀ hX0, one_pow, mul_one]
    ring
  have herase : algebraMap F[X] (RatFunc F) q.eraseLead * ((X : RatFunc F)⁻¹) ^ q.natDegree
      ∈ O.nonunits := by
    rcases q.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h | h
    · exact mul_inv_X_pow_mem_nonunits hC htn _ h
    · simp [h]
  rw [hsplit]
  exact sub_mem hmem herase

/-- The quotient of two polynomials with `deg p ≤ deg q` lies in `O`: both `p̂ · X⁻¹ ^ deg q` and
`q̂ · X⁻¹ ^ deg q` lie in `O`, and the second is a unit. -/
theorem div_mem_of_natDegree_le (hC : ∀ c : F, RatFunc.C c ∈ O)
    (htn : (X : RatFunc F)⁻¹ ∈ O.nonunits) {p q : F[X]} (hq : q ≠ 0)
    (hpq : p.natDegree ≤ q.natDegree) :
    algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q ∈ O := by
  have hX0 : (X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
  have hu0 : ((X : RatFunc F)⁻¹) ^ q.natDegree ≠ 0 := pow_ne_zero _ (inv_ne_zero hX0)
  have hq0 : algebraMap F[X] (RatFunc F) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hA := mul_inv_X_pow_mem hC (ValuationSubring.nonunits_subset htn) p hpq
  have hBinv : (algebraMap F[X] (RatFunc F) q * ((X : RatFunc F)⁻¹) ^ q.natDegree)⁻¹ ∈ O := by
    by_contra hcon
    exact mul_inv_X_pow_notMem_nonunits hC htn hq ((O.mem_nonunits_iff_or).2 (Or.inr hcon))
  have heq : algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q
      = (algebraMap F[X] (RatFunc F) p * ((X : RatFunc F)⁻¹) ^ q.natDegree)
        * (algebraMap F[X] (RatFunc F) q * ((X : RatFunc F)⁻¹) ^ q.natDegree)⁻¹ := by
    rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hu0, mul_one, div_eq_mul_inv]
  rw [heq]
  exact mul_mem hA hBinv

/-- The quotient of two polynomials with `deg q < deg p` does *not* lie in `O`: its inverse is a
nonunit. -/
theorem div_notMem_of_natDegree_lt (hC : ∀ c : F, RatFunc.C c ∈ O)
    (htn : (X : RatFunc F)⁻¹ ∈ O.nonunits) {p q : F[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : q.natDegree < p.natDegree) :
    algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q ∉ O := by
  have hX0 : (X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
  have hu0 : ((X : RatFunc F)⁻¹) ^ p.natDegree ≠ 0 := pow_ne_zero _ (inv_ne_zero hX0)
  have hp0 : algebraMap F[X] (RatFunc F) p ≠ 0 := RatFunc.algebraMap_ne_zero hp
  have hq0 : algebraMap F[X] (RatFunc F) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hAinv : (algebraMap F[X] (RatFunc F) p * ((X : RatFunc F)⁻¹) ^ p.natDegree)⁻¹ ∈ O := by
    by_contra hcon
    exact mul_inv_X_pow_notMem_nonunits hC htn hp ((O.mem_nonunits_iff_or).2 (Or.inr hcon))
  have hB := mul_inv_X_pow_mem_nonunits hC htn q hpq
  have hinv : (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q)⁻¹
      ∈ O.nonunits := by
    have heq : (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q)⁻¹
        = (algebraMap F[X] (RatFunc F) q * ((X : RatFunc F)⁻¹) ^ p.natDegree)
          * (algebraMap F[X] (RatFunc F) p * ((X : RatFunc F)⁻¹) ^ p.natDegree)⁻¹ := by
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hu0, mul_one, div_eq_mul_inv, mul_inv,
        inv_inv, mul_comm]
    rw [heq]
    exact ValuationSubring.mul_mem_nonunits hB hAinv
  intro hfO
  exact ((O.inv_mem_nonunits_iff).1 hinv).resolve_left (div_ne_zero hp0 hq0) hfO

/-- Every polynomial lies in a subring of `F(X)` that contains the constants and `X`. -/
theorem algebraMap_polynomial_mem (hC : ∀ c : F, RatFunc.C c ∈ O) (hX : (X : RatFunc F) ∈ O)
    (p : F[X]) : algebraMap F[X] (RatFunc F) p ∈ O := by
  refine Polynomial.induction_on' p (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    fun n a => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X]
  exact mul_mem (hC a) (pow_mem hX n)

section Classification

variable [DecidableEq (RatFunc F)]

/-- **The place at infinity.**  A valuation subring of `F(X)` containing the constants but *not*
`X` is exactly the valuation subring of `RatFunc.inftyValuation`.

The content is the degree comparison: writing `f = p / q` in lowest terms, `f ∈ O` if and only if
`deg p ≤ deg q`, which is `inftyValuation f ≤ 1`. -/
theorem eq_inftyValuationSubring (hC : ∀ c : F, RatFunc.C c ∈ O) (hX : (X : RatFunc F) ∉ O) :
    O = (RatFunc.inftyValuation F).valuationSubring := by
  have hX0 : (X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
  have htn : (X : RatFunc F)⁻¹ ∈ O.nonunits :=
    (O.mem_nonunits_iff_or).2 (Or.inr (by simpa using hX))
  ext f
  rw [Valuation.mem_valuationSubring_iff, RatFunc.inftyValuation_apply]
  rcases eq_or_ne f 0 with rfl | hf
  · simp [RatFunc.inftyValuationDef]
  · rw [RatFunc.inftyValuation_of_nonzero F hf, ← WithZero.exp_zero, WithZero.exp_le_exp,
      RatFunc.intDegree, sub_nonpos, Nat.cast_le]
    constructor
    · intro hfO
      by_contra hcon
      push Not at hcon
      exact div_notMem_of_natDegree_lt hC htn (RatFunc.num_ne_zero hf) f.denom_ne_zero hcon
        (by rwa [RatFunc.num_div_denom])
    · intro hle
      have hmem := div_mem_of_natDegree_le hC htn f.denom_ne_zero hle
      rwa [RatFunc.num_div_denom] at hmem

/-- The constants lie in the valuation subring at infinity. -/
theorem algebraMap_mem_inftyValuationSubring (c : F) :
    algebraMap F (RatFunc F) c ∈ (RatFunc.inftyValuation F).valuationSubring := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [Valuation.mem_valuationSubring_iff, RatFunc.algebraMap_eq_C, RatFunc.inftyValuation.C F hc]

/-- The valuation subring at infinity is proper: `X` is not in it. -/
theorem X_notMem_inftyValuationSubring :
    (X : RatFunc F) ∉ (RatFunc.inftyValuation F).valuationSubring := by
  rw [Valuation.mem_valuationSubring_iff, RatFunc.inftyValuation.X, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

theorem inftyValuationSubring_ne_top :
    (RatFunc.inftyValuation F).valuationSubring ≠ ⊤ := by
  intro h
  refine X_notMem_inftyValuationSubring (F := F) ?_
  rw [h]
  trivial

end Classification

end RatFunc
