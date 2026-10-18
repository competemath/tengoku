/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.JInvariantGoodReductionBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Potential good reduction forces the `j`-invariant integral at the base (issue #504)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be elliptic.  This file delivers the **ungated forward direction** of
Silverman AEC VII.5.5 in its quantified, base-landing form:

> If `W` acquires **good reduction over a discrete valuation subring `A ⊆ L`** of some field
> extension `L / K`, and `A` **lies over the base DVR `R`**, then the `j`-invariant `W.j` is
> **integral at the base place**: `∃ r : R, algebraMap R K r = W.j`.

This is the quantified strengthening of the per-extension core
`WeierstrassCurve.isIntegral_j_of_hasGoodReduction_baseChange` (#501,
`Reduction/JInvariantGoodReductionBaseChange.lean`), which only concludes
`algebraMap K L W.j ∈ A` — membership in the *extension's* valuation ring.  The new content is
landing the conclusion back in the base `R`, which needs the **DVR converse** below (valuation
`≤ 1` at the base place ⟹ membership in `R`), the step #501 deferred.

## Key points

* **The DVR converse** `exists_algebraMap_eq_of_valuation_le_one`: for a discrete valuation ring
  `R` any `x : K` with `v(x) ≤ 1` at the maximal-ideal place lies in the image of `R`.  For a
  general Dedekind domain this fails for a single place, but for a *local* ring the writeup
  `x·d = n` with `d ∈ (maximalIdeal R)ᶜ` (`exists_primeCompl_mul_eq_of_integer`) has `d` a **unit**
  (`IsLocalRing.notMem_maximalIdeal`), so `x = n / d ∈ R`.

* **Lies over `R`.** The condition that the valuation subring `A ⊆ L` "lies over" the base is
  packaged as the contraction bound `∀ x : K, algebraMap K L x ∈ A → v_R(x) ≤ 1`, i.e.
  `A ∩ K ⊆ R`.  This is the honest structural meaning of "lies over" and exactly what turns the
  `#501` conclusion `algebraMap K L W.j ∈ A` into `W.j ∈ R`.  It does **not** smuggle the
  theorem's content: the content — good reduction ⟹ `j ∈ A` — is `#501`.

## Main results

* `WeierstrassCurve.exists_algebraMap_eq_of_valuation_le_one` — the DVR converse.
* `WeierstrassCurve.valuation_j_le_one_of_hasGoodReduction_baseChange_over` — the sharp
  base-valuation form `v_R(W.j) ≤ 1`, the good-reduction mirror of the multiplicative
  `one_lt_valuation_j_of_hasMultiplicativeReduction_baseChange_over` (#509).
* `WeierstrassCurve.isIntegral_j_of_hasGoodReduction_baseChange_over` — the `∀`-form: any DVR
  extension `A` lying over `R` with good reduction of `W⁄L` forces `W.j ∈ R`.
* `WeierstrassCurve.not_hasGoodReduction_baseChange_over_of_j_not_mem` — the contrapositive: a
  non-integral `j` rules out good reduction over any DVR extension lying over `R`.

## Scope

This delivers the **ungated forward direction**.  The **converse** (`j` integral ⟹ potential good
reduction) needs the Tate curve / existence of a good-reduction extension, absent from the
repository and the pinned Mathlib, and is left to a follow-on.  A bundled
`HasPotentialGoodReduction` existential predicate is deliberately avoided: quantifying over a
fresh field `L` with its
`Field`/`Algebra` instances inside an `∃` is not ergonomic in Lean 4 (instances bound by an
existential are not registered for typeclass search), and the `∀`-form above carries the same
mathematical content cleanly.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.5, VII.5.4.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable (R) in
/-- **The DVR converse.** For a discrete valuation ring `R` with fraction field `K`, any `x : K`
whose valuation at the maximal-ideal place is `≤ 1` lies in the image of `R`: `∃ r, algebraMap R K
r = x`.  (For a general Dedekind domain this holds only when *every* place has valuation `≤ 1`;
locality of `R` is what upgrades the single-place statement.) -/
theorem exists_algebraMap_eq_of_valuation_le_one (x : K)
    (hv : valuation K (maximalIdeal R) x ≤ 1) : ∃ r : R, algebraMap R K r = x := by
  obtain ⟨n, d, hnd⟩ :=
    (IsDiscreteValuationRing.maximalIdeal R).exists_primeCompl_mul_eq_of_integer x hv
  -- `d ∈ (maximalIdeal R)ᶜ`, and `R` is local, so `d` is a unit.
  have hd : IsUnit (d : R) := notMem_maximalIdeal.mp d.prop
  have hdne : algebraMap R K (d : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd.ne_zero
  obtain ⟨b, hb⟩ := hd.exists_right_inv
  refine ⟨n * b, mul_right_cancel₀ hdne ?_⟩
  -- Clear the denominator: `algebraMap (n · b) · algebraMap d = x · algebraMap d = algebraMap n`.
  rw [hnd, ← map_mul]
  congr 1
  rw [mul_assoc, mul_comm b (d : R), hb, mul_one]

variable (R) in
/-- **Potential good reduction ⟹ `v_R(j) ≤ 1` (sharp `∀`-form).** If `W⁄L` has good reduction over
a discrete valuation subring `A ⊆ L` that **lies over** `R` (its contraction to `K` bounds the base
valuation), then the base valuation of `W.j` is `≤ 1`, i.e. `W.j` is non-negatively valued at the
base place.  This is the good-reduction mirror of the multiplicative
`one_lt_valuation_j_of_hasMultiplicativeReduction_baseChange_over` (#509, `1 < v_R(j)`), obtained
from the per-extension #501 `isIntegral_j_of_hasGoodReduction_baseChange` (`algebraMap K L W.j ∈ A`)
by reflecting the extension-place membership back to the base valuation via `hover`. -/
theorem valuation_j_le_one_of_hasGoodReduction_baseChange_over
    {L : Type*} [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (hover : ∀ x : K, algebraMap K L x ∈ A → valuation K (maximalIdeal R) x ≤ 1)
    (W : WeierstrassCurve K) [W.IsElliptic] (h : HasGoodReduction A (W⁄L)) :
    valuation K (maximalIdeal R) W.j ≤ 1 :=
  hover W.j (isIntegral_j_of_hasGoodReduction_baseChange A W h)

variable (R) in
/-- **Potential good reduction ⟹ `j` integral at the base (`∀`-form).** If `W⁄L` has good
reduction over a discrete valuation subring `A ⊆ L` that **lies over** `R` (its contraction to `K`
bounds the base valuation), then `W.j` is integral at the base place: `∃ r : R, algebraMap R K r =
W.j`.  This is the quantified, base-landing strengthening of
`isIntegral_j_of_hasGoodReduction_baseChange` (#501); it upgrades the sharp valuation bound
`valuation_j_le_one_of_hasGoodReduction_baseChange_over` to base membership via the DVR converse. -/
theorem isIntegral_j_of_hasGoodReduction_baseChange_over
    {L : Type*} [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (hover : ∀ x : K, algebraMap K L x ∈ A → valuation K (maximalIdeal R) x ≤ 1)
    (W : WeierstrassCurve K) [W.IsElliptic] (h : HasGoodReduction A (W⁄L)) :
    ∃ r : R, algebraMap R K r = W.j :=
  exists_algebraMap_eq_of_valuation_le_one R W.j
    (valuation_j_le_one_of_hasGoodReduction_baseChange_over R A hover W h)

variable (R) in
/-- **Contrapositive.** A `j`-invariant that is not integral at the base place rules out good
reduction over *any* discrete valuation subring extension lying over `R`. -/
theorem not_hasGoodReduction_baseChange_over_of_j_not_mem
    {L : Type*} [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (hover : ∀ x : K, algebraMap K L x ∈ A → valuation K (maximalIdeal R) x ≤ 1)
    (W : WeierstrassCurve K) [W.IsElliptic] (hj : ¬ ∃ r : R, algebraMap R K r = W.j) :
    ¬ HasGoodReduction A (W⁄L) :=
  fun h => hj (isIntegral_j_of_hasGoodReduction_baseChange_over R A hover W h)

end WeierstrassCurve
