/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.PotentialGoodReduction
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.PotentialMultiplicativeReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Potential good and potential multiplicative reduction are mutually exclusive (issue #525)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be elliptic.  This file records the **mutual exclusivity** of potential
good reduction and potential multiplicative reduction at the base place, as the immediate joint
consequence of the two sharp base-valuation lemmas of Silverman AEC VII.5.5:

* good reduction over a DVR extension `A ⊆ L` lying over `R` forces `v_R(W.j) ≤ 1`
  (`valuation_j_le_one_of_hasGoodReduction_baseChange_over`, #514);
* multiplicative reduction over a DVR extension `A' ⊆ L'` lying over `R` forces `1 < v_R(W.j)`
  (`one_lt_valuation_j_of_hasMultiplicativeReduction_baseChange_over`, #509).

`v_R(W.j) ≤ 1` and `1 < v_R(W.j)` are contradictory, so `W` cannot simultaneously acquire good
reduction over one DVR extension of `R` and multiplicative reduction over another.  This is the
base-landing, *potential* (base-change) form of the disjointness of reduction types: the
`v(j) ≥ 0` vs `v(j) < 0` dichotomy of Silverman AEC VII.5.5.

`ReductionTrichotomy.lean` already establishes disjointness of the good/multiplicative/additive
types **over a single fixed DVR** (same place).  The statements here are genuinely different: good
reduction over one extension versus multiplicative reduction over a possibly *different* extension,
both lying over the base `R`.

## Main results

* `WeierstrassCurve.not_hasGoodReduction_and_hasMultiplicativeReduction_baseChange_over` — the core
  exclusivity: no `W` has good reduction over `A` and multiplicative reduction over `A'`.
* `WeierstrassCurve.not_hasMultiplicativeReduction_baseChange_over_of_hasGoodReduction` — good
  reduction over `A` rules out multiplicative reduction over any DVR extension lying over `R`.
* `WeierstrassCurve.not_hasGoodReduction_baseChange_over_of_hasMultiplicativeReduction` — the
  symmetric companion.

## Scope

This is the **ungated forward dichotomy**.  The converse directions (`v(j) ≥ 0` ⟹ potential good,
`v(j) < 0` ⟹ potential multiplicative) need the Tate curve / Néron machinery, absent from the
repository and the pinned Mathlib, and are out of scope — exactly as for #504/#505/#509/#514.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.5.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable (R) in
/-- **Potential good and potential multiplicative reduction are mutually exclusive.**  An elliptic
curve `W / K` cannot simultaneously acquire good reduction over a discrete valuation subring
`A ⊆ L` lying over `R` (its contraction to `K` bounds the base valuation, `hoverA`) and
multiplicative reduction over a discrete valuation subring `A' ⊆ L'` lying over `R` (`hoverA'`):
the former forces `v_R(W.j) ≤ 1` (#514) and the latter `1 < v_R(W.j)` (#509).  Base-landing,
potential form of the reduction-type dichotomy, Silverman AEC VII.5.5. -/
theorem not_hasGoodReduction_and_hasMultiplicativeReduction_baseChange_over
    {L : Type*} [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (hoverA : ∀ x : K, algebraMap K L x ∈ A → valuation K (maximalIdeal R) x ≤ 1)
    {L' : Type*} [Field L'] [Algebra K L'] (A' : ValuationSubring L') [IsDiscreteValuationRing A']
    (hoverA' : ∀ r : R, algebraMap K L' (algebraMap R K r) ∈ A')
    (W : WeierstrassCurve K) [W.IsElliptic]
    (hgood : HasGoodReduction A (W⁄L)) (hmult : HasMultiplicativeReduction A' (W⁄L')) : False :=
  absurd (valuation_j_le_one_of_hasGoodReduction_baseChange_over R A hoverA W hgood)
    (not_le.2 (one_lt_valuation_j_of_hasMultiplicativeReduction_baseChange_over R A' hoverA' W
      hmult))

variable (R) in
/-- **Potential good reduction rules out potential multiplicative reduction.**  If `W⁄L` has good
reduction over a discrete valuation subring `A ⊆ L` lying over `R`, then `W` has multiplicative
reduction over *no* discrete valuation subring extension `A' ⊆ L'` lying over `R`. -/
theorem not_hasMultiplicativeReduction_baseChange_over_of_hasGoodReduction
    {L : Type*} [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (hoverA : ∀ x : K, algebraMap K L x ∈ A → valuation K (maximalIdeal R) x ≤ 1)
    (W : WeierstrassCurve K) [W.IsElliptic] (hgood : HasGoodReduction A (W⁄L))
    {L' : Type*} [Field L'] [Algebra K L'] (A' : ValuationSubring L') [IsDiscreteValuationRing A']
    (hoverA' : ∀ r : R, algebraMap K L' (algebraMap R K r) ∈ A') :
    ¬ HasMultiplicativeReduction A' (W⁄L') :=
  fun hmult => not_hasGoodReduction_and_hasMultiplicativeReduction_baseChange_over
    R A hoverA A' hoverA' W hgood hmult

variable (R) in
/-- **Potential multiplicative reduction rules out potential good reduction.**  If `W⁄L'` has
multiplicative reduction over a discrete valuation subring `A' ⊆ L'` lying over `R`, then `W` has
good reduction over *no* discrete valuation subring extension `A ⊆ L` lying over `R`. -/
theorem not_hasGoodReduction_baseChange_over_of_hasMultiplicativeReduction
    {L' : Type*} [Field L'] [Algebra K L'] (A' : ValuationSubring L') [IsDiscreteValuationRing A']
    (hoverA' : ∀ r : R, algebraMap K L' (algebraMap R K r) ∈ A')
    (W : WeierstrassCurve K) [W.IsElliptic] (hmult : HasMultiplicativeReduction A' (W⁄L'))
    {L : Type*} [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (hoverA : ∀ x : K, algebraMap K L x ∈ A → valuation K (maximalIdeal R) x ≤ 1) :
    ¬ HasGoodReduction A (W⁄L) :=
  fun hgood => not_hasGoodReduction_and_hasMultiplicativeReduction_baseChange_over
    R A hoverA A' hoverA' W hgood hmult

end WeierstrassCurve
