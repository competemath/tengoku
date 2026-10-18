/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.Divisors
import Tengoku.Seed.RingTheory.DedekindDomain.AdicValuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `count` ↔ adic-valuation bridge

For a Dedekind domain `R` with fraction field `K` and a height-one prime `v` of `R`, this file
relates two encodings of the `v`-adic order of an element `x ∈ K`:

* `FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)` — the exponent of `v` in the
  factorisation of the principal fractional ideal `⟨x⟩`, which is how the divisor calculus
  (`EllipticCurves.FunctionField.Divisors`, `WeierstrassCurve.Affine.ord`) measures orders of
  vanishing; and
* `IsDedekindDomain.HeightOneSpectrum.valuation`, Mathlib's `ℤᵐ⁰`-valued `v`-adic valuation on `K`,
  which is the encoding used by the ramification-transport lemma
  `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` (valuations multiply by the ramification
  index along a finite extension).

The bridge is
```
v.valuation K x = WithZero.exp (- count K v ⟨x⟩)      (for x ≠ 0)
```
equivalently `count K v ⟨x⟩ = - WithZero.log (v.valuation K x)`. Both sides are, by definition, the
same integer `(Associates.mk v.asIdeal).count (Associates.mk (span {·})).factors`; the content here
is only to line the two definitions up and to extend the integral case to fractions.

## Main statements

* `IsDedekindDomain.HeightOneSpectrum.valuation_eq_exp_neg_count`
* `IsDedekindDomain.HeightOneSpectrum.count_eq_neg_log_valuation`
* `WeierstrassCurve.Affine.valuation_eq_exp_neg_ord`
* `WeierstrassCurve.Affine.ord_eq_neg_log_valuation`

This is the count↔valuation bridge (issue #414 "rung 4", Brick B) consumed by the divisor-level
pullback `[n]∗` of the divisor-theoretic Weil pairing (issue #244): once the ramification data of
the finite `[n]∗`-extension is available, `valuation_liesOver` transports valuations and this lemma
converts the result back into the `ord`/`divisor` bookkeeping.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal WithZero
open scoped nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- **The `count` ↔ adic-valuation bridge.** For a nonzero `x ∈ K`, the `v`-adic valuation of `x`
is `exp` of `−` the exponent of `v` in the principal fractional ideal `⟨x⟩`. -/
theorem valuation_eq_exp_neg_count {x : K} (hx : x ≠ 0) :
    v.valuation K x = exp (- count K v (spanSingleton R⁰ x)) := by
  -- The integral case is a direct unfolding: both `intValuation` and `count` are literally
  -- `(Associates.mk v.asIdeal).count (Associates.mk (span {r})).factors`.
  have key : ∀ r : R, r ≠ 0 →
      v.valuation K (algebraMap R K r)
        = exp (- count K v (spanSingleton R⁰ (algebraMap R K r))) := by
    intro r hr
    have hspan : (Ideal.span {r} : Ideal R) ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hr
    rw [valuation_of_algebraMap, intValuation_if_neg v hr, ← coeIdeal_span_singleton,
      count_coe K v hspan]
  -- Reduce a general `x = a / b` to the integral case using multiplicativity of both sides.
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hb0
  have haK : algebraMap R K a ≠ 0 := fun h => hx (by rw [h, zero_div])
  have ha0 : a ≠ 0 := fun h => haK (by rw [h, map_zero])
  have hsa : spanSingleton R⁰ (algebraMap R K a) ≠ 0 := by
    rw [ne_eq, spanSingleton_eq_zero_iff]; exact haK
  have hsb : spanSingleton R⁰ (algebraMap R K b) ≠ 0 := by
    rw [ne_eq, spanSingleton_eq_zero_iff]; exact hbK
  -- The count of `⟨a/b⟩` is `count ⟨a⟩ - count ⟨b⟩`.
  have hcount : count K v (spanSingleton R⁰ (algebraMap R K a / algebraMap R K b))
      = count K v (spanSingleton R⁰ (algebraMap R K a))
        - count K v (spanSingleton R⁰ (algebraMap R K b)) := by
    rw [div_eq_mul_inv, ← spanSingleton_mul_spanSingleton, ← spanSingleton_inv,
      count_mul K v hsa (inv_ne_zero hsb), count_inv, sub_eq_add_neg]
  rw [map_div₀, key a ha0, key b hb0, hcount, ← exp_sub, exp_inj]
  ring

/-- **The `count` ↔ adic-valuation bridge, logarithmic form.** For a nonzero `x ∈ K`, the exponent
of `v` in `⟨x⟩` is `−` the (additive) `v`-adic valuation of `x`. -/
theorem count_eq_neg_log_valuation {x : K} (hx : x ≠ 0) :
    count K v (spanSingleton R⁰ x) = - log (v.valuation K x) := by
  rw [valuation_eq_exp_neg_count v hx, log_exp, neg_neg]

end IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
  (v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)

/-- The order of vanishing `ord v f` is `−` the (additive) `v`-adic valuation of `f`: the
divisor-calculus encoding agrees with Mathlib's adic valuation. -/
theorem valuation_eq_exp_neg_ord {f : W.FunctionField} (hf : f ≠ 0) :
    v.valuation W.FunctionField f = WithZero.exp (- ord v f) :=
  valuation_eq_exp_neg_count v hf

/-- The order of vanishing, as `−` the (additive) `v`-adic valuation. -/
theorem ord_eq_neg_log_valuation {f : W.FunctionField} (hf : f ≠ 0) :
    ord v f = - WithZero.log (v.valuation W.FunctionField f) :=
  count_eq_neg_log_valuation v hf

end WeierstrassCurve.Affine
