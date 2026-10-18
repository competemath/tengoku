/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.UniversalIdentification
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.LaurentMap
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.Law

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The unconditional identification `embedDoubleLaurent formalGroupZW = formalGroupLaurent`

`EllipticCurves.FormalGroup.UniversalIdentification` proved the identification of the two formal
group law constructions — the `(z, w)`-plane power series `W.formalGroupZW` and the `(x, y)`-plane
Laurent element `W.formalGroupLaurent` — at the **universal curve** `univ` over the char-`0` domain
`S = MvPolynomial (Fin 5) ℤ`.  This file transfers that identity to an **arbitrary** `CommRing R`
by base change, using the Laurent-side naturality layer
`EllipticCurves.FormalGroup.LaurentMap` (`HahnSeries.map_embedDoubleLaurent`,
`WeierstrassCurve.map_formalGroupLaurent`) and the MvPowerSeries-side naturality
`EllipticCurves.FormalGroup.GenuineLawMap` (`WeierstrassCurve.map_formalGroupZW`).

## Main results

* `WeierstrassCurve.embedDoubleLaurent_formalGroupZW` : the unconditional identification
  `HahnSeries.embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent`, for every `CommRing R`.
* `WeierstrassCurve.coeff_formalGroupLaurent_inner_of_lt` : **inner (`z₁`) pole-freeness** of
  `F_E` — every outer coefficient of `W.formalGroupLaurent` is a genuine power series in `z₁`.
  Closes the analytic core (#286).
* `WeierstrassCurve.ofDoubleLaurent_formalGroupLaurent` /
  `WeierstrassCurve.formalGroupSeries_eq_formalGroupZW` : the reader `ofDoubleLaurent` recovers
  `formalGroupZW`, so the extracted `W.formalGroupSeries` coincides with the genuine
  `W.formalGroupZW`.  This is the round-trip that #283/#263/#291 consume.

## Strategy

For `W : WeierstrassCurve R` let `f := W.specialize : S →+* R` be the ring hom `X i ↦ aᵢ`; then
`univ.map f = W` (`univ_map_specialize`).  All three of `univ`, `specialize` and
`univ_map_specialize` live in `EllipticCurves.UniversalCurve`, which imports only Mathlib.
Apply the double base-change ring hom
`Ψ f = HahnSeries.mapRingHom (HahnSeries.mapRingHom f)` to the universal identity: the left-hand
side transports via `map_embedDoubleLaurent` + `map_formalGroupZW`, the right-hand side via
`map_formalGroupLaurent`, and both `univ.map f` collapse to `W`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open scoped LaurentSeries
open HahnSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-! ### The unconditional identification -/

/-- **The unconditional identification** `embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent`
over an arbitrary `CommRing R`, obtained from the universal-domain identity
`embedDoubleLaurent_formalGroupZW_univ` by base change along `W.specialize`. -/
theorem embedDoubleLaurent_formalGroupZW (W : WeierstrassCurve R) :
    HahnSeries.embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent := by
  have key := congrArg (HahnSeries.mapRingHom (HahnSeries.mapRingHom W.specialize))
    embedDoubleLaurent_formalGroupZW_univ
  rwa [HahnSeries.map_embedDoubleLaurent, univ.map_formalGroupZW W.specialize,
    univ.map_formalGroupLaurent W.specialize, univ_map_specialize] at key

/-! ### Conclusion 1 — inner pole-freeness of `F_E` (closes #286) -/

/-- **Inner (`z₁`) pole-freeness of the Weierstrass formal group law.**  Every outer coefficient of
`W.formalGroupLaurent` is a genuine power series in the inner variable `z₁`: all its
negative-index inner coefficients vanish.  This closes the analytic core (#286): via the
identification `F_E = embedDoubleLaurent formalGroupZW`, `F_E` is written from a bivariate power
series, hence pole-free in both gradings by construction. -/
theorem coeff_formalGroupLaurent_inner_of_lt (W : WeierstrassCurve R) (n : ℤ) {g : ℤ} (hg : g < 0) :
    (W.formalGroupLaurent.coeff n).coeff g = 0 := by
  rw [← W.embedDoubleLaurent_formalGroupZW, HahnSeries.embedDoubleLaurent]
  rcases lt_or_ge n 0 with hn | hn
  · rw [coe_powerSeries_coeff_of_neg _ hn, HahnSeries.coeff_zero]
  · lift n to ℕ using hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk,
      coe_powerSeries_coeff_of_neg _ hg]

/-! ### Conclusion 2 — the round-trip `formalGroupSeries = formalGroupZW` -/

/-- **Round-trip.** Reading the Laurent formal group law back as a bivariate power series recovers
the genuine `(z, w)` series: `ofDoubleLaurent W.formalGroupLaurent = W.formalGroupZW`. -/
theorem ofDoubleLaurent_formalGroupLaurent (W : WeierstrassCurve R) :
    HahnSeries.ofDoubleLaurent W.formalGroupLaurent = W.formalGroupZW := by
  rw [← W.embedDoubleLaurent_formalGroupZW, HahnSeries.ofDoubleLaurent_embedDoubleLaurent]

/-- **The extracted formal group series is the genuine one.**
`W.formalGroupSeries = W.formalGroupZW`.  Since `formalGroupSeries := ofDoubleLaurent
formalGroupLaurent` (`Law.lean`), this is the round-trip that the commutativity, associativity, and
log-additivity packaging (#283/#263/#291) consume. -/
theorem formalGroupSeries_eq_formalGroupZW (W : WeierstrassCurve R) :
    W.formalGroupSeries = W.formalGroupZW := by
  rw [formalGroupSeries, W.ofDoubleLaurent_formalGroupLaurent]

end WeierstrassCurve
