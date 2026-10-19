/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.RingTheory.Localization.Away.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Localising away from two elements with the same non-vanishing locus

Material for `Mathlib/RingTheory/Localization/Away/Basic.lean`; see `README.md` on the mirror
tree. Upstreaming costs that file **nothing**: it is the file's own import, and the two extra
declarations named below are already in it.

`IsLocalization.Away r S` depends on `r` only through the saturation of `Submonoid.powers r` —
geometrically, only through the basic open `D(r) ⊆ Spec R`. Mathlib records the special case
where `r` and `r'` are *associated* (`IsLocalization.Away.of_associated` and
`IsLocalization.Away.iff_of_associated`), which is strictly stronger than having the same basic
open: `r` and `r ^ 2` always have the same basic open, and need not be associated — in `ℤ`,
`2` and `4` are not, the only units there being `1` and `-1`.

The general condition is symmetric divisibility of powers, and it is the condition Mathlib's own
`IsLocalization.Away.algebraMap_isUnit_iff` is already phrased in: `IsUnit (algebraMap R S r')`
holds exactly when `r'` divides a power of `r`. So the hypotheses below are, term by term, *"`r'`
becomes a unit"* and *"`r` becomes a unit"*, and no radical, prime spectrum or `Ideal` appears in
the statement or the proof.

## Main results

- `IsLocalization.Away.of_dvd_pow`: **a localisation away from `r` is a localisation away from
  `r'`**, when each of the two divides a power of the other.
- `IsLocalization.Away.iff_of_dvd_pow`: the same as an `Iff`, in the shape of
  `IsLocalization.Away.iff_of_associated`.
- `IsLocalization.Away.algEquivOfDvdPow`: the resulting isomorphism of the two localisations,
  over `R`.

## Implementation notes

`IsLocalization.Away.of_dvd_pow` is proved through `IsLocalization.Away.mk` rather than by
comparing submonoids. The three fields it asks for are the three places the hypotheses are used,
and each is one rewrite: writing `r' ^ m = r * c`, a fraction with denominator `r ^ n` is one
with denominator `r' ^ (m * n)` and numerator multiplied by `c ^ n`, and an equation killed by
`r ^ n` is killed by `r' ^ (m * n)`. Neither hypothesis is needed in the other's places, which is
why `IsLocalization.Away.iff_of_dvd_pow` can hand them back swapped.
-/

namespace IsLocalization.Away

variable {R : Type*} [CommSemiring R] (S : Type*) [CommSemiring S] [Algebra R S]

/-- **An `R`-algebra which is a localisation away from `r` is a localisation away from any `r'`
with the same non-vanishing locus**, the locus being recorded by the two divisibilities: `r'`
divides a power of `r` and `r` divides a power of `r'`.

Strictly weaker hypotheses than `IsLocalization.Away.of_associated`, which asks that `r` and `r'`
differ by a unit. -/
lemma of_dvd_pow {r r' : R} [IsLocalization.Away r S] (h : ∃ n, r' ∣ r ^ n)
    (h' : ∃ m, r ∣ r' ^ m) : IsLocalization.Away r' S := by
  obtain ⟨m, c, hc⟩ := h'
  refine mk _ ((algebraMap_isUnit_iff (S := S) r).mpr h) (fun s ↦ ?_) (fun a b hab ↦ ?_)
  · obtain ⟨n, a, hn⟩ := surj r s
    refine ⟨m * n, a * c ^ n, ?_⟩
    rw [← map_pow, pow_mul, hc, mul_pow, map_mul, map_pow, ← mul_assoc, hn, ← map_mul]
  · obtain ⟨n, hn⟩ := exists_of_eq r hab
    refine ⟨m * n, ?_⟩
    calc r' ^ (m * n) * a = c ^ n * (r ^ n * a) := by rw [pow_mul, hc, mul_pow]; ring
      _ = c ^ n * (r ^ n * b) := by rw [hn]
      _ = r' ^ (m * n) * b := by rw [pow_mul, hc, mul_pow]; ring

/-- **`IsLocalization.Away r S` depends on `r` only through its non-vanishing locus.** The `Iff`
form of `IsLocalization.Away.of_dvd_pow`, in the shape of
`IsLocalization.Away.iff_of_associated`. -/
lemma iff_of_dvd_pow {r r' : R} (h : ∃ n, r' ∣ r ^ n) (h' : ∃ m, r ∣ r' ^ m) :
    IsLocalization.Away r S ↔ IsLocalization.Away r' S :=
  ⟨fun _ ↦ of_dvd_pow S h h', fun _ ↦ of_dvd_pow S h' h⟩

variable (S' : Type*) [CommSemiring S'] [Algebra R S']

/-- **Two localisations away from elements with the same non-vanishing locus are isomorphic**, as
`R`-algebras.

The isomorphism is `IsLocalization.algEquiv` at `Submonoid.powers r'`, which is available once
`IsLocalization.Away.of_dvd_pow` has made `S` a localisation at that submonoid too. So it is the
*unique* `R`-algebra map between them, and in particular is compatible with everything either
localisation is used for. -/
noncomputable def algEquivOfDvdPow {r r' : R} [IsLocalization.Away r S]
    [IsLocalization.Away r' S'] (h : ∃ n, r' ∣ r ^ n) (h' : ∃ m, r ∣ r' ^ m) : S ≃ₐ[R] S' :=
  have : IsLocalization.Away r' S := of_dvd_pow S h h'
  IsLocalization.algEquiv (Submonoid.powers r') S S'

end IsLocalization.Away
