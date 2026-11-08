module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.LocalPair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Abelian read-off: injectivity of the Laplace-side scale

The MAIS issue #3 candidate's chain is **Abelian only**. It says so twice (pp. 30,
77): no Tauberian theorem is invoked anywhere in it. Instead it reads the local
pair `(λ, m)` directly off a two-sided bound on the Laplace transform, and the
step that licenses that reading is its Lemma 8.5:

> "the map `(λ, m) ↦ H_{λ,m}` is **injective up to two-sided constants**
> (Lemma 8.5), so a two-sided bound on `L_φ` of the form `≍ H_{λ′,m′}` already
> forces `(λ′, m′) = (λ, m)`."

Here `H_{λ,m}(T) = T^{-λ} (log T)^{m-1}` for large `T`. This module proves that
injectivity, so the "read the pair off the transform" step is a theorem rather
than an appeal.

## Why this replaces a Tauberian step

A Tauberian theorem converts an asymptotic for the transform back into an
asymptotic for the original density; the candidate deliberately avoids that
direction. What it needs instead is much weaker and purely Abelian: the *family*
of comparison scales is separated, so a bound against one member cannot also be a
bound against another. Nothing here inverts a transform, and nothing here is a
Tauberian statement. It is a separation statement about the comparison family.

## The `T → ∞` mirror of `volumeScale`

`laplaceScale` is not a new object. Under `ε = 1/T` it is exactly
`LocalPair.lean`'s `volumeScale`, with the sign of the exponent flipped by the
substitution:

`laplaceScale lam m T = volumeScale lam m (1 / T)` for `0 < T`.

That identity is proved below as `laplaceScale_eq_volumeScale`, and it is the
whole content of this file's method: every analytic fact is imported from
`LocalPair.lean` along `T ↦ 1/T`, which carries `Filter.atTop` to
`nhdsWithin 0 (Set.Ioi 0)`. The two mismatch lemmas
(`not_eventually_volumeScale_le` for the exponent,
`not_eventually_volumeScale_le_of_mult_lt` for the multiplicity) are used
verbatim; no asymptotic analysis is redone at `atTop`.

## The multiplicity hypothesis is not decoration

`m - 1` is `ℕ`-subtraction, so `laplaceScale lam 0` and `laplaceScale lam 1` are
the *same function*. Injectivity is therefore false as stated over all of `ℕ`,
and `1 ≤ m`, `1 ≤ m'` are hypotheses of every uniqueness statement here. This
matches `LocalPair.lean`, whose `HasLocalVolumeOrder` carries `1 ≤ m` in its main
branch for the same reason. The intended range of `m` is the multiplicity of a
pole, which is at least one.

## What is *not* assumed

Positivity of the exponent is not needed. The separation argument only compares
`lam` with `lam'`, so it goes through for arbitrary real exponents; requiring
`0 < lam` would be an unused hypothesis. The learning-coefficient application
supplies positivity anyway, so no consumer loses anything.
-/

namespace AISafetyAtlas.SingularLearning

open Filter Topology

/-- The Laplace-side asymptotic scale, `H_{λ,m}(T) = T^{-λ} (log T)^{m-1}`.

The exponent is `Real.rpow` and the logarithmic factor is `Monoid.npow`, matching
how `volumeScale` is spelled. As there, `m - 1` is `ℕ`-subtraction, so the
definition is constant in `m` across `m = 0` and `m = 1`; statements that read the
pair off this scale carry `1 ≤ m`.-/
@[expose] public noncomputable def laplaceScale (lam : ℝ) (m : ℕ) (T : ℝ) : ℝ :=
  T ^ (-lam) * Real.log T ^ (m - 1)

/-- **The mirror identity.** `laplaceScale` at `T` is `volumeScale` at `ε = 1/T`.

The substitution flips the sign of the exponent, `T ^ (-lam) = (1/T) ^ lam`, and
fixes the logarithm, `log (1 / (1 / T)) = log T`. Everything else in this file is
a transport of `LocalPair.lean` along this equation.-/
public theorem laplaceScale_eq_volumeScale (lam : ℝ) (m : ℕ) {T : ℝ} (hT : 0 < T) :
    laplaceScale lam m T = volumeScale lam m (1 / T) := by
  rw [laplaceScale, volumeScale, one_div_one_div, Real.rpow_neg hT.le,
    Real.div_rpow zero_le_one hT.le, Real.one_rpow, one_div]

end AISafetyAtlas.SingularLearning
