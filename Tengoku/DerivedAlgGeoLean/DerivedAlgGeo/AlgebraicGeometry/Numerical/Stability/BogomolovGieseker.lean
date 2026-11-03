/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.SlopeK3
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.K3

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bogomolov–Gieseker and Hodge index as supplied data, and what they buy

Two inequalities enter the repository here for the first time, both as fields of
supplied-data structures rather than as theorems, and both are then spent.

## Supplied, not proved

**Bogomolov–Gieseker.** For a `μ_H`-semistable sheaf on a polarised variety,
`∫ Δ(E)·H^(n-2) ≥ 0`. The classical proof runs through restriction to curves —
Mehta–Ramanathan, and in positive characteristic Flenner and Langer. None of
that machinery exists in this repository, and Mathlib has none of it at the pin.

**The Hodge index inequality.** For a divisor `D` on a surface with a
polarisation `H`, `(∫D·H)² ≥ (∫H²)(∫D²)`. The Hodge index theorem is likewise
absent from both this repository and Mathlib at the pin.

So both are carried as hypotheses, in the same idiom and with the same honesty
as the repository's other supplied-not-proved data. Nothing below proves either,
and nothing below is a claim about a sheaf.

**`Semistable` is opaque, and it has to be.** Slope-semistability is a property
of a *sheaf*: it quantifies over subsheaves and compares slopes. The numerical
layer has no subobjects — `N` is an abelian group with a rank and a Chern
character, and nothing more — so the predicate cannot be defined here. It is a
field, supplied by whichever layer can define it.

## What is genuinely new, and what is merely relocated

`Numerical/GrothendieckGroup/MukaiVector.lean` records `χ(E,E) ≤ 2` at
`neg_two_le_selfPairing_mukaiVector_iff` as "Bridgeland's Lemma 5.1, reduced to
one inequality about `χ`", blocked on #332 for want of simplicity and Serre
duality.

**This file does not close that gap. It relocates it.** The semistability
predicate is opaque and the inequality is a supplied field, so what was an
unproved theorem about sheaves becomes a named hypothesis.

What *is* new is that, given the hypothesis, the rank-`≤ 1` case needs no `Ext`
and no Serre duality at all. `K3.mukaiSelfPairing_eq` gives
`⟨v(E),v(E)⟩ = ∫Δ(E) − 2·rank(E)²`, so `∫Δ ≥ 0` together with `rank² ≤ 1` is
already enough. No cohomology appears anywhere in the derivation.

## Main results

* `BogomolovGiesekerData`, `HodgeIndexStatement` — the two supplied data.
* `Surface.nonneg_degree_discriminant` — `0 ≤ ∫Δ(E)` at `n = 2`.
* `Surface.discrH_nonneg` — `0 ≤ discrH`, the bridge to the `(s,t)` plane.
* `K3.chi₂_self_le`, `K3.mukaiSelfPairing_ge` — the two shifted readings.
* `K3.neg_two_le_mukaiSelfPairing_of_rank_le_one` and
  `K3.chi₂_self_le_two_of_rank_le_one` — Lemma 5.1 for `|r| ≤ 1`.
* `Examples.k3HodgeIndex` — a *proved* witness, by the equality case.
* `Examples.k3BogomolovSanity` — a sanity witness, **not** geometry.
-/

universe u v w

namespace AlgebraicGeometry.Numerical

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]

/-! ### The two supplied data -/

/-- **The Bogomolov–Gieseker inequality, as supplied data.**

Carries a choice of semistability predicate as well as a proposition, which is
why it is `…Data` and not `…Statement`.

Neither field is proved anywhere in this repository. See the module docstring:
the classical proof runs through restriction to curves, which does not exist
here or in Mathlib at the pin.-/
structure BogomolovGiesekerData (V : NumericalVarietyData n A N)
    (P : Polarization V.ring) where
  /-- Slope-semistability, supplied.

  It cannot be defined at this layer: semistability quantifies over subsheaves
  and the numerical layer has no subobjects. Whichever layer can define it
  supplies this field.-/
  Semistable : N → Prop
  /-- **Bogomolov–Gieseker**: a semistable class has nonnegative twisted
  discriminant degree. Supplied, not proved.-/
  nonneg : ∀ E : N, Semistable E → 0 ≤ discDegH V P E

/-- **The Hodge index inequality, as supplied data**: `(∫D·H)² ≥ (∫H²)(∫D²)`
for `D = c₁(E)`.

`…Statement` rather than `…Data`: it carries a proposition and no choice.

Not proved here. The Hodge index theorem for surfaces is absent from this
repository and from Mathlib at the pin.-/
structure HodgeIndexStatement (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) where
  /-- The algebraic index inequality at `c₁(E)`. Supplied, not proved.-/
  index_le : ∀ E : N,
    V.ring.degree (P.cls ^ 2) * V.ring.degree (V.chComp E 1 * V.chComp E 1)
      ≤ degH V P E ^ 2

/-! ### Spending Bogomolov–Gieseker on a surface -/

namespace Surface

variable {V : NumericalVarietyData 2 A N} {P : Polarization V.ring} {E : N}

/-- At `n = 2` the twist is trivial, so Bogomolov–Gieseker reads
`0 ≤ ∫_X Δ(E)` with no polarisation in the conclusion.
@isnad1 id=le.1h6v.s7.40bc737d1376 from=translated src=- shape=827b0f83 vocab=bf0863c3
-/
theorem nonneg_degree_discriminant (B : BogomolovGiesekerData V P)
    (hE : B.Semistable E) : 0 ≤ V.ring.degree (V.discriminant E) := by
  have h := B.nonneg E hE
  rwa [discDegH_eq] at h

/-- **The bridge lemma**: the tilt discriminant of a semistable class is
nonnegative.

This is the one thing Bogomolov–Gieseker alone does *not* give, because
`discrH` weights the rank slot by `∫H²` while `∫Δ` does not. The chain is

```
discrH = (∫c₁·H)² − 2(∫H²)·r·∫ch₂
       ≥ (∫H²)(∫c₁²) − 2(∫H²)·r·∫ch₂        (Hodge index)
       = (∫H²)·∫Δ(E) ≥ 0                     (Bogomolov–Gieseker, ∫H² > 0)
```

`0 < ∫H²` comes from the `Polarization`'s own `degree_pow_pos` field at
`n = 2`; it is not a separate hypothesis. This is the declaration the `(s,t)`
transport consumes.
@isnad1 id=le.2h6v.s6.1f29d1714fb2 from=translated src=- shape=2d2449ea vocab=5dee36fb
-/
theorem discrH_nonneg (B : BogomolovGiesekerData V P) (hI : HodgeIndexStatement V P)
    (hE : B.Semistable E) : 0 ≤ discrH V P E := by
  have hH : 0 < V.ring.degree (P.cls ^ 2) := P.degree_pow_pos
  have hD := nonneg_degree_discriminant B hE
  rw [V.degree_discriminant] at hD
  have hidx := hI.index_le E
  rw [discrH_eq]
  nlinarith [mul_nonneg hH.le hD, hidx, hH]

end Surface

/-! ### The K3 consequences -/

namespace K3

variable {V : NumericalVarietyData 2 A N} {P : Polarization V.ring} {E : N}

/-- `χ(E,E) ≤ 2·rank(E)²` for a semistable class on a K3.

`chi₂_self` writes `χ(E,E) = 2r² − ∫Δ(E)`; Bogomolov–Gieseker removes the
second term.
@isnad1 id=le.2h6v.s7.e93a5dd59a08 from=translated src=- shape=f8273556 vocab=d98a1385
-/
theorem chi₂_self_le (B : BogomolovGiesekerData V P) (hK3 : IsK3 V)
    (hE : B.Semistable E) : V.chi₂ E E ≤ 2 * (V.rank E : ℚ) ^ 2 := by
  rw [chi₂_self V hK3]
  linarith [Surface.nonneg_degree_discriminant B hE]

/-- `⟨v(E),v(E)⟩ ≥ −2·rank(E)²` for a semistable class.

`IsK3`-free, exactly as `mukaiSelfPairing_eq` is: the identity relating the
Mukai self-pairing to the discriminant is arithmetic and holds on any surface.
Only the *reading* of `(r, c₁, s)` as a Mukai vector is K3-specific.
@isnad1 id=le.1h6v.s7.8a09f3ae590a from=translated src=- shape=b9d31b18 vocab=543b24ca
-/
theorem mukaiSelfPairing_ge (B : BogomolovGiesekerData V P) (hE : B.Semistable E) :
    -2 * (V.rank E : ℚ) ^ 2 ≤ mukaiSelfPairing V E := by
  rw [mukaiSelfPairing_eq]
  linarith [Surface.nonneg_degree_discriminant B hE]

/-- **Bridgeland's Lemma 5.1, for rank at most one in absolute value.**

`⟨v(E),v(E)⟩ ≥ −2` for a semistable class with `rank(E)² ≤ 1`.

Three things this is not, stated plainly because each is easy to over-read:

* **It is not the general case.** For `|r| ≥ 2` the bound degrades to `−2r²`
  and stays there; `mukaiSelfPairing_ge` is all that survives. The general
  statement needs simplicity and Serre duality, which is #740's chain and is
  untouched here.
* **It is not a discharge of #332.** The conclusion is conditional on a supplied
  `BogomolovGiesekerData`, so the gap that issue records is relocated into a
  named hypothesis, not closed.
* **It is not cohomological.** No `Ext`, no `Hom`, no Serre duality appears in
  the derivation — `mukaiSelfPairing_eq` plus `rank² ≤ 1` is the whole proof.
  That is what is genuinely new here.
@isnad1 id=le.2h6v.s7.cfdf3a70e7e9 from=translated src=- shape=27bafdde vocab=2d1a1829
-/
theorem neg_two_le_mukaiSelfPairing_of_rank_le_one (B : BogomolovGiesekerData V P)
    (hE : B.Semistable E) (hr : V.rank E ^ 2 ≤ 1) : -2 ≤ mukaiSelfPairing V E := by
  have h := mukaiSelfPairing_ge B hE
  have hr' : ((V.rank E : ℚ)) ^ 2 ≤ 1 := by exact_mod_cast hr
  nlinarith [h, hr']

/-- The same statement read through `χ`: `χ(E,E) ≤ 2` for a semistable class of
rank at most one in absolute value. Same three caveats as
`neg_two_le_mukaiSelfPairing_of_rank_le_one`.
@isnad1 id=le.3h6v.s7.61ec2cef0d2e from=translated src=- shape=b41dc7d2 vocab=3cb82303
-/
theorem chi₂_self_le_two_of_rank_le_one (B : BogomolovGiesekerData V P) (hK3 : IsK3 V)
    (hE : B.Semistable E) (hr : V.rank E ^ 2 ≤ 1) : V.chi₂ E E ≤ 2 := by
  have h := chi₂_self_le B hK3 hE
  have hr' : ((V.rank E : ℚ)) ^ 2 ≤ 1 := by exact_mod_cast hr
  nlinarith [h, hr']

variable {Λ : Type w} [AddCommGroup Λ]

/-- The lattice-side reading, recorded so the two forms are known to agree:
through `neg_two_le_selfPairing_mukaiVector_iff` the `χ` bound above *is* the
Mukai-lattice bound `⟨v(E),v(E)⟩ ≥ −2` on the supplied integral lattice.
@isnad1 id=le.4h8v.s7.de6b0d71532a from=translated src=- shape=103b997f vocab=428831b7
-/
theorem neg_two_le_selfPairing_mukaiVector_of_rank_le_one (D : IntegralMukaiData V Λ)
    (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (B : BogomolovGiesekerData V P)
    (hE : B.Semistable E) (hr : V.rank E ^ 2 ≤ 1) :
    -2 ≤ Mukai.selfPairing D.b (D.mukaiVector E) :=
  (D.neg_two_le_selfPairing_mukaiVector_iff hHRR hK3 E).mpr
    (chi₂_self_le_two_of_rank_le_one B hK3 hE hr)

end K3

/-! ### Witnesses on the rank-one K3 model -/

namespace Examples

open AlgebraicGeometry.Numerical.Examples

end Examples

end AlgebraicGeometry.Numerical
