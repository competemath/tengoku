/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.GenuineLawTransfer
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.WThreeFunctionalEq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Laurent image of the sum-point `w`-series `w ∘ F_E`

Let `F = W.formalGroupZW : MvPowerSeries (Fin 2) R` be the genuine `(z, w)` Weierstrass formal group
law and `WF := W.formalW.subst F` its associated `w`-series of the group sum (`w ∘ F`, a genuine
bivariate power series of order `3`).  This file records the image of `WF` under the writer
`HahnSeries.embedDoubleLaurent : MvPowerSeries (Fin 2) R → R⸨z₁⸩⸨z₂⸩`.

It is a step on the Laurent route towards the **invariant-differential invariance** `(★)`
`(ω_E ∘ F)·∂_{z₂}F = ω_E(z₂)` (issue #315): the invariance is proved by transporting the substituted
form `Eq.Ω_F` (`EllipticCurves.FormalGroup.InvariantDifferentialInvariance`) to the Laurent side,
where `F`, `WF` become the explicit `(z, w)`-coordinates of `P₃ = P₁ ⊕ P₂` and the addition formulas
can be differentiated (`EllipticCurves.FormalGroup.LaurentDerivation`).  Everything in `Eq.Ω_F`
involving `WF = w ∘ F` needs `WF`'s Laurent image, which is what this file supplies.

## Main result

* `WeierstrassCurve.embedDoubleLaurent_formalW_subst_formalGroupZW_functional_eq` :
  `embedDoubleLaurent WF` satisfies the **Weierstrass functional equation with local parameter**
  `F_E = W.formalGroupLaurent`.  Writing `V = embedDoubleLaurent WF`,
  `V = F_E³ + (a₁F_E + a₂F_E²)·V + (a₃ + a₄F_E)·V² + a₆·V³`.
  This is the image, under the ring homomorphism `embedDoubleLaurentRingHom`, of the fixed-point
  identity `formalW_subst_formalGroupZW_fixed`, using the merged identification
  `embedDoubleLaurent F = W.formalGroupLaurent` (`embedDoubleLaurent_formalGroupZW`).

## The gap this section used to name — CLOSED, by route 2 below

⚠️ **This section is retained as the reduction it always was, but it is no longer a statement of
missing work.**  The single identity it isolates is
`WeierstrassCurve.embedDoubleLaurent_formalW_subst_formalGroupZW`
(`EllipticCurves.FormalGroup.GenuineWThreeIdentification`, issue #333), merged and unconditional
over every `CommRing R`.  ⚠️ **Route 2 of the two offered below is the one that was taken**, and it
consumes this file's own main result: `embedDoubleLaurent_formalW_subst_formalGroupZW_univ` pairs
`embedDoubleLaurent_formalW_subst_formalGroupZW_functional_eq` with
`formalWThree_functional_eq` at the universal curve, cancels the bracket by
`bracket_univ_ne_zero` — ⚠️ rather than by the inner-pole-freeness argument route 1 proposes —
and base-changes along `W.specialize`.  With `#338` it closes `(★)` and hence #315; see
`EllipticCurves.FormalGroup.LogAdditivityUnconditional`.

## The reduction of the Laurent route to a single identity

`WeierstrassCurve.formalWThree_functional_eq`
(`EllipticCurves.FormalGroup.WThreeFunctionalEq`) proves that the transported third `w`-coordinate
`W₃ := -y₃⁻¹ = W.formalWThree` satisfies the **identical** functional equation with the **same**
parameter `F_E = W.formalGroupLaurent`.  Hence `embedDoubleLaurent WF` and `W₃` are two solutions of
one and the same Weierstrass functional equation at the parameter `F_E`.  The remaining content of
the Laurent route is therefore exactly the single identity

`embedDoubleLaurent (W.formalW.subst W.formalGroupZW) = W.formalWThree`   (i.e. `w ∘ F_E = -y₃⁻¹`).

`embedDoubleLaurent WF` is pole-free by construction (it is the writer image of a genuine bivariate
power series), so this identity is equivalent to the **inner pole-freeness of `-y₃⁻¹`** — a genuine
#286-magnitude fact that the #286/#310 identification of `F_E` itself deliberately side-stepped (it
was closed by the third-root matching of `EllipticCurves.FormalGroup.GenuineLawIdentification` /
`UniversalIdentification`, not the `w`-fixed-point uniqueness route).  Two routes were open to
close it, and ⚠️ **route 2 is the one `#333` took**:

1. **Uniqueness route.** Show `W₃` is inner pole-free, so `HahnSeries.ofDoubleLaurent W₃` is genuine
   `MvPowerSeries (Fin 2) R`; apply `ofDoubleLaurent` to `formalWThree_functional_eq` (valid because
   the elements are pole-free, so the reader is multiplicative on them) and use
   `ofDoubleLaurent_formalGroupLaurent : ofDoubleLaurent F_E = F` to see it solves
   `u = W.wOpSubst F u`; then `eq_formalW_subst_of_wOpSubst_fixed`
   (`EllipticCurves.FormalGroup.ExpansionSubst`) forces it to equal `WF`, and
   `embedDoubleLaurent_ofDoubleLaurent` transports back.
2. **Universal-domain route.** Prove `embedDoubleLaurent WF = W₃` at the universal curve over the
   char-`0` domain `S = MvPolynomial (Fin 5) ℤ` (mirroring `embedDoubleLaurent_formalGroupZW_univ`),
   then base-change along `W.specialize` via `map_embedDoubleLaurent`, a `map` lemma for `WF`, and
   `map_formalYThree`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **The Laurent image of `w ∘ F_E` satisfies the Weierstrass functional equation.**  Writing
`WF = W.formalW.subst W.formalGroupZW` and `F_E = W.formalGroupLaurent`,

`embedDoubleLaurent WF
  = F_E³ + (a₁F_E + a₂F_E²)·(embedDoubleLaurent WF)
      + (a₃ + a₄F_E)·(embedDoubleLaurent WF)² + a₆·(embedDoubleLaurent WF)³`.

This is the image of the fixed-point identity `formalW_subst_formalGroupZW_fixed`
(`WF = W.wOpSubst F WF`, with `W.wOpSubst t u = t³ + (a₁t + a₂t²)u + (a₃ + a₄t)u² + a₆u³`) under the
ring hom `HahnSeries.embedDoubleLaurentRingHom`, after replacing `embedDoubleLaurent F` by
`W.formalGroupLaurent` (`embedDoubleLaurent_formalGroupZW`).

It is the exact `WF`-analogue of `formalWThree_functional_eq` for `W₃ = -y₃⁻¹`; the two together
reduce the Laurent route to `(★)` to the single identity
`embedDoubleLaurent WF = W.formalWThree` (see the module docstring). -/
theorem embedDoubleLaurent_formalW_subst_formalGroupZW_functional_eq :
    HahnSeries.embedDoubleLaurent (W.formalW.subst W.formalGroupZW)
      = W.formalGroupLaurent ^ 3
        + (HahnSeries.C (HahnSeries.C W.a₁) * W.formalGroupLaurent
            + HahnSeries.C (HahnSeries.C W.a₂) * W.formalGroupLaurent ^ 2)
          * HahnSeries.embedDoubleLaurent (W.formalW.subst W.formalGroupZW)
        + (HahnSeries.C (HahnSeries.C W.a₃)
            + HahnSeries.C (HahnSeries.C W.a₄) * W.formalGroupLaurent)
          * HahnSeries.embedDoubleLaurent (W.formalW.subst W.formalGroupZW) ^ 2
        + HahnSeries.C (HahnSeries.C W.a₆)
          * HahnSeries.embedDoubleLaurent (W.formalW.subst W.formalGroupZW) ^ 3 := by
  -- Push `embedDoubleLaurentRingHom` through the fixed point `WF = wOpSubst F WF`.
  have h := congrArg (⇑HahnSeries.embedDoubleLaurentRingHom) W.formalW_subst_formalGroupZW_fixed
  rw [wOpSubst] at h
  simp only [map_add, map_mul, map_pow, HahnSeries.embedDoubleLaurentRingHom_apply,
    HahnSeries.embedDoubleLaurent_C, W.embedDoubleLaurent_formalGroupZW] at h
  exact h

end WeierstrassCurve
