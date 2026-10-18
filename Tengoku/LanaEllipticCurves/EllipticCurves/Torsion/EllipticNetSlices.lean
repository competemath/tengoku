/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.WardR1Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `IsEllipticNet` has no content beyond `IsEllipticSequence`

Mathlib's `IsEllipticNet W` is `∀ p q r s : ℤ, IsEllipticNet.rel W p q r s = 0`, a **four**-index
condition; `IsEllipticSequence W` is its `s = 0` slice, and `IsEllipticNet.isEllipticSequence` is
the only implication `Mathlib` records between them.  This file proves the converse for any `W`
whose values at nonzero indices are regular:

```
IsEllipticNet W  ↔  IsEllipticSequence W          (isEllipticNet_iff_isEllipticSequence)
```

Combined with `IsEllipticNet.isEllipticSequence_iff_rel_one` of
`EllipticCurves.Torsion.WardR1`, which collapses `IsEllipticSequence` onto its own `r = 1`
sub-slice, this gives, for an odd normalised `W` with regular values,

```
IsEllipticNet W  ↔  ∀ p q : ℤ, rel W p q 1 0 = 0   (isEllipticNet_iff_rel_one)
```

— the **whole** four-index elliptic-net condition is Ward's two-parameter addition formula.

## ⚠️ What this means for Ward's theorem, and what it does not

`EllipticCurves.Torsion.WardR1Core` isolates the `r = 1` slice for `normEDS` into the single
hypothesis `WeierstrassCurve.WardGapCore`.  The corollaries below therefore give
`IsEllipticNet (normEDS b c d)` over **every** `CommRing`, conditional on exactly `WardGapCore` and
on nothing further: the `s ≠ 0` layer is not additional content.

⚠️ **Nothing here proves, weakens or bears on `WardGapCore` itself.**  As with
`one_sq_mul_rel_zero`, what is removed is a rung that was never there.

⚠️ **`IsEllipticNet` is still only one of the two conjuncts of Mathlib's `IsEllipticDvdSequence`.**
The other, `IsDvdSequence (normEDS b c d)`, is proved neither in `Mathlib` nor here, so discharging
`WardGapCore` would close half of that `TODO`.

## How the four indices come off

Three ingredients, all of them identities of `rel` over an arbitrary `CommRing` with **no** oddness,
**no** `W 0 = 0` and **no** normalisation:

* `IsEllipticNet.rel_reindex_sum` : `rel W p q r s = rel W (q + r + s) q r (p - q - r)`.  A
  term-by-term reindexing: it sends the fourth index to `p - q - r`, which is **even** whenever
  `p + q + r` is.
* `IsEllipticNet.rel_reindex_avg` : `rel W p q r s = rel W p (p - r) (p - q) (q + r + s - p)`.  The
  `rel`-coordinate form of Mathlib's `IsEllipticNet.atomRel_avg_sub`; it sends the fourth index to
  `q + r + s - p`, which is **even** whenever `p + q + r + s` is.
* `IsEllipticNet.sub_mul_mul_rel` : `W (s - k) * W k * rel W p q r s` is a `W(·)W(·)`-combination of
  three relators with fourth index `s - 2 * k`, so at `s = 2 * k` it descends onto `s = 0` at the
  cost of the multiplier `W k ^ 2`.

⚠️ The first two are what makes the odd `s` layer collapse, and **neither is available inside a
single parity class**: for `s` odd, one of `p + q + r` and `p + q + r + s` is even, so exactly one
of the two reindexings lands on an even fourth index — and it is not always the same one.  Both are
needed, which is why `Mathlib`'s `atomRel_avg_sub` alone does not settle this.

⚠️ The **regularity hypothesis** `∀ n ≠ 0, IsRegular (W n)` is the price of `sub_mul_mul_rel`'s
multiplier and nothing else; it is used only at `s = 2 * k`, `k ≠ 0`.  It holds for
`normEDS X₀ X₁ X₂` over the integral domain `UnivEDS` by
`WeierstrassCurve.normEDS_univ_ne_zero`, which is why the `normEDS` corollaries below need no
hypothesis of their own.  ⚠️ It **is** necessary and cannot simply be deleted:
`IsEllipticNet.exists_odd_isEllipticSequence_not_isEllipticNet`
(`EllipticCurves.Torsion.EllipticNetRegularity`) exhibits an odd `W` over an explicit `CommRing`
that is an elliptic sequence and is not an elliptic net.

⚠️ That is necessity of this hypothesis, **not** sharpness of it.  The witness there has
`W n * W n = 0` at *every* index, so regularity fails as badly as it can and nothing is measured
about intermediate weakenings.  ⚠️ Nor does it reach `isEllipticNet_iff_rel_one` below, which also
assumes `W 1 = 1`: the witness cannot be normalised, and whether `hreg` is removable for a
normalised `W` is unmeasured.

## Main statements

* `IsEllipticNet.rel_reindex_sum`, `IsEllipticNet.rel_reindex_avg` : the two reindexings.
* `IsEllipticNet.sub_mul_mul_rel` : the `s → s - 2 * k` exchange identity.
* `IsEllipticNet.isEllipticNet_of_isEllipticSequence`,
  `IsEllipticNet.isEllipticNet_iff_isEllipticSequence`,
  `IsEllipticNet.isEllipticNet_iff_rel_one` : the collapse.
* `WeierstrassCurve.normEDS_isEllipticNet_of_gapCore`,
  `WeierstrassCurve.Affine.ψ_isEllipticNet_of_gapCore` and its `evalEval` companion :
  `IsEllipticNet` for `normEDS` and for the division polynomials, conditional on `WardGapCore`.

## References

* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).
* K. Stange, *Elliptic nets and elliptic curves*, Algebra & Number Theory 5 (2011).
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace IsEllipticNet

variable {R : Type*} [CommRing R] (W : ℤ → R)

/-! ### Two reindexings of the relator -/

/-- **`rel W p q r s = rel W (q + r + s) q r (p - q - r)`**, for every sequence `W : ℤ → R` over
every `CommRing`.

⚠️ A **formal identity**, and in fact a term-by-term one: the three products of `rel` on the right
are those of `rel` on the left, in the order `1, 2, 3`.  No recurrence, no `W 1 = 1`, no oddness.
It is the `rel`-coordinate form of the transformation
`(α, β, γ, δ) ↦ ((α+β+γ+δ)/2, (α+β-γ-δ)/2, (α-β+γ-δ)/2, (α-β-γ+δ)/2)` of the four arguments of
Mathlib's `IsEllipticNet.atomRel`, which permutes the **twelve** half-indices `(x ± y) / 2` that the
six `atom`s are built from, and thereby preserves each of `atomRel`'s three `atom`-products — which
is where the term-by-term matching above comes from.

⚠️ It does **not** permute the six `atom`s themselves; it re-pairs them.  The atoms of
`atomRel W 1 3 5 9` are `W 2 * W (-1)`, `W 7 * W (-2)`, `W 3 * W (-2)`, `W 6 * W (-3)`,
`W 5 * W (-4)`, `W 4 * W (-1)`, and the transformation sends `(1, 3, 5, 9)` to `(9, -5, -3, 1)`,
whose first atom `atom W 9 (-5) = W 2 * W 7` is none of the six.

⚠️ Its use is that it sends the fourth index to `p - q - r`, of the same parity as `p + q + r`, so
it makes the fourth index **even** whenever `p + q + r` is — whatever the parity of `s`. -/
lemma rel_reindex_sum (p q r s : ℤ) : rel W p q r s = rel W (q + r + s) q r (p - q - r) := by
  simp only [rel]
  ring_nf

/-- **`rel W p q r s = rel W p (p - r) (p - q) (q + r + s - p)`**, for every sequence `W : ℤ → R`
over every `CommRing`.

⚠️ A **formal identity**, and — like `rel_reindex_sum` — a term-by-term one, the three products
matching in the order `1, 2, 3`.  No recurrence, no `W 1 = 1`, no oddness.  It is the
`rel`-coordinate form of Mathlib's `IsEllipticNet.atomRel_avg_sub`, and unlike that lemma it needs
no same-parity side condition, because in these coordinates the parity condition is automatic.

⚠️ Its use is that it sends the fourth index to `q + r + s - p`, of the same parity as
`p + q + r + s`, so it makes the fourth index **even** whenever `p + q + r + s` is. -/
lemma rel_reindex_avg (p q r s : ℤ) : rel W p q r s = rel W p (p - r) (p - q) (q + r + s - p) := by
  simp only [rel]
  ring_nf

/-! ### The exchange identity that lowers the fourth index -/

/-- **The fourth index can be lowered by `2 * k`**: for every sequence `W : ℤ → R` over every
`CommRing`,

```
W (s - k) * W k * rel W p q r s
  = W (r + s) * W r * rel W (p + k) (q + k) k (s - 2 * k)
    - W (q + s) * W q * rel W (p + k) (r + k) k (s - 2 * k)
    + W (p + s) * W p * rel W (q + k) (r + k) k (s - 2 * k) .
```

⚠️ A **formal identity**: no recurrence, no `W 1 = 1` and — in contrast with
`IsEllipticNet.one_sq_mul_rel_zero`, whose shape it shares — **no oddness of `W`**.  The right-hand
side expands into nine products of six `W`-values; the three carrying the factor `W (s - k) * W k`
are the left-hand side, and the other six cancel in three pairs, each pair being one monomial with
opposite signs from two different summands.

⚠️ The shift is by `2 * k` and never by an odd amount, which is why the two reindexings above are
needed as well.  At `s = 2 * k` the multiplier is `W k ^ 2` and the right-hand side lives entirely
in the `s = 0` layer. -/
lemma sub_mul_mul_rel (p q r s k : ℤ) :
    W (s - k) * W k * rel W p q r s =
      W (r + s) * W r * rel W (p + k) (q + k) k (s - 2 * k)
      - W (q + s) * W q * rel W (p + k) (r + k) k (s - 2 * k)
      + W (p + s) * W p * rel W (q + k) (r + k) k (s - 2 * k) := by
  simp only [rel]
  ring_nf

/-- **The layer at `s - 2 * k` gives the layer at `s`**, provided the multiplier `W (s - k) * W k`
of `sub_mul_mul_rel` is a regular element. -/
lemma rel_eq_zero_of_rel_sub_two_mul {s : ℤ} (k : ℤ) (hreg : IsRegular (W (s - k) * W k))
    (h : ∀ p q r : ℤ, rel W p q r (s - 2 * k) = 0) (p q r : ℤ) : rel W p q r s = 0 := by
  have key : W (s - k) * W k * rel W p q r s = W (s - k) * W k * 0 := by
    rw [sub_mul_mul_rel W p q r s k, h, h, h]
    ring
  exact hreg.left key

/-! ### The collapse -/

/-- **`IsEllipticSequence W` implies `IsEllipticNet W`**, for any `W : ℤ → R` over any `CommRing`
whose values at nonzero indices are regular.

⚠️ Neither oddness nor `W 1 = 1` is used: the `s = 0` layer alone carries the whole four-index
relation.  The two reindexings `rel_reindex_sum` and `rel_reindex_avg` move the fourth index into
`2ℤ`, and `sub_mul_mul_rel` then descends from `2 * k` to `0` at the cost of `W k ^ 2`, which is the
only place the hypothesis `hreg` is spent. -/
theorem isEllipticNet_of_isEllipticSequence (hreg : ∀ n : ℤ, n ≠ 0 → IsRegular (W n))
    (h : IsEllipticSequence W) : IsEllipticNet W := by
  have heven : ∀ k p q r : ℤ, rel W p q r (2 * k) = 0 := by
    intro k p q r
    rcases eq_or_ne k 0 with rfl | hk
    · simpa using h p q r
    · refine rel_eq_zero_of_rel_sub_two_mul W k ?_ (fun a b c => ?_) p q r
      · rw [show (2 : ℤ) * k - k = k by ring]
        exact (hreg k hk).mul (hreg k hk)
      · rw [show (2 : ℤ) * k - 2 * k = 0 by ring]
        exact h a b c
  intro p q r s
  rcases Int.even_or_odd s with hs | hs
  · obtain ⟨m, hm⟩ := hs
    rw [show s = 2 * m by omega]
    exact heven m p q r
  · rcases Int.even_or_odd (p + q + r) with hd | hd
    · obtain ⟨m, hm⟩ := hd
      rw [rel_reindex_sum W p q r s, show p - q - r = 2 * (m - q - r) by omega]
      exact heven _ _ _ _
    · obtain ⟨m, hm⟩ := hd
      obtain ⟨n, hn⟩ := hs
      rw [rel_reindex_avg W p q r s, show q + r + s - p = 2 * (m + n + 1 - p) by omega]
      exact heven _ _ _ _

/-- **`IsEllipticNet W ↔ IsEllipticSequence W`**, for any `W : ℤ → R` over any `CommRing` whose
values at nonzero indices are regular.  The forward direction is Mathlib's
`IsEllipticNet.isEllipticSequence`. -/
theorem isEllipticNet_iff_isEllipticSequence (hreg : ∀ n : ℤ, n ≠ 0 → IsRegular (W n)) :
    IsEllipticNet W ↔ IsEllipticSequence W :=
  ⟨fun h => h.isEllipticSequence, isEllipticNet_of_isEllipticSequence W hreg⟩

/-- **`IsEllipticNet W ↔ ∀ p q, rel W p q 1 0 = 0`**, for an odd normalised `W` whose values at
nonzero indices are regular: the four-index elliptic-net condition is exactly Ward's two-parameter
addition formula.

Composite of `isEllipticNet_iff_isEllipticSequence` with `isEllipticSequence_iff_rel_one`; the two
extra hypotheses `odd` and `h1` are used only by the latter. -/
theorem isEllipticNet_iff_rel_one (odd : W.Odd) (h1 : W 1 = 1)
    (hreg : ∀ n : ℤ, n ≠ 0 → IsRegular (W n)) :
    IsEllipticNet W ↔ ∀ p q : ℤ, rel W p q 1 0 = 0 :=
  (isEllipticNet_iff_isEllipticSequence W hreg).trans (isEllipticSequence_iff_rel_one W odd h1)

end IsEllipticNet

/-! ### `IsEllipticNet` for `normEDS`, conditional on `WardGapCore` -/

namespace WeierstrassCurve

open MvPolynomial

/-- **`IsEllipticNet (normEDS X₀ X₁ X₂)` over the universal ring, conditional on `WardGapCore`.**
The `s = 0` layer is `normEDS_isEllipticSequence_of_gapCore`; `UnivEDS` is an integral domain and
`normEDS_univ_ne_zero` makes every value at a nonzero index regular, which is exactly the hypothesis
of `IsEllipticNet.isEllipticNet_of_isEllipticSequence`. -/
theorem normEDS_isEllipticNet_univ_of_gapCore (hgap : WardGapCore) :
    IsEllipticNet (normEDS (X 0 : UnivEDS) (X 1) (X 2)) :=
  IsEllipticNet.isEllipticNet_of_isEllipticSequence _
    (fun n hn => IsRegular.of_ne_zero (normEDS_univ_ne_zero n hn))
    (normEDS_isEllipticSequence_of_gapCore _ _ _ hgap)

variable {R : Type*} [CommRing R]

/-- **`IsEllipticNet (normEDS b c d)` over an arbitrary `CommRing`, conditional on `WardGapCore`.**

⚠️ The regularity hypothesis of `IsEllipticNet.isEllipticNet_of_isEllipticSequence` is *not*
available over a general `R` — `normEDS b c d n` may well be a zero divisor there — so the proof
runs over `UnivEDS`, where it is, and specialises along the ℤ-algebra map `X₀ ↦ b, X₁ ↦ c, X₂ ↦ d`
exactly as `normEDS_rel_one_of_gapCore` does for the `r = 1` slice.

Together with `normEDS_isEllipticSequence_of_gapCore` this says that the `s ≠ 0` layer of Mathlib's
elliptic-net relation is **not** additional content for `normEDS`: both layers are `WardGapCore`. -/
theorem normEDS_isEllipticNet_of_gapCore (b c d : R) (hgap : WardGapCore) :
    IsEllipticNet (normEDS b c d) := by
  intro p q r s
  set φ : UnivEDS →+* R := (aeval ![b, c, d] : UnivEDS →ₐ[ℤ] R).toRingHom with hφ
  have hcomp : φ ∘ normEDS (X 0 : UnivEDS) (X 1) (X 2) = normEDS b c d := by
    funext n
    rw [Function.comp_apply, map_normEDS]
    congr 1 <;> simp [hφ]
  have h := IsEllipticNet.map_rel (normEDS (X 0 : UnivEDS) (X 1) (X 2)) φ p q r s
  rw [normEDS_isEllipticNet_univ_of_gapCore hgap, map_zero, hcomp] at h
  exact h.symm

namespace Affine

variable (W : Affine R)

/-- `IsEllipticNet W.ψ` — the division polynomials of `W` form an elliptic **net** in `R[X][Y]`, not
merely an elliptic sequence — conditional on `WardGapCore`.  Instance of
`normEDS_isEllipticNet_of_gapCore` at `b = W.ψ₂`, `c = C W.Ψ₃`, `d = C W.preΨ₄`. -/
theorem ψ_isEllipticNet_of_gapCore (hgap : WardGapCore) : IsEllipticNet W.ψ :=
  normEDS_isEllipticNet_of_gapCore W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) hgap

variable {x y : R}

/-- `IsEllipticNet` for the point-values `n ↦ ψₙ(x, y)` at an affine point of `W`, conditional on
`WardGapCore`.  Obtained from `ψ_isEllipticNet_of_gapCore` through the evaluation ring hom. -/
theorem ψ_isEllipticNet_evalEval_of_gapCore (hgap : WardGapCore) :
    IsEllipticNet (fun n ↦ (W.ψ n).evalEval x y) := by
  intro p q r s
  have h := IsEllipticNet.map_rel W.ψ (evalEvalRingHom x y) p q r s
  rw [ψ_isEllipticNet_of_gapCore W hgap p q r s, map_zero] at h
  exact h.symm

end Affine

end WeierstrassCurve
