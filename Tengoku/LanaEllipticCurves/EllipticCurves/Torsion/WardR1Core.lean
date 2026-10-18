/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.WardR1

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ward's theorem, the `r = 1` slice: the elliptic addition formula for `normEDS`

Building on the infrastructure of `EllipticCurves.Torsion.WardR1` (symmetries of the relator, the
`q ∈ {0, 1}` base slices, and the universal-ring nonvanishing framework), this file develops the
`r = 1` slice of the elliptic-net relation for the canonical normalised elliptic divisibility
sequence `normEDS b c d` over an arbitrary `CommRing R`:

```
IsEllipticNet.rel (normEDS b c d) p q 1 0 = 0    for all p q : ℤ,
```

which, using `normEDS 1 = 1`, is exactly **Ward's elliptic addition formula** (Ward 1948):

```
W (p + q) * W (p - q) = W (p + 1) * W (p - 1) * W q ^ 2 - W (q + 1) * W (q - 1) * W p ^ 2 .
```

This is (the `r = 1` slice of) the standing Mathlib `TODO` "prove that `normEDS` satisfies
`IsEllipticDvdSequence`" in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

## What this file delivers

The full addition formula reduces, over the universal coefficient ring `UnivEDS = ℤ[X₀, X₁, X₂]`,
to a **single core** — the gap `≥ 3` case, isolated here as the hypothesis `WardGapCore`. That
hypothesis is **discharged**, in `EllipticCurves.Torsion.WardHalving`; see *"Why the core is
isolated here, and where it is discharged"* below. Everything else is discharged unconditionally
and sorry-free in this file:

* the ℤ → ℕ sign reduction (`IsEllipticNet.rel_one_neg_left`/`_right`) and the swap antisymmetry
  extending `b ≤ a` to all pairs (`IsEllipticNet.rel_one_swap`);
* the **diagonal** `p = q` slice, `normEDS_rel_one_univ_diag` / `normEDS_rel_one_diag` /
  `Affine.ψ_rel_one_diag` — proved from the swap antisymmetry and characteristic `0` of the
  universal ring, then transferred to every `CommRing R` (so it is **unconditional**);
* the bases `q ∈ {0, 1}` (`normEDS_rel_one_zero`/`_one`) and the two doubling bands
  `|p − q| ∈ {1, 2}` (the two-term recurrences `normEDS_rel_odd`/`normEDS_rel_even`);
* the **complete** `UnivEDS → R` transfer (`aeval Xᵢ ↦ b, c, d` composed with `map_rel` and
  `map_normEDS`) and the specialisation to the division polynomials `W.ψ` and their point-values.

Consequently the whole `r = 1` slice is available **conditionally on the single fact `WardGapCore`**
(`normEDS_rel_one_of_gapCore`, `Affine.ψ_rel_one_of_gapCore`, `..._evalEval_of_gapCore`), and
feeding the hypothesis in is exactly how the unconditional form is obtained downstream:
`EllipticCurves.Torsion.WardHalving` proves `WeierstrassCurve.wardGapCore : WardGapCore`, and its
`WeierstrassCurve.normEDS_rel_one` is literally `normEDS_rel_one_of_gapCore b c d wardGapCore`. The
`_of_gapCore` API below is therefore what that file consumes, not something it supersedes.

## ⚠️ The `r = 1` slice is not a slice: it **is** `IsEllipticSequence`

Mathlib defines `IsEllipticSequence W` as `∀ p q r, rel W p q r 0 = 0`, and it is natural to read
the `r = 1` case as a first step towards it. It is not a step — it is the whole thing. For any odd
`W` over any `CommRing`, `IsEllipticNet.one_sq_mul_rel_zero`
(`EllipticCurves.Torsion.WardR1`) gives

```
W 1 ^ 2 * rel W p q r 0
  = W r ^ 2 * rel W p q 1 0 + W p ^ 2 * rel W q r 1 0 + W q ^ 2 * rel W r p 1 0,
```

a formal identity closed by `ring` after one oddness rewrite, with no recurrence and no `W 1 = 1`.
So `normEDS_isEllipticSequence_of_gapCore` below is conditional on **exactly** `WardGapCore` and on
nothing else, and there is no further induction between the two.

⚠️ **This proves nothing about `WardGapCore` and does not weaken it.** It says how much the `r = 1`
slice already buys, not that the slice is any closer. ⚠️ And it is **one of the two conjuncts** of
Mathlib's `IsEllipticDvdSequence`: the other, `IsDvdSequence (normEDS b c d)`, is proved neither in
Mathlib nor here, so discharging `WardGapCore` — done in `EllipticCurves.Torsion.WardHalving` —
closes **half** of that `TODO` and no more.

⚠️ **The `s ≠ 0` layer is not a further rung either.** It is natural to read
`normEDS_isEllipticSequence_of_gapCore` as the `s = 0` case of the four-index `IsEllipticNet`, with
the general `s` still to come. It is not: `EllipticCurves.Torsion.EllipticNetSlices` proves
`IsEllipticNet W ↔ IsEllipticSequence W` for every `W` whose values at nonzero indices are regular,
and specialises it to `WeierstrassCurve.normEDS_isEllipticNet_of_gapCore` — `IsEllipticNet
(normEDS b c d)` over every `CommRing`, conditional on **exactly** the `WardGapCore` below. So both
layers of Mathlib's elliptic-net relation are this one hypothesis. ⚠️ Every name in this paragraph
is a **forward reference**: that module imports this one and is not in this file's import closure,
so nothing below uses any of them. It changes no statement here.

## Why the core is isolated here, and where it is discharged

⚠️ **`WardGapCore` is proved.** `EllipticCurves.Torsion.WardHalving` supplies
`WeierstrassCurve.wardGapCore` by an **elementary** strong induction on `|p| + |q|` whose step
**halves the index**: one `ring`-closed certificate per parity class of `(p, q)`, each expressing
`W 2 ^ j * rel W p q 1 0` (with `j = 3, 1, 1, 2`) as a combination of the two two-term relators and
of instances of `rel` whose `|p| + |q|` is strictly smaller on the range where the step is used.
No sigma-function theta identity and no van der Poorten–Swart machinery appear in it. The core is
stated here as a hypothesis because that is the form the downstream proof consumes — a division of
labour, not an obstruction.

⚠️ **The negative result that follows is about a different search, and it stands.** Writing
`h(p, q)` for the relator, the bands `|p − q| = 1, 2, 3` all admit uniform bounded-degree
`linear_combination` certificates in the two-term recurrences, but it was verified — by an exact
multivariate polynomial-certificate search (each `W(n)` an independent symbol) and against the
literature (Ward 1948; Silverman AEC III, Exercise 3.7; Stange, *Elliptic nets and elliptic
curves*; van der Poorten–Swart) — that the bands `|p − q| = 5, 7, …` admit **no** bounded-degree
certificate even allowing every smaller relator plus both doublings: the minimum certificate degree
grows with the gap.

⚠️ That search runs along the **gap** axis at a fixed index — derive the band `|p − q| = g` from
the bands `|p − q| < g` at the *same* index. The induction that works never uses that axis: it
halves the index instead, which is the recursion `normEDS` is actually defined by (`normEDSRec`,
`preNormEDS'_even` / `preNormEDS'_odd`). Both facts hold at once. This section used to infer from
the measurement that the core *"cannot be closed by an elementary induction"* and needs *"a
research-level formalisation"*: the measurement was right, the inference was wrong, and it is the
inference that has been retired. **Keep the measurement** — it is the only record here of why the
gap-axis route is hopeless, and deleting it would invite a re-run of a search already known to fail.

⚠️ Every name this section takes from `EllipticCurves.Torsion.WardHalving` — `wardGapCore` and
`normEDS_rel_one` — is a **forward reference**: that module imports this one (through
`EllipticCurves.Torsion.EllipticNetSlices`) and is not in this file's import closure, so nothing
below uses either of them. It changes no statement here.

## Main statements

* `WeierstrassCurve.WardGapCore` : the isolated gap `≥ 3` core, over the universal ring `UnivEDS`.
* `WeierstrassCurve.normEDS_rel_one_univ_of_gapCore` : Ward's addition formula over `UnivEDS`,
  conditional on `WardGapCore`.
* `WeierstrassCurve.normEDS_rel_one_of_gapCore` : the addition formula over an arbitrary `CommRing`,
  conditional on `WardGapCore`.
* `WeierstrassCurve.Affine.ψ_rel_one_of_gapCore` : its specialisation to the division polynomials.
* `WeierstrassCurve.normEDS_rel_one_diag` / `Affine.ψ_rel_one_diag` : the diagonal `p = q` slice,
  **unconditional**.
* `WeierstrassCurve.normEDS_isEllipticSequence_of_gapCore`,
  `WeierstrassCurve.Affine.ψ_isEllipticSequence_of_gapCore` and its `evalEval` companion :
  `IsEllipticSequence` at *every* `r`, conditional on the same `WardGapCore`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4 (Exercise 3.7).
* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

open MvPolynomial

/-! ### The isolated gap `≥ 3` core -/

/-- **The gap `≥ 3` core of Ward's `r = 1` addition formula**, stated over the universal coefficient
ring `UnivEDS = ℤ[X₀, X₁, X₂]`: for natural indices `b ≥ 2` and `a ≥ b + 3`,
`rel (normEDS X₀ X₁ X₂) a b 1 0 = 0`.

This single fact is the entire content of Ward's `r = 1` slice that is not proved in this file. It
is **discharged** in `EllipticCurves.Torsion.WardHalving`, as `WeierstrassCurve.wardGapCore`, by an
elementary index-halving induction — a forward reference, since that module imports this one. All
of `normEDS_rel_one_of_gapCore` and its corollaries are unconditional apart from a hypothesis of
this form, and that is how the unconditional theorems there are built. -/
def WardGapCore : Prop :=
  ∀ a b : ℕ, 2 ≤ b → b + 3 ≤ a →
    IsEllipticNet.rel (normEDS (X 0 : UnivEDS) (X 1) (X 2)) (a : ℤ) (b : ℤ) 1 0 = 0

/-! ### The diagonal slice (unconditional) -/

/-- The diagonal `p = q` slice of Ward's `r = 1` relator over the universal ring: it is its own
negative by the swap antisymmetry (`rel_one_swap`), and `UnivEDS` has characteristic zero, so it
vanishes. Unconditional. -/
theorem normEDS_rel_one_univ_diag (x : ℤ) :
    IsEllipticNet.rel (normEDS (X 0 : UnivEDS) (X 1) (X 2)) x x 1 0 = 0 := by
  set W : ℤ → UnivEDS := normEDS (X 0 : UnivEDS) (X 1) (X 2) with hW
  have hodd : W.Odd := normEDS_odd_fun (X 0 : UnivEDS) (X 1) (X 2)
  have hs := IsEllipticNet.rel_one_swap W hodd x x
  have h2 : (2 : UnivEDS) * IsEllipticNet.rel W x x 1 0 = 0 := by
    linear_combination hs
  have htwo : (2 : UnivEDS) ≠ 0 := by
    have h := (MvPolynomial.C_injective (Fin 3) ℤ).ne (by norm_num : (2 : ℤ) ≠ 0)
    simpa using h
  exact (mul_eq_zero.mp h2).resolve_left htwo

/-! ### The addition formula in the universal ring, conditional on the core -/

/-- **Ward's addition formula in the universal coefficient ring, conditional on `WardGapCore`.**
For the generic normalised elliptic divisibility sequence `normEDS X₀ X₁ X₂` over the domain
`UnivEDS = ℤ[X₀, X₁, X₂]`, the `r = 1` elliptic-net relator vanishes for all `p, q`, once the
gap `≥ 3` core is supplied. Every other case (sign reduction, swap, diagonal, `q ∈ {0, 1}`, the two
doubling bands) is discharged here unconditionally. -/
theorem normEDS_rel_one_univ_of_gapCore (hgap : WardGapCore) (p q : ℤ) :
    IsEllipticNet.rel (normEDS (X 0 : UnivEDS) (X 1) (X 2)) p q 1 0 = 0 := by
  set W : ℤ → UnivEDS := normEDS (X 0 : UnivEDS) (X 1) (X 2) with hW
  have hodd : W.Odd := normEDS_odd_fun (X 0 : UnivEDS) (X 1) (X 2)
  -- It suffices to prove the relation for natural-number indices, using the symmetries
  -- `rel_one_neg_left` and `rel_one_neg_right` to remove signs.
  suffices h : ∀ a b : ℕ, IsEllipticNet.rel W (a : ℤ) (b : ℤ) 1 0 = 0 by
    obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg p
    · obtain ⟨b, rfl | rfl⟩ := Int.eq_nat_or_neg q
      · exact h a b
      · rw [IsEllipticNet.rel_one_neg_right W hodd]
        exact h a b
    · obtain ⟨b, rfl | rfl⟩ := Int.eq_nat_or_neg q
      · rw [IsEllipticNet.rel_one_neg_left W hodd]
        exact h a b
      · rw [IsEllipticNet.rel_one_neg_left W hodd, IsEllipticNet.rel_one_neg_right W hodd]
        exact h a b
  -- The diagonal `p = q` slice (unconditional).
  have hdiag : ∀ x : ℤ, IsEllipticNet.rel W x x 1 0 = 0 := by
    intro x
    rw [hW]
    exact normEDS_rel_one_univ_diag x
  -- Core over `ℕ` with `b ≤ a`. Bases: `b ≤ 1`, the diagonal `a = b`, the two doubling bands
  -- `a = b + 1` (`normEDS_rel_odd`) and `a = b + 2` (`normEDS_rel_even`), and the gap `≥ 3` core.
  have hcore : ∀ a b : ℕ, b ≤ a → IsEllipticNet.rel W (a : ℤ) (b : ℤ) 1 0 = 0 := by
    intro a b hba
    obtain ⟨t, rfl⟩ : ∃ t, a = b + t := ⟨a - b, by omega⟩
    rcases b with _ | _ | b
    · -- `b = 0`
      have h0 := normEDS_rel_one_zero (X 0 : UnivEDS) (X 1) (X 2) ((0 + t : ℕ) : ℤ)
      rw [← hW] at h0
      simpa using h0
    · -- `b = 1`
      have h1 := normEDS_rel_one_one (X 0 : UnivEDS) (X 1) (X 2) ((1 + t : ℕ) : ℤ)
      rw [← hW] at h1
      simpa using h1
    · -- `b ≥ 2`
      rcases t with _ | _ | _ | t
      · -- `t = 0`: diagonal `a = b`
        convert hdiag ((b : ℤ) + 2) using 2 <;> push_cast <;> ring
      · -- `t = 1`: band 1 (odd doubling)
        have hb1 := normEDS_rel_odd (X 0 : UnivEDS) (X 1) (X 2) ((b : ℤ) + 2)
        rw [← hW] at hb1
        convert hb1 using 2 <;> push_cast <;> ring
      · -- `t = 2`: band 2 (even doubling)
        have hb2 := normEDS_rel_even (X 0 : UnivEDS) (X 1) (X 2) ((b : ℤ) + 3)
        rw [← hW] at hb2
        convert hb2 using 2 <;> push_cast <;> ring
      · -- `t ≥ 3`: the genuine gap `≥ 3` Ward core, supplied by `hgap`.
        have hg := hgap (b + 2 + (t + 3)) (b + 2) (by omega) (by omega)
        rw [← hW] at hg
        convert hg using 2
  -- Extend from `b ≤ a` to all pairs via the swap antisymmetry.
  intro a b
  rcases le_total b a with hba | hab
  · exact hcore a b hba
  · have hthis := hcore b a hab
    rw [IsEllipticNet.rel_one_swap W hodd (b : ℤ) (a : ℤ), hthis, neg_zero]

/-! ### The addition formula over an arbitrary commutative ring -/

section Transfer

variable {R : Type*} [CommRing R] (b c d : R)

/-- The diagonal `p = q` slice of Ward's `r = 1` relation over any `CommRing R`, **unconditional**.
Obtained by specialising `normEDS_rel_one_univ_diag` along the ℤ-algebra map `X₀ ↦ b, X₁ ↦ c,
X₂ ↦ d`. -/
theorem normEDS_rel_one_diag (p : ℤ) : IsEllipticNet.rel (normEDS b c d) p p 1 0 = 0 := by
  set φ : UnivEDS →+* R := (aeval ![b, c, d] : UnivEDS →ₐ[ℤ] R).toRingHom with hφ
  have hcomp : φ ∘ normEDS (X 0 : UnivEDS) (X 1) (X 2) = normEDS b c d := by
    funext n
    rw [Function.comp_apply, map_normEDS]
    congr 1 <;> simp [hφ]
  have h := IsEllipticNet.map_rel (normEDS (X 0 : UnivEDS) (X 1) (X 2)) φ p p 1 0
  rw [normEDS_rel_one_univ_diag, map_zero, hcomp] at h
  exact h.symm

/-- **Ward's elliptic addition formula for `normEDS`, the `r = 1` slice, conditional on
`WardGapCore`.** Over any `CommRing R`, the `r = 1` elliptic-net relator of the canonical normalised
EDS vanishes: `IsEllipticNet.rel (normEDS b c d) p q 1 0 = 0` for all `p, q`. Equivalently,
`W(p+q)·W(p−q) = W(p+1)·W(p−1)·W(q)² − W(q+1)·W(q−1)·W(p)²` with `W := normEDS b c d`.

Proved by specialising `normEDS_rel_one_univ_of_gapCore` along the ℤ-algebra map
`X₀ ↦ b, X₁ ↦ c, X₂ ↦ d`. -/
theorem normEDS_rel_one_of_gapCore (hgap : WardGapCore) (p q : ℤ) :
    IsEllipticNet.rel (normEDS b c d) p q 1 0 = 0 := by
  set φ : UnivEDS →+* R := (aeval ![b, c, d] : UnivEDS →ₐ[ℤ] R).toRingHom with hφ
  have hcomp : φ ∘ normEDS (X 0 : UnivEDS) (X 1) (X 2) = normEDS b c d := by
    funext n
    rw [Function.comp_apply, map_normEDS]
    congr 1 <;> simp [hφ]
  have h := IsEllipticNet.map_rel (normEDS (X 0 : UnivEDS) (X 1) (X 2)) φ p q 1 0
  rw [normEDS_rel_one_univ_of_gapCore hgap, map_zero, hcomp] at h
  exact h.symm

/-- **`IsEllipticSequence (normEDS b c d)`, conditional on `WardGapCore`** — the `s = 0` layer of
the elliptic-net relation at *every* `r`, not only at `r = 1`.

⚠️ **Nothing is proved about `WardGapCore` here, and this is not a weakening of it.** The step from
the `r = 1` slice to the general `r` is the formal identity
`IsEllipticNet.one_sq_mul_rel_zero`, which holds for any odd `W` over any `CommRing` and is closed
by `ring`. What it shows is that the `r = 1` slice was already the whole of the elliptic-sequence
property; see `IsEllipticNet.isEllipticSequence_iff_rel_one`.

⚠️ This is **one of the two conjuncts** of Mathlib's `IsEllipticDvdSequence`, whose other conjunct
`IsDvdSequence (normEDS b c d)` is not proved in Mathlib or here. Discharging `WardGapCore` would
therefore close half of that `TODO`, not all of it. -/
theorem normEDS_isEllipticSequence_of_gapCore (hgap : WardGapCore) :
    IsEllipticSequence (normEDS b c d) :=
  IsEllipticNet.isEllipticSequence_of_rel_one _ (normEDS_odd_fun b c d) (normEDS_one b c d)
    (normEDS_rel_one_of_gapCore b c d hgap)

end Transfer

/-! ### Specialisation to the division polynomials -/

namespace Affine

variable {R : Type*} [CommRing R] (W : Affine R)

/-- The diagonal `p = q` slice of Ward's addition formula for the division polynomials `W.ψ`,
as an identity in `R[X][Y]`. **Unconditional.** -/
theorem ψ_rel_one_diag (p : ℤ) : IsEllipticNet.rel W.ψ p p 1 0 = 0 :=
  normEDS_rel_one_diag W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) p

/-- Ward's addition formula for the division polynomials `W.ψ`, as an identity in `R[X][Y]`:
`IsEllipticNet.rel W.ψ p q 1 0 = 0`, conditional on `WardGapCore`. Instance of
`normEDS_rel_one_of_gapCore` at `b = W.ψ₂`, `c = C W.Ψ₃`, `d = C W.preΨ₄` (recall
`W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)`). -/
theorem ψ_rel_one_of_gapCore (hgap : WardGapCore) (p q : ℤ) :
    IsEllipticNet.rel W.ψ p q 1 0 = 0 :=
  normEDS_rel_one_of_gapCore W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) hgap p q

/-- `IsEllipticSequence W.ψ` — the division polynomials of `W` form an elliptic sequence in
`R[X][Y]` — conditional on `WardGapCore`. -/
theorem ψ_isEllipticSequence_of_gapCore (hgap : WardGapCore) : IsEllipticSequence W.ψ :=
  normEDS_isEllipticSequence_of_gapCore W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) hgap

variable {x y : R}

/-- The diagonal `p = q` slice of Ward's addition formula among the point-values of the division
polynomials at an affine point `(x, y)` of `W`. **Unconditional.** -/
theorem ψ_rel_one_evalEval_diag (p : ℤ) :
    IsEllipticNet.rel (fun n ↦ (W.ψ n).evalEval x y) p p 1 0 = 0 := by
  have h := IsEllipticNet.map_rel W.ψ (evalEvalRingHom x y) p p 1 0
  rw [ψ_rel_one_diag, map_zero] at h
  exact h.symm

/-- Ward's addition formula among the point-values of the division polynomials at an affine point
`(x, y)` of `W`: `IsEllipticNet.rel (fun n ↦ (W.ψ n).evalEval x y) p q 1 0 = 0`, conditional on
`WardGapCore`. -/
theorem ψ_rel_one_evalEval_of_gapCore (hgap : WardGapCore) (p q : ℤ) :
    IsEllipticNet.rel (fun n ↦ (W.ψ n).evalEval x y) p q 1 0 = 0 := by
  have h := IsEllipticNet.map_rel W.ψ (evalEvalRingHom x y) p q 1 0
  rw [ψ_rel_one_of_gapCore W hgap, map_zero] at h
  exact h.symm

/-- `IsEllipticSequence` for the point-values `n ↦ ψₙ(x, y)` at an affine point of `W`,
conditional on `WardGapCore`. -/
theorem ψ_isEllipticSequence_evalEval_of_gapCore (hgap : WardGapCore) :
    IsEllipticSequence (fun n ↦ (W.ψ n).evalEval x y) := by
  intro p q r
  have h := IsEllipticNet.map_rel W.ψ (evalEvalRingHom x y) p q r 0
  rw [ψ_isEllipticSequence_of_gapCore W hgap p q r, map_zero] at h
  exact h.symm

end Affine

end WeierstrassCurve
