/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.EllipticNetRel
import Tengoku.Seed.Algebra.MvPolynomial.CommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ward's theorem, the `r = 1` slice: infrastructure for the elliptic addition formula

The goal of Ward's theorem (`r = 1` slice) is, for the canonical normalised elliptic divisibility
sequence `W = normEDS b c d` over a `CommRing R`, the `r = 1` slice of the elliptic-net relation

```
IsEllipticNet.rel W p q 1 0 = 0    for all p q : ℤ,
```

which, using `W 1 = 1`, is exactly the **elliptic addition formula** of Ward (1948),

```
W (p + q) * W (p - q) = W (p + 1) * W (p - 1) * W q ^ 2 - W (q + 1) * W (q - 1) * W p ^ 2 .
```

This is a standing Mathlib `TODO` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, "prove
that `normEDS` satisfies `IsEllipticDvdSequence`"). This file assembles the reusable, sorry-free
**infrastructure** for a proof:

* the **symmetry reductions** of the relator (even in `p`, even in `q`, antisymmetric under the swap
  `p ↔ q`), which reduce the statement to `p ≥ q ≥ 0`;
* the **collapse of the general `r`, `s = 0` relator onto the `r = 1` one**
  (`IsEllipticNet.one_sq_mul_rel_zero`), whence `IsEllipticSequence W ↔ ∀ p q, rel W p q 1 0 = 0`
  for odd normalised `W` — so the `r = 1` slice is not a *slice* of Mathlib's
  `IsEllipticSequence` at all, it is the whole of it, and the step between them is `ring`;
* the trivial `q ∈ {0, 1}` slices; the diagonal bands `p - q ∈ {1, 2}` are already the two-term
  recurrences `normEDS_rel_odd` / `normEDS_rel_even` of
  `EllipticCurves/Torsion/EllipticNetRel.lean`;
* the **universal-ring nonvanishing framework**: the identity sequence `n ↦ n` is `normEDS 2 3 2`
  (`normEDS_two_three_two`), whence `normEDS X₀ X₁ X₂ n ≠ 0` for `n ≠ 0` in the integral domain
  `ℤ[X₀, X₁, X₂]` (`normEDS_univ_ne_zero`). This lets the remaining Ward induction be carried out
  over a *domain* (where nonzero `W`-values may be cancelled) and then transferred to an arbitrary
  `CommRing` via `IsEllipticNet.map_rel` and the evaluation `Xᵢ ↦ b, c, d`.

The remaining `∀ p q` core is carried out in `EllipticCurves.Torsion.WardR1Core`, which imports
this file, and it is **closed**. That file proves the diagonal `p = q` slice **unconditionally**
(`normEDS_rel_one_diag`, `Affine.ψ_rel_one_diag`) together with the full `UnivEDS → R` transfer,
and isolates everything left as the **single** hypothesis `WardGapCore` — for natural `b ≥ 2` and
`a ≥ b + 3`, `rel (normEDS X₀ X₁ X₂) a b 1 0 = 0` over `UnivEDS` — with `normEDS_rel_one_of_gapCore`
and `Affine.ψ_rel_one_of_gapCore` conditional on it; and `EllipticCurves.Torsion.WardHalving`
discharges that hypothesis (`WeierstrassCurve.wardGapCore`) by an elementary strong induction on
`|p| + |q|` whose step halves the index. So `WeierstrassCurve.normEDS_rel_one` and
`WeierstrassCurve.normEDS_isEllipticSequence` hold over an arbitrary `CommRing` with no hypothesis
at all. ⚠️ That closes the elliptic-net half of the Mathlib `TODO` and only that half: the other
conjunct, `IsDvdSequence (normEDS b c d)`, is proved neither in Mathlib nor here. ⚠️ And it does
not contradict the *gap-axis* certificate search recorded in `WardR1Core`, which failed and still
fails — the induction that works is along a different axis.

⚠️ **This paragraph has now gone stale twice, the same way both times.** It first read *"The
remaining `∀ p q` core — the Ward induction over the domain — is left to a follow-up"*: the
follow-up was written, and what went stale was the size it ascribed to the remainder. It then read
*"Ward's `r = 1` slice is still open"*, and the file that closed the slice — downstream, importing
this one — never touched this sentence. Both times a claim about what is left outlived the work
that falsified it, and both times that work was in a file this one cannot see. ⚠️ Every name this
paragraph takes from `EllipticCurves.Torsion.WardR1Core` and `EllipticCurves.Torsion.WardHalving`
— `WardGapCore`, `normEDS_rel_one_diag`, `Affine.ψ_rel_one_diag`, `normEDS_rel_one_of_gapCore`,
`Affine.ψ_rel_one_of_gapCore`, `wardGapCore`, `normEDS_rel_one`, `normEDS_isEllipticSequence` — is
a forward reference: those modules import this file and are not in this file's import closure, so
nothing below uses any of them. Nothing else in the paragraph is: `UnivEDS` is defined below in this
file, and `rel` (Mathlib's `IsEllipticNet.rel`) and `normEDS` are Mathlib's — all three are what the
statements below are about.

## Main statements

* `IsEllipticNet.rel_one_neg_left`, `rel_one_neg_right`, `rel_one_swap` : symmetries of the relator.
* `IsEllipticNet.one_sq_mul_rel_zero` : `W 1 ^ 2 · rel W p q r 0` as a `W(·)²`-combination of three
  `r = 1` relators, for any odd `W`; `IsEllipticNet.isEllipticSequence_of_rel_one` and
  `isEllipticSequence_iff_rel_one` are its consequences.
* `IsEllipticNet.signMultiplesOfThree` : an odd sequence that satisfies the `r = 1` slice
  identically and is not an elliptic sequence — the witness that the normalisation `W 1 = 1`
  cannot be dropped from the two lemmas above.
* `WeierstrassCurve.normEDS_rel_one_zero`, `normEDS_rel_one_one` : the `q ∈ {0, 1}` slices.
* `WeierstrassCurve.normEDS_two_three_two` : `normEDS 2 3 2 n = n`.
* `WeierstrassCurve.normEDS_univ_ne_zero` : nonvanishing of `normEDS` in `ℤ[X₀, X₁, X₂]`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4 (Exercise 3.7).
* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace IsEllipticNet

variable {R : Type*} [CommRing R] (W : ℤ → R)

/-! ### Symmetries of the `r = 1`, `s = 0` relator -/

/-- The relator `rel W p q 1 0` is even in its first argument. -/
lemma rel_one_neg_left (odd : W.Odd) (p q : ℤ) : rel W (-p) q 1 0 = rel W p q 1 0 := by
  simp only [rel, add_zero]
  rw [show -p + q = -(p - q) by ring, show -p - q = -(p + q) by ring,
    show -p + 1 = -(p - 1) by ring, show -p - 1 = -(p + 1) by ring,
    odd (p - q), odd (p + q), odd (p - 1), odd (p + 1), odd p]
  ring

/-- The relator `rel W p q 1 0` is even in its second argument. -/
lemma rel_one_neg_right (odd : W.Odd) (p q : ℤ) : rel W p (-q) 1 0 = rel W p q 1 0 := by
  simp only [rel, add_zero]
  rw [show p + -q = p - q by ring, show p - -q = p + q by ring, show -q + 1 = -(q - 1) by ring,
    show -q - 1 = -(q + 1) by ring, odd (q - 1), odd (q + 1), odd q]
  ring

/-- The relator `rel W p q 1 0` is antisymmetric under swapping its two arguments. -/
lemma rel_one_swap (odd : W.Odd) (p q : ℤ) : rel W q p 1 0 = -rel W p q 1 0 := by
  simp only [rel, add_zero]
  rw [show q + p = p + q by ring, show q - p = -(p - q) by ring, odd (p - q)]
  ring

/-! ### The general `r`, `s = 0` relator is a combination of three `r = 1` relators

⚠️ The `_zero` in the name below is the **fourth** argument `s`, not `r`; `r` is arbitrary. -/

/-- **`W 1 ^ 2 · rel W p q r 0 = W r ^ 2 · rel W p q 1 0 + W p ^ 2 · rel W q r 1 0 +
W q ^ 2 · rel W r p 1 0`**, for every odd `W` over every `CommRing`.

⚠️ This is a **formal identity**, not a fact about elliptic divisibility sequences: no recurrence,
no `W 1 = 1`, no `normEDS` and no curve.  Writing `Aₓ = W (x + 1) · W (x - 1)` and `Bₓ = W x ^ 2`,
**six** of the nine terms of the right-hand side mention `W (x ± 1)`; those six appear in the cyclic
pattern `-Aₐ B_b B_c + A_b Bₐ B_c` and cancel; the three that survive are `W 1 ^ 2` times the
left-hand side.  Oddness is used in exactly one place, to rewrite `W (r - p)` as `-W (p - r)`.

Its content is that `Mathlib`'s `IsEllipticSequence W`, which is `∀ p q r, rel W p q r 0 = 0`,
carries **no information beyond its `r = 1` slice** — see `isEllipticSequence_iff_rel_one`. -/
lemma one_sq_mul_rel_zero (odd : W.Odd) (p q r : ℤ) :
    W 1 ^ 2 * rel W p q r 0 =
      W r ^ 2 * rel W p q 1 0 + W p ^ 2 * rel W q r 1 0 + W q ^ 2 * rel W r p 1 0 := by
  simp only [rel, add_zero]
  rw [show r + p = p + r by ring, show r - p = -(p - r) by ring, odd (p - r)]
  ring

/-- **The `r = 1` slice of the elliptic-net relation implies the whole `s = 0` layer**, for an odd
normalised `W`.  Immediate from `one_sq_mul_rel_zero`, since `W 1 = 1` makes the multiplier `1`. -/
lemma isEllipticSequence_of_rel_one (odd : W.Odd) (h1 : W 1 = 1)
    (h : ∀ p q : ℤ, rel W p q 1 0 = 0) : IsEllipticSequence W := by
  intro p q r
  have hrel := one_sq_mul_rel_zero W odd p q r
  rw [h p q, h q r, h r p, h1] at hrel
  simpa using hrel

/-- **`IsEllipticSequence W ↔ ∀ p q, rel W p q 1 0 = 0`**, for an odd normalised `W`.

The forward direction is `r := 1`; the reverse is `isEllipticSequence_of_rel_one`.  ⚠️ So Ward's
`r = 1` slice and the full `s = 0` elliptic-sequence property are **the same statement**, and the
step between them is a `ring` call rather than an induction.

⚠️ **`h1` cannot be dropped**: `signMultiplesOfThree` below is odd and satisfies the `r = 1` slice
`∀ p q, rel W p q 1 0 = 0` *identically*, yet is not an elliptic sequence
(`not_isEllipticSequence_signMultiplesOfThree`, witnessed at `rel W 3 6 9 0 = -1`).  It has
`W 1 = 0`, so it does not rule out weakening `h1` to *`W 1` is not a zero divisor* — over a domain,
to `W 1 ≠ 0`.  That weakening is available only because `one_sq_mul_rel_zero` is stated
unconditionally in `W 1`, with the factor `W 1 ^ 2` on the left rather than an `h1` hypothesis. -/
lemma isEllipticSequence_iff_rel_one (odd : W.Odd) (h1 : W 1 = 1) :
    IsEllipticSequence W ↔ ∀ p q : ℤ, rel W p q 1 0 = 0 :=
  ⟨fun h p q => h p q 1, isEllipticSequence_of_rel_one W odd h1⟩

/-! ### The normalisation `W 1 = 1` is necessary in `isEllipticSequence_of_rel_one`

Oddness alone does **not** let the `r = 1` slice be propagated to general `r`: the sequence below is
odd, satisfies `rel W p q 1 0 = 0` for *every* pair `p, q` — identically, not on a range — and is
not an elliptic sequence.  So the two lemmas above are stated at the right strength rather than
over-hypothesised.  ⚠️ Nothing here bears on `normEDS`, which is normalised
(`WeierstrassCurve.normEDS_one`), nor on Ward's theorem. -/

section RelOneCounterexample

/-- The sign function restricted to the multiples of `3`: `n ↦ Int.sign n` when `3 ∣ n`, and `0`
otherwise.  This is the witness that `W 1 = 1` cannot be dropped from
`isEllipticSequence_of_rel_one`; see `signMultiplesOfThree_rel_one` and
`not_isEllipticSequence_signMultiplesOfThree`. -/
def signMultiplesOfThree : ℤ → ℤ := fun n => if (3 : ℤ) ∣ n then n.sign else 0

/-- `signMultiplesOfThree` is odd, so it meets the hypothesis `odd` of
`isEllipticSequence_of_rel_one`. -/
lemma signMultiplesOfThree_odd : Function.Odd signMultiplesOfThree := by
  intro n
  simp only [signMultiplesOfThree, Int.sign_neg, dvd_neg]
  split <;> simp

/-- `signMultiplesOfThree 1 = 0`: the witness fails the hypothesis `h1`, and this is the only
hypothesis of `isEllipticSequence_of_rel_one` that it fails. -/
lemma signMultiplesOfThree_one : signMultiplesOfThree 1 = 0 := by
  norm_num [signMultiplesOfThree]

/-- `3 ∣ n + 1` and `3 ∣ n - 1` would give `3 ∣ 2`, so at most one of the two neighbours of `n` is a
multiple of `3` and the product of their values vanishes. -/
lemma signMultiplesOfThree_add_one_mul_sub_one (n : ℤ) :
    signMultiplesOfThree (n + 1) * signMultiplesOfThree (n - 1) = 0 := by
  by_cases h : (3 : ℤ) ∣ n + 1
  · have h' : ¬ (3 : ℤ) ∣ n - 1 := by
      intro h2
      have : (3 : ℤ) ∣ 2 := by simpa using dvd_sub h h2
      omega
    simp [signMultiplesOfThree, h']
  · simp [signMultiplesOfThree, h]

/-- **The whole `r = 1` slice holds for `signMultiplesOfThree`**, for every `p` and `q`:
`signMultiplesOfThree 1 = 0` kills the term `W (p + q) · W (p - q) · W 1 ^ 2`, and
`signMultiplesOfThree_add_one_mul_sub_one` kills the other two. -/
lemma signMultiplesOfThree_rel_one (p q : ℤ) : rel signMultiplesOfThree p q 1 0 = 0 := by
  have hp := signMultiplesOfThree_add_one_mul_sub_one p
  have hq := signMultiplesOfThree_add_one_mul_sub_one q
  simp only [rel, add_zero, signMultiplesOfThree_one]
  linear_combination (norm := ring1)
    (-(signMultiplesOfThree q * signMultiplesOfThree q)) * hp +
      (signMultiplesOfThree p * signMultiplesOfThree p) * hq

/-- **`signMultiplesOfThree` is not an elliptic sequence**, although it is odd and satisfies the
whole `r = 1` slice: `rel signMultiplesOfThree 3 6 9 0 = -1 + 1 - 1 = -1`.  Together with
`signMultiplesOfThree_odd` and `signMultiplesOfThree_rel_one`, this is exactly the statement that
`h1` is not removable from `isEllipticSequence_of_rel_one`. -/
lemma not_isEllipticSequence_signMultiplesOfThree :
    ¬ IsEllipticSequence signMultiplesOfThree := by
  intro h
  have h369 := h 3 6 9
  simp only [rel, signMultiplesOfThree] at h369
  revert h369
  decide

end RelOneCounterexample

end IsEllipticNet

/-! ### Ward's theorem for `normEDS`, the `r = 1` slice -/

namespace WeierstrassCurve

section NormEDS

variable {R : Type*} [CommRing R] (b c d : R)

/-- Oddness of the canonical normalised EDS as a `Function.Odd` fact. -/
lemma normEDS_odd_fun : (normEDS b c d).Odd := fun n => normEDS_neg b c d n

/-- The `q = 0` slice of Ward's `r = 1` relation vanishes: `rel (normEDS b c d) p 0 1 0 = 0`. -/
lemma normEDS_rel_one_zero (p : ℤ) : IsEllipticNet.rel (normEDS b c d) p 0 1 0 = 0 := by
  have h : normEDS b c d (-1) = -1 := by rw [normEDS_neg, normEDS_one]
  simp only [IsEllipticNet.rel, add_zero, sub_zero, zero_add, zero_sub, normEDS_zero, normEDS_one,
    h]
  ring

/-- The `q = 1` slice of Ward's `r = 1` relation vanishes: `rel (normEDS b c d) p 1 1 0 = 0`. -/
lemma normEDS_rel_one_one (p : ℤ) : IsEllipticNet.rel (normEDS b c d) p 1 1 0 = 0 := by
  simp only [IsEllipticNet.rel, add_zero]
  rw [show (1 : ℤ) - 1 = 0 by ring, normEDS_zero]
  ring

end NormEDS

/-! ### The universal ring and nonvanishing -/

section Universal

open MvPolynomial

/-- The identity sequence `n ↦ n` is the normalised EDS with parameters `b = 2`, `c = 3`, `d = 2`:
`normEDS 2 3 2 n = n` over `ℤ`. Both two-term recurrences hold for `W n = n` with these parameters
(as polynomial identities in `m`), and the initial values match. This is the witness used to prove
nonvanishing of `normEDS` in the universal ring. -/
lemma normEDS_two_three_two (n : ℤ) : normEDS (2 : ℤ) 3 2 n = n := by
  have hnat : ∀ m : ℕ, normEDS (2 : ℤ) 3 2 (m : ℤ) = (m : ℤ) := by
    intro m
    induction m using normEDSRec' with
    | zero => simp
    | one => simp
    | two => simp
    | three => simp
    | four => simp
    | even m ih =>
      have i1 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3 - 1) = (m : ℤ) + 3 - 1 := by
        have := ih (m + 2) (by omega)
        rwa [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 3 - 1 by push_cast; ring] at this
      have i2 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3) = (m : ℤ) + 3 := by
        have := ih (m + 3) (by omega)
        rwa [show ((m + 3 : ℕ) : ℤ) = (m : ℤ) + 3 by push_cast; ring] at this
      have i3 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3 + 2) = (m : ℤ) + 3 + 2 := by
        have := ih (m + 5) (by omega)
        rwa [show ((m + 5 : ℕ) : ℤ) = (m : ℤ) + 3 + 2 by push_cast; ring] at this
      have i4 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3 - 2) = (m : ℤ) + 3 - 2 := by
        have := ih (m + 1) (by omega)
        rwa [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 3 - 2 by push_cast; ring] at this
      have i5 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3 + 1) = (m : ℤ) + 3 + 1 := by
        have := ih (m + 4) (by omega)
        rwa [show ((m + 4 : ℕ) : ℤ) = (m : ℤ) + 3 + 1 by push_cast; ring] at this
      have h := normEDS_even (2 : ℤ) 3 2 ((m : ℤ) + 3)
      rw [i1, i2, i3, i4, i5] at h
      rw [show ((2 * (m + 3) : ℕ) : ℤ) = 2 * ((m : ℤ) + 3) by push_cast; ring]
      have h2 : normEDS (2 : ℤ) 3 2 (2 * ((m : ℤ) + 3)) * 2 = 2 * ((m : ℤ) + 3) * 2 := by
        rw [h]; ring
      exact mul_right_cancel₀ two_ne_zero h2
    | odd m ih =>
      have i1 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 2 + 2) = (m : ℤ) + 2 + 2 := by
        have := ih (m + 4) (by omega)
        rwa [show ((m + 4 : ℕ) : ℤ) = (m : ℤ) + 2 + 2 by push_cast; ring] at this
      have i2 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 2) = (m : ℤ) + 2 := by
        have := ih (m + 2) (by omega)
        rwa [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by push_cast; ring] at this
      have i3 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 2 - 1) = (m : ℤ) + 2 - 1 := by
        have := ih (m + 1) (by omega)
        rwa [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 2 - 1 by push_cast; ring] at this
      have i4 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 2 + 1) = (m : ℤ) + 2 + 1 := by
        have := ih (m + 3) (by omega)
        rwa [show ((m + 3 : ℕ) : ℤ) = (m : ℤ) + 2 + 1 by push_cast; ring] at this
      have h := normEDS_odd (2 : ℤ) 3 2 ((m : ℤ) + 2)
      rw [i1, i2, i3, i4] at h
      rw [show ((2 * (m + 2) + 1 : ℕ) : ℤ) = 2 * ((m : ℤ) + 2) + 1 by push_cast; ring, h]; ring
  induction n using Int.negInduction with
  | nat n => exact hnat n
  | neg ih m => rw [normEDS_neg, ih]

/-- The universal coefficient ring for a normalised EDS: `ℤ[X₀, X₁, X₂]`. It is an integral
domain, and `normEDS X₀ X₁ X₂ n` is nonzero for `n ≠ 0` (via the specialisation `Xᵢ ↦ 2, 3, 2`,
which sends `normEDS` to the identity sequence). -/
abbrev UnivEDS : Type := MvPolynomial (Fin 3) ℤ

/-- In the universal ring `ℤ[X₀, X₁, X₂]`, the value `normEDS X₀ X₁ X₂ n` is nonzero whenever
`n ≠ 0`: specialising `X₀ ↦ 2, X₁ ↦ 3, X₂ ↦ 2` maps it to `normEDS 2 3 2 n = n ≠ 0`. -/
lemma normEDS_univ_ne_zero (n : ℤ) (hn : n ≠ 0) :
    normEDS (X 0 : UnivEDS) (X 1) (X 2) n ≠ 0 := by
  intro h
  have hφ := map_normEDS (aeval ![(2 : ℤ), 3, 2] : UnivEDS →ₐ[ℤ] ℤ) (X 0 : UnivEDS) (X 1) (X 2) n
  rw [h, map_zero] at hφ
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hφ
  rw [show (![(2 : ℤ), 3, 2] 2) = 2 from rfl, normEDS_two_three_two] at hφ
  exact hn hφ.symm

end Universal

end WeierstrassCurve
