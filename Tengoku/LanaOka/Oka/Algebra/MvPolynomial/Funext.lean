/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Algebra.MvPolynomial.Funext
import Tengoku.Seed.Topology.Separation.Basic
import Tengoku.Seed.Topology.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A multivariate polynomial vanishing on a non-empty open set is zero

Material for `Mathlib/Algebra/MvPolynomial/Funext.lean`; see `README.md` on the mirror tree.

`MvPolynomial.funext_set` there says that two polynomials over an integral domain agreeing on a
**box with infinite sides** are equal. A caller who has a non-empty *open* set instead has to turn
one into the other, and that is three steps: a point of an open set of `σ → R` has a box
neighbourhood inside it (`isOpen_pi_iff`), each side of that box is either a neighbourhood of a
point or the whole of `R` and so is infinite (`infinite_of_mem_nhds`), and then
`MvPolynomial.funext_set` applies. This file is those three steps, once.

## What it does and does not need

**There is no analysis in it and no identity theorem.** The hypotheses are that `R` is an integral
domain carrying a topology in which points are closed and no point is isolated — `T1Space` and
`(𝓝[≠] x).NeBot` at every `x` — and there is no hypothesis on the index type at all. `ℂ` satisfies
both by instances Mathlib already has, and so do `ℝ`, `ℚ` and any non-discrete normed field. **The
statement is an algebraic one with a topological hypothesis**, which is worth saying because the
places in this repository that wanted it describe it as *"a polynomial vanishing on a non-empty
open subset of `ℂ^n` is zero"* and that phrasing invites an appeal to analyticity that is not
needed.

**The index type is not assumed finite, and a first draft assumed it.** The short proof uses
`isOpen_pi_iff'`, the box characterisation for a *finite* index type, and every caller in this
repository indexes by `ULift (Fin n)` — so `[Finite σ]` costs nothing here and was in the first
version of this file with a paragraph claiming the statement fails without it. **That claim is
false and the two extra lines below are the price of not making it**: for an infinite index type
`isOpen_pi_iff` gives a box constraining a *finite* set `I` of coordinates, the sides outside `I`
are the whole of `R`, and those are infinite for the same reason the constrained ones are —
`infinite_of_mem_nhds` at `Set.univ`, which is a neighbourhood of every point. So the general
statement is true, it is what is proved, and the hypothesis is gone.

## Where this would go upstream, decided by measuring both candidates

`Mathlib/Algebra/MvPolynomial/Funext.lean` imports no topology, so this file's mirror path is a
claim that two topology imports may be added there. **The competing destination is
`Mathlib/Topology/Algebra/MvPolynomial.lean`**, which exists, which is where a topological
statement about `MvPolynomial` would look at home, and which is the choice a reader would expect
this file to have made. It is the more expensive one, and the two figures are the reason for the
path above rather than a preference:

* at `Mathlib/Algebra/MvPolynomial/Funext.lean`, whose closure is 1173 Mathlib modules, the two
  topology imports cost **45**;
* at `Mathlib/Topology/Algebra/MvPolynomial.lean`, whose closure is 1154, the algebra import —
  `Mathlib.Algebra.MvPolynomial.Funext`, which is the whole engine of the proof — costs **130**.

Both measured with `scripts/import_cost.py` in this checkout, the file written out at each path in
turn. **Split by destination and not by subject** is `README.md`'s rule and the cheaper
destination wins; a Mathlib reviewer who disagrees is disagreeing with 45 against 130 and not with
a preference.

## Main results

- `MvPolynomial.eq_zero_of_eval_eq_zero_of_isOpen`: **a polynomial vanishing at every point of a
  non-empty open subset of `σ → R` is zero**, for any index type and an integral domain that is a
  `T1Space` with no isolated point.
-/

open Filter Topology

namespace MvPolynomial

/-- **A multivariate polynomial vanishing on a non-empty open set is zero.**

The open set is given by a point `x₀` in it rather than by a non-emptiness hypothesis, because
every caller has the point: it is the image of a point of the space whose emptiness is being ruled
out.

`isOpen_pi_iff` produces a box neighbourhood of `x₀` inside `U`, constraining a finite set `I` of
coordinates; the box handed to `MvPolynomial.funext_set` is that one outside `I` widened to the
whole of `R`, so that it is indexed by all of `σ` as `funext_set` requires. Each side is infinite
by `infinite_of_mem_nhds` — at `u i` for `i ∈ I` and at `Set.univ` otherwise — which is where
`T1Space` and the punctured-neighbourhood hypothesis are spent, and the second case is why no
finiteness of `σ` is needed. The last `simpa` is `map_zero` on the right-hand side of
`funext_set`, which is stated as an equality of two evaluations. -/
theorem eq_zero_of_eval_eq_zero_of_isOpen {σ : Type*} {R : Type*} [CommRing R]
    [IsDomain R] [TopologicalSpace R] [T1Space R] [∀ x : R, (𝓝[≠] x).NeBot]
    {p : MvPolynomial σ R} {U : Set (σ → R)} (hU : IsOpen U) {x₀ : σ → R} (hx₀ : x₀ ∈ U)
    (h : ∀ x ∈ U, eval x p = 0) : p = 0 := by
  classical
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hU x₀ hx₀
  refine funext_set (fun i ↦ if i ∈ I then u i else Set.univ) (fun i ↦ ?_) (fun x hx ↦ ?_)
  · by_cases hi : i ∈ I
    · simpa [hi] using infinite_of_mem_nhds (x₀ i) ((hu i hi).1.mem_nhds (hu i hi).2)
    · simpa [hi] using infinite_of_mem_nhds (x₀ i) (univ_mem (α := R))
  · have hxU : x ∈ U := hsub fun i hi ↦ by
      simpa [Finset.mem_coe.1 hi] using hx i (Set.mem_univ i)
    simpa using h x hxU

end MvPolynomial
