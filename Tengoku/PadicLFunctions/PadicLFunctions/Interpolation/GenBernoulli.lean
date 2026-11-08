/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.FieldTheory.KummerExtension
import Tengoku.Seed.NumberTheory.BernoulliPolynomials
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots
import Tengoku.Seed.NumberTheory.DirichletCharacter.Basic
import Tengoku.Seed.RingTheory.PowerSeries.WellKnown
import Tengoku.PadicLFunctions.PadicLFunctions.KubotaLeopoldt.ZetaValues

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Generalised Bernoulli numbers (the L-values of RJW §5)

RJW route the special values `L(χ, −k)` through the complex Mellin theory
(Lem 5.5/5.9 via `thm:l-function`, §2). As in §4 (where `ζ(1−k)` was the
rational `zetaNeg` and the complex comparison was quarantined), the `p`-adic
statements use the *generalised Bernoulli numbers* `B_{k,χ}` as the canonical
value, following the cross-reference Washington, *Introduction to Cyclotomic
Fields* §4.1–4.2 ("B_{n,χ}" and Thm 4.2: `L(1−n, χ) = −B_{n,χ}/n`); the
complex bridge is `GenBernoulliComplex.lean`.

`B_{k,χ} := N^{k−1} ∑_{a=1}^{N} χ(a)·B_k(a/N)` for `χ` mod `N` (Washington
Prop 4.1's polynomial form; the `a`-range `1..N` matters — it makes the
trivial-character case reduce to `B_k(1) = bernoulli' k`).
-/

open Finset

namespace PadicLFunctions

variable {L : Type*} [Field L] [CharZero L] {N : ℕ} [NeZero N]

/-- L5.1.9: the generalised Bernoulli number `B_{k,χ} ∈ L` of a Dirichlet
character `χ` mod `N` valued in a characteristic-zero field:
`B_{k,χ} = N^{k−1} ∑_{a=1}^{N} χ(a)·B_k(a/N)`
(Bernoulli-polynomial form; Washington §4.1, Prop 4.1).-/
noncomputable def _root_.DirichletCharacter.genBernoulli
    (χ : DirichletCharacter L N) (k : ℕ) : L :=
  (N : L) ^ ((k : ℤ) - 1) *
    ∑ a ∈ range N, χ (a + 1 : ℕ) *
      Polynomial.eval (((a : L) + 1) / (N : L)) ((Polynomial.bernoulli k).map (algebraMap ℚ L))

/-- The L-value `L(χ, −k)` in its `p`-adic incarnation:
`LvalNeg χ k = −B_{k+1,χ}/(k+1)` (Washington Thm 4.2).-/
noncomputable def LvalNeg (χ : DirichletCharacter L N) (k : ℕ) : L :=
  -(χ.genBernoulli (k + 1)) / (k + 1)

section generatingFunction

open PowerSeries

end generatingFunction

end PadicLFunctions
