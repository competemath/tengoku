/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.WeakSplitting.SplitsCompletely
public import Tengoku.Seed.NumberTheory.RamificationInertia.Inertia
public import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Analytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local-factor identity at a prime that splits completely

For a nonzero prime `p` of `R = 𝓞 K` that splits completely in a finite
extension `M / K` (with `S = 𝓞 M`), the finite product of local Euler
factors over the primes of `S` lying above `p` collapses to a power of the
single local factor at `p`. Concretely,
$$
\prod_{Q \mid p}\bigl(1 - N(Q)^{-s}\bigr) =
  \bigl(1 - N(p)^{-s}\bigr)^{[M : K]},
$$
because each `Q` above `p` has residue degree one (so `N(Q) = N(p)`) and
there are exactly `[M : K]` such primes (REF-21b).

This is the single-prime building block (REF-21c1) for the global Euler-
product identity REF-21c2 between the partial Dedekind zeta functions of
`M` and `K`.

## Main results

* `BernoulliRegular.Ideal.SplitsCompletely.absNorm_eq_of_mem`: under
  `SplitsCompletely`, every prime `Q` of `S` above `p` satisfies
  `absNorm Q = absNorm p`.
* `BernoulliRegular.Ideal.SplitsCompletely.prod_localFactor_eq_pow`: the
  finite product `∏ Q above p, (1 - N(Q)^{-s})` equals
  `(1 - N(p)^{-s}) ^ [M : K]`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable (K L : Type*) [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra R L] [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L]
variable [Module.Finite R S] [Module.IsTorsionFree R S]
variable [Module.Free ℤ R] [Module.Free ℤ S]

end Ideal

end BernoulliRegular
