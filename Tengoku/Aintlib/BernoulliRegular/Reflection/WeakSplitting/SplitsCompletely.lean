module

public import Tengoku.Seed.NumberTheory.RamificationInertia.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A prime ideal that splits completely in an extension

This file defines `BernoulliRegular.Ideal.SplitsCompletely`, the predicate
that every prime ideal of `S` lying over a fixed prime `p` of `R` is
unramified with trivial residue extension. Concretely, every such prime
has ramification index `1` and inertia degree `1`.

In the number-field setting (`R = 𝓞 K`, `S = 𝓞 M`, `M / K` finite), this is
the standard "`p` splits completely in `M`" property: there are exactly
`[M : K]` primes above `p`, each unramified with residue degree one.

The cardinality consequence
`SplitsCompletely.card_primesOverFinset_eq_finrank` follows immediately from
`Ideal.sum_ramification_inertia` (the fundamental identity
`∑ e_P · f_P = [L : K]`). The converse, packaged as an `Iff`, characterizes
splitting completely purely by the cardinality of the prime fibre.

This is the basic local input for the polar-density / weak-splitting argument
of `BernoulliRegular/Reflection/kummer_reflection.tex`, Section 5.

## Main definitions

* `BernoulliRegular.Ideal.SplitsCompletely`: the predicate
  `∀ P ∈ IsDedekindDomain.primesOverFinset p S,
    ramificationIdx' p P = 1 ∧ inertiaDeg' p P = 1`.

## Main results

* `BernoulliRegular.Ideal.SplitsCompletely.card_primesOverFinset_eq_finrank`:
  if `p` splits completely in `S`, the number of primes of `S` lying over `p`
  equals `[Frac S : Frac R]`.
* `BernoulliRegular.Ideal.splitsCompletely_iff_card_primesOverFinset_eq_finrank`:
  conversely, the cardinality condition characterizes `SplitsCompletely`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Ideal

variable {R : Type*} [CommRing R]

variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable (K L : Type*) [Field K] [Field L]
variable [IsDedekindDomain R]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra R L] [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L]
variable [Module.Finite R S] [Module.IsTorsionFree R S]

end Ideal

end BernoulliRegular
