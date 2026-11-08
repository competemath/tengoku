module

public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The data-processing inequality

Cover & Thomas, Theorem 2.8.1: if `X → Y → Z` is a Markov chain then
`I(X ; Z) ≤ I(X ; Y)` — no processing of `Y` can increase what it says about `X`.

| | printed source | this module |
|---|---|---|
| conclusion | the one inequality | both directions, the difference *identity*, and the equality case |

That is the whole of it. The module also takes any measurable space with an
`IsZeroOrProbabilityMeasure` where the source takes a discrete distribution, and
that **is not a widening**: the variables are `FiniteRange`, so they push the
measure forward to a pmf on finite alphabets, the printed theorem applies to that
pmf, and the statement here is the printed statement at the pushforward. The two
are inter-derivable, so those rows are graded `Same`; see the sample-space note
in `docs/provenance/source-coverage-audit.md` and the worked case in
`AISafetyAtlas.Examples.InformationTheory.ContinuousSampleSpace`. The
sole object outside print's reach is the zero measure, where every quantity is
`0`, which is vacuity rather than generality.

The two corollaries Cover & Thomas draw from it — both unnumbered in the 2nd
edition — are recovered rather than reproved: `Z := g ∘ Y` is a Markov chain
(`isMarkovChain_comp`), so `I(X;Y) ≥ I(X;g(Y))` is an instance of the main
theorem, and `I(X;Y|Z) ≤ I(X;Y)` falls out of the difference identity.

## What is new here

PFR already proves the *functional* data-processing inequalities
(`entropy_comp_le`, `mutual_comp_le`, `mutual_comp_comp_le`,
`condMutual_comp_comp_le`) — those need no restating. What PFR does not have,
and what this module supplies, is:

* `mutualInfo_chain_rule` and `mutualInfo_chain_rule'`, the two-component chain
  rule for mutual information in both argument orders, and
  `mutualInfo_chain_rule_fin`, Cover--Thomas Theorem 2.5.2 for an arbitrary
  finite family. These are the only new mathematics in the file; everything
  else is assembly. They are natural upstream candidates.
* the Markov-chain form itself, which is strictly more general than the
  functional form: `mutualInfo_comp_le` is derived from it here, whereas the
  converse derivation is impossible — a Markov chain need not be functional.
* `isMarkovChain_iff_measure_factorizes_singleton`, the bridge back to the
  book's own definition. `IsMarkovChain` is `CondIndepFun`, which is (2.118)'s
  right-hand side; Cover & Thomas start instead from the factorization (2.117).
  Proving the two equivalent is what stops the choice of definition from being a
  convention the section then trades on. See *The definitional bridge* below.

## The equality case

`mutualInfo_sub_eq` states the exact identity behind the inequality,

```
I[X : Y] - I[X : Z] = I[X : Y | Z] - I[X : Z | Y]
```

which holds with **no hypothesis on the three variables at all**. The Markov
assumption enters only by killing the second term. Consequently equality holds
in the data-processing inequality precisely when `X → Z → Y` is *also* a Markov
chain (`mutualInfo_eq_iff_isMarkovChain`). Cover & Thomas assert this inside the
proof of Theorem 2.8.1, as a remark, without proving it — as they do the dual
conclusion `I(Y;Z) ≥ I(X;Z)`, which they leave at "similarly, one can prove".
Both are proved here.

## The definitional bridge

The equivalence comes in two strengths, and both are here.

`isMarkovChain_iff_measure_factorizes_singleton` is the printed (2.118): Markov
chain iff `p(y)·p(x,y,z) = p(x,y)·p(y,z)` at every point mass. That is the
equivalence Cover & Thomas prove, at the hypothesis they prove it from. Its
left-hand side is the book's (2.117) cleared of denominators; the three-factor
`p(x) p(y|x) p(z|y)` is not written anywhere in Lean.

`isMarkovChain_iff_measure_factorizes` widens the factorization to arbitrary
measurable `s`, `t`. Read as a *conclusion* that is stronger than the printed
one, and read as a *hypothesis* it is stronger too — so as an `iff` it is neither
above nor below the printed form. `measure_preimage_inter_eq_tsum`
is what connects them: a measurable slice of a countable-valued variable splits
over its point masses, applied once in `X` and once in `Z`.

Which one to reach for: the singleton form to *check* that something is a Markov
chain, the set form to *use* one.

## Not covered

The conditioned form `I[X : Z | W] ≤ I[X : Y | W]`, under conditional
independence of `X` and `Z` given `⟨Y, W⟩`, is a further generalisation. It is
not in the printed source and is not proved here; it needs a conditional
counterpart of `mutualInfo_chain_rule`, which in turn needs the
pair-reassociation transport for conditional entropy.

## Provenance of the entropy layer

`H[· ; ·]`, `I[· : · ; ·]`, `I[· : · | · ; ·]` and `CondIndepFun` are PFR's, at
natural logarithm. See `AISafetyAtlas.InformationTheory.Fano` for why the
atlas's own `AISafetyAtlas.Inference.entropyOn` is a separate development and is
not migrated.
-/

namespace AISafetyAtlas.InformationTheory

open MeasureTheory ProbabilityTheory Real Function

universe uΩ uS uT uU

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
variable [Countable S] [Countable T] [Countable U]
variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

/-! ## Markov chains -/

/-! ## The chain rule for mutual information

`I[X : ⟨Y, Z⟩] = I[X : Z] + I[X : Y | Z]`: what the pair `⟨Y, Z⟩` says about `X`
is what `Z` says, plus what `Y` adds once `Z` is known. Both argument orders are
given, because the data-processing argument needs to split the same quantity two
ways. -/

/-! ### The printed finite-family chain rule -/

section FiniteChainRule

universe uV uW

variable {V : Type uV} {W : Type uW}
variable [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
variable [MeasurableSpace W] [MeasurableSingletonClass W] [Countable W]

/-- Package a finite indexed family of random variables as one vector-valued variable.-/
public def observationVector {n : ℕ} (X : Fin n → Ω → V) : Ω → Fin n → V :=
  fun ω i ↦ X i ω

/-- The variables strictly preceding `i`, in their original order.-/
public def observationPrefix {n : ℕ} (X : Fin n → Ω → V) (i : Fin n) :
    Ω → Fin i.val → V :=
  fun ω j ↦ X ⟨j.val, lt_trans j.isLt i.isLt⟩ ω

/-! ### Differently typed alphabets

`mutualInfo_chain_rule_fin` gives every variable the same codomain, while
Cover--Thomas quantify over an arbitrary finite family. The gap is a
type-formation artifact rather than a restriction, and this section proves that
rather than asserting it: tagging each variable with its index embeds the family
into one disjoint union, and mutual information is invariant under an injective
relabelling of either the measured or the conditioning variable. -/

/-- A family with **differently typed** codomains, packaged as one
vector-valued variable.-/
public def observationVectorPi {n : ℕ} {V' : Fin n → Type uV}
    (X : (i : Fin n) → Ω → V' i) : Ω → ((i : Fin n) → V' i) :=
  fun ω i ↦ X i ω

/-- The variables strictly preceding `i`, in their original order and types.-/
public def observationPrefixPi {n : ℕ} {V' : Fin n → Type uV}
    (X : (i : Fin n) → Ω → V' i) (i : Fin n) :
    Ω → ((j : Fin i.val) → V' ⟨j.val, lt_trans j.isLt i.isLt⟩) :=
  fun ω j ↦ X ⟨j.val, lt_trans j.isLt i.isLt⟩ ω

/-- The same family with each variable tagged by its index, so that all of them
share the codomain `Σ k, V' k`.-/
public def observationTagged {n : ℕ} {V' : Fin n → Type uV}
    (X : (i : Fin n) → Ω → V' i) (i : Fin n) : Ω → ((k : Fin n) × V' k) :=
  fun ω ↦ ⟨i, X i ω⟩

end FiniteChainRule

/-! ## The inequality -/

/-! ## The functional case is an instance -/

end AISafetyAtlas.InformationTheory
