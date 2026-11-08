module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Learning
public import Tengoku.Seed.Logic.Equiv.Fintype
public import Tengoku.Seed.Data.Sym.Card
public import Tengoku.Seed.Data.Fintype.Powerset
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Combinatorics.PermInvariance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sharp No Free Lunch: closed under permutation, both directions

`AISafetyAtlas.Learning` proves No Free Lunch for the **uniform** average over
all objectives. That is one point of a much larger picture, and the picture has
an exact boundary: NFL holds for a weighting of the objectives **if and only if**
that weighting is invariant under permutations of the search domain.

This is `CT-10`. Sources:

* D. Schumacher, M. D. Vose, L. D. Whitley, *The No Free Lunch and Problem
  Description Length*, GECCO 2001 — the first closed-under-permutation
  characterization, stated for a **set** of objectives.
* C. Igel, M. Toussaint, *A No-Free-Lunch Theorem for Non-Uniform Distributions
  of Target Functions*, J. Math. Modelling and Algorithms 3(4), 2004,
  doi `10.1023/B:JMMA.0000049381.24625.f7` — both directions, for a
  **distribution**.

## Why this is the general statement

The uniform cores already in `AISafetyAtlas.Learning` are the special case of a
constant weight, which is permutation-invariant for trivial reasons; that
derivation is `no_free_lunch_embedding_of_sharp`. The set form of
Schumacher–Vose–Whitley is the case of an indicator weight
(`permInvariant_of_closedUnderPermutation`).

The condition is also what makes NFL *vacuous* in practice: real priors over
learning problems are structured, hence not permutation-symmetric, hence outside
the hypothesis. Knowing the exact boundary is what lets a consumer say so.

## Where this is stronger than the printed sources

| | printed | this module |
|---|---|---|
| weight | a probability distribution over objectives | **any** real-valued weight — no nonnegativity, no normalization |
| the necessary direction | assumes NFL for all algorithms, all lengths, all measures | assumes it only for **schedules**, at the single length `m = \|X\|`, and only at **indicator** measures |

Splitting the two directions this way is the substantive gain: the hypothesis of
`permInvariant_of_nfl` is much weaker than the conclusion of
`nfl_adaptive_of_permInvariant`, so the `iff` in `nfl_adaptive_iff_permInvariant`
is not the sharpest form of either half. Dropping nonnegativity and normalization
matters because it makes the result applicable to signed weightings —
differences of two priors, for instance — for which "distribution" is the wrong
word and the printed statements do not apply.

**Not a widening: the sample length.** NFL at every sample length `m` is *not* a
gain over print, though it can look like one. Igel–Toussaint's
Theorem 5 already concludes "for any two algorithms `a` and `b`, any value
`k ∈ ℝ`, any `m ∈ {1, …, |X|}`, and any performance measure `c`" — every sample
length and every cost measure are in the printed statement. The sufficient
direction here matches print on that axis; it does not exceed it.

## The algorithm class

Both sources quantify over **non-repeating black-box** algorithms, which choose
each query from the costs already seen. That is `AdaptiveRule` together with the
no-revisit hypothesis `∀ c, Injective (ruleVisit r c)`, and
`nfl_adaptive_of_permInvariant` is the sufficient direction over exactly that
class. `nfl_of_permInvariant` is the fixed-schedule special case, kept because
it is the form the rest of the atlas consumes.

The bridge is `scheduleRule`, which reads a schedule as a rule ignoring its
history. It also carries the necessary direction upward for free: a probe built
from schedules is already a probe built from rules.

## Explicit non-claims

No time-varying objectives: the objective is fixed for the run. **Stochastic
algorithms are covered** — see `mixtureTrace` and `stochasticTrace` below, which
are Droste–Jansen–Wegener's own two pictures of a randomized search heuristic —
so this is no longer a non-claim, and what is left on that axis belongs to
Wolpert–Macready rather than to Igel–Toussaint or SVW. The characterization is of
the **prior** axis — what is proved about the algorithm class is that it does not
matter, not that every algorithm is covered. The loss-axis `iff`
(`homogeneous_iff_learner_indep`) is a separate, folklore result and is
untouched.

**The bridge from Theorem 4 to "this family is not closed under permutation" is
not proved here.** Theorem 4 says a non-trivial neighbourhood relation is not
permutation-invariant. It does *not* follow that a search space carrying such a
relation has no permutation-closed prior, and unqualified that is **false** —
`PermInvariant` is a predicate on `ObjectiveWeight X Y`, a neighbourhood
relation is a relation on `X`, and the uniform weight is permutation-invariant
whatever structure `X` carries. Print supplies the missing step separately, in
its Examples 2 and 3, and neither is formalized. See the non-claim beside
`exists_perm_rel_not_iff` for the detail.

**The double-exponential asymptotic of Theorem 3 is not proved.** The counts and
the printed fraction are; the claim that the fraction vanishes double
exponentially is an estimate on binomial coefficients and is graded `No`.
-/

open Classical
open Fintype Function
open AISafetyAtlas.Combinatorics

namespace AISafetyAtlas.Learning

universe uX uY

variable {X : Type uX} {Y : Type uY}

/-! ## Weighted aggregate performance -/

/--
A weighting of the objectives. Deliberately **not** required to be nonnegative
or to sum to one: every result below holds for an arbitrary real weight, and the
probability-distribution case of the printed sources is the special case.-/
public abbrev ObjectiveWeight (X Y : Type*) := (X → Y) → ℝ

/--
Aggregate performance of a schedule under a weighting of the objectives.
`AISafetyAtlas.Learning.aggregatePerformance` is the constant-weight case.-/
@[expose] public noncomputable def weightedPerformance [Fintype X] [Fintype Y] {m : ℕ}
    (P : ObjectiveWeight X Y) (Φ : CostPerformance m Y) (σ : Fin m ↪ X) : ℝ :=
  ∑ f : X → Y, P f * Φ (fun i => f (σ i))

/--
Aggregate performance of an **adaptive rule** under a weighting of the
objectives: the weighted total, over all objectives, of a functional of the cost
sequence the rule observes.

The schedule form `weightedPerformance` is the special case
`weightedTrace P Φ (scheduleRule σ)` — see `weightedPerformance_eq_adaptive`.-/
@[expose] public noncomputable def weightedTrace [Fintype X] [Fintype Y] {m : ℕ}
    (P : ObjectiveWeight X Y) (Ψ : (Fin m → Y) → ℝ) (r : AdaptiveRule X Y m) : ℝ :=
  ∑ f : X → Y, P f * Ψ (observed r f)

/--
**Closed under permutation.** Relabelling the search domain does not change the
weight an objective receives. For an indicator weight this is exactly
Schumacher–Vose–Whitley's condition on a *set*; for a distribution it is
Igel–Toussaint's.-/
@[expose] public def PermInvariant (P : ObjectiveWeight X Y) : Prop :=
  ∀ (π : Equiv.Perm X) (f : X → Y), P (f ∘ π) = P f

/-! ## Any two schedules of the same length differ by a permutation -/

/-! ## Permutation invariance is sufficient -/

/-! ## Permutation invariance is sufficient for adaptive algorithms too

Both printed sources quantify over *non-repeating black-box* algorithms, which
choose each query from the costs already seen. `nfl_of_permInvariant` above
covers only fixed schedules, so on its own it is narrower than print. This
section removes that restriction, using the adaptive model of
`AISafetyAtlas.Learning`. -/

/-! ### Permuting the algorithm, and permuting the objective

Schumacher–Vose–Whitley's duality: relabelling the search domain can be charged
either to the algorithm or to the objective, and the trace is the same. This is
the structural fact their characterization rests on, so it is proved here rather
than absorbed into the NFL argument. -/

/-- Relabel an adaptive rule by a permutation of the search domain: wherever the
rule would query `x`, the relabelled rule queries `π x`.-/
@[expose] public def permRule {m : ℕ} (π : Equiv.Perm X) (r : AdaptiveRule X Y m) :
    AdaptiveRule X Y m :=
  fun k h => π (r k h)

/-! ## Fixed schedules are adaptive rules

The adaptive class contains the non-adaptive one, so the necessary direction
transfers without being reproved: a probe built from schedules is already a probe
built from rules. -/

/-- A fixed schedule read as an adaptive rule — one that ignores the costs it has
seen.-/
@[expose] public def scheduleRule {m : ℕ} (σ : Fin m ↪ X) : AdaptiveRule X Y m :=
  fun k _ => σ k

/-- What a schedule rule observes is the schedule's cost sequence.-/
public theorem observed_scheduleRule {m : ℕ} (σ : Fin m ↪ X) (f : X → Y) :
    observed (scheduleRule σ) f = fun k => f (σ k) :=
  observed_of_consistent _ f _ fun _ => rfl

/-- Weighted performance of a schedule, read through the adaptive machinery.-/
public theorem weightedPerformance_eq_adaptive [Fintype X] [Fintype Y] {m : ℕ}
    (P : ObjectiveWeight X Y) (Φ : CostPerformance m Y) (σ : Fin m ↪ X) :
    weightedPerformance P Φ σ = weightedTrace P Φ (scheduleRule σ) := by
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [observed_scheduleRule]

/-! ## Stochastic rules

Igel–Toussaint state Theorem 1 for *"any two (deterministic or stochastic,
cf. [1]) algorithms"*, citing Droste–Jansen–Wegener on randomized search
heuristics. `AdaptiveRule` is deterministic, so everything above quantifies over
a subclass of what the source does. This section removes that restriction.

**The modelling choice matters, and it is the point of the section.** A
stochastic rule is *not* modelled as an abstract weighted family of deterministic
rules. That would prove only that No Free Lunch is preserved under mixtures, and
would leave exactly the residual it is meant to close: nothing would say the
source's algorithms *are* such mixtures. Instead the randomness is where a
randomized heuristic actually puts it — the rule reads a **choice** at each step,
alongside the costs it has seen — and fixing the choice sequence yields a
deterministic rule **definitionally**, by `induced`. No representation theorem is
needed because there is nothing to represent.

An arbitrary weight on choice *sequences* is deliberate: it allows the steps'
choices to be correlated, so independent per-step randomization is a special
case, and so is the abstract mixture picture, by taking `C` to index rules.

**That residual is closed, at the primary source.** `C` is a `Fintype`, so this
covers finite choice sets only — and Droste–Jansen–Wegener's text makes that
print's own setting rather than an atlas restriction. At p. 134: *"The number of
different deterministic search strategies is finite. Let m be its number. A
randomized search strategy is a probability distribution p = (p₁, …, p_m) and
chooses the ith deterministic strategy with probability p_i."* `mixtureTrace`
below is that definition, and `surjective_induced_playChoice` records that the
choice-sequence form here reaches all of it.
-/

/--
A **stochastic** adaptive query rule: given the costs observed so far *and* a
choice drawn at this step, pick the next query point.

The deterministic `AdaptiveRule X Y m` is the case where `C` is a subsingleton.-/
public abbrev StochasticRule (X Y C : Type*) (m : ℕ) : Type _ :=
  ∀ k : Fin m, (Fin k → Y) → C → X

/--
The deterministic rule obtained by fixing the whole choice sequence in advance.

This is a definition, not a theorem: a stochastic rule with its randomness
resolved *is* a deterministic rule, with no factorization argument in between.-/
@[expose] public def induced {C : Type*} {m : ℕ}
    (r : StochasticRule X Y C m) (c : Fin m → C) : AdaptiveRule X Y m :=
  fun k hist => r k hist (c k)

/--
Aggregate performance of a stochastic rule: the weighted total, over choice
sequences, of the deterministic performance each sequence induces.

The weight is an arbitrary real, as everywhere in this file; a probability
distribution over the choices is the special case, and is what the sources take.-/
@[expose] public noncomputable def stochasticTrace [Fintype X] [Fintype Y]
    {C : Type*} [Fintype C] {m : ℕ}
    (P : ObjectiveWeight X Y) (Ψ : (Fin m → Y) → ℝ)
    (w : (Fin m → C) → ℝ) (r : StochasticRule X Y C m) : ℝ :=
  ∑ c : Fin m → C, w c * weightedTrace P Ψ (induced r c)

/-! ### The source's own definition: a distribution over deterministic behaviours

Igel's survey of these theorems states, citing Droste–Jansen–Wegener, that *"a
randomized search algorithm `a` can be described by a probability distribution
`p_a` over deterministic search behaviors"*, and writes the performance as

`E{c(Y(f,m,a))} = ∑_{a' ∈ A} p_a(a') · c(Y(f,m,a'))`,

where *"the set `A` contain[s] all deterministic search behaviors"*. So the
mixture picture is not a proxy for the source's randomized algorithms — it **is**
the source's definition of them, and `mixtureTrace` is that equation.

The same passage names the other view: *"drawing all realizations of random
variables required by a randomized search method **at once prior to the search
process** and to use these events as inputs to a deterministic algorithm"*, which
is `stochasticTrace`. So the section above and this one are the source's own two
descriptions of the same object, and `surjective_induced_playChoice` records that
the choice-sequence form reaches every behaviour the mixture form ranges over.

Both are finite objects here: `A` is a `Fintype` because `X` and `Y` are, so
nothing in this section restricts the randomness available. -/

/--
**Igel's equation (8).** The performance of a randomized algorithm as the
expectation, over all deterministic search behaviours, of their performance
weighted by the algorithm's own distribution.

The weight is an arbitrary real, as everywhere in this file; a probability
distribution over `A` is the case the source states.-/
@[expose] public noncomputable def mixtureTrace [Fintype X] [Fintype Y]
    [DecidableEq Y] {m : ℕ}
    (P : ObjectiveWeight X Y) (Ψ : (Fin m → Y) → ℝ)
    (p : AdaptiveRule X Y m → ℝ) : ℝ :=
  ∑ a : AdaptiveRule X Y m, p a * weightedTrace P Ψ a

/--
The stochastic rule that simply plays the behaviour it is handed: with the choice
alphabet taken to be the deterministic behaviours themselves, drawing a choice
*is* drawing an algorithm.-/
@[expose] public def playChoice {m : ℕ} :
    StochasticRule X Y (AdaptiveRule X Y m) m :=
  fun k hist a => a k hist

/-! ### Schumacher–Vose–Whitley's equivalent formulations

Their NFL1–NFL4 are four readings of the same fact. NFL1 (equal performance under
any overall measure) is `no_free_lunch_adaptive_of_sharp`; NFL4 is the weighted
form the source declines and `nfl_adaptive_iff_permInvariant` supplies. The other
two are one lemma each, and are here so the group is not left uncovered. -/

/-! ## Permutation invariance is necessary -/

/-! ## The printed special cases

Both earlier formulations are instances of the weighted statement, recovered by
choosing the weight. Neither is reproved. -/

/-! ## How many objective sets satisfy the condition

The `iff` above says NFL holds exactly on the permutation-closed sets. Igel and
Toussaint's Theorem 3 asks how many of those there are, and answers that almost
none of them are: the count is `2 ^ C(|X| + |Y| − 1, |X|) − 1`, against
`2 ^ (|Y| ^ |X|) − 1` subsets in all.

The argument is short once Lemma 1 is in hand. A permutation-closed set is a
union of orbits, an orbit is a basis class, and a basis class is fixed by the
multiset of cost values an objective takes — so the orbits are exactly the
multisets of size `|X|` drawn from `Y`, of which there are `C(|X| + |Y| − 1,
|X|)`, and a permutation-closed set is any set of them.

`spectrum` is that multiset, as an element of Mathlib's `Sym`, which is what
turns the counting into `Sym.card_sym_eq_choose`.
-/

/-! ## Neighbourhood structure breaks the symmetry

Theorem 3 says permutation-closed priors are rare by count. Theorem 4 is the
first step of print's argument that the structures search actually uses are
never among them — **only the first step**, and the rest is not formalized here;
see the non-claim at the end of this section.

Igel–Toussaint's *neighbourhood relation* on the search space is a **symmetric**
`n : X × X → {0,1}`, non-trivial when some pair of distinct points neighbours
and some pair does not, and their theorem is that no such relation survives
every relabelling of the space.

Nothing about that is specific to search — or, as it turns out, to symmetry.
The content is a fact about the action of `Equiv.Perm X` on binary relations:
**a relation invariant under every permutation of `X` is constant off the
diagonal, and constant on it.** No such relation distinguishes any point from
any other, so "invariant under every relabelling" is not a condition a relation
can meet while carrying structure.

**Explicit non-claim: the bridge to No Free Lunch is not proved here.** It is
tempting to write that a space with a non-trivial neighbourhood structure
therefore has no permutation-closed prior, so that
`nfl_adaptive_iff_permInvariant` never applies to it. That does not follow, and
unqualified it is **false**: `PermInvariant` is a predicate on
`ObjectiveWeight X Y`, a neighbourhood relation is a relation on `X`, and the
uniform weight is permutation-invariant no matter what structure `X` carries.

Getting from Theorem 4 to *"`F` is not closed under permutation"* takes a
further argument about a family whose membership condition reads the relation,
and print supplies it separately in its Examples 2 and 3 — steepness, and a
bound on the number of local minima. Example 2's argument is not a corollary of
Theorem 4: it turns on *"for every f ∈ F there exists a permutation that maps a
global minimum and a global maximum of f to neighboring points"*, which is a
claim about where permutations can send extrema. **Neither example is
formalized**, and both are graded `No` in the coverage audit.
-/

end AISafetyAtlas.Learning
