module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Preference.Reasonable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Propositions 7 and 8 in the source's own parameterization

## Statement intent

- **Objects.** The source's composite operations
  `F = {F₁ = f₁ ∘ f₅ ∘ f₃, F₂ = f₂ ∘ f₆ ∘ f₃, F₃ = f₄ ∘ f₂ ∘ f₆ ∘ f₃, F₄ = f₄}`
  of §5.1.2, and a complexity assignment on planner/reward pairs.
- **Assumptions.** The source defines the *`F`-complexity* of a language `L` as
  `max_{(p,R), Fᵢ ∈ F} K_L(Fᵢ(p,R)) − K_L(p,R)`, and calls `L` a
  *`c`-reasonable language for `F`* when that quantity is at most `c`.
  `ReasonableForF` records exactly that, as a single bound indexed by `Fin 4`.
- **Quantifier order.** The constant is fixed by the language, before any pair
  or policy is chosen.
- **Conclusion.** Proposition 7 at distance **`c`**, and Proposition 8 in both
  directions at distance `c`.

## Why this module exists

`AISafetyAtlas.Preference.Reasonable` states the same two propositions under a
*reparameterized* interface: it assumes separate evaluation and construction
bounds mediated by a complexity on policies, and therefore concludes `2 * c`.
That is a valid conditional variation but is not the source's definition.

The difference is structural, not a proof artifact. Each `Fᵢ` maps a pair to a
pair, so a bound on `Fᵢ` never passes through the complexity of a policy. There
is consequently no `KPolicy` field here at all, and the constant does not
double. Both modules are kept: this one for source parity, the other because
`AISafetyAtlas.Preference.Complexity` instantiates its evaluation bound
concretely.

## Difference from the source

The source formalizes "amongst the lowest complexity in `S`" using
`min_{(p',R') ∈ S} K_L(p',R')`, an attained minimum, and its proof begins "pick
`(p, R)` to be the simplest pair compatible with `π̇`". `AmongLowestCompatible`
instead quantifies universally over compatible pairs. That avoids assuming the
minimum is attained and is implied by the source's reading whenever it is, so
the statement here is the more general of the two.

## Explicit non-claims

- **Not** a construction of any `c`-reasonable language, nor a proof that a
  nontrivial one exists. The source argues for existence informally. The only
  inhabitant exhibited in the atlas is degenerate; see the non-claims in
  `AISafetyAtlas.Preference.Reasonable`.
- **Not** the source's Conjecture 9, which is the missing half that would make
  the informal Theorem 2 bite.
- **Not** a claim that the *intended* pair has high complexity.

Survey row: **BY-011**. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Preference.Source

open AISafetyAtlas.Preference

variable {S A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

/-! ## The composite operations -/

/-- `F₁ = f₁ ∘ f₅ ∘ f₃`: evaluate the pair, then build the indifferent pair.-/
@[expose] public def F₁ (x : Pair S A) : Pair S A := op1 (op5 (op3 x))

/-- `F₂ = f₂ ∘ f₆ ∘ f₃`: evaluate the pair, then build the greedy pair.-/
@[expose] public noncomputable def F₂ (x : Pair S A) : Pair S A := op2 (op6 (op3 x))

/-- `F₃ = f₄ ∘ f₂ ∘ f₆ ∘ f₃`: as `F₂`, then negate.-/
@[expose] public noncomputable def F₃ (x : Pair S A) : Pair S A :=
  op4 (op2 (op6 (op3 x)))

/-- `F₄ = f₄`: the anti-rational negation, included so that `F`-complexity is
non-negative, as the source's footnote observes.-/
@[expose] public def F₄ (x : Pair S A) : Pair S A := op4 x

/-- The family `F` as a single indexed operation, so that the source's
`max` over `Fᵢ ∈ F` becomes one uniform bound.-/
@[expose] public noncomputable def Fmap : Fin 4 → Pair S A → Pair S A
  | 0 => F₁
  | 1 => F₂
  | 2 => F₃
  | 3 => F₄

/-! ## `c`-reasonable languages for `F` -/

/--
A complexity assignment on pairs whose `F`-complexity is at most `c`.

This is the source's definition: no policy complexity appears, because every
`Fᵢ` maps a pair to a pair.-/
public structure ReasonableForF (S A : Type*)
    [Fintype A] [Nonempty A] [DecidableEq A] where
  /-- Complexity of a planner/reward pair.-/
  KPair : Pair S A → ℕ
  /-- The bound on the `F`-complexity.-/
  c : ℕ
  /-- The `F`-complexity of the language is at most `c`.-/
  F_complexity_le : ∀ (i : Fin 4) (x : Pair S A), KPair (Fmap i x) ≤ KPair x + c

namespace ReasonableForF

variable (L : ReasonableForF S A)

/-- Compatibility, as in the source: the pair evaluates to the policy.

`AISafetyAtlas.Preference.ReasonableLanguage.Compatible` is this same definition,
character for character and with the same type, in the other language
structure's namespace. `scripts/report_predicate_duplicates.py` surfaced the
pair; the cross-reference is here so neither can be read as the only one.-/
@[expose] public def Compatible (x : Pair S A) (π : Policy S A) : Prop := op3 x = π

/--
`x` is amongst the lowest-complexity pairs compatible with `π`.

Stated without assuming an attained minimum: `x` is compatible, and no
compatible pair beats it by more than `c`.-/
@[expose] public def AmongLowestCompatible (π : Policy S A) (x : Pair S A) : Prop :=
  Compatible x π ∧ ∀ y : Pair S A, Compatible y π → L.KPair x ≤ L.KPair y + L.c

/-! ### The composites send any compatible pair to the degenerate pairs -/

/-! ### Proposition 7, at distance `c` -/

/-! ### Proposition 8, both directions at `c` -/

/-! ### Conjecture 9 and the conditional form of the informal Theorem 2 -/

/--
**Conjecture 9 (informal complexity proposition), as a predicate.**

The source's conjecture is that for a human policy `π` and a *reasonable*
compatible pair `x`, the complexity of `x` "is not close to minimal amongst the
pairs compatible with `π`".

Negating `AmongLowestCompatible` gives exactly that: some compatible pair beats
`x` by more than `c`.

This is a **definition, never an assumption**. Nothing in the atlas asserts it,
and no axiom or structure field carries it. The source itself argues for it
qualitatively and does not prove it. It is stated here only so that the
conditional theorem below can be recorded honestly.-/
@[expose] public def NotAmongLowestCompatible (π : Policy S A) (x : Pair S A) : Prop :=
  Compatible x π ∧ ∃ y : Pair S A, Compatible y π ∧ L.KPair y + L.c < L.KPair x

end ReasonableForF

end AISafetyAtlas.Preference.Source
