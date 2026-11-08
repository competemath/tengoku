module

public import Tengoku
public import Tengoku.Seed.Analysis.SpecialFunctions.BinaryEntropy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fano's inequality

Cover & Thomas (2nd ed.) give this in three pieces, and the split is exactly
where the content is. **Theorem 2.10.1** bounds `H(X|X̂)` by
`H(Pe) + Pe·log|𝒳|` for an estimator with `X → Y → X̂`, deliberately *not*
restricting `X̂`'s alphabet. An unnumbered **corollary** (their 2.139) drops the
Markov and functional hypotheses entirely — "let `X̂ = Y` in Fano's inequality" —
but keeps the weaker constant `log|𝒳|`. A second unnumbered **corollary** (their
2.140) recovers the sharp `log(|𝒳| − 1)`, at the price of requiring the estimator
to be a function `X̂ : 𝒴 → 𝒳` landing in `X`'s own alphabet.

Both constants are proved here, from one lemma. `fano_of_log_le` isolates the
only thing either constant depends on — how many values the truth can still take
once the estimate is known to be wrong — and everything else is an instance:

| statement | estimate | constant | printed as |
|---|---|---|---|
| `fano_of_log_le` | arbitrary | any `L` dominating `log \|A.erase (X' ω)\|` | — |
| `fano` | confined to `A` | `log(\|A\| − 1)` | the constant of 2.140 |
| `fano_unrestricted` | arbitrary | `log \|A\|` | 2.10.1, 2.139 |
| `fano_of_embedding` | **in another type**, via an injection | `log \|A\|` | 2.10.1 |

Against the source, on each axis:

| | printed source | this module |
|---|---|---|
| estimate | 2.10.1/2.139 arbitrary at `log \|𝒳\|`; sharp constant only for a *function* `X̂ : 𝒴 → 𝒳` | both, and the sharp case needs no functional and no Markov hypothesis — only that the estimate lands in `A` |
| alphabet | the full ambient `𝒳` | **any** `Finset A` containing `X`, so `A` may be the union of the ranges |

The last row is a real sharpening and not bookkeeping: `log(|A| − 1)` with
`A` the union of the ranges is strictly smaller than `log(|𝒳| − 1)` whenever the
variables do not exhaust the alphabet.

**Why the sharp constant needs an alphabet hypothesis.** The `−1` is exactly the
value `X̂` rules out. If `X̂` takes a value outside `A`, conditioning on the error
event removes nothing and the constant is `log |A|` — which is `fano_unrestricted`,
and is why Cover & Thomas's sharp corollary requires `X̂ : 𝒴 → 𝒳`. The hypothesis
here is theirs in the weakest form that still supports the constant: not that the
estimate is a function into the alphabet, only that it lands in `A`.

## Downstream

`fano_le_log_two_add` and `le_errorProb` carry the constants of the two
weakenings the source records next to the theorem, (2.131) and (2.132). Like
(2.140), both printed statements bound `H(X|Y)` rather than `H(X|X̂)`, so the
declarations that *are* (2.131) and (2.132) are their chained forms in
`AISafetyAtlas.Examples.InformationTheory`. `entropy_le_fano` is the remark about
estimating with no observation at all. The chained readings, which need the
data-processing inequality, are in `AISafetyAtlas.Examples.InformationTheory`.

## The right-hand side

`Mathlib.Analysis.SpecialFunctions.BinaryEntropy` defines

```
qaryEntropy q p = p * log (q - 1 : ℤ) + binEntropy p
```

at natural logarithm, which *is* Fano's bound, and `binEntropy` is used here
directly. The conclusion is nevertheless written out as
`P_e * log (|A| - 1) + binEntropy P_e` rather than as `qaryEntropy |A| P_e`,
because `qaryEntropy`'s body is not exposed outside its own module: neither
`rfl`, `unfold` nor `simp` can see through it, and Mathlib exports no
`qaryEntropy_def`. The two are definitionally equal; only the rewriting is
blocked. Should that definition ever be exposed, the statement can be restated
against it without touching the proof.

## The alphabet hypotheses are pointwise

`hXA : ∀ ω, X ω ∈ A` quantifies over all of `Ω`, including `μ`-null sets, and
the same holds of every alphabet hypothesis below. That is strictly stronger than
the almost-everywhere condition the proofs would tolerate, and it is what a
consumer must discharge. It is not a defect against Cover & Thomas, whose
variables are finitely supported, but the statements should not be read as a.e.
conditions.

## Provenance of the entropy layer

`H[· ; ·]`, `H[· | · ; ·]` and the chain rules are PFR's
(`PFR.ForMathlib.Entropy.Basic`), also at natural logarithm. The atlas's own
`AISafetyAtlas.Inference.entropyOn` is a separate development built for Wolpert's
section 8; it is **not** migrated and nothing here depends on it. A transport
between the two belongs in its own module.
-/

namespace AISafetyAtlas.InformationTheory

open MeasureTheory ProbabilityTheory Real Function

universe uΩ uS uT

variable {Ω : Type uΩ} {S : Type uS}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
variable [Countable S] [DecidableEq S]

/-! ## The error event -/

/-- The error indicator of an estimate: `true` exactly where `X'` misses `X`.-/
@[expose] public def errorIndicator (X X' : Ω → S) : Ω → Bool :=
  fun ω => decide (X ω ≠ X' ω)

/-- The error probability `P_e = μ(X ≠ X')`.-/
@[expose] public noncomputable def errorProb (μ : Measure Ω) (X X' : Ω → S) : ℝ :=
  (μ {ω | X ω ≠ X' ω}).toReal

-- `FiniteRange (errorIndicator X X')` needs no instance here: the indicator is
-- `Bool`-valued and PFR already derives `FiniteRange` from a finite codomain.

omit [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] in
/-- Pairing a value with the error bit it induces is injective in that value:
the first coordinate recovers it. This is what lets the error bit be adjoined to
`X` without changing the conditional entropy.-/
private theorem injective_pairError (y : S) :
    Injective (fun x : S => (x, decide (x ≠ y))) := by
  intro a b hab
  exact congrArg Prod.fst hab

/-! ## Step 1 — adjoining the error bit is free -/

/-! ## Step 2 — splitting off the error bit -/

/-! ## Step 3 — the error bit's entropy is the binary entropy of `P_e` -/

/-! ## Step 4 — averaging a fibrewise bound -/

/-! ## Step 5 — the two fibres of the error bit -/

/-- The conditioner used throughout: the error bit paired with the estimate.-/
@[expose] public def errorPair (X X' : Ω → S) : Ω → Bool × S :=
  fun ω => (errorIndicator X X' ω, X' ω)

/-! ## Step 6 — the `true` half of the pair carries exactly `P_e` -/

/-! ## Fano's inequality -/

/-! ## The estimate in a genuinely different alphabet -/

/-! ## The two weakenings Cover & Thomas record alongside -/

/-! ## Fano with no observation at all -/

end AISafetyAtlas.InformationTheory
