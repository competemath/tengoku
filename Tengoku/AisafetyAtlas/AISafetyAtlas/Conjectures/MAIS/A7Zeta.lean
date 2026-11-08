module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS.O7Proof
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS.O77Chart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `A7-ZETA-BRIDGE` — MAIS-A7's own definition of the local pair

`MAIS-A7.tex` `def:llc` does not define `(λ, m)` by a volume asymptotic. It
defines them by the zeta integral

    Z(z; w*, δ) = ∫_{B_δ(w*)} |L(w) − L(w*)|^z dw,

which resolution of singularities continues meromorphically to `ℂ`; `−λ` is its
largest pole and `m` that pole's order. The band-volume statement

    vol{w ∈ B_δ(w*) : |L(w) − L(w*)| < ε} ≍ ε^λ (log 1/ε)^(m−1)

appears immediately afterwards, introduced with the words *"In words:"* — a
gloss on the definition, outside the definition environment.

Every MAIS-O7 and MAIS-O77 theorem in this repository is about the gloss. The
substitution between the two was recorded in ledger prose and nowhere else,
while the identical substitution for `MAIS-A6`'s `def:local` was carried as
`O70-ZETA-BRIDGE`: a frozen proposition with consumers, stress artifacts and a
printed debt. This module removes that asymmetry. The gap is the same size it
was; it is now a hypothesis a reader can see in a binder rather than a sentence
they have to find.

## Why this is not `O70-ZETA-BRIDGE`

Neither half of that frontier reaches A7, and the second reason is the sharper.

*The germ is wrong.* `O70ZetaPoleBridge` speaks of `rrrLossCoords M N H C`
itself, because MAIS-O70's points are exact factorizations, where the loss
vanishes and the centred band germ **is** the loss. A7 quantifies over an
arbitrary point of the loss, and the object print integrates there is the
centred band `|L − L(w*)|`. Where `L(w*) ≠ 0` — which is every nonterminal
rung, `MAIS-O77(b)`'s whole subject — the centring is not removable, and
nothing about the loss alone says anything about that germ.

The two clauses this module serves sit on opposite sides of that line, so the
bridge is stated at the centred germ for both rather than case-split: `MAIS-O7`'s
terminal rung and `MAIS-O77(a)`'s fiber are exact factorizations, where the
centring collapses; `MAIS-O7`'s rank-zero rung and every point of `MAIS-O77(b)`
are saddles, where it does not.

*The antecedent is stronger than what is proved.* `O70ZetaPoleBridge` consumes
`HasExactLocalPair` — a ratio tending to `1`. MAIS-O7 and MAIS-O77(b) establish
`HasLocalVolumeOrder`, two-sided bounds only. Assuming the O70 bridge would
therefore not deliver the A7 rows even at the right germ, because they do not
supply its hypothesis. The bridge below is stated over what is actually proved.

## Why it is narrow

`ZetaPair.lean` records that the general proposition — for every nonnegative
germ the volume pair is the zeta pair — is **false**: a logarithmic correction
to the sublevel volume turns the pole into a branch point. What repairs it is
the hypothesis print carries, real-analyticity, and the reduced-rank loss is
polynomial in its coordinates, so it holds here. Stating the bridge at the germ
family it is used on rather than in general keeps the frontier at something that
could be true, which is the same rule `O70ZetaPoleBridge` follows.

`0 < lam` is print's own exclusion, in the form this interface can check: `def:llc`
requires `L` not identically `L(w*)` on any neighbourhood, "otherwise `Z` vanishes
identically and the invariants are undefined". A locally constant germ has
`HasLocalVolumeOrder` only in its degenerate branch, where `lam = 0`.

**Nothing here proves the bridge.** It is assumed, and every theorem that uses it
carries it in its binders.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.SingularLearning

/-- **`A7-ZETA-BRIDGE`.** Print's `def:llc`, at the germs A7 uses it on: for the
reduced-rank loss centred at an arbitrary point, a two-sided volume order is the
zeta pole order.

Assumed, not proved.-/
@[expose] public def A7ZetaVolumeBridge : Prop :=
  ∀ M N H : ℕ, 0 < M → 0 < N → 0 < H →
    ∀ (C : Matrix (Fin M) (Fin N) ℝ)
      (w : EuclideanSpace ℝ (Fin (H * N + M * H))) (lam : ℝ) (m : ℕ),
      0 < lam →
      HasLocalVolumeOrder (centeredBandGerm (rrrLossCoords M N H C) w) w lam m →
        HasZetaPoleOrder (centeredBandGerm (rrrLossCoords M N H C) w) w lam m

/-! ## MAIS-O7 in print's own definition -/

/-! ## MAIS-O77(a) in print's own definition

Part (a) is the one clause that needs **both** frontiers, and it is stated here
so that the exposure is legible rather than inferred: the volume-order table
already rests on `EigenvalueLawStatement`, and reading it as A7's pair adds
`A7ZetaVolumeBridge` on top.

`0 < lam` is print's own exclusion again, and here it is **derived** rather than
assumed: a factorization forces its rank stratum admissible, and `o70Lambda_pos`
makes the table value positive on every admissible stratum. So the theorem
quantifies over every exact factorization, with no side condition a caller has
to discharge. -/

/-! ## MAIS-O77(b) in print's own definition -/

end AISafetyAtlas.Conjectures.MAIS
