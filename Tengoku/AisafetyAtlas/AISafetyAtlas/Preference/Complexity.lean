module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Preference
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.Properties
public import Tengoku.Seed.Computability.Primrec.List

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Simplicity does not break the planner/reward tie

## Statement intent

- **Objects.** Behaviours and rewards as bit strings
  (`Kolmogorov.BitString = List Bool`), and plain Kolmogorov complexity
  `Kolmogorov.plainK` relative to an optimal conditional decompressor `U`.
- **Assumptions.** `U` is optimal conditional (`isOptimalConditional`), the same
  hypothesis the vendored Chaitin development uses. The reward is fixed first;
  the constant is then uniform in the behaviour.
- **Quantifier order.** Constants are chosen before behaviours: there *exists*
  a constant such that for *every* behaviour the bound holds. Constants never
  depend on the behaviour, which is what makes the statements bite.
- **Conclusion.** Both bounds, **for one canonical encoding only**. *Lower*
  (`explanation_at_least_behaviour`): the behaviour is computably recoverable
  from `encodeExplanation r b`, so *that string* is not more than a constant
  simpler than the behaviour. It quantifies over the manufactured strings
  `encodeExplanation r b`, **not** over arbitrary planner/reward pairs compatible
  with `b`. *Upper*
  (`degenerate_explanation_cheap`): the degenerate explanation is at most a
  constant more complex than the behaviour. Together
  (`explanation_complexity_eq_behaviour`) the degenerate explanation sits within
  additive constants of the behaviour's own complexity. It does **not** follow
  that it is within a constant of the minimum over all compatible explanations:
  there is no planner type, no compatibility predicate and no minimum over
  explanations in this module, so that stronger reading is unproved here.
- **Difference from the source.** Armstrong and Mindermann, §5.1, argue that
  "the complexity of `π̇` is close to a lower bound on any pair compatible with
  it" via the evaluation map `(p, R) ↦ p(R)`, and that "degenerate decompositions
  are themselves close to this bound"; Proposition 7 combines these. Here the
  evaluation map is realised concretely as `decodeBehaviour` on a
  self-delimiting encoding, and the source's framework of `c`-reasonable
  languages and "comparable complexity" is replaced by plain additive constants
  over `Kolmogorov.plainK`. Crucially the source applies evaluation
  `(p, R) ↦ p(R)` to *every* compatible pair, whereas `decodeBehaviour` inverts
  one fixed encoding, so the lower bound here is strictly narrower than the
  source's. Only the degenerate pair `(p_π̇, 0)` is treated. The quantified-over-
  all-compatible-pairs statement lives in
  `AISafetyAtlas.Preference.ReasonableLanguage.policy_le_of_compatible`, over an
  abstract complexity measure rather than `plainK`.

## Explicit non-claims

- **Not** a claim that no prior can distinguish the pairs — only that a prior
  built from plain Kolmogorov complexity cannot, up to an additive constant.
- **Not** a treatment of the source's anti-rational pair `(-p_g, -R_π̇)` or of
  its regret analysis.
- **Not** a lower bound over arbitrary explanations. It is a bi-Lipschitz fact
  about one canonical pairing encoding.
- **Not** the formal core of the source's Proposition 7, which quantifies over
  all compatible pairs; see `Reasonable.lean` for that.
- **Not** a statement about resource-bounded or computable-in-practice priors;
  the source's Appendix A discusses those separately.

Survey row: **BY-011**. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Preference

open Kolmogorov

/--
A self-delimiting encoding of the degenerate explanation of behaviour `b` under
a fixed reward `r`: the length of `b` in unary, a `false` marker, then `b`, then
`r`. The degenerate planner is the one that ignores its reward and returns `b`,
so `b` together with `r` is exactly the data of that explanation.-/
@[expose] public def encodeExplanation (r b : BitString) : BitString :=
  (b.map fun _ => true) ++ (false :: (b ++ r))

/--
Recover the behaviour from its encoded degenerate explanation: read the unary
length prefix, drop it and the marker, then take that many bits. This is the
encoded form of the source's evaluation map `(p, R) ↦ p(R)`.-/
@[expose] public def decodeBehaviour (x : BitString) : BitString :=
  ((x.dropWhile id).tail).take ((x.takeWhile id).length)

private theorem takeWhile_encode (r b : BitString) :
    (encodeExplanation r b).takeWhile id = b.map fun _ => true := by
  unfold encodeExplanation
  induction b with
  | nil => simp
  | cons a t ih => simp

private theorem dropWhile_encode (r b : BitString) :
    (encodeExplanation r b).dropWhile id = false :: (b ++ r) := by
  unfold encodeExplanation
  induction b with
  | nil => simp
  | cons a t ih => simp

end AISafetyAtlas.Preference
