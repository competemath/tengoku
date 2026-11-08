module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Computability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Verification limits for extensional program behavior

## Primary surface

| Role | Declaration | Import | One-line |
|---|---|---|---|
| **Law** | `rice` | this module | No total verifier for nontrivial behavioral properties |
| **Bridge** | `AgentBehavior.no_behavioral_safety_verifier` | `.AgentBehavior` | Downstream packaging (BY-012; reviewed bridge) |
| **Bridge** | `Robot.action_safety_unverifiable` | `.Robot` | Robot-facing RELATED reduction (BY-033; reviewed) |

This module does not import the two bridge modules, so the last two rows need
`AISafetyAtlas.Verification.AgentBehavior` or `AISafetyAtlas.Verification.Robot`
of their own — or `AISafetyAtlas`, which carries all three.

## Statement intent

- Object: partial ℕ I/O behavior; codes via Mathlib `eval`.
- Conclusion: no total computable verifier for nontrivial behavioral properties.
- Source form: `Computability.rice_code_iff`.

## Explicit non-claims

Does **not** claim every practical AI property is behavioral, that a particular
system is this evaluator, or that sound incomplete methods are impossible.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Verification

/-- A property stated directly on partial input/output behavior.-/
public abbrev BehavioralProperty := Set (ℕ →. ℕ)

/-- The behavior represented by `program` satisfies `property`.-/
@[expose] public def Holds (property : BehavioralProperty) (program : Code) : Prop :=
  eval program ∈ property

/-- A behavioral property with accepted and rejected representable behaviors.-/
@[expose] public def Nontrivial (property : BehavioralProperty) : Prop :=
  (∃ accepted, Holds property accepted) ∧
    (∃ rejected, ¬ Holds property rejected)

/-- The property has a total computable decision procedure on program codes.-/
@[expose] public def HasVerifier (property : BehavioralProperty) : Prop :=
  ComputablePred (Holds property)

end AISafetyAtlas.Verification
