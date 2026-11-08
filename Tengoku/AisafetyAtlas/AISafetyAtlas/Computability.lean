module

public import Tengoku.Seed.Computability.Halting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Computability limits

Thin wrappers over Mathlib `Computability.Halting`. No AI-safety bridge.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Law** | `rice` | Extensional Rice (function form) |
| **Law** | `rice_code_iff` | Extensional code-set Rice |
| **Law** | `halting_problem` / `halting_re` | Halting RE / undecidability packaging |

Prefer `Verification.rice` when the caller states a property on behavior rather
than on codes directly.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Computability

end AISafetyAtlas.Computability
