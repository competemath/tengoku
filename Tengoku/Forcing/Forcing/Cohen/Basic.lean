/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Forcing.Forcing.FinitePartialFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cohen forcing conditions

The Cohen forcing notion `Fn(ω, 2)`: finite partial functions `ℕ ⇀ Bool`, ordered by reverse
inclusion. This is the finite-partial-function carrier (`Forcing.FinitePartialFunction`) at
index type `ℕ` and value type `Bool`; everything representation-independent — the operations,
the order structure, compatibility as agreement, `insert_le_iff`, the union lemmas, and
fresh-coordinate existence — lives there and applies here by instantiation.

What is genuinely Cohen-specific begins in the next files: the coordinate and diagonal
requirements, and the generic real.

## Main definitions

* `Forcing.Cohen.Cond`: a Cohen condition.
-/

namespace Forcing.Cohen

/-- A *Cohen condition*: a finite partial function `ℕ ⇀ Bool`, thought of as a finite amount of
information about a real.-/
abbrev Cond : Type :=
  FinitePartialFunction (fun _ : ℕ => Bool)

/-!
### Sanity examples

Everything below is inherited from `FinitePartialFunction`; these examples pin down the two
facts that make Cohen forcing nontrivial — conditions can disagree, and disjoint coordinates
never conflict — and confirm that the generic API instantiates without friction.
-/

open FinitePartialFunction

end Forcing.Cohen
