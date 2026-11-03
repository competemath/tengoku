/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.Algebra.Polynomial.FieldDivision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Definition 1.7: Signed Remainder Sequence

For $P, Q \in K[X]$, the *signed remainder sequence* of $P$ and $Q$ is
the sequence $(P, Q, -\!\operatorname{Rem}(P, Q), \dots)$ where each
subsequent entry is the negation of the remainder of the two preceding
ones. The sequence stabilises at $0$ once it first reaches $0$.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

open Classical in
/-- BPR Definition 1.7: The signed remainder sequence of P and Q.
    - `SRemS P Q 0 = P`
    - `SRemS P Q 1 = Q`
    - `SRemS P Q (n+2) = −Rem(SRemS P Q n, SRemS P Q (n+1))` when `SRemS P Q (n+1) ≠ 0`
    - `SRemS P Q (n+2) = 0` when `SRemS P Q (n+1) = 0`

    The sequence stabilizes at 0 once reached.-/
noncomputable def SRemS (P Q : K[X]) : ℕ → K[X]
  | 0 => P
  | 1 => Q
  | n + 2 =>
    let prev := SRemS P Q (n + 1)
    if prev = 0 then 0
    else -(SRemS P Q n % prev)

open Classical in
/-- SRemS(P, Q, 0) = P.
@isnad1 id=eq.0h3v.s5.838350b0460f from=translated src=- shape=0777a3e8 vocab=a8b8db07
-/
@[simp] theorem SRemS_fst (P Q : K[X]) : SRemS P Q 0 = P := rfl

open Classical in
/-- SRemS(P, Q, 1) = Q.
@isnad1 id=eq.0h3v.s5.4cd6ee2f1e60 from=translated src=- shape=e3ae3aea vocab=a8b8db07
-/
@[simp] theorem SRemS_snd (P Q : K[X]) : SRemS P Q 1 = Q := by simp [SRemS]

end Azurite.BPR
