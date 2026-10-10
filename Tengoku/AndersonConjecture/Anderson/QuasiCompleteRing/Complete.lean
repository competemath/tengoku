/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.AndersonConjecture.Anderson.Basic
import Tengoku

/-!
# Complete Implies Quasi-Complete

A complete Noetherian local ring is quasi-complete
(Anderson, 2014, Theorem 3).
-/

open scoped Pointwise

section Helpers
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
end Helpers

/-
## Anderson Theorem 3: Complete implies quasi-complete

If R is a complete Noetherian local ring (i.e., IsAdicComplete M R),
then R is quasi-complete.

Proof idea: Uses Artin-Rees / topology of the M-adic completion.
Given a descending chain {A_n}, pass to M/∩A_n. The M-adic topology
on the Artinian quotient M/J^k M forces stabilization.
-/
