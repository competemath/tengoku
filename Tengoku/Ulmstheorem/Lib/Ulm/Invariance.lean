import Tengoku.Ulmstheorem.Lib.PGroups.UlmInvariants

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Invariance of Ulm data under isomorphism

This module contains the easy direction of Ulm's theorem: isomorphisms preserve
both the Ulm filtration and the classical `P_α / P_{α+1}` quotients, hence the
Ulm invariants.
-/

open Cardinal Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
