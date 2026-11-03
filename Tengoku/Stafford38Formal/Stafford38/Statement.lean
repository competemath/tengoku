module
public import Tengoku.Stafford38Formal.proofs.stafford38_reduction
public import Tengoku.Stafford38Formal.proofs.weyl_symplectic
public import Tengoku.Stafford38Formal.Stafford38.ChallengeDefinitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# The universal Stafford 3.8 target

This file gives proof-side aliases of the Mathlib-only challenge definitions
in `Stafford38.ChallengeDefinitions`. The end-to-end theorem proves this
shared statement; its certificate retains the written multiplication order.
-/

namespace Stafford38

/-- The presented `n`th Weyl algebra with its standard symplectic form.-/
abbrev WeylAlg (k : Type*) [Field k] (n : ℕ) :=
  Stafford38Challenge.WeylAlg k n

/-- Exact proposition required for the publication theorem.-/
abbrev UniversalStatement.{u} : Prop := Stafford38Challenge.UniversalStatement.{u}

/-- The paper-facing name is definitionally the literal challenge predicate.
@isnad1 id=iff.0h0v.s1.129e3dfcc926 from=translated src=- shape=25b03439 vocab=abcdeb08
-/
theorem challenge_universalStatement_iff.{u} :
    Stafford38Challenge.UniversalStatement.{u} ↔ UniversalStatement.{u} := Iff.rfl

end Stafford38
