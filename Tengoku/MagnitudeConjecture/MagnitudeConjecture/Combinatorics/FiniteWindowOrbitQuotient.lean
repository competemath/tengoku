import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.OrbitQuotientAction
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.SupportInteractionSeparation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite control windows in orbit quotients

Once residual finiteness has separated distinct subgroup translates of a
finite control window, passage to the subgroup-orbit quotient is faithful on
that window: its points remain distinct and the quotient creates no new
instances of the chosen interaction relation.  This is the set-theoretic
locality statement used before transporting vertices, arrows, and meshes in
the covering argument.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.CoveringSeparation

universe u v w

variable {G : Type u} [Group G]
variable {X : Type v} [MulAction G X]

/-- Two subgroup-orbits interact when some representatives interact.  This
definition is representative-free and does not require the relation to be
invariant under translating its two variables independently.-/
def OrbitQuotientInteracts (N : Subgroup G) (R : X → X → Prop)
    (x y : MulAction.orbitRel.Quotient N X) : Prop :=
  ∃ x' ∈ x.orbit, ∃ y' ∈ y.orbit, R x' y'

variable {O : Type w} [MulAction G O] [IsCancelSMul G O]

end MagnitudeConjecture.CoveringSeparation
