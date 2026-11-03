import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Algebra.IndecomposableLocalEnd
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-type almost-split data for right modules

This file connects the magnitude campaign's categorical finite
indecomposable skeleton with the donor's module-theoretic finite-type
almost-split existence theorem.  The two notions of indecomposability are
bridged through the local endomorphism ring, and no classification of modules
is used.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u v

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The categorical endomorphism ring of an FG module agrees with its usual
module endomorphism ring.-/
def fgEndModuleEndRingEquiv
    (M : RightModule.FinitelyGeneratedCategory A) :
    End M ≃+* Module.End Aᵐᵒᵖ M := by
  let U := forget₂ (RightModule.FinitelyGeneratedCategory A)
    (RightModule.Category A)
  letI : U.Additive := ⟨by intros; rfl⟩
  exact
    (CategoryTheory.Functor.endRingEquivOfFullyFaithful U M).trans
      (ModuleCat.endRingEquiv (U.obj M))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
