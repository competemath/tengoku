/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Generator-level interface for Zhou's spatial factor map.  The analytic
crossed-product construction is reduced to the kernel, quotient, and vacuum
transport equations used by the regular factor.
Paper: §3.
-/
module

public import Tengoku.LeanPool.LeanPool.ConnesRigidity.Core
public import Tengoku
import Tengoku.LeanPool.LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.SemidirectClosure

/-!
The semidirect generator transport component of the Connes rigidity formalization.
-/

@[expose] public section

namespace Connes
namespace SemidirectGeneratorTransport

noncomputable section

/- The regular operators from the two semidirect factors form the generator
family used by the closure reduction. Paper: §3.
-/
/--
The `generatorSet` construction used in the Connes rigidity formalization.
-/
def generatorSet
    {A K : Type*} [Group A] [Group K]
    (φ : K →* MulAut A) :
    Set (GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K)) :=
  (Set.range fun a : A =>
    (leftRegularRepresentation (A ⋊[φ] K) (SemidirectProduct.inl a) :
      GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K))) ∪
  (Set.range fun k : K =>
    (leftRegularRepresentation (A ⋊[φ] K) (SemidirectProduct.inr k) :
      GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K)))

/- The generator transport equations give equality of the two generator
sets. Paper: §3. -/

/- The generator equations imply transport of regular-factor membership.
Paper: §3. -/

end
end SemidirectGeneratorTransport
end Connes
