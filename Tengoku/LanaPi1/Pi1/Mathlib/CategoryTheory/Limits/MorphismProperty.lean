module

public import Tengoku.Seed.CategoryTheory.Limits.MorphismProperty

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

-- import Pi1.FundamentalGroup.AffineColimits

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty.Over

noncomputable
instance {C : Type*} [Category C] (P : MorphismProperty C) (X : C)
    [HasPullbacks C] [P.IsStableUnderComposition] [P.ContainsIdentities]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    CreatesFiniteLimits (Over.forget P ⊤ X) :=
  createsFiniteLimitsOfCreatesTerminalAndPullbacks _

variable {C : Type*} [Category C] (P Q : MorphismProperty C)
variable [HasPullbacks C] [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
  [Q.IsMultiplicative]

end CategoryTheory.MorphismProperty.Over
