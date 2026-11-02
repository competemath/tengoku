import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Tengoku.Seed.CategoryTheory.Abelian.Projective.Resolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Realization of degree-one Ext classes

In an abelian category with enough projectives, every degree-one Ext class is
represented by a short exact sequence.  The construction pushes the kernel of
a projective presentation out along a degree-zero representative supplied by
the long exact Ext sequence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.ExtOneRealization

universe w v u

variable {D : Type u} [Category.{v} D] [Abelian D]

namespace PushoutExtension

variable {P X T : D} (p : P ⟶ X)
variable (f : kernel p ⟶ T)

/-- The map from the pushout middle object to the presented endpoint.-/
def projection : pushout (kernel.ι p) f ⟶ X :=
  pushout.desc p 0 (by simp)

@[simp, reassoc]
theorem inl_projection :
    pushout.inl (kernel.ι p) f ≫ projection p f = p := by
  exact pushout.inl_desc _ _ _

@[simp, reassoc]
theorem inr_projection :
    pushout.inr (kernel.ι p) f ≫ projection p f = 0 := by
  exact pushout.inr_desc _ _ _

/-- The pushout short complex.-/
def shortComplex : ShortComplex D :=
  ShortComplex.mk (pushout.inr (kernel.ι p) f) (projection p f)
    (inr_projection p f)

variable [Epi p]

/-- The comparison from the kernel presentation to its pushout.-/
def fromPresentation :
    ShortComplex.mk (kernel.ι p) p (kernel.condition p) ⟶
      shortComplex p f where
  τ₁ := f
  τ₂ := pushout.inl (kernel.ι p) f
  τ₃ := 𝟙 X
  comm₁₂ := pushout.condition.symm
  comm₂₃ := by
    change pushout.inl (kernel.ι p) f ≫ projection p f = p ≫ 𝟙 X
    simp

end PushoutExtension

variable [HasExt.{w} D] [EnoughProjectives D]

end MagnitudeConjecture.ExtOneRealization
