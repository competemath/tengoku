import Tengoku.KuroshProblemAtGkDimensionTwo.CriticalGK2.LocalOperation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual block-power containment of the local PI operation

The repeated block space is the linear span of genuine products of the two
physical stem blocks.  A homogeneous source polynomial expands into such
products.  The local PI operation consequently lives in the intended repeated
block space, including the padding blocks.
-/

namespace CriticalGK2

open scoped BigOperators

/-- A product of the two actual physical stem blocks, with its source word.-/
noncomputable def physicalBlockProduct (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (w : FreeMonoid Bool) : BinaryFreeAlgebra F :=
  (w.toList.map fun b => stemEmbedding F n t (binaryLetter F b)).prod

/-- The concrete repeated block space, formed by taking linear spans of products.-/
noncomputable def repeatedBlockSpace (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (m : ℕ) : Submodule F (BinaryFreeAlgebra F) :=
  Submodule.span F {z | ∃ w : FreeMonoid Bool,
    w.length = m ∧ z = physicalBlockProduct F n t w}

end CriticalGK2
