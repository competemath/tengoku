import Tengoku.StringDiagramsLean.StringDiagrams.Super.TwoSOp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The 2-super-opposite is a 2-supercategory

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 3.4:
`𝔄^{sop}` satisfies the axioms of a 2-supercategory, including the super interchange law
(`TwoSOp.twoSupercategory`).
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory BicategoryStruct TwoSupercategory
universe r u v w
namespace TwoSOp
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

end TwoSOp
end StringDiagrams
