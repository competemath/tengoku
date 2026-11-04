import Tengoku.Seed.CategoryTheory.Preadditive.Mat
import Tengoku.Seed.CategoryTheory.Linear.Basic
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Linear structure on finite matrix categories
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.CategoryTheory

universe w v u

section Linear

variable {K : Type w} [Semiring K]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]

/-- The pointwise linear structure on the finite matrix category.-/
instance matLinear : Linear K (Mat_ C) where
  homModule M N :=
    Pi.module M.ι (fun i ↦ ∀ j : N.ι, M.X i ⟶ N.X j) K
  smul_comp := by
    intro X Y Z k f g
    apply Mat_.hom_ext
    intro i j
    change (∑ l, (k • f i l) ≫ g l j) =
      k • ∑ l, f i l ≫ g l j
    simp [Finset.smul_sum]
  comp_smul := by
    intro X Y Z f k g
    apply Mat_.hom_ext
    intro i j
    change (∑ l, f i l ≫ (k • g l j)) =
      k • ∑ l, f i l ≫ g l j
    simp [Finset.smul_sum]

end Linear

section Finite

variable {K : Type w} [DivisionRing K]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]

end Finite

end QuotientSubmoduleEquidistribution.CategoryTheory
