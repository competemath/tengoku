/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.T3ModelCompanion.T3.GroupTheory.AssociatedGraded.Lie

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Truncating the associated graded at degree three

For a group of exponent three, only degrees one, two and three contribute to the associated
graded. This file gives the canonical linear equivalence from the direct sum of the actual
central quotients to the finite product of those three quotients. It is used to assemble
the three maps in the paper's exterior description of a free group's associated graded.

Paper-ID: preliminaries.associated_graded_properties, preliminaries.free_graded_equiv
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.19(1) and Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`.
-/

@[expose] public section

open scoped DirectSum

namespace T3.AssociatedGraded

variable (G : Type*) [Group G] [Fact (HasExponentThree G)]

/-- The associated graded is the product of its three possibly nonzero components.

Paper-ID: preliminaries.associated_graded_properties, preliminaries.free_graded_equiv
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.19(1) and Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`.-/
def truncationEquiv : GradedModule G ≃ₗ[ZMod 3] Layer G 1 × Layer G 2 × Layer G 3 where
  toFun x := (x 1, x 2, x 3)
  invFun x := DirectSum.lof (ZMod 3) ℕ (Layer G) 1 x.1 +
    DirectSum.lof (ZMod 3) ℕ (Layer G) 2 x.2.1 + DirectSum.lof (ZMod 3) ℕ (Layer G) 3 x.2.2
  left_inv x := by
    apply DFinsupp.ext
    intro n
    by_cases h₁ : n = 1
    · subst n
      simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    by_cases h₂ : n = 2
    · subst n
      simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    by_cases h₃ : n = 3
    · subst n
      simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Subsingleton.elim _ _
    · have := layer_subsingleton_of_four_le (G := G) Fact.out (show 4 ≤ n by omega)
      exact Subsingleton.elim _ _
  right_inv x := by
    apply Prod.ext
    · simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    · apply Prod.ext <;> simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Truncation reads the three homogeneous coordinates.

Paper-ID: preliminaries.free_graded_equiv
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29, `proposition:gr(F) is Grassmann algebra`.
@isnad1 id=eq.0h2v.s11.e00af6cdda16 from=translated src=- shape=e8f21baa vocab=a0d509d5
-/
@[simp]
theorem truncationEquiv_apply (x : GradedModule G) : truncationEquiv G x = (x 1, x 2, x 3) := rfl

/-- The inverse truncation inserts the three homogeneous coordinates into the direct sum.

Paper-ID: preliminaries.free_graded_equiv
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29, `proposition:gr(F) is Grassmann algebra`.
@isnad1 id=eq.0h2v.s12.828af83e1e02 from=translated src=- shape=2a974180 vocab=8b5c4980
-/
@[simp]
theorem truncationEquiv_symm_apply (x : Layer G 1 × Layer G 2 × Layer G 3) :
    (truncationEquiv G).symm x = DirectSum.lof (ZMod 3) ℕ (Layer G) 1 x.1 +
      DirectSum.lof (ZMod 3) ℕ (Layer G) 2 x.2.1 + DirectSum.lof (ZMod 3) ℕ (Layer G) 3 x.2.2 := rfl

/-- The degree-three coordinate of a bracket is the sum of its two mixed-degree terms.

Paper-ID: preliminaries.associated_graded_properties, preliminaries.free_graded_equiv
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.19 and Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`.
@isnad1 id=eq.0h3v.s12.f569ab1d82b2 from=translated src=- shape=6a0cef52 vocab=35656935
-/
@[simp]
theorem bracket_three (x y : GradedModule G) :
    ⁅x, y⁆ 3 = bracketLayer (by decide) (by decide) (x 2) (y 1) -
      bracketLayer (by decide) (by decide) (y 2) (x 1) := by
  simp [bracket_eq, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]

end T3.AssociatedGraded
