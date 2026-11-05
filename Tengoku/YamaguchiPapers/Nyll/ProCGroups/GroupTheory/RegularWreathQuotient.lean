/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ProCGroups.WreathProducts
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Algebra.Group.Pi.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quotients of regular wreath modules

Restriction to a finite subgroup followed by multiplication along the fibers
of a quotient is equivariant and surjective. This produces regular wreath
quotients after restricting the right factor to the subgroup.
-/

namespace ProCGroups

universe u v w

variable {A : Type u} [CommGroup A] {Q : Type v} [Group Q] [Finite Q]
  {B : Type w} [Group B]

/-- Multiply the coordinates in each fiber of a homomorphism from a subgroup.-/
noncomputable def regularWreathFiberNorm (J : Subgroup Q) (ρ : J →* B) :
    (Q → A) →* (B → A) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  refine {
    toFun := fun f b => ∏ j : J, if ρ j = b then f (j : Q) else 1
    map_one' := ?_
    map_mul' := ?_ }
  · funext b
    simp only [Pi.one_apply, ite_self, Finset.prod_const_one]
  · intro f g
    funext b
    simp only [Pi.mul_apply, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : ρ j = b
    · rw [ite_eq_left hj, ite_eq_left hj, ite_eq_left hj]
    · rw [ite_eq_right hj, ite_eq_right hj, ite_eq_right hj, one_mul]

end ProCGroups
