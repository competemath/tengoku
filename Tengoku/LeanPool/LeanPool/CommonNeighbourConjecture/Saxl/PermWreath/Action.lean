/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/
module

public import Tengoku.LeanPool.LeanPool.CommonNeighbourConjecture.Saxl.PermWreath.Defs

/-!
# The product action of a permutation wreath product

For `g = (f, q)` the action on `ι → Δ` is

`(g • x) i = f i • x (q⁻¹ • i)`.
-/

@[expose] public section

namespace Saxl

variable (X Q ι Δ : Type*)
variable [Group X] [Group Q] [MulAction Q ι]

section Action

variable [MulAction X Δ]

/-- The product action of an arbitrary permutation wreath product. -/
instance permWreathMulAction : MulAction (PermWreath X Q ι) (ι → Δ) where
  smul g x i := g.left i • x (g.right⁻¹ • i)
  one_smul x := by
    funext i
    change (1 : X) • x ((1 : Q)⁻¹ • i) = x i
    simp only [inv_one, one_smul]
  mul_smul g h x := by
    funext i
    change
      (g.left i * h.left (g.right⁻¹ • i)) •
          x ((g.right * h.right)⁻¹ • i) =
        g.left i • (h.left (g.right⁻¹ • i) •
          x (h.right⁻¹ • (g.right⁻¹ • i)))
    simp only [mul_inv_rev, mul_smul]

end Action

section Additive

variable [AddMonoid Δ] [DistribMulAction X Δ]

/-- The product action is additive whenever the component action is additive. -/
instance permWreathDistribMulAction :
    DistribMulAction (PermWreath X Q ι) (ι → Δ) where
  toMulAction := permWreathMulAction X Q ι Δ
  smul_zero g := by
    funext i
    change g.left i • (0 : Δ) = 0
    exact smul_zero _
  smul_add g x y := by
    funext i
    change g.left i • (x (g.right⁻¹ • i) + y (g.right⁻¹ • i)) = _
    exact smul_add _ _ _

end Additive

section Scalars

variable {F : Type*} [MulAction X Δ] [SMul F Δ]
variable [SMulCommClass X F Δ]

/-- The product action commutes with scalars whenever the component action does.
@isnad1 id=smulcomm.0h5v.s7.f760b22fead1 from=translated src=- shape=217c805a vocab=7d0ccbbc
-/
instance permWreathSMulCommClass :
    SMulCommClass (PermWreath X Q ι) F (ι → Δ) where
  smul_comm g a x := by
    funext i
    change g.left i • (a • x (g.right⁻¹ • i)) =
      a • (g.left i • x (g.right⁻¹ • i))
    exact smul_comm _ _ _

end Scalars

section CoordinateLemmas

variable [MulAction X Δ]

/-- The defining coordinate formula for the product action.
@isnad1 id=eq.0h7v.s8.a45421516bdd from=translated src=- shape=30d26a76 vocab=4aecf6a2
-/
@[simp]
theorem permWreath_smul_apply (g : PermWreath X Q ι) (x : ι → Δ) (i : ι) :
    (g • x) i = g.left i • x (g.right⁻¹ • i) := rfl

/-- Coordinate form of the identity law.
@isnad1 id=eq.0h6v.s7.a363ea2e2487 from=translated src=- shape=4f97b1f5 vocab=1060a257
-/
theorem one_smul_coord (x : ι → Δ) (i : ι) :
    ((1 : PermWreath X Q ι) • x) i = x i := by
  simp

/-- Fully expanded coordinate form of the multiplication law.
@isnad1 id=eq.0h8v.s9.144d43b97029 from=translated src=- shape=3e3793b6 vocab=d5473c6f
-/
theorem mul_smul_coord (g h : PermWreath X Q ι) (x : ι → Δ) (i : ι) :
    ((g * h) • x) i =
      g.left i • (h.left (g.right⁻¹ • i) •
        x (h.right⁻¹ • (g.right⁻¹ • i))) := by
  simp [mul_smul]

/-- A base-group element acts independently in each coordinate.
@isnad1 id=eq.0h7v.s8.c115abc1ee19 from=translated src=- shape=6cbcafa5 vocab=c5b04254
-/
theorem base_smul_coord (f : ι → X) (x : ι → Δ) (i : ι) :
    (PermWreath.base X Q ι f • x) i = f i • x i := by
  simp

/-- A top-group element acts by reindexing the coordinates.
@isnad1 id=eq.0h7v.s8.9bc5164e45c0 from=translated src=- shape=82877824 vocab=ccb2953a
-/
theorem top_smul_coord (q : Q) (x : ι → Δ) (i : ι) :
    (PermWreath.top X Q ι q • x) i = x (q⁻¹ • i) := by
  simp

end CoordinateLemmas

end Saxl
