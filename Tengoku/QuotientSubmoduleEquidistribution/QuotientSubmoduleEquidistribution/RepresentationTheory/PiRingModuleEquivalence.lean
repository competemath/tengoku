import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.PiRingModule
import Tengoku.Seed.Algebra.Module.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinate-idempotent decomposition of product-ring modules

For finite `V`, every module over `V → K` is the product of the subspaces
fixed by the coordinate idempotents.  This proves essential surjectivity of
`PiRingModule.totalFunctor` and hence the expected category equivalence.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.PiRingModule

universe uK uV w

variable (K : Type uK) (V : Type uV)
variable [Field K] [Fintype V] [DecidableEq V]

omit [Fintype V] in
@[simp]
theorem coordinateIdempotent_mul_self (i : V) :
    coordinateIdempotent K V i * coordinateIdempotent K V i =
      coordinateIdempotent K V i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, h]

omit [Fintype V] in
theorem coordinateIdempotent_mul_eq_zero {i j : V} (h : i ≠ j) :
    coordinateIdempotent K V i * coordinateIdempotent K V j = 0 := by
  funext k
  by_cases hi : k = i
  · subst k
    simp [coordinateIdempotent, h]
  · simp [coordinateIdempotent, hi]

@[simp]
theorem sum_coordinateIdempotent :
    ∑ i : V, coordinateIdempotent K V i = 1 := by
  funext j
  simp [coordinateIdempotent]

omit [Fintype V] in
theorem mul_coordinateIdempotent (s : V → K) (i : V) :
    s * coordinateIdempotent K V i =
      algebraMap K (V → K) (s i) * coordinateIdempotent K V i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, h]

/-- A tagged copy of the underlying additive group, used to register scalar
restriction along the diagonal map `K → V → K` without identifying two
different bundled `ModuleCat` carriers by definitional equality.-/
structure ScalarCarrier
    (X : ModuleCat.{max uV w} (V → K)) where
  val : X

namespace ScalarCarrier

/-- Forget the scalar-restriction tag.-/
def equiv (X : ModuleCat.{max uV w} (V → K)) : ScalarCarrier K V X ≃ X where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq V] in
@[ext]
theorem ext {X : ModuleCat.{max uV w} (V → K)}
    {x y : ScalarCarrier K V X} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance (X : ModuleCat.{max uV w} (V → K)) :
    AddCommGroup (ScalarCarrier K V X) :=
  (equiv K V X).addCommGroup

end ScalarCarrier

/-- Projection onto one coordinate idempotent, as an endomorphism of the
product-ring module.-/
def coordinateProjection
    (X : ModuleCat.{max uV w} (V → K)) (j : V) : X →ₗ[V → K] X :=
  LinearMap.lsmul (V → K) X (coordinateIdempotent K V j)

omit [Fintype V] in
@[simp]
theorem coordinateProjection_apply
    (X : ModuleCat.{max uV w} (V → K)) (j : V) (x : X) :
    coordinateProjection K V X j x = coordinateIdempotent K V j • x := rfl

end QuotientSubmoduleEquidistribution.PiRingModule
