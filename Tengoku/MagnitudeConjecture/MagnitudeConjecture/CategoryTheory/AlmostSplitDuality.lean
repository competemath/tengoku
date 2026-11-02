import Tengoku.Seed.CategoryTheory.Abelian.Opposite
import Tengoku.Seed.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Almost-split morphisms under anti-equivalence

An equivalence from an opposite category turns a minimal right almost-split
morphism into a minimal left almost-split morphism.  The small generic proof is
adapted from the adjacent OP-conjecture formalization; no OP-specific theorem
or module is imported.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]

/-! ## Irreducible morphisms -/

section Abelian

variable [Abelian C] [Abelian D]

/-- The cokernel of the contravariant image of a morphism is canonically
isomorphic to the image of its kernel.-/
def cokernelMapOpIsoKernel
    (E : Cᵒᵖ ≌ D) {X Y : C} (f : X ⟶ Y) :
    cokernel (E.functor.map f.op) ≅
      E.functor.obj (Opposite.op (kernel f)) :=
  (PreservesCokernel.iso E.functor f.op).symm ≪≫
    E.functor.mapIso (cokernelOpOp f)

/-- Precomposing the mapped morphism by an endpoint isomorphism does not
change its cokernel.-/
def cokernelPrecompMapOpIsoKernel
    (E : Cᵒᵖ ≌ D) {X Y : C} (f : X ⟶ Y)
    {Y' : D} (i : Y' ≅ E.functor.obj (Opposite.op Y)) :
    cokernel (i.hom ≫ E.functor.map f.op) ≅
      E.functor.obj (Opposite.op (kernel f)) :=
  (cokernel.mapIso
      (i.hom ≫ E.functor.map f.op) (E.functor.map f.op)
      i (Iso.refl _) (by simp)).trans
    (cokernelMapOpIsoKernel E f)

end Abelian

end QuotientSubmoduleEquidistribution
