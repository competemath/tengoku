import Tengoku.Seed.Algebra.Module.MinimalAxioms
import Tengoku.Seed.Algebra.Module.TransferInstance
import Tengoku.Seed.Algebra.TrivSqZeroExt.Basic
import Tengoku.Seed.Algebra.Category.ModuleCat.ChangeOfRings
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.SplitBasicCoordinateSystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Split basic algebras as trivial square-zero extensions

For a split basic algebra with square-zero Jacobson radical, this file
packages the radical as a bimodule over the coordinate semisimple algebra and
upgrades the linear decomposition to an algebra equivalence with Mathlib's
`TrivSqZeroExt`.
-/

set_option autoImplicit false

noncomputable section

namespace QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData

universe u v

variable {K B : Type u} {I : Type v}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]
  [Fintype I] [DecidableEq I]

/-- A copy of the Jacobson radical whose type remembers the chosen coordinate
data, allowing its left and right coordinate-algebra actions to be registered
as instances without ambiguity.-/
structure RadicalBimodule
    (D : QuotientCoordinateData (K := K) (B := B) (I := I)) where
  val : Ring.jacobson B

namespace RadicalBimodule

variable
    (D : QuotientCoordinateData (K := K) (B := B) (I := I))

/-- Forget the tagged bimodule wrapper.-/
def equiv : RadicalBimodule D ≃ Ring.jacobson B where
  toFun := RadicalBimodule.val
  invFun := RadicalBimodule.mk
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
/--
@isnad1 id=eq.1h6v.s6.f5b6902a5d6e from=translated src=- shape=371fe54e vocab=65564f82
-/
theorem ext' {x y : RadicalBimodule D} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance : AddCommGroup (RadicalBimodule D) :=
  (equiv D).addCommGroup

instance : SMul Bᵐᵒᵖ (RadicalBimodule D) where
  smul b x :=
    ⟨⟨(x.val : B) * MulOpposite.unop b,
      (Ring.jacobson B).mul_mem_right _ x.val.property⟩⟩

instance : Module Bᵐᵒᵖ (RadicalBimodule D) :=
  Module.ofMinimalAxioms
    (by
      intro b x y
      apply ext' D
      apply Subtype.ext
      change ((x.val : B) + y.val) * MulOpposite.unop b =
        (x.val : B) * MulOpposite.unop b + y.val * MulOpposite.unop b
      exact add_mul _ _ _)
    (by
      intro a b x
      apply ext' D
      apply Subtype.ext
      change (x.val : B) * (MulOpposite.unop a + MulOpposite.unop b) =
        x.val * MulOpposite.unop a + x.val * MulOpposite.unop b
      exact mul_add _ _ _)
    (by
      intro a b x
      apply ext' D
      apply Subtype.ext
      change (x.val : B) * MulOpposite.unop (a * b) =
        (x.val * MulOpposite.unop b) * MulOpposite.unop a
      simp [mul_assoc])
    (by
      intro x
      apply ext' D
      apply Subtype.ext
      change (x.val : B) * 1 = x.val
      exact mul_one _)

instance : Module (I → K)ᵐᵒᵖ (RadicalBimodule D) :=
  Module.compHom _ (RingHom.op D.coordinateSection.toRingHom)

end RadicalBimodule

end QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData
