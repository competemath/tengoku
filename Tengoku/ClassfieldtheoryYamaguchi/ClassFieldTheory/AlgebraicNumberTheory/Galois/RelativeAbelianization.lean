/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
/-!
# Relative topological abelianization

For a possibly infinite Galois extension `M/F`, this file identifies the
topological abelianization of `Gal(M/F)` with the Galois group of the
intermediate field fixed by the closed commutator subgroup.
-/

open scoped IsMulCommutative

noncomputable section

universe u v

namespace ClassFieldTower.Martinet

variable (F : Type u) (M : Type v)
variable [Field F] [Field M] [Algebra F M] [IsGalois F M]

/-- Closed commutator subgroup of a relative, possibly infinite, Galois
group.-/
def relativeCommutatorClosure : ClosedSubgroup Gal(M / F) where
  toSubgroup := (commutator Gal(M / F)).topologicalClosure
  isClosed' := Subgroup.isClosed_topologicalClosure _

/--
@isnad1 id=normal.0h2v.s6.139b99f18ad3 from=translated src=- shape=0e1343b4 vocab=a1667501
-/
local instance relativeCommutatorClosure_normal :
    (relativeCommutatorClosure F M).Normal := by
  change ((commutator Gal(M / F)).topologicalClosure).Normal
  infer_instance

/-- Maximal abelian intermediate field of a relative Galois extension.-/
def relativeMaximalAbelianSubextension : IntermediateField F M :=
  IntermediateField.fixedField (relativeCommutatorClosure F M).toSubgroup

/-- The relative maximal abelian subextension is Galois.
@isnad1 id=isgalois.0h2v.s6.d5edd66b5c17 from=translated src=- shape=17830135 vocab=f38b1036
-/
theorem relativeMaximalAbelianSubextension_isGalois :
    IsGalois F (relativeMaximalAbelianSubextension F M) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (relativeMaximalAbelianSubextension F M)).1
  change (IntermediateField.fixedField
    (relativeCommutatorClosure F M).toSubgroup).fixingSubgroup.Normal
  rw [InfiniteGalois.fixingSubgroup_fixedField
    (relativeCommutatorClosure F M)]
  infer_instance

/--
@isnad1 id=isgalois.0h2v.s6.d5edd66b5c17 from=translated src=- shape=17830135 vocab=f38b1036
-/
local instance relativeMaximalAbelianSubextension.instIsGalois :
    IsGalois F (relativeMaximalAbelianSubextension F M) :=
  relativeMaximalAbelianSubextension_isGalois F M

/-- Algebraic quotient equivalence for relative abelianization.-/
noncomputable def relativeAbelianizationMulEquiv :
    TopologicalAbelianization Gal(M / F) ≃*
      Gal(relativeMaximalAbelianSubextension F M / F) :=
  InfiniteGalois.normalAutEquivQuotient (relativeCommutatorClosure F M)

/-- The quotient equivalence sends a class to restriction.
@isnad1 id=eq.0h3v.s13.95de0c5f4147 from=translated src=- shape=6b0201d6 vocab=5fe4889b
-/
@[simp]
theorem relativeAbelianizationMulEquiv_mk (sigma : Gal(M / F)) :
    relativeAbelianizationMulEquiv F M (QuotientGroup.mk sigma) =
      AlgEquiv.restrictNormalHom (relativeMaximalAbelianSubextension F M) sigma :=
  rfl

/-- The algebraic relative-abelianization equivalence is continuous.
@isnad1 id=continuo.0h2v.s13.c77255b3722f from=translated src=- shape=68570a24 vocab=ea753b84
-/
theorem relativeAbelianizationMulEquiv_continuous :
    Continuous (relativeAbelianizationMulEquiv F M) := by
  apply (QuotientGroup.isQuotientMap_mk
    (relativeCommutatorClosure F M).toSubgroup).continuous_iff.2
  refine (InfiniteGalois.restrictNormalHom_continuous
    (relativeMaximalAbelianSubextension F M)).congr ?_
  intro sigma
  exact (relativeAbelianizationMulEquiv_mk F M sigma).symm

/-- The topological abelianization is the Galois group of the maximal
relative abelian subfield.-/
noncomputable def relativeTopologicalAbelianizationEquiv :
    TopologicalAbelianization Gal(M / F) ≃ₜ*
      Gal(relativeMaximalAbelianSubextension F M / F) := by
  let h := Continuous.homeoOfEquivCompactToT2
    (relativeAbelianizationMulEquiv_continuous F M)
  exact
    { toMulEquiv := relativeAbelianizationMulEquiv F M
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

end ClassFieldTower.Martinet
