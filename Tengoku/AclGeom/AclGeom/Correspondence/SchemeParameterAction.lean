/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Tengoku.AclGeom.AclGeom.Correspondence.ParameterAction
import Tengoku.Seed.AlgebraicGeometry.Group.Affine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The coordinate automorphism of a parameter-dependent scheme action

An actual `Spec A`-point of a group scheme acting on `Spec R` gives an `A`-algebra automorphism
of `A ⊗[k] R`, by pullback along the parameter-preserving action automorphism.
Named consumer: the generic translate in the source curve-action genus argument.

**Status:** proved; the actual generic-action consumer is in `SchemeGenericTranslate`.
The source classification remains open.
-/

namespace AclGeom.SchemeParameterAction

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
  {A R : Type u} [CommRing A] [CommRing R] [Algebra k A] [Algebra k R]
  [ModObj G ((Spec (.of R)).asOver (Spec (.of k)))]

private def tensorSchemeAut
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G) :
    Aut (Spec (.of (A ⊗[k] R))) :=
  (pullbackSpecIso k A R).symm ≪≫
    (Over.forget (Spec (.of k))).mapIso
      (ModObj.parameterAut ((Spec (.of R)).asOver (Spec (.of k))) g) ≪≫
    pullbackSpecIso k A R

end

end AclGeom.SchemeParameterAction
