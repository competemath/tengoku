/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.RingTheory.GradedAlgebra.Opposite

/-!
# Graded left modules as right modules over the graded opposite

A left module over an internally graded algebra `A` determines a right module over the
Koszul-signed graded opposite of `A`. On homogeneous elements of degrees `p` and `q`, the action is

`x * op(a) = (-1) ^ (p * q) • (a • x)`.

The construction applies to additive commutative monoids and preserves both the ground-ring scalar
tower and the module grading.

## Main definitions

* `GradedOpposite.leftToRightModule`: the right action of the graded opposite associated to a
  graded left module.

## Main results

* `GradedOpposite.leftToRight_smul_of_mem`: the action on homogeneous elements is the Koszul-signed
  original left action.
* `GradedOpposite.leftToRight_isScalarTower` and
  `GradedOpposite.leftToRight_gradedSMul`: compatibility with the ground-ring action and the
  module grading.

The sign convention follows B. Keller, *Introduction to A-infinity algebras and modules*,
Section 3.1.
-/

public section

namespace TauCeti.GradedOpposite

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The right action of the graded opposite associated to a graded left `A`-module.

It is obtained by restricting scalars along `(GradedOpposite G)ᵐᵒᵖ ≃ₐ[R] A` and conjugating the
result by the quadratic twist of the module grading. -/
@[instance_reducible]
noncomputable def leftToRightModule (G : InternalGrading R A) (H : InternalGrading R M) :
    Module (GradedOpposite G)ᵐᵒᵖ M := by
  letI : Module (GradedOpposite G)ᵐᵒᵖ M :=
    Module.compHom M (opAlgEquiv G).toRingHom
  exact H.quadraticTwistEquiv.toAddEquiv.module (GradedOpposite G)ᵐᵒᵖ

omit [IsScalarTower R A M] in
/-- The graded-opposite action is conjugation of scalar restriction by the quadratic twist. -/
@[simp]
theorem leftToRight_smul (G : InternalGrading R A) (H : InternalGrading R M)
    (s : (GradedOpposite G)ᵐᵒᵖ) (x : M) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    s • x = H.quadraticTwist
      (opAlgEquiv G s • H.quadraticTwist x) := by
  unfold leftToRightModule
  -- Normalize the transferred `AddEquiv` action to the corresponding `LinearEquiv` maps.
  change H.quadraticTwistEquiv.symm
      (opAlgEquiv G s • H.quadraticTwistEquiv x) = _
  rw [H.quadraticTwistEquiv_symm_apply, H.quadraticTwistEquiv_apply]

/-- The ground-ring action commutes with the transported graded-opposite action. -/
theorem leftToRight_isScalarTower (G : InternalGrading R A)
    (H : InternalGrading R M) :
    letI : Module (GradedOpposite G)ᵐᵒᵖ M := leftToRightModule G H
    IsScalarTower R (GradedOpposite G)ᵐᵒᵖ M := by
  let _ : Module (GradedOpposite G)ᵐᵒᵖ M :=
    Module.compHom M (opAlgEquiv G).toRingHom
  let _ : IsScalarTower R (GradedOpposite G)ᵐᵒᵖ M :=
    ⟨fun r s x ↦ by
      -- Normalize only the action on `M` supplied by `Module.compHom`.
      change opAlgEquiv G (r • s) • x = r • (opAlgEquiv G s • x)
      rw [map_smul, smul_assoc]⟩
  exact H.quadraticTwistEquiv.isScalarTower (GradedOpposite G)ᵐᵒᵖ

end TauCeti.GradedOpposite
