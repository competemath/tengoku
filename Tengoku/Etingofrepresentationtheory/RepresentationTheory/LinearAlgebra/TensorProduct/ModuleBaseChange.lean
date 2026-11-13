/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Module base change -/

open scoped TensorProduct

namespace RepresentationTheory.LinearAlgebra.TensorProduct.ModuleBaseChange

variable {K A V W S T : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]

section OneAlgebra

variable [CommRing S] [Algebra K S]

/-- The algebra homomorphism from the original algebra to scalar-linear endomorphisms of the
scalar-extended module.-/
noncomputable def baseAlgebraAction : A →ₐ[K] Module.End S (S ⊗[K] V) :=
  (Module.End.baseChangeHom K S V).comp (Algebra.lsmul K K V)

/-- The algebra homomorphism from the scalar-extended algebra to scalar-linear endomorphisms of
the scalar-extended module.-/
noncomputable def scalarExtensionAction : (S ⊗[K] A) →ₐ[S] Module.End S (S ⊗[K] V) :=
  AlgHom.liftEquiv K S A (Module.End S (S ⊗[K] V))
    (baseAlgebraAction (A := A) (V := V) (S := S))

/-- The module structure on the scalar extension of a module over the scalar-extended algebra.-/
noncomputable instance instModuleTensorProduct : Module (S ⊗[K] A) (S ⊗[K] V) :=
  Module.compHom (S ⊗[K] V) (R := Module.End S (S ⊗[K] V))
    (scalarExtensionAction (A := A) (V := V) (S := S)).toRingHom

/-- Scalar multiplication by the extended algebra agrees with evaluation of its action
homomorphism on the extended module.
@isnad1 id=eq.0h6v.s11.7bfd59dff0dc from=translated src=- shape=a656714d vocab=94c57bf2
-/
theorem smul_eq_scalarExtensionAction (y : S ⊗[K] A) (x : S ⊗[K] V) :
    (y • x : S ⊗[K] V) = scalarExtensionAction (A := A) (V := V) (S := S) y x :=
  rfl

/-- An extended-algebra tensor formed from a scalar and the algebra unit acts by scalar
multiplication on the extended module.
@isnad1 id=eq.0h6v.s10.70eb004a6783 from=translated src=- shape=fe1cc21e vocab=66f88808
-/
theorem tmul_one_smul_eq_smul (s : S) (x : S ⊗[K] V) :
    ((s ⊗ₜ[K] (1 : A) : S ⊗[K] A) • x : S ⊗[K] V) = s • x := by
  rw [smul_eq_scalarExtensionAction, scalarExtensionAction, AlgHom.liftEquiv_tmul, map_one]
  rfl

end OneAlgebra

section Pushforward

variable [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]

end Pushforward

section PushforwardFunctorial

variable {U : Type*} [AddCommGroup U] [Module K U] [Module A U] [IsScalarTower K A U]
variable [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]

end PushforwardFunctorial

end RepresentationTheory.LinearAlgebra.TensorProduct.ModuleBaseChange
