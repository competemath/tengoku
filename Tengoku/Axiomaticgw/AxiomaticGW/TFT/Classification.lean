/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.TFT.Frobenius

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Recovering Frobenius data from a two-dimensional TFT

The one-point correlator recovers the Frobenius counit. The three-point
correlator, with its last input converted through the perfect metric, recovers
a bilinear product on the state space.

The existing `CommFrobeniusAlgebra` structure is parameterized by pre-existing
`CommRing` and `Algebra` typeclasses. Consequently, installing a product
recovered on a bare module as a new ring instance is a separate foundational
task. This file also provides the reverse construction when those algebra
typeclasses are already present and the recovered trace pairing is compatible
with them.
-/

@[expose] public section

namespace AxiomaticGW

namespace TwoDimensionalTFT

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- The three-point correlator, curried into three successive linear maps.-/
def threePointFunction (T : TwoDimensionalTFT R V) :
    V →ₗ[R] V →ₗ[R] V →ₗ[R] R :=
  (LinearMap.compRight R
    (SymmetricPerfectPairing.finTwoToBilin (R := R) (V := V))).comp
    (multilinearCurryLeftEquiv R (fun _ : Fin 3 ↦ V) R).toLinearMap <|
    T.correlator 0 (Fin 3)

/-- Evaluation of the curried three-point function.-/
@[simp]
theorem threePointFunction_apply (T : TwoDimensionalTFT R V)
    (x y z : V) :
    T.threePointFunction x y z =
      T.correlator 0 (Fin 3) (Fin.cons x (Fin.cons y fun _ ↦ z)) := by
  simp only [threePointFunction, Nat.succ_eq_add_one, Nat.reduceAdd,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    multilinearCurryLeftEquiv_apply, LinearMap.compRight_apply,
    SymmetricPerfectPairing.finTwoToBilin_apply,
    MultilinearMap.curryLeft_apply]

/-- The product recovered from the three-point correlator by raising its last
index with the inverse metric.-/
noncomputable def product (T : TwoDimensionalTFT R V) :
    V →ₗ[R] V →ₗ[R] V :=
  (LinearMap.compRight R
      (LinearMap.compRight R T.pairing.toDual.symm.toLinearMap)).comp
    ((LinearMap.compRight R
      (SymmetricPerfectPairing.finTwoToBilin (R := R) (V := V))).comp
      (multilinearCurryLeftEquiv R (fun _ : Fin 3 ↦ V) R).toLinearMap) <|
    T.correlator 0 (Fin 3)

/-- The recovered product is characterized by the original three-point
correlator.-/
theorem pairing_product (T : TwoDimensionalTFT R V) (x y z : V) :
    T.pairing.form (T.product x y) z = T.threePointFunction x y z := by
  rw [← T.pairing.toDual_apply]
  simp only [product, Nat.succ_eq_add_one, Nat.reduceAdd,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    multilinearCurryLeftEquiv_apply, LinearMap.compRight_apply,
    LinearEquiv.apply_symm_apply, SymmetricPerfectPairing.finTwoToBilin_apply,
    MultilinearMap.curryLeft_apply, threePointFunction]

end TwoDimensionalTFT

section ExistingAlgebra

namespace TwoDimensionalTFT

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- Compatibility required to interpret a two-dimensional TFT on an already
existing algebra as a `CommFrobeniusAlgebra`.-/
def IsTraceCompatible (T : TwoDimensionalTFT R A) : Prop :=
  ∀ x y : A, T.counit (x * y) = T.pairing.form x y

/-- Recover a Frobenius algebra on an existing commutative algebra when its
multiplication is compatible with the correlator counit and metric.-/
def toCommFrobeniusAlgebra
    (T : TwoDimensionalTFT R A) (h : T.IsTraceCompatible) :
    CommFrobeniusAlgebra R A where
  counit := T.counit
  isPerfPair := by
    have hform : tracePairing T.counit = T.pairing.form := by
      ext x y
      exact h x y
    rw [hform]
    exact T.pairing.isPerfPair

end TwoDimensionalTFT

end ExistingAlgebra

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- The one-point correlator of the theory associated to `F` recovers its
original counit.-/
theorem toTwoDimensionalTFT_counit
    (F : CommFrobeniusAlgebra R A) :
    F.toTwoDimensionalTFT.counit = F.counit := by
  ext x
  change F.correlator 0 (Fin 1) (fun _ ↦ x) = F.counit x
  simp only [correlator_apply,
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.prod_const,
    Finset.card_singleton, pow_one, pow_zero, mul_one]

/-- The forward two-dimensional TFT satisfies trace compatibility with the
original algebra.-/
theorem toTwoDimensionalTFT_isTraceCompatible
    (F : CommFrobeniusAlgebra R A) :
    F.toTwoDimensionalTFT.IsTraceCompatible := by
  intro x y
  rw [F.toTwoDimensionalTFT_counit]
  exact F.pairing_apply x y

/-- Recovering the Frobenius structure from its associated two-dimensional TFT
returns the original structure.-/
theorem toCommFrobeniusAlgebra_toTwoDimensionalTFT
    (F : CommFrobeniusAlgebra R A) :
    F.toTwoDimensionalTFT.toCommFrobeniusAlgebra
        F.toTwoDimensionalTFT_isTraceCompatible = F := by
  apply CommFrobeniusAlgebra.ext
  change F.toTwoDimensionalTFT.counit = F.counit
  exact F.toTwoDimensionalTFT_counit

end CommFrobeniusAlgebra

end AxiomaticGW
