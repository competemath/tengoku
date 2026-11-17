/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Combinatorics.StableArity
public import Tengoku.Axiomaticgw.AxiomaticGW.TFT.Frobenius

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar-valued topological CohFTs

This is the stable-arity, scalar-valued form of a topological CohFT. Its values
model degree-zero classes. A later general CohFT will replace the scalar
codomain by an abstract stable-curve cohomology system.
-/

@[expose] public section

namespace AxiomaticGW

/-- A scalar-valued topological CohFT indexed only by stable genera and finite
label types.-/
structure TopologicalCohFT (R V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] [Module.Free R V] [Module.Finite R V] where
  /-- The metric used at every node.-/
  pairing : SymmetricPerfectPairing R V
  /-- The flat unit.-/
  unit : V
  /-- The scalar class assigned to a stable genus and label type.-/
  omega : (g : ℕ) → (S : Type) → [Fintype S] → StableArity g S →
    MultilinearMap R (fun _ : S ↦ V) R
  /-- Naturality under relabelling.-/
  relabel : ∀ (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T),
    (omega g S hS).domDomCongr e = omega g T hT
  /-- The flat-unit axiom.-/
  unit_insert : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (a : S → V),
    omega g (Option S) (StableArity.option h)
        (fun | none => unit | some s => a s) =
      omega g S h a
  /-- Nonseparating gluing.-/
  nonseparating : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity (g + 1) S),
    pairing.selfContract
        (omega g (S ⊕ Fin 2) (StableArity.sum_fin_two_iff.mpr h)) =
      omega (g + 1) S h
  /-- Separating gluing for two stable components.-/
  separating : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T)),
    pairing.pairContract (omega g₁ (Option S) h₁) (omega g₂ (Option T) h₂) =
      omega (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)
  /-- Inserting the unit into the stable three-point correlator recovers the
  metric.-/
  normalization : ∀ a : Fin 2 → V,
    omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two
        (fun | none => unit | some i => a i) =
      pairing.form (a 0) (a 1)

namespace TwoDimensionalTFT

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- Restrict a two-dimensional TFT to its stable arities,
producing a scalar-valued topological CohFT.-/
def toTopologicalCohFT (T : TwoDimensionalTFT R V) :
    TopologicalCohFT R V where
  pairing := T.pairing
  unit := T.unit
  omega := fun g S _ _ ↦ T.correlator g S
  relabel := fun g S U _ _ _ _ e ↦ T.relabel g S U e
  unit_insert := fun g S _ _ a ↦ T.unit_insert g S a
  nonseparating := fun g S _ _ ↦ T.nonseparating g S
  separating := fun g₁ g₂ S U _ _ _ _ ↦ T.separating g₁ g₂ S U
  normalization := by
    intro a
    convert (T.unit_insert 0 (Fin 2) a).trans (T.normalization a) using 1
    congr 1
    funext x
    rcases x with _ | i <;> rfl

end TwoDimensionalTFT

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- The scalar-valued topological CohFT associated to a commutative Frobenius
algebra.-/
noncomputable def toTopologicalCohFT (F : CommFrobeniusAlgebra R A) :
    TopologicalCohFT R A :=
  F.toTwoDimensionalTFT.toTopologicalCohFT

end CommFrobeniusAlgebra

end AxiomaticGW
