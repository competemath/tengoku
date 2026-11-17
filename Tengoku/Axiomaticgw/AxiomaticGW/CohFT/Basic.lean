/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.CohFT.StableCurve
public import Tengoku.Axiomaticgw.AxiomaticGW.Linear.Contraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Full unital cohomological field theories

The state space is intentionally ungraded in this foundational interface. The
stable-curve targets retain their internal codimension grading, and a later
`GradedCohFT` extension adds state-space grading without changing these maps.
-/

@[expose] public section

namespace AxiomaticGW

/-- A full all-genus unital CohFT valued in an abstract stable-curve
cohomology system.-/
structure CohFT (R V : Type*) [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (C : StableCurveCohomology R) where
  /-- The metric used to contract every node.-/
  pairing : SymmetricPerfectPairing R V
  /-- The flat unit.-/
  unit : V
  /-- The cohomology-valued class assigned to a stable genus and label type.-/
  omega : (g : ℕ) → (S : Type) → [Fintype S] → (h : StableArity g S) →
    MultilinearMap R (fun _ : S ↦ V) (C.H g S)
  /-- Simultaneous relabelling of markings and multilinear inputs.-/
  relabel : ∀ (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T),
    (C.rename g S T hS hT e).toLinearMap.compMultilinearMap
        ((omega g S hS).domDomCongr e) =
      omega g T hT
  /-- Inserting the flat unit is pullback along the forgetful map.-/
  unit_insert : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (a : S → V),
    omega g (Option S) (StableArity.option h)
        (fun | none => unit | some s => a s) =
      C.forget g S h (omega g S h a)
  /-- Pullback to a nonseparating boundary equals contraction of its two node
  insertions.-/
  nonseparating : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity (g + 1) S),
    pairing.selfContractTarget
        ((omega g (Option (Option S)) (StableArity.double_option_iff.mpr h)).domDomCongr
          (doubleOptionEquiv S)) =
      (C.nonseparating g S h).toLinearMap.compMultilinearMap
        (omega (g + 1) S h)
  /-- Pullback to a separating boundary equals contraction of the two component
  classes against the copairing.-/
  separating : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T)),
    pairing.pairContractTarget (omega g₁ (Option S) h₁)
        (omega g₂ (Option T) h₂) =
      (C.separating g₁ g₂ S T h₁ h₂).toLinearMap.compMultilinearMap
        (omega (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂))
  /-- The stable three-point class with one unit insertion is the metric times
  the cohomological unit.-/
  normalization : ∀ a : Fin 2 → V,
    omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two
        (fun | none => unit | some i => a i) =
      algebraMap R (C.H 0 (Option (Fin 2))) (pairing.form (a 0) (a 1))

/-- Reusable grading data for a state space with a fixed metric and unit. The
pairing has complementary codimension degree `dimension`, as for Poincare
duality on a complex manifold.-/
structure GradedStateSpace (R V : Type*) [CommRing R]
    [AddCommGroup V] [Module R V]
    (pairing : SymmetricPerfectPairing R V) (unit : V) where
  /-- Complex dimension governing complementary degrees.-/
  dimension : ℕ
  /-- Codimension grading of the state space.-/
  degree : ℕ → Submodule R V
  /-- Every state has a finite homogeneous decomposition.-/
  [decomposition : DirectSum.Decomposition degree]
  /-- The distinguished unit has codimension degree zero.-/
  unit_mem_degree_zero : unit ∈ degree 0
  /-- The metric vanishes unless the two codimensions are complementary.-/
  pairing_vanishes : ∀ {p q : ℕ} {x y : V},
    x ∈ degree p → y ∈ degree q → p + q ≠ dimension → pairing.form x y = 0

/-- State-space grading attached to a bare CohFT without changing its class
maps or axioms.-/
structure GradedCohFT {R V : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {C : StableCurveCohomology R} (Ω : CohFT R V C) extends
      GradedStateSpace R V Ω.pairing Ω.unit

end AxiomaticGW
