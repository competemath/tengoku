/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.GW.Descendants.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descendant--ancestor comparison

Mathematically, stable-map and stable-curve cotangent classes differ on loci
contracted by stabilization. The current interface records only their
residual difference. It does not encode support on boundary strata,
factorization, or a derivation from a stabilization morphism.
-/

@[expose] public section

namespace AxiomaticGW

universe u

/-- A residual decomposition comparing stabilized stable-map descendants
with stable-curve ancestors. This structure alone does not certify that the
residual is geometrically boundary-supported.-/
structure DescendantAncestorComparison
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    (P : PsiClasses C) (M : StableMapDescendants Omega) where
  /-- Residual difference. The field name is retained for API compatibility;
  no boundary-support property is part of its type.-/
  boundaryCorrection : ∀ (g : ℕ) (S : Type) [Fintype S]
    (_h : StableArity g S), B → (S → ℕ) →
      MultilinearMap R (fun _ : S ↦ V) (C.H g S)
  /-- Stable-map descendants equal ancestors plus the recorded residual.-/
  comparison : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (k : S → ℕ),
    M.descendantClass g S h beta k =
      Omega.ancestorClass P g S h beta k +
        boundaryCorrection g S h beta k

namespace DescendantAncestorComparison

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {P : PsiClasses C} {M : StableMapDescendants Omega}

/-- The recorded residual is uniquely the descendant class minus the ancestor
class. This makes explicit that the weak comparison structure alone carries no
additional boundary-support information.
@isnad1 id=eq.1h13v.s10.889e7cb93739 from=translated src=- shape=3aebf6b0 vocab=c41d429a
-/
theorem boundaryCorrection_eq_sub
    (X : DescendantAncestorComparison P M) (g : ℕ) (S : Type)
    [Fintype S] (h : StableArity g S) (beta : B) (k : S → ℕ) :
    X.boundaryCorrection g S h beta k =
      M.descendantClass g S h beta k -
        Omega.ancestorClass P g S h beta k := by
  apply eq_sub_of_add_eq
  rw [add_comm]
  exact (X.comparison g S h beta k).symm

/-- The residual vanishes when every cotangent power is zero.
@isnad1 id=eq.1h12v.s9.18d7df8ebafe from=translated src=- shape=9361a27d vocab=e2aac775
-/
theorem boundaryCorrection_zero (X : DescendantAncestorComparison P M)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (beta : B) :
    X.boundaryCorrection g S h beta (fun _ ↦ 0) = 0 := by
  have hcomparison := X.comparison g S h beta (fun _ ↦ 0)
  rw [M.descendantClass_zero, Omega.ancestorClass_zero] at hcomparison
  have hsubtract := congrArg
    (fun f ↦ f - Omega.omega g S h beta) hcomparison
  simpa only [add_sub_cancel_left, sub_self] using hsubtract.symm

/-- The residual is natural under simultaneous relabelling of markings,
powers, and state-space inputs.
@isnad1 id=eq.2h15v.s9.78ca94aa8e2f from=translated src=- shape=50394cb4 vocab=b853358f
-/
theorem boundaryCorrection_relabel
    (X : DescendantAncestorComparison P M) (g : ℕ) (S T : Type)
    [Fintype S] [Fintype T] (hS : StableArity g S)
    (hT : StableArity g T) (e : S ≃ T) (beta : B) (k : S → ℕ) :
    (C.rename g S T hS hT e).toLinearMap.compMultilinearMap
        ((X.boundaryCorrection g S hS beta k).domDomCongr e) =
      X.boundaryCorrection g T hT beta (fun t ↦ k (e.symm t)) := by
  rw [X.boundaryCorrection_eq_sub, X.boundaryCorrection_eq_sub]
  apply MultilinearMap.ext
  intro a
  simp only [LinearMap.compMultilinearMap_apply,
    MultilinearMap.domDomCongr_apply, sub_apply, map_sub]
  have hdescendant := congrArg (fun f ↦ f a)
    (M.relabel g S T hS hT e beta k)
  have hancestor := congrArg (fun f ↦ f a)
    (Omega.ancestorClass_relabel P g S T hS hT e beta k)
  exact congrArg₂ (fun x y ↦ x - y) hdescendant hancestor

/-- For homogeneous inputs, the residual has the same total codimension as
the descendant and ancestor classes it compares.
@isnad1 id=mem.3h16v.s10.59e2b4b65477 from=translated src=- shape=590e8bb4 vocab=752fdc42
-/
theorem boundaryCorrection_degree
    (X : DescendantAncestorComparison P M) (g : ℕ) (S : Type)
    [Fintype S] (h : StableArity g S) (beta : B) (k p : S → ℕ)
    (a : S → V) (q : ℕ) (ha : ∀ s, a s ∈ Omega.graded.degree (p s))
    (hq : GWOutputDegree Omega.graded.dimension g
      ((∑ s, p s) + ∑ s, k s) q (Omega.c1Degree beta)) :
    X.boundaryCorrection g S h beta k a ∈ (C.H g S).degree q := by
  rw [X.boundaryCorrection_eq_sub]
  exact Submodule.sub_mem _
    (M.descendant_total_degree g S h beta k p a q ha hq)
    (Omega.ancestorClass_total_degree P g S h beta k p a q ha hq)

/-- Integrating the residual decomposition gives the numerical
descendant--ancestor identity.
@isnad1 id=eq.1h14v.s9.2c090e3076fd from=translated src=- shape=e2d7749f vocab=ca2f0b6b
-/
theorem invariant_eq_ancestor_add_boundary
    (X : DescendantAncestorComparison P M) (I : StableCurveIntegration C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (k : S → ℕ) :
    M.invariant I g S h beta k =
      Omega.ancestorInvariant P I g S h beta k +
        (I.integrate g S h).compMultilinearMap
          (X.boundaryCorrection g S h beta k) := by
  apply MultilinearMap.ext
  intro a
  change I.integrate g S h (M.descendantClass g S h beta k a) =
    I.integrate g S h (Omega.ancestorClass P g S h beta k a) +
      I.integrate g S h (X.boundaryCorrection g S h beta k a)
  have hcomparison := congrArg (fun f ↦ f a) (X.comparison g S h beta k)
  rw [hcomparison]
  change I.integrate g S h
      (Omega.ancestorClass P g S h beta k a +
        X.boundaryCorrection g S h beta k a) = _
  rw [map_add]

end DescendantAncestorComparison

end AxiomaticGW
