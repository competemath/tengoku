/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.GW.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stable-map descendants and stable-curve ancestors

Ancestor classes use cotangent lines on stable curves. Stable-map descendants
are separate pushed-forward classes and agree with the primary theory only when
all powers vanish.
-/

@[expose] public section

namespace AxiomaticGW

universe u

namespace GromovWittenTheory

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R}

/-- A curve-class-resolved ancestor class, formed with stable-curve `psi`.-/
def ancestorClass (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k : S → ℕ) :
    MultilinearMap R (fun _ : S ↦ V) (C.H g S) :=
  (CohFT.multiplyPsi P g S h k).compMultilinearMap
    (Omega.omega g S h beta)

@[simp]
theorem ancestorClass_apply (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k : S → ℕ) (a : S → V) :
    Omega.ancestorClass P g S h beta k a =
      Omega.omega g S h beta a * P.monomial g S h k := rfl

@[simp]
theorem ancestorClass_zero (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) :
    Omega.ancestorClass P g S h beta (fun _ ↦ 0) =
      Omega.omega g S h beta := by
  apply MultilinearMap.ext
  intro a
  simp only [ancestorClass_apply, PsiClasses.monomial_zero, mul_one]

/-- Relabelling transports markings, ancestor powers, and inputs together.-/
theorem ancestorClass_relabel (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T)
    (beta : B) (k : S → ℕ) :
    (C.rename g S T hS hT e).toLinearMap.compMultilinearMap
        ((Omega.ancestorClass P g S hS beta k).domDomCongr e) =
      Omega.ancestorClass P g T hT beta (fun t ↦ k (e.symm t)) := by
  ext a
  change C.rename g S T hS hT e
      (Omega.ancestorClass P g S hS beta k (fun s ↦ a (e s))) =
    Omega.ancestorClass P g T hT beta (fun t ↦ k (e.symm t)) a
  rw [ancestorClass_apply, ancestorClass_apply]
  rw [map_mul, P.rename_monomial]
  have homega := congrArg (fun f ↦ f a)
    (Omega.relabel g S T hS hT e beta)
  exact homega ▸ rfl

/-- Ancestor powers add their codimension to the primary output degree.-/
theorem ancestorClass_degree (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k p : S → ℕ) (a : S → V) (q : ℕ)
    (ha : ∀ s, a s ∈ Omega.graded.degree (p s))
    (hq : GWOutputDegree Omega.graded.dimension g (∑ s, p s) q
      (Omega.c1Degree beta)) :
    Omega.ancestorClass P g S h beta k a ∈
      (C.H g S).degree (q + ∑ s, k s) := by
  apply SetLike.mul_mem_graded
  · exact Omega.omega_degree g S h beta p a q ha hq
  · exact P.monomial_degree g S h k

/-- Ancestor classes vanish when the primary expected codimension is
negative; stable-curve psi powers are multiplied only after stabilization.-/
theorem ancestorClass_eq_zero_of_negative (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k p : S → ℕ) (a : S → V)
    (ha : ∀ s, a s ∈ Omega.graded.degree (p s))
    (hnegative : ((∑ s, p s : ℕ) : ℤ) +
        (g : ℤ) * (Omega.graded.dimension : ℤ) <
      (Omega.graded.dimension : ℤ) + Omega.c1Degree beta) :
    Omega.ancestorClass P g S h beta k a = 0 := by
  rw [ancestorClass_apply,
    Omega.omega_eq_zero_of_negative g S h beta p a ha hnegative, zero_mul]

/-- Ancestor classes satisfy the total codimension rule. If the psi
powers would require a negative primary degree, the primary class vanishes.-/
theorem ancestorClass_total_degree (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k p : S → ℕ) (a : S → V)
    (q : ℕ) (ha : ∀ s, a s ∈ Omega.graded.degree (p s))
    (hq : GWOutputDegree Omega.graded.dimension g
      ((∑ s, p s) + ∑ s, k s) q (Omega.c1Degree beta)) :
    Omega.ancestorClass P g S h beta k a ∈ (C.H g S).degree q := by
  by_cases hk : (∑ s, k s) ≤ q
  · have hprimary : GWOutputDegree Omega.graded.dimension g (∑ s, p s)
        (q - ∑ s, k s) (Omega.c1Degree beta) := by
      unfold GWOutputDegree at hq ⊢
      rw [Nat.cast_sub hk]
      omega
    have hdegree := Omega.ancestorClass_degree P g S h beta k p a
      (q - ∑ s, k s) ha hprimary
    simpa only [ancestorClass_apply, Nat.sub_add_cancel hk] using hdegree
  · have hnegative : ((∑ s, p s : ℕ) : ℤ) +
        (g : ℤ) * (Omega.graded.dimension : ℤ) <
      (Omega.graded.dimension : ℤ) + Omega.c1Degree beta := by
      unfold GWOutputDegree at hq
      omega
    rw [Omega.ancestorClass_eq_zero_of_negative P g S h beta k p a ha
      hnegative]
    exact Submodule.zero_mem _

/-- Numerical ancestor invariant in a fixed curve class.-/
def ancestorInvariant (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (k : S → ℕ) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  (I.integrate g S h).compMultilinearMap
    (Omega.ancestorClass P g S h beta k)

@[simp]
theorem ancestorInvariant_apply (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (k : S → ℕ) (a : S → V) :
    Omega.ancestorInvariant P I g S h beta k a =
      I.integrate g S h
        (Omega.omega g S h beta a * P.monomial g S h k) := rfl

/-- Numerical ancestor invariants are invariant under simultaneous
relabelling of markings, powers, and inputs.-/
theorem ancestorInvariant_relabel (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T)
    (beta : B) (k : S → ℕ) :
    (Omega.ancestorInvariant P I g S hS beta k).domDomCongr e =
      Omega.ancestorInvariant P I g T hT beta
        (fun t ↦ k (e.symm t)) := by
  ext a
  rw [MultilinearMap.domDomCongr_apply]
  simp only [ancestorInvariant_apply]
  rw [← I.integrate_rename g S T hS hT e]
  rw [map_mul, P.rename_monomial]
  have homega := congrArg (fun f ↦ f a)
    (Omega.relabel g S T hS hT e beta)
  exact homega ▸ rfl

/-- A homogeneous ancestor invariant vanishes unless its total codimension is
the dimension of the stable-curve space.-/
theorem ancestorInvariant_eq_zero_of_degree_ne
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k p : S → ℕ) (a : S → V) (q : ℕ)
    (ha : ∀ s, a s ∈ Omega.graded.degree (p s))
    (hq : GWOutputDegree Omega.graded.dimension g (∑ s, p s) q
      (Omega.c1Degree beta))
    (hne : q + ∑ s, k s ≠ StableArity.dimension g S) :
    Omega.ancestorInvariant P I g S h beta k a = 0 := by
  exact I.integrate_of_degree_ne g S h (q + ∑ s, k s)
    (Omega.ancestorClass P g S h beta k a)
    (Omega.ancestorClass_degree P g S h beta k p a q ha hq) hne

/-- A homogeneous ancestor invariant vanishes unless its total expected
codimension is the dimension of the stable-curve space.-/
theorem ancestorInvariant_eq_zero_of_total_degree_ne
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k p : S → ℕ) (a : S → V)
    (q : ℕ) (ha : ∀ s, a s ∈ Omega.graded.degree (p s))
    (hq : GWOutputDegree Omega.graded.dimension g
      ((∑ s, p s) + ∑ s, k s) q (Omega.c1Degree beta))
    (hne : q ≠ StableArity.dimension g S) :
    Omega.ancestorInvariant P I g S h beta k a = 0 := by
  exact I.integrate_of_degree_ne g S h q
    (Omega.ancestorClass P g S h beta k a)
    (Omega.ancestorClass_total_degree P g S h beta k p a q ha hq) hne

end GromovWittenTheory

/-- Stable-map descendant classes after stabilization to the stable-curve
target. This family is deliberately distinct from `PsiClasses`.-/
structure StableMapDescendants {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} (Omega : GromovWittenTheory R V B D C) where
  /-- Stabilized descendant class with stable-map cotangent powers `k`.-/
  descendantClass : ∀ (g : ℕ) (S : Type) [Fintype S]
    (_h : StableArity g S), B → (S → ℕ) →
      MultilinearMap R (fun _ : S ↦ V) (C.H g S)
  /-- Zero cotangent powers recover the primary GW class.-/
  descendantClass_zero : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B),
    descendantClass g S h beta (fun _ ↦ 0) = Omega.omega g S h beta
  /-- Relabelling transports markings, powers, and inputs together.-/
  relabel : ∀ (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (hS : StableArity g S) (hT : StableArity g T)
      (e : S ≃ T) (beta : B) (k : S → ℕ),
    (C.rename g S T hS hT e).toLinearMap.compMultilinearMap
        ((descendantClass g S hS beta k).domDomCongr e) =
      descendantClass g T hT beta (fun t ↦ k (e.symm t))
  /-- Stable-map descendant powers contribute to the total stabilized output
  degree, including when they compensate a negative primary degree.-/
  descendant_total_degree : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (k p : S → ℕ) (a : S → V) (q : ℕ),
    (∀ s, a s ∈ Omega.graded.degree (p s)) →
      GWOutputDegree Omega.graded.dimension g
        ((∑ s, p s) + ∑ s, k s) q
        (Omega.c1Degree beta) →
      descendantClass g S h beta k a ∈ (C.H g S).degree q
  /-- A stable-map descendant class vanishes when its total expected
  codimension, including psi powers, is negative.-/
  descendant_eq_zero_of_negative : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (k p : S → ℕ) (a : S → V),
    (∀ s, a s ∈ Omega.graded.degree (p s)) →
      ((∑ s, p s : ℕ) : ℤ) + ((∑ s, k s : ℕ) : ℤ) +
          (g : ℤ) * (Omega.graded.dimension : ℤ) <
        (Omega.graded.dimension : ℤ) + Omega.c1Degree beta →
      descendantClass g S h beta k a = 0

namespace StableMapDescendants

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}

/-- Compatibility form of the descendant degree law when the primary output
degree is already a natural number.-/
theorem descendant_degree (M : StableMapDescendants Omega)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (k p : S → ℕ) (a : S → V) (q : ℕ)
    (ha : ∀ s, a s ∈ Omega.graded.degree (p s))
    (hq : GWOutputDegree Omega.graded.dimension g (∑ s, p s) q
      (Omega.c1Degree beta)) :
    M.descendantClass g S h beta k a ∈
      (C.H g S).degree (q + ∑ s, k s) := by
  apply M.descendant_total_degree g S h beta k p a (q + ∑ s, k s) ha
  unfold GWOutputDegree at hq ⊢
  simp only [Nat.cast_add]
  omega

/-- Integrate a stabilized descendant class.-/
def invariant (M : StableMapDescendants Omega)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k : S → ℕ) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  (I.integrate g S h).compMultilinearMap
    (M.descendantClass g S h beta k)

@[simp]
theorem invariant_apply (M : StableMapDescendants Omega)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k : S → ℕ) (a : S → V) :
    M.invariant I g S h beta k a =
      I.integrate g S h (M.descendantClass g S h beta k a) := rfl

/-- Numerical stable-map descendant invariants are invariant under
simultaneous relabelling of markings, powers, and inputs.-/
theorem invariant_relabel (M : StableMapDescendants Omega)
    (I : StableCurveIntegration C) (g : ℕ) (S T : Type)
    [Fintype S] [Fintype T] (hS : StableArity g S)
    (hT : StableArity g T) (e : S ≃ T) (beta : B) (k : S → ℕ) :
    (M.invariant I g S hS beta k).domDomCongr e =
      M.invariant I g T hT beta (fun t ↦ k (e.symm t)) := by
  ext a
  rw [MultilinearMap.domDomCongr_apply]
  simp only [invariant_apply]
  rw [← I.integrate_rename g S T hS hT e]
  have hdescendant := congrArg (fun f ↦ f a)
    (M.relabel g S T hS hT e beta k)
  exact hdescendant ▸ rfl

@[simp]
theorem invariant_zero (M : StableMapDescendants Omega)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) :
    M.invariant I g S h beta (fun _ ↦ 0) =
      (I.integrate g S h).compMultilinearMap
        (Omega.omega g S h beta) := by
  simp only [invariant, M.descendantClass_zero]

end StableMapDescendants

end AxiomaticGW
