/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.CohFT.Ancestors
public import Tengoku.Axiomaticgw.AxiomaticGW.Frobenius.Examples
public import Tengoku.Seed.Algebra.BigOperators.Finprod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The point target and intersections on stable-curve moduli

For a point target the state space is the coefficient ring, the primary class
is the unit class, and ancestors are exactly psi-class intersection numbers on
`Mbar(g,S)`. The final definition states the all-genus DVV recursion as the
additional tautological relation that a geometric stable-curve model must
prove; it is not derivable from the primitive psi pullback rules alone.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

universe u

namespace PointTarget

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R}

/-- The point-target primary class. Its scalar value is the product of all
state-space inputs, embedded as a degree-zero stable-curve class.-/
noncomputable def primaryClass (g : ℕ) (S : Type) [Fintype S]
    (_h : StableArity g S) :
    MultilinearMap R (fun _ : S ↦ R) (C.H g S) :=
  (Algebra.linearMap R (C.H g S)).compMultilinearMap
    ((CommFrobeniusAlgebra.baseRing R).correlator g S)

/--
@isnad1 id=eq.1h5v.s9.8ef94a0e5bd4 from=translated src=- shape=b9558545 vocab=62ddb8df
-/
@[simp]
theorem primaryClass_apply (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (a : S → R) :
    primaryClass (C := C) g S h a = algebraMap R (C.H g S) (∏ s, a s) := by
  simp only [primaryClass, LinearMap.compMultilinearMap_apply,
    CommFrobeniusAlgebra.correlator_apply,
    CommFrobeniusAlgebra.baseRing_handleElement, one_pow, mul_one,
    CommFrobeniusAlgebra.baseRing_counit_apply, Algebra.linearMap_apply,
    map_prod]

/-- A stable point-target psi-class intersection number.-/
noncomputable def intersectionNumber (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (k : S → ℕ) : R := by
  classical
  exact if h : StableArity g S then
    I.integrate g S h (P.monomial g S h k)
  else 0

/--
@isnad1 id=eq.1h7v.s8.5d1eff4a7f71 from=translated src=- shape=8676ad3c vocab=8f3bc86a
-/
@[simp]
theorem intersectionNumber_of_stable (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (k : S → ℕ) :
    intersectionNumber P I g S k =
      I.integrate g S h (P.monomial g S h k) := by
  simp only [intersectionNumber, h, ↓reduceDIte]

/--
@isnad1 id=eq.1h7v.s6.e5b49e0ceec0 from=translated src=- shape=d3888462 vocab=2b309946
-/
@[simp]
theorem intersectionNumber_of_unstable (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : ¬StableArity g S) (k : S → ℕ) :
    intersectionNumber P I g S k = 0 := by
  simp only [intersectionNumber, h, ↓reduceDIte]

/-- Point-target ancestors: primary inputs multiply the psi-class intersection
number.-/
noncomputable def ancestor (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (k : S → ℕ) :
    MultilinearMap R (fun _ : S ↦ R) R :=
  (I.integrate g S h).compMultilinearMap
    ((CohFT.multiplyPsi P g S h k).compMultilinearMap
      (primaryClass (C := C) g S h))

/--
@isnad1 id=eq.1h8v.s7.2d8c9a5cf35b from=translated src=- shape=8c271a3e vocab=c8452bc5
-/
@[simp]
theorem ancestor_apply (P : PsiClasses C) (I : StableCurveIntegration C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (k : S → ℕ) (a : S → R) :
    ancestor P I g S h k a =
      (∏ s, a s) * intersectionNumber P I g S k := by
  rw [intersectionNumber_of_stable P I g S h]
  simp only [ancestor, LinearMap.compMultilinearMap_apply,
    CohFT.multiplyPsi, primaryClass_apply]
  change I.integrate g S h
      (algebraMap R (C.H g S) (∏ s, a s) * P.monomial g S h k) = _
  rw [← Algebra.smul_def, map_smul]
  rfl

/-- Relabelling the marked points does not change a point intersection
number.
@isnad1 id=eq.2h9v.s6.eaeac7659dce from=translated src=- shape=9e6ce0cb vocab=a7099e4b
-/
theorem intersectionNumber_relabel (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S T : Type)
    [Fintype S] [Fintype T] (hS : StableArity g S)
    (hT : StableArity g T) (e : S ≃ T) (k : S → ℕ) :
    intersectionNumber P I g T (fun t ↦ k (e.symm t)) =
      intersectionNumber P I g S k := by
  rw [intersectionNumber_of_stable P I g T hT,
    intersectionNumber_of_stable P I g S hS]
  rw [← P.rename_monomial g S T hS hT e k]
  exact I.integrate_rename g S T hS hT e _

/-- A point-target psi-class intersection number vanishes unless the psi codimension
equals the dimension of `Mbar(g,S)`.
@isnad1 id=eq.2h7v.s6.72daf94809bb from=translated src=- shape=f9751d09 vocab=336ca636
-/
theorem intersectionNumber_eq_zero_of_degree_ne (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (k : S → ℕ)
    (hne : (∑ s, k s) ≠ StableArity.dimension g S) :
    intersectionNumber P I g S k = 0 := by
  rw [intersectionNumber_of_stable P I g S h]
  exact I.integrate_of_degree_ne g S h (∑ s, k s)
    (P.monomial g S h k) (P.monomial_degree g S h k) hne

/-- The normalized zero-dimensional point intersection is
`<tau_0 tau_0 tau_0>_0 = 1`.
@isnad1 id=eq.1h4v.s9.68c7ba0cb2d0 from=translated src=- shape=2c683705 vocab=d7941fc5
-/
theorem intersectionNumber_zero_three (P : PsiClasses C)
    (I : StableCurveIntegration C)
    (hI : I.integrate 0 (Fin 3) StableArity.zero_fin_three 1 = 1) :
    intersectionNumber P I 0 (Fin 3) (fun _ ↦ 0) = 1 := by
  rw [intersectionNumber_of_stable P I 0 (Fin 3)
    StableArity.zero_fin_three]
  simpa only [PsiClasses.monomial_zero] using hI

/-- One marked point in genus one is stable.
@isnad1 id=stablear.0h0v.s4.201f3f31d5ab from=translated src=- shape=648e8daf vocab=e101b635
-/
theorem genusOne_one_stable : StableArity 1 (Fin 1) := by
  simp only [StableArity, mul_one, Fintype.card_unique, Nat.reduceAdd,
    Std.le_refl]

/-- The exceptional initial value needed alongside DVV is
`<tau_1>_1 = 1/24`. The hypothesis isolates the corresponding geometric
intersection calculation.
@isnad1 id=eq.1h4v.s9.c3f4a5880732 from=translated src=- shape=30f2b2e2 vocab=3054b7a2
-/
theorem intersectionNumber_one_one (P : PsiClasses C)
    (I : StableCurveIntegration C)
    (hI : I.integrate 1 (Fin 1) genusOne_one_stable
      (P.psi 1 (Fin 1) genusOne_one_stable 0) =
        algebraMap ℚ R (1 / 24 : ℚ)) :
    intersectionNumber P I 1 (Fin 1) (fun _ ↦ 1) =
      algebraMap ℚ R (1 / 24 : ℚ) := by
  rw [intersectionNumber_of_stable P I 1 (Fin 1) genusOne_one_stable]
  simpa only [PsiClasses.monomial, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, pow_one, Finset.prod_singleton, one_div]
    using hI

/-- The point primary class passes the `Mbar(0,4)` WDVV boundary test: both
boundary restrictions of the unit class agree.
@isnad1 id=eq.0h3v.s13.523d559513c3 from=translated src=- shape=27075917 vocab=aecb233a
-/
theorem unitClass_wdvv (G : GenusZeroGeometry C) :
    (C.separating 0 0 (Fin 2) (Fin 2)
      StableArity.zero_option_fin_two StableArity.zero_option_fin_two)
        (C.rename 0 (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
          (StableArity.separating StableArity.zero_option_fin_two
            StableArity.zero_option_fin_two)
          (StableArity.separating StableArity.zero_option_fin_two
            StableArity.zero_option_fin_two)
          wdvvPermutation 1) =
      (C.separating 0 0 (Fin 2) (Fin 2)
        StableArity.zero_option_fin_two StableArity.zero_option_fin_two) 1 := by
  have h := congrArg
    (fun f ↦ f (1 : C.H 0 (Fin 2 ⊕ Fin 2))) G.mbarZeroFourBoundary
  exact h

/-- The odd double factorial `(2n+1)!!`.-/
def oddDoubleFactorial (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range (n + 1), (2 * j + 1)

/-- Coefficient for merging `tau_(k+1)` with `tau_d` in the DVV recursion.-/
def dvvMergeWeight (k d : ℕ) : ℚ :=
  (oddDoubleFactorial (k + d) : ℚ) /
    if d = 0 then 1 else oddDoubleFactorial (d - 1)

/-- The all-genus DVV recursion for point-target psi-class intersections.

The intersection-number definition supplies the unstable value `0`; the
formula therefore includes stable and unstable splittings uniformly. A
geometric model of stable curves should prove this proposition from the DVV
tautological relation.-/
def DVVRecursion (P : PsiClasses C) (I : StableCurveIntegration C) : Prop :=
  ∀ (g k : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (_h : StableArity g S) (d : S → ℕ),
    algebraMap ℚ R (oddDoubleFactorial (k + 1) : ℚ) *
        intersectionNumber P I g (Option S)
          (fun | none => k + 1 | some s => d s) =
      (∑ s, algebraMap ℚ R (dvvMergeWeight k (d s)) *
        intersectionNumber P I g S (Function.update d s (d s + k))) +
      algebraMap ℚ R (1 / 2 : ℚ) *
        (if _hk : k = 0 then (0 : R) else
          ∑ ab ∈ Finset.antidiagonal (k - 1),
            algebraMap ℚ R
                ((oddDoubleFactorial ab.1 : ℚ) *
                  oddDoubleFactorial ab.2) *
              ((if _hg : g = 0 then (0 : R) else
                  intersectionNumber P I (g - 1) (Option (Option S))
                    (fun x ↦ match x with
                      | none => ab.1
                      | some none => ab.2
                      | some (some s) => d s)) +
                ∑ T ∈ (Finset.univ : Finset S).powerset,
                  ∑ g₁ ∈ Finset.range (g + 1),
                    intersectionNumber P I g₁ (Option {s // s ∈ T})
                        (fun | none => ab.1 | some s => d s.1) *
                      intersectionNumber P I (g - g₁)
                        (Option {s // s ∈ (Finset.univ : Finset S) \ T})
                        (fun | none => ab.2 | some s => d s.1)))

end PointTarget

end AxiomaticGW
