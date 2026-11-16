/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.GW.Basic
public import Tengoku.Axiomaticgw.AxiomaticGW.Frobenius.Examples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Constant curve-class-resolved GW theory

The first model of the coefficientwise GW interface places the base-ring
topological CohFT in curve class zero.
-/

@[expose] public section

namespace AxiomaticGW

universe u

namespace EffectiveCurveMonoid

variable {B : Type u} [AddCancelCommMonoid B]

/-- A beta-zero family of multilinear maps.-/
noncomputable def atZero {R V H : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommMonoid H] [Module R H]
    {S : Type}
    (f : MultilinearMap R (fun _ : S ↦ V) H) (beta : B) :
    MultilinearMap R (fun _ : S ↦ V) H := by
  classical
  exact if beta = 0 then f else 0

@[simp]
theorem atZero_zero {R V H : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommMonoid H] [Module R H]
    {S : Type}
    (f : MultilinearMap R (fun _ : S ↦ V) H) :
    atZero f (0 : B) = f := by
  simp only [atZero, ↓reduceIte]

@[simp]
theorem atZero_of_ne {R V H : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommMonoid H] [Module R H]
    {S : Type}
    (f : MultilinearMap R (fun _ : S ↦ V) H) {beta : B} (h : beta ≠ 0) :
    atZero f beta = 0 := by
  simp only [atZero, h, ↓reduceIte]

end EffectiveCurveMonoid

namespace constantGromovWittenTheory

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  {B : Type u} [AddCancelCommMonoid B]

/-- The base-ring topological CohFT used by the reference theory.-/
noncomputable def topological : TopologicalCohFT R R :=
  (CommFrobeniusAlgebra.baseRing R).toTopologicalCohFT

/-- The base-ring theory promoted to the constant stable-curve target.-/
noncomputable def cohft :
    CohFT R R (constantStableCurveCohomology R) :=
  (topological R).toConstantCohFT

/-- The base ring has the grading concentrated in codimension zero.-/
noncomputable def gradedState :
    GradedStateSpace R R (cohft R).pairing (cohft R).unit where
  dimension := 0
  degree := constantDegree R
  decomposition := constantDegree.decomposition R
  unit_mem_degree_zero := by
    simp only [constantDegree, ↓reduceIte, cohft, topological,
      Submodule.mem_top]
  pairing_vanishes := by
    intro p q x y hx hy hpq
    have hp_or_hq : p ≠ 0 ∨ q ≠ 0 := by omega
    rcases hp_or_hq with hp | hq
    · have hx0 : x = 0 := by
        simpa only [constantDegree, hp, ↓reduceIte, Submodule.mem_bot]
          using hx
      subst x
      simp only [map_zero, LinearMap.zero_apply]
    · have hy0 : y = 0 := by
        simpa only [constantDegree, hq, ↓reduceIte, Submodule.mem_bot]
          using hy
      subst y
      simp only [map_zero]

/-- The constant primary GW theory is supported only at beta zero.-/
noncomputable def theory (D : EffectiveCurveMonoid B) :
    GromovWittenTheory R R B D (constantStableCurveCohomology R) where
  pairing := (cohft R).pairing
  unit := (cohft R).unit
  graded := gradedState R
  c1Degree := 0
  omega := fun g S _ h beta ↦
    EffectiveCurveMonoid.atZero ((cohft R).omega g S h) beta
  relabel := by
    intro g S T _ _ hS hT e beta
    by_cases hbeta : beta = 0
    · subst beta
      simpa only [EffectiveCurveMonoid.atZero_zero]
        using (cohft R).relabel g S T hS hT e
    · simp only [EffectiveCurveMonoid.atZero_of_ne _ hbeta]
      apply MultilinearMap.ext
      intro a
      simp only [LinearMap.compMultilinearMap_apply,
        MultilinearMap.domDomCongr_apply, zero_apply,
        AlgEquiv.toLinearMap_apply, AlgEquiv.coe_refl, id_eq]
  unit_insert := by
    intro g S _ h beta a
    by_cases hbeta : beta = 0
    · subst beta
      simp only [EffectiveCurveMonoid.atZero_zero]
      change (cohft R).omega g (Option S) (StableArity.option h)
          (fun | none => (cohft R).unit | some s => a s) =
        (constantStableCurveCohomology R).forget g S h
          ((cohft R).omega g S h a)
      exact (cohft R).unit_insert g S h a
    · simp only [EffectiveCurveMonoid.atZero, hbeta, ↓reduceIte, zero_apply,
        AlgHom.coe_id, id_eq]
  nonseparating := by
    intro g S _ h beta
    by_cases hbeta : beta = 0
    · subst beta
      simpa only [EffectiveCurveMonoid.atZero_zero, AlgHom.toLinearMap_id,
        LinearMap.id_compMultilinearMap]
        using (cohft R).nonseparating g S h
    · simp only [EffectiveCurveMonoid.atZero_of_ne _ hbeta]
      apply MultilinearMap.ext
      intro a
      rw [SymmetricPerfectPairing.selfContractTarget_apply]
      rw [show ((MultilinearMap.domDomCongr (doubleOptionEquiv S) 0).currySum a) = 0 by
        apply MultilinearMap.ext
        intro b
        simp only [MultilinearMap.currySum_apply',
          MultilinearMap.domDomCongr_apply, zero_apply]]
      exact map_zero _
  separating := by
    intro g₁ g₂ S T _ _ h₁ h₂ beta
    by_cases hbeta : beta = 0
    · subst beta
      simp only [D.splittings_zero, Finset.sum_singleton,
        EffectiveCurveMonoid.atZero_zero]
      exact (cohft R).separating g₁ g₂ S T h₁ h₂
    · have hsum : (∑ split ∈ D.splittings beta,
          (cohft R).pairing.pairContractTarget
            (EffectiveCurveMonoid.atZero
              ((cohft R).omega g₁ (Option S) h₁) split.1)
            (EffectiveCurveMonoid.atZero
              ((cohft R).omega g₂ (Option T) h₂) split.2)) = 0 := by
        apply Finset.sum_eq_zero
        intro split hsplit
        have hadd := (D.mem_splittings split.1 split.2 beta).mp hsplit
        by_cases h₁zero : split.1 = 0
        · have h₂ne : split.2 ≠ 0 := by
            intro h₂zero
            apply hbeta
            simpa only [h₁zero, h₂zero, add_zero] using hadd.symm
          rw [EffectiveCurveMonoid.atZero_of_ne _ h₂ne]
          apply MultilinearMap.ext
          intro a
          rw [SymmetricPerfectPairing.pairContractTarget_apply]
          rw [show
              (((EffectiveCurveMonoid.atZero
                ((cohft R).omega g₁ (Option S) h₁) split.1).domCoprod 0).domDomCongr
                  (SymmetricPerfectPairing.separatingLabelsEquiv S T)).currySum a = 0 by
            apply MultilinearMap.ext
            intro b
            simp only [MultilinearMap.currySum_apply',
              MultilinearMap.domDomCongr_apply,
              MultilinearMap.domCoprod_apply, zero_apply,
              TensorProduct.tmul_zero]]
          exact map_zero _
        · rw [EffectiveCurveMonoid.atZero_of_ne _ h₁zero]
          apply MultilinearMap.ext
          intro a
          rw [SymmetricPerfectPairing.pairContractTarget_apply]
          rw [show
              ((MultilinearMap.domCoprod 0
                (EffectiveCurveMonoid.atZero
                  ((cohft R).omega g₂ (Option T) h₂) split.2)).domDomCongr
                    (SymmetricPerfectPairing.separatingLabelsEquiv S T)).currySum a = 0 by
            apply MultilinearMap.ext
            intro b
            simp only [MultilinearMap.currySum_apply',
              MultilinearMap.domDomCongr_apply,
              MultilinearMap.domCoprod_apply, zero_apply,
              TensorProduct.zero_tmul]]
          exact map_zero _
      rw [hsum]
      simp only [Algebra.TensorProduct.toLinearMap_includeLeft,
        EffectiveCurveMonoid.atZero, hbeta, ↓reduceIte,
        LinearMap.compMultilinearMap_zero]
  normalization_zero := by
    intro a
    simp only [EffectiveCurveMonoid.atZero_zero]
    change (cohft R).omega 0 (Option (Fin 2))
        StableArity.zero_option_fin_two
        (fun | none => (cohft R).unit | some i => a i) =
      algebraMap R ((constantStableCurveCohomology R).H 0 (Option (Fin 2)))
        ((cohft R).pairing.form (a 0) (a 1))
    exact (cohft R).normalization a
  normalization_nonzero := by
    intro beta hbeta a
    simp only [EffectiveCurveMonoid.atZero, hbeta, ↓reduceIte, zero_apply]
  omega_degree := by
    intro g S _ h beta p a q ha hdegree
    by_cases hbeta : beta = 0
    · subst beta
      simp only [EffectiveCurveMonoid.atZero_zero]
      by_cases hp : ∀ s, p s = 0
      · have hq : q = 0 := by
          simp only [GWOutputDegree, map_zero, gradedState] at hdegree
          have hsum : ∑ s, p s = 0 := by
            simp only [hp, Finset.sum_const_zero]
          omega
        subst q
        simp only [constantDegree, ↓reduceIte, Submodule.mem_top]
      · obtain ⟨s, hs⟩ := not_forall.mp hp
        have has : a s = 0 := by
          have hsMem := ha s
          change a s ∈ constantDegree R (p s) at hsMem
          simpa only [constantDegree, hs, ↓reduceIte, Submodule.mem_bot]
            using hsMem
        rw [(cohft R).omega g S h |>.map_coord_zero s has]
        exact Submodule.zero_mem _
    · rw [EffectiveCurveMonoid.atZero_of_ne _ hbeta]
      exact Submodule.zero_mem _
  omega_eq_zero_of_negative := by
    intro g S _ h beta p a ha hnegative
    change ((∑ s, p s : ℕ) : ℤ) + (g : ℤ) * 0 < 0 + 0 at hnegative
    omega

@[simp]
theorem theory_omega_zero (D : EffectiveCurveMonoid B)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) :
    (theory R D).omega g S h 0 = (cohft R).omega g S h := by
  simp only [theory, EffectiveCurveMonoid.atZero_zero]

end constantGromovWittenTheory

end AxiomaticGW
