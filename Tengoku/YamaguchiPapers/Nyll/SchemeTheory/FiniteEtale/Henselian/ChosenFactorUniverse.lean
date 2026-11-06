/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenFactor.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A uniquely chosen finite etale factor in a separate universe

The strict-Henselian chosen-factor argument does not depend on the base and
factor carriers living in the same universe.  This file records the
universe-polymorphic form needed when the factor is a localization of an
integral closure in a generic tensor component.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Polynomial

universe uR uS

/-- A finite etale local algebra over a Henselian local ring with separably
closed residue field is the base, with independent carrier universes.-/
theorem
    algebraMap_bijective_of_henselian_of_isSepClosed_residue_of_finiteEtale_local_universe
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [IsLocalRing S]
    [Module.Finite R S] [FaithfulSMul R S] [Algebra.Etale R S]
    [IsSepClosed (IsLocalRing.ResidueField R)] :
    Function.Bijective (algebraMap R S) := by
  obtain ⟨β, hβ⟩ := IsLocalRing.exists_adjoin_eq_top (R := R) (S := S)
  let f : R[X] := minpoly R β
  have hfMonic : f.Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral β)
  obtain ⟨a₀, ha₀⟩ :=
    IsSepClosed.algebraMap_surjective
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
      (IsLocalRing.residue S β)
  have hfRootResidue : aeval a₀ f = 0 := by
    apply (algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)).injective
    rw [map_zero,
      Polynomial.map_aeval_eq_aeval_map
        (R := R) (S := IsLocalRing.ResidueField R)
        (T := IsLocalRing.ResidueField R)
        (U := IsLocalRing.ResidueField S)
        (φ := IsLocalRing.residue R)
        (ψ := algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S)) rfl f a₀,
      ha₀]
    rw [show f.map (IsLocalRing.residue R) =
        minpoly (IsLocalRing.ResidueField R)
          (IsLocalRing.residue S β) by
      simpa [f] using
        IsLocalRing.minpoly_map_residue (R := R) (S := S) hβ]
    exact minpoly.aeval _ _
  have hfDerivativeResidue : aeval a₀ f.derivative ≠ 0 := by
    intro hzero
    have hmap := congrArg
      (algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S)) hzero
    rw [map_zero,
      Polynomial.map_aeval_eq_aeval_map
        (R := R) (S := IsLocalRing.ResidueField R)
        (T := IsLocalRing.ResidueField R)
        (U := IsLocalRing.ResidueField S)
        (φ := IsLocalRing.residue R)
        (ψ := algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S)) rfl f.derivative a₀,
      ha₀] at hmap
    have hDerivativeMap :
        f.derivative.map (IsLocalRing.residue R) =
          (minpoly (IsLocalRing.ResidueField R)
            (IsLocalRing.residue S β)).derivative := by
      have hm :
          f.map (IsLocalRing.residue R) =
            minpoly (IsLocalRing.ResidueField R)
              (IsLocalRing.residue S β) := by
        simpa [f] using
          IsLocalRing.minpoly_map_residue (R := R) (S := S) hβ
      simpa [Polynomial.derivative_map] using
        congrArg Polynomial.derivative hm
    rw [hDerivativeMap] at hmap
    exact
      (Algebra.IsSeparable.isSeparable
        (IsLocalRing.ResidueField R)
        (IsLocalRing.residue S β)).aeval_derivative_ne_zero
          (minpoly.aeval _ _) hmap
  have hHensel := ((HenselianLocalRing.TFAE R).out 1 2).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨a, haRoot, haResidue⟩ :=
    hHensel f hfMonic a₀ hfRootResidue hfDerivativeResidue
  have hresidue :
      IsLocalRing.residue S (algebraMap R S a) =
        IsLocalRing.residue S β := by
    rw [← IsLocalRing.ResidueField.algebraMap_residue, haResidue, ha₀]
  have hnotUnit : ¬ IsUnit (β - algebraMap R S a) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp [hresidue]
  have hβImage : β = algebraMap R S a := by
    let g : S[X] := f.map (algebraMap R S)
    apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
      (f := g) (a := β) (b := algebraMap R S a)
    · simpa [g, f, aeval_def] using minpoly.aeval R β
    · simpa [g, eval_map] using congrArg (algebraMap R S) haRoot
    · exact hnotUnit
    · simpa [g, Polynomial.derivative_map, aeval_def] using
        IsLocalRing.isUnit_aeval_derivative_minpoly_of_adjoin_eq_top
          (R := R) (S := S) hβ
  have htopEqBot : (⊤ : Subalgebra R S) = ⊥ := by
    rw [← hβ]
    apply le_antisymm
    · apply Algebra.adjoin_le
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      rw [hβImage]
      exact Subalgebra.algebraMap_mem ⊥ a
    · exact bot_le
  exact ⟨FaithfulSMul.algebraMap_injective R S,
    Algebra.surjective_algebraMap_iff.mpr htopEqBot⟩

end EtaleFundamentalGroups

end
