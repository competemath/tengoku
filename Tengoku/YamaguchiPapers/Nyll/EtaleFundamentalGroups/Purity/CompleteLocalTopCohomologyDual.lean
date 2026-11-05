/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.CompleteLocalArtinianDualFinite
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyArtinian
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologySupportDimensionNonvanishing
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTopMultiplication
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.EssentialModuleExtension
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.InjectiveResidueFieldCogenerator
import Tengoku.Seed.Algebra.Category.Grp.Zero
import Tengoku.Seed.Algebra.Group.Action.Basic
import Tengoku.Seed.Algebra.Module.Submodule.Range
import Tengoku.Seed.Algebra.Module.Torsion.Free
import Tengoku.Seed.RingTheory.AdicCompletion.Basic
import Tengoku.Seed.RingTheory.Artinian.Module
import Tengoku.Seed.RingTheory.Finiteness.Basic
import Tengoku.Seed.RingTheory.KrullDimension.Module
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The dual of top local cohomology over a complete local domain

Every nonzero scalar acts surjectively on positive top local cohomology
of a local domain. Its linear dual is therefore torsion-free. For a
complete domain, top nonvanishing and separation by an injective module
containing the residue field also make this dual nonzero. Artinianness
and maximal-ideal-power torsion make the dual into the residue-field
injective hull finitely generated.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

open CategoryTheory Limits IsLocalRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]

/-- The linear dual of positive top local cohomology is torsion-free,
because every nonzero scalar is surjective on the original module.
@isnad1 id=istorsio.1h3v.s9.5936406e0462 from=translated src=- shape=5ce3eb4f vocab=ec350ab5
-/
theorem isTorsionFree_linearMap_topLocalCohomology
    (E : Type v) [AddCommGroup E] [Module R E] (d : ℕ)
    (hdim : ringKrullDim R = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    Module.IsTorsionFree R
      (derivedLocalCohomologyModule (maximalIdeal R) (ModuleCat.of R R) (d + 1) →ₗ[R] E) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro x f hxf
  by_cases hxzero : x = 0
  · exact Or.inl hxzero
  · apply Or.inr
    have hsurj : Function.Surjective
        (fun z : derivedLocalCohomologyModule (maximalIdeal R)
          (ModuleCat.of R R) (d + 1) => x • z) := by
      by_cases hxm : x ∈ maximalIdeal R
      · exact derivedLocalCohomologyScalarMap_maximalIdeal_surjective_succ
          d hdim x hxzero hxm
      · exact (notMem_maximalIdeal.mp hxm).smul_bijective.surjective
    ext z
    obtain ⟨w, hw⟩ := hsurj z
    rw [← hw, map_smul]
    exact DFunLike.congr_fun hxf w

omit [IsDomain R] in
/-- The dual with values in an injective module containing the residue
field detects the nonzero top cohomology of a complete local domain.
@isnad1 id=nontrivi.2h4v.s9.1174703d3b5a from=translated src=- shape=4123eb4c vocab=7d42eafa
-/
theorem nontrivial_linearMap_topLocalCohomology
    [IsAdicComplete (maximalIdeal R) R]
    {E : Type u} [AddCommGroup E] [Module R E] [Module.Injective R E]
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (d : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞)) :
    Nontrivial
      (derivedLocalCohomologyModule (maximalIdeal R) (ModuleCat.of R R) d →ₗ[R] E) := by
  let H : ModuleCat.{u} R :=
    derivedLocalCohomologyModule (maximalIdeal R) (ModuleCat.of R R) d
  have hnonzero : ¬ IsZero
      (derivedLocalCohomology (maximalIdeal R) (ModuleCat.of R R) d) :=
    derivedLocalCohomology_maximalIdeal_not_isZero_of_supportDim_eq
      (ModuleCat.of R R) d ((Module.supportDim_self_eq_ringKrullDim R).trans hdim)
  have hnotSubsingleton : ¬ Subsingleton H :=
    fun h => hnonzero (AddCommGrpCat.isZero_iff_subsingleton.mpr h)
  let : Nontrivial H := not_subsingleton_iff_nontrivial.mp hnotSubsingleton
  obtain ⟨z, hz⟩ := exists_ne (0 : H)
  obtain ⟨f, hf⟩ := exists_linearMap_apply_ne_zero_of_injective_residueField i hi z hz
  refine ⟨⟨f, 0, ?_⟩⟩
  intro hfzero
  exact hf (DFunLike.congr_fun hfzero z)

omit [IsDomain R] in
/-- The dual of maximal-support local cohomology with values in the
residue-field injective hull is finite over a complete local ring.
@isnad1 id=finite.2h5v.s9.0f4ffa32c1d6 from=translated src=- shape=e52c2a8c vocab=7e4b796f
-/
theorem finite_linearMap_localCohomology_maximalIdeal
    [IsAdicComplete (maximalIdeal R) R]
    {E : Type u} [AddCommGroup E] [Module R E] [Module.Injective R E]
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (hess : IsEssentialSubmodule (LinearMap.range i))
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ) :
    Module.Finite R
      (derivedLocalCohomologyModule (maximalIdeal R) M d →ₗ[R] E) := by
  let : IsArtinian R (derivedLocalCohomologyModule (maximalIdeal R) M d) :=
    isArtinian_derivedLocalCohomologyModule_maximalIdeal M d
  exact finite_linearMap_to_completeLocal_residueFieldHull_of_artinian i hi hess
    (derivedLocalCohomologyModule_exists_idealPower_smul_eq_zero (maximalIdeal R) M d)

end EtaleFundamentalGroups.Purity
