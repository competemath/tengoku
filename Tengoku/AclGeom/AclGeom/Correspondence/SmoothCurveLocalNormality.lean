/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.SmoothCurveDifferentials
import Tengoku.AclGeom.AclGeom.Correspondence.SmoothCurveCotangentSplit
import Tengoku.Seed.RingTheory.LocalRing.Module
import Tengoku.Seed.RingTheory.Ideal.Cotangent
import Tengoku.Seed.RingTheory.DiscreteValuationRing.TFAE
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.RingTheory.Flat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local normality from smooth curve differentials

**Status:** proved over an ACF base for an essentially finite-type formally smooth Noetherian
local domain with algebraic residue field and a one-variable fraction field. The residue
section, differential rank and cotangent bound are internal. The maximal ideal is principal,
hence the ring is integrally closed. Named consumer: every closed-point stalk of the actual
smooth integral curve.

These are ACF dimension-one results. Projective presentation, joint regularity of extended
rational families, rational-action regularization and the full original classifier remain
owed. Original group/chunk/six-point statements, algebraization/descent and every true
bypassed auxiliary remain obligations. All eight original #21 work items and the full durable
goal remain active and incomplete.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.SmoothCurveStalks
noncomputable section
open IsLocalRing
open scoped TensorProduct
universe u v w
variable {k : Type u} {R : Type v} {F : Type w}
variable [Field k] [IsAlgClosed k] [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsNoetherianRing R] [Algebra k R] [Algebra.EssFiniteType k R]
  [Algebra.FormallySmooth k R] [Field F] [Algebra k F] [Algebra R F]
  [IsScalarTower k R F] [IsFractionRing R F]
  [Algebra.IsAlgebraic k (ResidueField R)]

omit [IsDomain R] [IsNoetherianRing R] in
/-- Smoothness and the actual one-variable fraction field bound the local cotangent
space by one. The residue section and generic differential rank are internal.
Named consumer: local normality of an actual smooth integral curve.
@isnad1 id=le.1h3v.s8.3b6d2579f624 from=translated src=- shape=e9a6b49c vocab=9694bf76
-/
theorem finrank_cotangent_le_one (htr : Algebra.trdeg k F = 1) :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
  let S := ResidueField R
  let ρ : S →ₐ[k] k := IsAlgClosed.lift
  let σ : S →ₐ[k] R := (Algebra.ofId k R).comp ρ
  have hσ : (IsScalarTower.toAlgHom k R S).comp σ = AlgHom.id k S := by
    ext x
    obtain ⟨c, rfl⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := S)).2 x
    simp only [AlgHom.commutes]
  have hsurj : Function.Surjective (algebraMap R S) := residue_surjective
  have hinj := kerCotangentToTensor_injective_of_section hsurj σ hσ
  have hker : maximalIdeal R = RingHom.ker (algebraMap R S) := (ker_residue).symm
  let e := Ideal.Cotangent.equivOfEq (maximalIdeal R)
    (RingHom.ker (algebraMap R S)) hker
  let f := (KaehlerDifferential.kerCotangentToTensor k R S).comp e.toLinearMap
  let fS : CotangentSpace R →ₗ[S] S ⊗[R] KaehlerDifferential k R :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c x ↦ by
        obtain ⟨r, rfl⟩ := hsurj c
        change f ((algebraMap R S r) • x) = (algebraMap R S r) • f x
        rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]
        exact f.map_smul r x }
  have hfS : Function.Injective fS := hinj.comp e.injective
  have : Module.Free R (KaehlerDifferential k R) := Module.free_of_flat_of_isLocalRing
  have : Algebra.EssFiniteType R F :=
    Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors R)
  have : Algebra.EssFiniteType k F := Algebra.EssFiniteType.comp k R F
  have : Algebra.FormallyEtale R F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have hdim : Module.finrank R (KaehlerDifferential k R) = 1 := by
    have h := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R F).finrank_eq
    rw [Module.finrank_baseChange] at h
    exact h.trans (finrank_differential_eq_one htr)
  have hle := LinearMap.finrank_le_finrank_of_injective hfS
  simpa only [Module.finrank_baseChange, hdim] using hle

/-- Smooth local curve rings with algebraic residue field are integrally closed.
No cotangent-rank or normality certificate is supplied. Named consumer: the actual
closed-point stalk of a smooth integral dimension-one scheme.
@isnad1 id=isintegr.1h3v.s7.3c8e6067ebd8 from=translated src=- shape=3c8b0505 vocab=1aea2bb0
-/
theorem isIntegrallyClosed_of_smooth (htr : Algebra.trdeg k F = 1) : IsIntegrallyClosed R := by
  have hm : (maximalIdeal R).IsPrincipal :=
    finrank_cotangentSpace_le_one_iff.mp (finrank_cotangent_le_one htr)
  have : IsDedekindDomain R :=
    (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 5 3 |>.mp hm
  infer_instance

end
end AclGeom.SmoothCurveStalks
