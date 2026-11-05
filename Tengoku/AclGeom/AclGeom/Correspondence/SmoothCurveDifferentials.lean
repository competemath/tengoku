/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Curves.Places
import Tengoku.Seed.FieldTheory.SeparablyGenerated
import Tengoku.Seed.RingTheory.AlgebraicIndependent.Adjoin
import Tengoku.Seed.RingTheory.Etale.Field
import Tengoku.Seed.RingTheory.Etale.Kaehler
import Tengoku.Seed.RingTheory.Kaehler.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differential rank of a one-variable field

**Status:** proved over perfect fields for an essentially finite-type field of transcendence
degree one, in independent universes. A separating transcendence basis and formally etale
differential comparison give rank one. The existing one-variable function-field class supplies
transcendence degree one. Named consumer: the actual smooth curve stalk cotangent bound.

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
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin
universe u v
variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- The actual Kähler differential space of a separably generated one-variable field
has dimension one. Named consumer: the actual smooth curve stalk's cotangent bound.
@isnad1 id=eq.1h2v.s7.1dc68b883321 from=translated src=- shape=4651a7e6 vocab=f9ee7987
-/
theorem finrank_differential_eq_one [PerfectField k] [Algebra.EssFiniteType k F]
    (htr : Algebra.trdeg k F = 1) :
    Module.finrank F (KaehlerDifferential k F) = 1 := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  have hcard : s.card = 1 := by
    have h := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, htr] at h
    exact_mod_cast h
  have hr : Set.range ((↑) : s → F) = (s : Set F) := by ext; simp
  let P := MvPolynomial s k
  let A := Algebra.adjoin k (s : Set F)
  let K := IntermediateField.adjoin k (s : Set F)
  let e : P ≃ₐ[k] A := hs.1.aevalEquiv.trans
    (Subalgebra.equivOfEq _ _ (congrArg (Algebra.adjoin k) hr))
  let : Algebra P K := ((algebraMap A K).comp e.toRingHom).toAlgebra
  have : IsScalarTower k P K := IsScalarTower.of_algebraMap_eq fun c ↦ by
    symm
    change algebraMap A K (e (algebraMap k P c)) = algebraMap k K c
    rw [e.commutes, ← IsScalarTower.algebraMap_apply k A K]
  have : IsFractionRing P K :=
    IsFractionRing.of_ringEquiv_left e.toRingEquiv (fun _ ↦ rfl)
  let : Algebra P F := ((algebraMap K F).comp (algebraMap P K)).toAlgebra
  have : IsScalarTower P K F := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k P F := IsScalarTower.of_algebraMap_eq fun c ↦ by
    symm
    change algebraMap K F (algebraMap P K (algebraMap k P c)) = algebraMap k F c
    rw [← IsScalarTower.algebraMap_apply k P K, ← IsScalarTower.algebraMap_apply k K F]
  have : Algebra.IsSeparable K F := hsep
  have : Algebra.FormallyEtale P K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  have : Algebra.FormallyEtale K F := Algebra.FormallyEtale.of_isSeparable K F
  have : Algebra.FormallyEtale P F := Algebra.FormallyEtale.comp P K F
  let b := ((KaehlerDifferential.mvPolynomialBasis k s).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k P F)
  simpa only [Fintype.card_coe, hcard] using Module.finrank_eq_card_basis b

end
end AclGeom.SmoothCurveStalks
