/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.RingTheory.IntegralClosure.IntegrallyClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral Lift

**Status:** proved, with a named consumer in the actual curve-completion construction.
These lemmas reach CurveCompletion.connectedGroup_completion_and_extensions: an actual
one-dimensional connected algebraic group over an ACF base embeds openly in a constructed
proper normal integral dimension-one curve, and its individual automorphisms extend uniquely.
The original smooth separated curve is retained. Projectivity, jointly regular extended
families and the full rational/non-affine classifier remain separate source obligations.
The source of truth is `sources/blueprint.tex`, Lemma `affine-action` (#21).
-/

namespace AclGeom.CurveCompletion
noncomputable section
universe u v w z

/-- An integral chart map into the fraction field of an integrally closed ring lifts
uniquely whenever its base map already lies in the ring. Named consumer: valuative
properness of the actual normalized two-chart curve.-/
theorem existsUnique_integral_lift
    {R : Type u} {A : Type v} {O : Type w} {K : Type z}
    [CommRing R] [CommRing A] [CommRing O] [IsDomain O] [Field K]
    [Algebra R A] [Algebra R O] [Algebra R K] [Algebra O K]
    [IsScalarTower R O K] [IsFractionRing O K] [IsIntegrallyClosed O]
    [Algebra.IsIntegral R A] (φ : A →ₐ[R] K) :
    ∃! ψ : A →ₐ[R] O, (IsScalarTower.toAlgHom R O K).comp ψ = φ := by
  let f := IsScalarTower.toAlgHom R O K
  let e := AlgEquiv.ofInjective f (IsFractionRing.injective O K)
  have hmem (a : A) : φ a ∈ f.range := by
    have hi : IsIntegral O (φ a) :=
      ((Algebra.IsIntegral.isIntegral (R := R) a).map φ).tower_top
    exact (isIntegrallyClosed_iff K).mp inferInstance hi
  let ψ := e.symm.toAlgHom.comp (φ.codRestrict f.range hmem)
  have hψ : f.comp ψ = φ := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict f.range hmem a))
  refine ⟨ψ, hψ, ?_⟩
  intro θ hθ
  ext a
  apply IsFractionRing.injective O K
  exact AlgHom.congr_fun (hθ.trans hψ.symm) a

end
end AclGeom.CurveCompletion
