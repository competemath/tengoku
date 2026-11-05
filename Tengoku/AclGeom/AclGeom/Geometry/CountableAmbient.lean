/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex, Claude
-/
import Tengoku.AclGeom.AclGeom.Geometry.FreshSequences
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Countably many independent variables in an algebraically closed ambient

The countable transcendence bound is shared by
`Config.AffineGridNormalization` and the universal domains over the original and
algebraic bases in `Config.UniversalConfigurationInput`.
-/

namespace AclGeom

open MvPolynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The algebraic closure of the field of rational functions in countably many variables over
`K` has transcendence degree at least `ℵ₀` over `k`.
@isnad1 id=le.0h2v.s8.5340d43245b4 from=translated src=- shape=703a0ec7 vocab=3b57e753
-/
theorem aleph0_le_trdeg_algebraicClosure :
    Cardinal.aleph0 ≤
      Algebra.trdeg k (AlgebraicClosure (FractionRing (MvPolynomial ℕ K))) := by
  let Ω := AlgebraicClosure (FractionRing (MvPolynomial ℕ K))
  let φ : MvPolynomial ℕ K →ₐ[K] Ω := IsScalarTower.toAlgHom K (MvPolynomial ℕ K) Ω
  have hφ : Function.Injective φ := by
    change Function.Injective (algebraMap (MvPolynomial ℕ K) Ω)
    rw [IsScalarTower.algebraMap_eq (MvPolynomial ℕ K) (FractionRing (MvPolynomial ℕ K)) Ω]
    exact (algebraMap (FractionRing (MvPolynomial ℕ K)) Ω).injective.comp
      (IsFractionRing.injective (MvPolynomial ℕ K) (FractionRing (MvPolynomial ℕ K)))
  have hX := (MvPolynomial.algebraicIndependent_X ℕ K).map' hφ
  have hXk := AlgebraicIndependent.restrictScalars (algebraMap k K).injective hX
  simpa only [Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_id'] using
    hXk.lift_cardinalMk_le_trdeg

end AclGeom
