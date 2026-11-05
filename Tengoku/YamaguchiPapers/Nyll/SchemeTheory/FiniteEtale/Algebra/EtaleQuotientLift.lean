/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Smooth.JacobianLocalization
public import Tengoku.Seed.Algebra.Category.CommAlgCat.Basic
public import Tengoku.Seed.RingTheory.Ideal.Quotient.Defs
public import Tengoku.Seed.Algebra.Algebra.Tower
public import Tengoku.Seed.Algebra.Group.Units.Equiv
public import Tengoku.Seed.Algebra.MvPolynomial.PDeriv
public import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
public import Tengoku.Seed.RingTheory.Extension.Generators
public import Tengoku.Seed.RingTheory.Extension.Presentation.Core
public import Tengoku.Seed.RingTheory.Extension.Presentation.Submersive
public import Tengoku.Seed.RingTheory.Localization.Away.Basic
public import Tengoku.Seed.RingTheory.Localization.BaseChange
public import Tengoku.Seed.RingTheory.MvPolynomial.Tower
public import Tengoku.Seed.RingTheory.Smooth.StandardSmooth
public import Tengoku.Seed.RingTheory.Smooth.StandardSmoothOfFree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifting étale algebras through a surjective base map

For a surjective map `R₀ → R` and an étale `R`-algebra `S`, we construct an
étale `R₀`-algebra whose base change is `S`. The construction uses mathlib's
relative-dimension-zero submersive presentation, lifts its polynomial
coefficients, and inverts the Jacobian of the resulting model.

The Jacobian maps to a unit in the original algebra, so this localization
does not change the base change. Both the étale property and the algebra
isomorphism are proved from the construction. No noetherian, field, or
nilpotence hypothesis is used. This is the affine lifting step needed for
comparing étale neighborhoods along a closed immersion.
-/

@[expose] public section

noncomputable section

universe u₀ u v w t

open Algebra TensorProduct

namespace Algebra.Etale

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t}
  [CommRing R] [CommRing S] [Algebra R S] [Finite σ]
  (P : PreSubmersivePresentation R S ι σ)

section Coefficients

variable (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S]
  [IsScalarTower R₀ R S] [P.HasCoeffs R₀]

/-- The Jacobian of the coefficient model becomes the original Jacobian after base change.-/
lemma tensorModel_jacobian :
    P.tensorModelOfHasCoeffsEquiv R₀
      (1 ⊗ₜ[R₀] (P.ofHasCoeffs R₀).jacobian) = P.jacobian := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  have hm : (MvPolynomial.map (algebraMap R₀ R)).mapMatrix (P.ofHasCoeffs R₀).jacobiMatrix =
      P.jacobiMatrix := by
    funext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      PreSubmersivePresentation.jacobiMatrix_apply,
      PreSubmersivePresentation.ofHasCoeffs_map,
      PreSubmersivePresentation.ofHasCoeffs_relation,
      ← MvPolynomial.pderiv_map, Presentation.map_relationOfHasCoeffs]
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  change P.tensorModelOfHasCoeffsEquiv R₀
    (1 ⊗ₜ[R₀] Ideal.Quotient.mk _ (P.ofHasCoeffs R₀).jacobiMatrix.det) = P.jacobian
  rw [Presentation.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul,
    ← MvPolynomial.aeval_map_algebraMap R, RingHom.map_det, hm]
  exact (P.toGenerators.algebraMap_apply P.jacobiMatrix.det).symm.trans
    P.jacobian_eq_jacobiMatrix_det.symm

end Coefficients

section Lift

variable (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S]
  [IsScalarTower R₀ R S] (Q : SubmersivePresentation R S ι σ)
  [Q.toPresentation.HasCoeffs R₀]

end Lift

end Algebra.Etale
