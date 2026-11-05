/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Tengoku.Seed.Algebra.Ring.Aut
import Tengoku.Seed.Algebra.Group.Hom.Instances

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The canonical action on abelian absolute Galois characters

Precomposition with inverse conjugation gives a left action. Its group law
uses independence from the chosen extensions to the algebraic closure.
-/

namespace KummerTheory

variable {K A : Type*} [Field K] [CommGroup A]

/-- Pull a character back along the conjugation attached to the inverse base map.-/
noncomputable def absoluteGaloisCharacterTransform (τ : RingAut K)
    (f : Gal(AlgebraicClosure K/K) →* A) : Gal(AlgebraicClosure K/K) →* A :=
  f.comp (absoluteGaloisConjugateEquiv τ.symm).toMonoidHom

/-- Evaluation of the character transform.
@isnad1 id=eq.0h5v.s11.0cb3a06fd1d4 from=translated src=- shape=cdb898ac vocab=46d50829
-/
theorem absoluteGaloisCharacterTransform_apply (τ : RingAut K)
    (f : Gal(AlgebraicClosure K/K) →* A) (σ : Gal(AlgebraicClosure K/K)) :
    absoluteGaloisCharacterTransform τ f σ =
      f (absoluteGaloisConjugate τ.symm σ) := by
  rfl

/-- The transform by the identity is independent of its possibly nonidentity lift.
@isnad1 id=eq.0h3v.s10.86c573b2db7a from=translated src=- shape=768bd9db vocab=bf174a5d
-/
theorem absoluteGaloisCharacterTransform_one (f : Gal(AlgebraicClosure K/K) →* A) :
    absoluteGaloisCharacterTransform 1 f = f := by
  apply MonoidHom.ext
  intro σ
  rw [absoluteGaloisCharacterTransform_apply, RingAut.one_eq_refl, RingEquiv.symm_refl]
  unfold absoluteGaloisConjugate
  rw [map_semilinearGaloisConjugate_eq f (RingEquiv.refl K)
    (RingEquiv.refl (AlgebraicClosure K))
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) (RingEquiv.refl K))
    (semilinear_refl_algebraMap (K := K) (Ω := AlgebraicClosure K))
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K)
      (RingEquiv.refl K)), semilinearGaloisConjugate_refl]

/-- The transforms compose in the order required for a left action.
@isnad1 id=eq.0h5v.s10.aec51ca97559 from=translated src=- shape=b0fc5417 vocab=d1c5f092
-/
theorem absoluteGaloisCharacterTransform_mul (τ υ : RingAut K)
    (f : Gal(AlgebraicClosure K/K) →* A) :
    absoluteGaloisCharacterTransform (τ * υ) f =
      absoluteGaloisCharacterTransform τ (absoluteGaloisCharacterTransform υ f) := by
  apply MonoidHom.ext
  intro σ
  rw [absoluteGaloisCharacterTransform_apply, absoluteGaloisCharacterTransform_apply,
    absoluteGaloisCharacterTransform_apply]
  have hbase : (τ * υ).symm = τ.symm.trans υ.symm := by rfl
  rw [hbase]
  unfold absoluteGaloisConjugate
  rw [map_semilinearGaloisConjugate_eq f (τ.symm.trans υ.symm)
    ((IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ.symm).trans
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) υ.symm))
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K)
      (τ.symm.trans υ.symm))
    (semilinear_trans_algebraMap τ.symm υ.symm
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ.symm)
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) υ.symm)
      (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) τ.symm)
      (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) υ.symm))
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K)
      (τ.symm.trans υ.symm)), semilinearGaloisConjugate_trans]

/-- Each base automorphism acts by an automorphism of the abelian character group.-/
noncomputable def absoluteGaloisCharacterTransformEquiv (τ : RingAut K) :
    MulAut (Gal(AlgebraicClosure K/K) →* A) where
  toFun := absoluteGaloisCharacterTransform τ
  invFun := absoluteGaloisCharacterTransform τ⁻¹
  left_inv f := by
    rw [← absoluteGaloisCharacterTransform_mul, inv_mul_cancel,
      absoluteGaloisCharacterTransform_one]
  right_inv f := by
    rw [← absoluteGaloisCharacterTransform_mul, mul_inv_cancel,
      absoluteGaloisCharacterTransform_one]
  map_mul' f g := by
    apply MonoidHom.ext
    intro σ
    simp only [absoluteGaloisCharacterTransform_apply, MonoidHom.mul_apply]

/-- Evaluation of the automorphism of the abelian character group.
@isnad1 id=eq.0h4v.s12.b2ae486abcf8 from=translated src=- shape=5a8a3472 vocab=7bd2ceb7
-/
theorem absoluteGaloisCharacterTransformEquiv_apply (τ : RingAut K)
    (f : Gal(AlgebraicClosure K/K) →* A) :
    absoluteGaloisCharacterTransformEquiv τ f = absoluteGaloisCharacterTransform τ f := by
  rfl

/-- The canonical action of base-field automorphisms on abelian Galois characters.-/
noncomputable def absoluteGaloisCharacterAction :
    RingAut K →* MulAut (Gal(AlgebraicClosure K/K) →* A) where
  toFun := absoluteGaloisCharacterTransformEquiv
  map_one' := by
    apply MulEquiv.ext
    intro f
    rw [absoluteGaloisCharacterTransformEquiv_apply, MulAut.one_apply,
      absoluteGaloisCharacterTransform_one]
  map_mul' τ υ := by
    apply MulEquiv.ext
    intro f
    rw [MulAut.mul_apply, absoluteGaloisCharacterTransformEquiv_apply,
      absoluteGaloisCharacterTransformEquiv_apply, absoluteGaloisCharacterTransformEquiv_apply,
      absoluteGaloisCharacterTransform_mul]

/-- Evaluation of the canonical action.
@isnad1 id=eq.0h4v.s14.46449c6e93bd from=translated src=- shape=b0aa67e1 vocab=3150682f
-/
theorem absoluteGaloisCharacterAction_apply (τ : RingAut K)
    (f : Gal(AlgebraicClosure K/K) →* A) :
    absoluteGaloisCharacterAction τ f = absoluteGaloisCharacterTransform τ f := by
  rfl

end KummerTheory
