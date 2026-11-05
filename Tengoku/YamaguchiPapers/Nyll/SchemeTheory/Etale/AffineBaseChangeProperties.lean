/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.AlgebraicGeometry.Morphisms.Etale
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Finite
import Tengoku.Seed.AlgebraicGeometry.Pullbacks
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Descent.EtalePrimeLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ring properties of actual affine base changes

The canonical tensor-product spectrum isomorphism identifies the structure
map, so properties of the scheme pullback give properties of the tensor
algebra with its canonical scalar action. Prime localization then gives
etaleness at every point over the chosen base prime.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

namespace SchemeTheory

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

private def tensorSpecBaseChangeIso :
    Spec (.of (A ⊗[R] B)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  (pullbackSpecIso R A B).symm ≪≫
    pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))

private theorem tensorSpecBaseChangeIso_hom_snd :
    (tensorSpecBaseChangeIso R A B).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] B))) := by
  simp only [tensorSpecBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst']

/-- Etaleness of the actual affine pullback gives etaleness of the tensor
algebra over the new base.
@isnad1 id=etale.1h3v.s8.f91eca1031d5 from=translated src=- shape=e7266dae vocab=8f26d447
-/
theorem tensorProduct_etale_of_spec_baseChange
    (h : Etale (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))))) :
    Algebra.Etale A (A ⊗[R] B) := by
  let := h
  have hcomp : Etale ((tensorSpecBaseChangeIso R A B).hom ≫
      pullback.snd _ _) := inferInstance
  rw [tensorSpecBaseChangeIso_hom_snd] at hcomp
  exact RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hcomp)

/-- Finiteness of the actual affine pullback gives module finiteness of
its canonical tensor algebra.
@isnad1 id=finite.1h3v.s8.51db7bc63c33 from=translated src=- shape=e7266dae vocab=b82f2d5e
-/
theorem tensorProduct_finite_of_spec_baseChange
    (h : IsFinite (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))))) :
    Module.Finite A (A ⊗[R] B) := by
  let := h
  have hcomp : IsFinite ((tensorSpecBaseChangeIso R A B).hom ≫
      pullback.snd _ _) := inferInstance
  rw [tensorSpecBaseChangeIso_hom_snd] at hcomp
  exact RingHom.finite_algebraMap.mp (IsFinite.SpecMap_iff _ |>.mp hcomp)

/-- Etaleness after the actual base change to a prime localization implies
etaleness at every target prime over that base prime.
@isnad1 id=isetalea.2h4v.s9.bbec818407f4 from=translated src=- shape=53de04a2 vocab=41b8d365
-/
theorem isEtaleAt_of_spec_baseChange_atPrime
    (p : PrimeSpectrum R)
    (h : Etale (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal))))))
    (P : PrimeSpectrum B)
    (hP : PrimeSpectrum.comap (algebraMap R B) P = p) :
    Algebra.IsEtaleAt R P.asIdeal := by
  let : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] B) :=
    tensorProduct_etale_of_spec_baseChange R (Localization.AtPrime p.asIdeal) B h
  have hloc : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl)) :=
    Algebra.Etale.of_equiv (Localization.tensorRightAlgEquiv p.asIdeal.primeCompl B)
  exact isEtaleAt_of_localizedAlgebra_etale p hloc P hP

end SchemeTheory
