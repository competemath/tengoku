/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Basic
import Tengoku.Seed.RingTheory.Nilpotent.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nilpotence of the scheme-theoretic kernel of a square-zero `Spec.map`

If `φ : R ⟶ S` is a ring map with `RingHom.ker φ ^ 2 = ⊥` (a square-zero quotient), then the
scheme-theoretic kernel `(Spec.map φ).ker : IdealSheafData (Spec R)` is nilpotent.

This is the bridge that lets `AlgebraicGeometry.FormallyUnramified.hom_ext` — whose thickening
hypothesis is `IsNilpotent i.ker` — be applied to the affine square-zero thickening `Spec.map φ`
produced by `AlgebraicGeometry.FormallyUnramified.of_hom_ext`, which supplies only the ring-level
`RingHom.ker φ ^ 2 = ⊥`. Used by
`ModularCurves.EllipticCurve.MulByHom.formallyUnramified_of_torsionπ`.

## Main results

* `AlgebraicGeometry.ideal_ker_SpecMap_top`: the top-affine-open component of `(Spec.map φ).ker`
  is `(RingHom.ker φ).comap (ΓSpecIso R).hom`.
* `AlgebraicGeometry.isNilpotent_ker_SpecMap`:
  `RingHom.ker φ ^ 2 = ⊥ → IsNilpotent (Spec.map φ).ker`.
-/

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

open Scheme.IdealSheafData

universe u

variable {R S : CommRingCat.{u}}

/-- The value of the scheme-theoretic kernel of `Spec.map φ` on the top affine open is the
kernel of `φ`, pulled back along the isomorphism `Γ(Spec R, ⊤) ≅ R`.
@isnad1 id=eq.0h3v.s12.064192e784c3 from=translated src=- shape=96a0c5f2 vocab=3303824a
-/
lemma ideal_ker_SpecMap_top (φ : R ⟶ S) :
    (Spec.map φ).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom := by
  have hinj : Function.Injective (Scheme.ΓSpecIso S).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).1
  have hh : (Scheme.ΓSpecIso S).hom.hom.comp (Spec.map φ).appTop.hom
      = φ.hom.comp (Scheme.ΓSpecIso R).hom.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality]
  have happ : RingHom.ker (Spec.map φ).appTop.hom =
      (RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom := by
    calc RingHom.ker (Spec.map φ).appTop.hom
        = RingHom.ker ((Scheme.ΓSpecIso S).hom.hom.comp (Spec.map φ).appTop.hom) := by
          rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj,
            ← RingHom.ker_eq_comap_bot]
      _ = RingHom.ker (φ.hom.comp (Scheme.ΓSpecIso R).hom.hom) := by rw [hh]
      _ = (RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom := (RingHom.comap_ker _ _).symm
  rw [Scheme.ker_of_isAffine]
  have hofid : (ofIdealTop (RingHom.ker (Spec.map φ).appTop.hom)).ideal ⟨⊤, isAffineOpen_top _⟩
      = RingHom.ker (Spec.map φ).appTop.hom := by
    simp
  rw [hofid, happ]

/-- If `φ : R ⟶ S` is a square-zero quotient (`RingHom.ker φ ^ 2 = ⊥`), then the
scheme-theoretic kernel `(Spec.map φ).ker` is nilpotent.
@isnad1 id=isnilpot.1h3v.s8.e6eb3cf8a1db from=translated src=- shape=75e02a3f vocab=66fe54e7
-/
lemma isNilpotent_ker_SpecMap (φ : R ⟶ S) (h : RingHom.ker φ.hom ^ 2 = ⊥) :
    IsNilpotent (Spec.map φ).ker := by
  have hle : ((RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom) ^ 2 = ⊥ := by
    apply le_bot_iff.mp
    calc ((RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom) ^ 2
        = (RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom
            * (RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom := pow_two _
      _ ≤ (RingHom.ker φ.hom * RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom := by
          apply Ideal.mul_le.mpr
          intro a ha b hb
          rw [Ideal.mem_comap] at ha hb ⊢
          rw [map_mul]
          exact Ideal.mul_mem_mul ha hb
      _ = ((RingHom.ker φ.hom) ^ 2).comap (Scheme.ΓSpecIso R).hom.hom := by rw [← pow_two]
      _ = (⊥ : Ideal R).comap (Scheme.ΓSpecIso R).hom.hom := by rw [h]
      _ = ⊥ := Ideal.comap_bot_of_injective _
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1
  have key : (Spec.map φ).ker ^ 2 = ⊥ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp only [ideal_pow, ideal_bot, Pi.pow_apply, Pi.bot_apply]
    rw [ideal_ker_SpecMap_top]
    exact hle
  exact ⟨2, key⟩

end AlgebraicGeometry
