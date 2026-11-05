/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Etale.Field
import Tengoku.Seed.RingTheory.Localization.Away.Lemmas
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.Normalization.GenericFiber.SmoothIntegralClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A specified generic component of a finite etale algebra

For a finite etale algebra over a normal domain, a maximal ideal of the
generic fibre selects one field component.  This file descends the primitive
idempotent of that specified component through smooth integral-closure base
change.  The selected component normalization is thereby an actual
idempotent factor of the original finite etale algebra.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct
open Polynomial

universe uR uT uK

section ArtinianComponent

variable {G : Type*} [CommRing G] [IsArtinianRing G] [IsReduced G]

/-- The primitive idempotent supported at a specified maximal ideal of a
reduced Artinian ring.-/
noncomputable def artinianSelectedComponentIdempotent
    (m : Ideal G) [m.IsMaximal] : G := by
  classical
  exact (IsArtinianRing.equivPi G).symm
    (Pi.single (⟨m, inferInstance⟩ : MaximalSpectrum G) 1)

theorem quotient_artinianSelectedComponentIdempotent_eq_zero
    (m : Ideal G) [m.IsMaximal] (M : MaximalSpectrum G)
    (hM : M ≠ (⟨m, inferInstance⟩ : MaximalSpectrum G)) :
    Ideal.Quotient.mk M.asIdeal
        (artinianSelectedComponentIdempotent m) = 0 := by
  classical
  let M₀ : MaximalSpectrum G := ⟨m, inferInstance⟩
  let v : ∀ I : MaximalSpectrum G, G ⧸ I.asIdeal := Pi.single M₀ 1
  have hev : IsArtinianRing.equivPi G
      (artinianSelectedComponentIdempotent m) = v := by
    change IsArtinianRing.equivPi G
      ((IsArtinianRing.equivPi G).symm v) = v
    exact (IsArtinianRing.equivPi G).apply_symm_apply v
  calc
    _ = IsArtinianRing.equivPi G
        (artinianSelectedComponentIdempotent m) M :=
      (IsArtinianRing.equivPi_apply _ _ _).symm
    _ = v M := congrFun hev M
    _ = _ := by simp [v, M₀, hM]

@[simp]
theorem quotient_artinianSelectedComponentIdempotent
    (m : Ideal G) [m.IsMaximal] :
    Ideal.Quotient.mk m (artinianSelectedComponentIdempotent m) = 1 := by
  classical
  let M₀ : MaximalSpectrum G := ⟨m, inferInstance⟩
  let v : ∀ I : MaximalSpectrum G, G ⧸ I.asIdeal := Pi.single M₀ 1
  have hev : IsArtinianRing.equivPi G
      (artinianSelectedComponentIdempotent m) = v := by
    change IsArtinianRing.equivPi G
      ((IsArtinianRing.equivPi G).symm v) = v
    exact (IsArtinianRing.equivPi G).apply_symm_apply v
  calc
    _ = IsArtinianRing.equivPi G
        (artinianSelectedComponentIdempotent m)
          (⟨m, inferInstance⟩ : MaximalSpectrum G) :=
      (IsArtinianRing.equivPi_apply _ _ _).symm
    _ = v M₀ := congrFun hev M₀
    _ = _ := by simp [v, M₀]

theorem artinianSelectedComponentIdempotent_isIdempotentElem
    (m : Ideal G) [m.IsMaximal] :
    IsIdempotentElem (artinianSelectedComponentIdempotent m) := by
  classical
  apply (IsArtinianRing.equivPi G).injective
  ext M
  simp only [map_mul, IsArtinianRing.equivPi_apply]
  by_cases hM : M = (⟨m, inferInstance⟩ : MaximalSpectrum G)
  · subst M
    rw [quotient_artinianSelectedComponentIdempotent, one_mul]
  · rw [quotient_artinianSelectedComponentIdempotent_eq_zero m M hM, zero_mul]

/-- Multiplication by the selected primitive idempotent kills exactly the
elements vanishing in the specified field component.-/
theorem artinianSelectedComponentIdempotent_mul_eq_zero_iff
    (m : Ideal G) [m.IsMaximal] (x : G) :
    artinianSelectedComponentIdempotent m * x = 0 ↔
      Ideal.Quotient.mk m x = 0 := by
  classical
  constructor
  · intro h
    have hmap := congrArg (Ideal.Quotient.mk m) h
    simpa using hmap
  · intro hx
    apply (IsArtinianRing.equivPi G).injective
    ext M
    simp only [map_mul, map_zero, IsArtinianRing.equivPi_apply]
    by_cases hM : M = (⟨m, inferInstance⟩ : MaximalSpectrum G)
    · subst M
      simpa using hx
    · rw [quotient_artinianSelectedComponentIdempotent_eq_zero m M hM, zero_mul]

/-- An integral element of a specified residue-field component, extended by
zero on every other Artinian component, is represented by an integral element
of the whole Artinian ring.-/
theorem exists_integral_artinianElement_supported_at_component
    {R : Type uR} [CommRing R] [Algebra R G]
    (m : Ideal G) [m.IsMaximal]
    (x : G ⧸ m) (hx : IsIntegral R x) :
    ∃ y : G, IsIntegral R y ∧ Ideal.Quotient.mk m y = x := by
  classical
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective x
  let e : G := artinianSelectedComponentIdempotent m
  let y : G := e * z
  have hym : Ideal.Quotient.mk m y = x := by
    simp [y, e, hz]
  obtain ⟨p, hpMonic, hpx⟩ := hx
  have hyIntegral : IsIntegral R y := by
    let q : R[X] := X * p
    refine ⟨q, monic_X.mul hpMonic, ?_⟩
    apply (IsArtinianRing.equivPi G).injective
    ext M
    simp only [map_zero, IsArtinianRing.equivPi_apply]
    have hmap_aeval (w : G) (f : R[X]) :
        Ideal.Quotient.mk M.asIdeal (aeval w f) =
          aeval (Ideal.Quotient.mk M.asIdeal w) f := by
      simpa using
        (map_aeval_eq_aeval_map
          (R := R) (S := G) (T := R) (U := G ⧸ M.asIdeal)
          (φ := RingHom.id R)
          (ψ := Ideal.Quotient.mk M.asIdeal)
          (by ext r; rfl) f w)
    change Ideal.Quotient.mk M.asIdeal (aeval y q) = 0
    rw [hmap_aeval]
    by_cases hM : M = (⟨m, inferInstance⟩ : MaximalSpectrum G)
    · subst M
      rw [hym]
      change aeval x q = 0
      rw [show q = X * p by rfl, map_mul, aeval_X]
      change x * aeval x p = 0
      change aeval x p = 0 at hpx
      rw [hpx, mul_zero]
    · rw [show Ideal.Quotient.mk M.asIdeal y = 0 by
        simp [y, e,
          quotient_artinianSelectedComponentIdempotent_eq_zero m M hM]]
      simp [q]
  exact ⟨y, hyIntegral, hym⟩

end ArtinianComponent

section FiniteEtaleComponent

variable {R : Type uR} {T : Type uT} {K : Type uK}

/-- The field component of the generic fibre selected by a maximal ideal.-/
abbrev FiniteEtaleGenericFiberComponent
    [CommRing R] [CommRing T] [Algebra R T]
    [Field K] [Algebra R K]
    (m : Ideal (T ⊗[R] K)) := (T ⊗[R] K) ⧸ m

/-- The finite-etale algebra maps canonically to the integral closure of the
base in a selected generic-fibre component.-/
noncomputable def genericFiberComponentToIntegralClosure
    [CommRing R] [CommRing T] [Algebra R T] [Module.Finite R T]
    [Field K] [Algebra R K]
    (m : Ideal (T ⊗[R] K)) :
    T →ₐ[R] integralClosure R (FiniteEtaleGenericFiberComponent m) := by
  letI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  let gΩ : T →ₐ[R] FiniteEtaleGenericFiberComponent m :=
    (Ideal.Quotient.mkₐ R m).comp Algebra.TensorProduct.includeLeft
  exact gΩ.codRestrict _ fun t ↦
    (Algebra.IsIntegral.isIntegral (R := R) t).map gΩ

end FiniteEtaleComponent

end EtaleFundamentalGroups

end
