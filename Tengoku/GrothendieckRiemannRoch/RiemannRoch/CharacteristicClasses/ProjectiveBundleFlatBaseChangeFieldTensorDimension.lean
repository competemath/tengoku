/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveBundleFlatBaseChangeRelativeDimension
import Tengoku.Seed.RingTheory.AlgebraicIndependent.Adjoin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Generic component dimensions under field scalar extension

A genuine tensor cancellation isomorphism transports minimal primes and quotient
transcendence degrees. An actual transcendence basis and its rational-function
intermediate field then prove that every minimal-prime quotient of L ⊗[K] F has
transcendence degree trdeg_K F over L, for arbitrary field extensions. No finite
basis or degree formula is supplied as an input.

For an arbitrary domain A, the denominator localization L ⊗[K] A → L ⊗[K] Frac(A)
is constructed. Flat generic-point contraction proves that a minimal prime avoids
those denominators. Localization preserves its quotient transcendence degree,
and the field calculation proves the corresponding formula for L ⊗[K] A.

This does not yet prove the projective morphism's PureRelDim. General non-domain
fibres require reduction by the contracted minimal prime; actual scheme fibre,
coefficient support, residue-field and height identifications also remain. No
lifted PureRelDim or Segre naturality equality is assumed or asserted. All proofs
use default elaboration budgets.
-/

universe u

noncomputable section
open scoped TensorProduct

namespace AlgebraicGeometry.Chow.ProjectiveBaseChangeDimension

section TensorCancellation
variable {K L B F : Type*} [CommRing K] [CommRing L] [CommRing B] [CommRing F]
    [Algebra K L] [Algebra K B] [Algebra K F] [Algebra B F] [IsScalarTower K B F]
local instance rightScalarTensor_rightAlgebra : Algebra B (L ⊗[K] B) := Algebra.TensorProduct.rightAlgebra

/-- Associate a genuine field scalar extension with an intermediate scalar ring.-/
def rightScalarTensorCancel : (L ⊗[K] B) ⊗[B] F ≃ₐ[L] L ⊗[K] F :=
  let e₁ := Algebra.TensorProduct.comm B (L ⊗[K] B) F
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[B] F)
    (Algebra.TensorProduct.commRight K B L).symm
  let e₃ := Algebra.TensorProduct.cancelBaseChange K B F F L
  let e₄ := Algebra.TensorProduct.comm K F L
  { __ := e₁.toRingEquiv.trans (e₂.toRingEquiv.trans
      (e₃.toRingEquiv.trans e₄.toRingEquiv))
    commutes' := by
      intro l
      change _ = l ⊗ₜ[K] (1 : F)
      simp [e₁, e₂, e₃, e₄] }

@[simp]
theorem rightScalarTensorCancel_tmul (l : L) (b : B) (f : F) :
    rightScalarTensorCancel ((l ⊗ₜ[K] b) ⊗ₜ[B] f) =
      l ⊗ₜ[K] (algebraMap B F b * f) := by
  simp [rightScalarTensorCancel, Algebra.smul_def]

end TensorCancellation

section QuotientTransport
variable {K R S : Type u} [CommRing K] [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S]

theorem scalarTensor_minimalPrime_comap (e : R ≃ₐ[K] S)
    {q : Ideal S} (hq : q ∈ minimalPrimes S) :
    q.comap e.toRingHom ∈ minimalPrimes R := by
  have h := @Ideal.minimalPrimes_comap_of_surjective R S inferInstance inferInstance
    e.toRingHom e.surjective (⊥ : Ideal S) q hq
  simpa only [Ideal.comap_bot_of_injective e.toRingHom e.injective] using h

theorem scalarTensor_quotient_trdeg_comap (e : R ≃ₐ[K] S) (q : Ideal S) :
    Algebra.trdeg K (R ⧸ q.comap e.toRingHom) = Algebra.trdeg K (S ⧸ q) := by
  have heq : q = (q.comap e.toRingHom).map e.toRingHom :=
    (Ideal.map_comap_of_surjective e.toRingHom e.surjective q).symm
  exact (Ideal.quotientEquivAlg (q.comap e.toRingHom) q e heq).trdeg_eq

end QuotientTransport

section RationalFieldExtension
variable {K L σ F : Type u} [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra K F]
    [Algebra (FractionRing (MvPolynomial σ K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial σ K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial σ K)) F]
local instance rationalField_rightAlgebra :
    Algebra (FractionRing (MvPolynomial σ K))
      (L ⊗[K] FractionRing (MvPolynomial σ K)) := Algebra.TensorProduct.rightAlgebra

/-- Generic components of the actual scalar extension of an algebraic extension
of a rational-function field have the original basis cardinal as their degree.-/
theorem rationalFieldExtensionTensor_trdeg
    {q : Ideal (L ⊗[K] F)} (hq : q ∈ minimalPrimes (L ⊗[K] F)) :
    Algebra.trdeg L ((L ⊗[K] F) ⧸ q) = Cardinal.mk σ := by
  let T := (L ⊗[K] FractionRing (MvPolynomial σ K))
    ⊗[FractionRing (MvPolynomial σ K)] F
  letI : CommRing T := inferInstance
  let e : T ≃ₐ[L] L ⊗[K] F := rightScalarTensorCancel
  let p : Ideal T := q.comap e.toRingHom
  have hp : p ∈ minimalPrimes T := scalarTensor_minimalPrime_comap e hq
  have htr := rationalFunctionTensor_algebraicExtension_trdeg
    (K := K) (L := L) (σ := σ) (F := F) p hp
  calc
    Algebra.trdeg L ((L ⊗[K] F) ⧸ q) = Algebra.trdeg L (T ⧸ p) :=
      (scalarTensor_quotient_trdeg_comap e q).symm
    _ = Cardinal.mk σ := htr

end RationalFieldExtension

/-- Localization does not change the transcendence degree of the quotient by a
prime disjoint from its denominators.-/
theorem localization_quotient_trdeg
    {K R S : Type u} [Field K] [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
    (M : Submonoid R) [IsLocalization M S]
    (q : Ideal R) [q.IsPrime] (hd : Disjoint (M : Set R) (q : Set R)) :
    Algebra.trdeg K (S ⧸ q.map (algebraMap R S)) = Algebra.trdeg K (R ⧸ q) := by
  let Q := q.map (algebraMap R S)
  have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S q inferInstance hd
  letI : Q.IsPrime := hQ
  have hc : Q.under R = q := IsLocalization.under_map_of_isPrime_disjoint M S inferInstance hd
  letI : Algebra (R ⧸ q) (S ⧸ Q) :=
    Ideal.Quotient.algebraQuotientOfLEComap (show q ≤ Q.under R from hc.symm.le)
  haveI : IsScalarTower K (R ⧸ q) (S ⧸ Q) := by
    refine IsScalarTower.of_algebraMap_eq fun k ↦ ?_
    symm
    change Ideal.quotientMap Q (algebraMap R S) _ (algebraMap K (R ⧸ q) k) = _
    rw [Ideal.quotientMap_algebraMap]
    simp only [← IsScalarTower.algebraMap_apply, Ideal.Quotient.mk_algebraMap]
  letI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ q) M) (S ⧸ Q) := inferInstance
  letI : FaithfulSMul (R ⧸ q) (S ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective (R ⧸ q) (S ⧸ Q)).mpr
      (Ideal.quotientMap_injective' hc.le)
  letI : Algebra.IsAlgebraic (R ⧸ q) (S ⧸ Q) :=
    IsLocalization.isAlgebraic (S ⧸ Q) (Algebra.algebraMapSubmonoid (R ⧸ q) M)
  exact SchemeNormalCone.Algebra.trdeg_eq_of_isAlgebraic K (R ⧸ q) (S ⧸ Q)

/-- Every generic component of scalar extension of a field has its original
transcendence degree over the new scalar field. No finite-generation assumption
is needed. The proof chooses a genuine transcendence basis, not a desired degree
formula.-/
theorem fieldTensor_trdeg_quotient
    {K L F : Type u} [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra K F]
    {q : Ideal (L ⊗[K] F)} (hq : q ∈ minimalPrimes (L ⊗[K] F)) :
    Algebra.trdeg L ((L ⊗[K] F) ⧸ q) = Algebra.trdeg K F := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K F
  let M := IntermediateField.adjoin K (Set.range ((↑) : s → F))
  let B := FractionRing (MvPolynomial s K)
  let e : B ≃ₐ[K] M := hs.1.aevalEquivField
  let j : B →ₐ[K] F := M.val.comp e.toAlgHom
  letI : Algebra B F := j.toRingHom.toAlgebra
  letI : IsScalarTower K B F := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  letI : Algebra.IsAlgebraic M F := hs.isAlgebraic_field
  haveI : Algebra.IsAlgebraic B F :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq e.toRingHom (RingHom.id F)
      e.surjective Function.injective_id (by rfl)
  calc
    Algebra.trdeg L ((L ⊗[K] F) ⧸ q) = Cardinal.mk s :=
      rationalFieldExtensionTensor_trdeg (σ := s) hq
    _ = Algebra.trdeg K F := hs.cardinalMk_eq_trdeg

/-- Generic components of scalar extension of an arbitrary domain preserve its
transcendence degree. The denominator localization is constructed, not assumed.
In particular this applies to finite-type integral fibres.-/
theorem domainFieldTensor_trdeg_quotient
    {K L A : Type u} [Field K] [Field L] [CommRing A] [IsDomain A]
    [Algebra K L] [Algebra K A]
    {q : Ideal (L ⊗[K] A)} (hq : q ∈ minimalPrimes (L ⊗[K] A)) :
    Algebra.trdeg L ((L ⊗[K] A) ⧸ q) = Algebra.trdeg K A := by
  let T := L ⊗[K] A
  let F := FractionRing A
  let U := L ⊗[K] F
  letI : CommRing T := inferInstance
  letI : CommRing U := inferInstance
  let φ : T →ₐ[L] U := Algebra.TensorProduct.map (AlgHom.id L L)
    (IsScalarTower.toAlgHom K A F)
  letI : Algebra T U := φ.toRingHom.toAlgebra
  letI : IsScalarTower L T U := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let M := (nonZeroDivisors A).map
    (Algebra.TensorProduct.includeRight (R := K) (A := L))
  have hφ : (algebraMap T U).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap A F) := by
    apply RingHom.ext
    intro a
    rfl
  letI : IsLocalization M U :=
    IsLocalization.tensorProduct_tensorProduct_right K L (nonZeroDivisors A) F hφ
  letI : q.IsPrime := hq.1.1
  letI : Algebra A T := Algebra.TensorProduct.rightAlgebra
  letI : Module.Free K L := Module.Free.of_divisionRing K L
  letI : Module.Flat A T := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight K A L).toLinearEquiv.symm
  have hq0 : q.under A = ⊥ := by
    have h := minimalPrime_under_of_flat (R := A) hq
    simpa only [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] using h
  have hd : Disjoint (M : Set T) (q : Set T) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hqa
    have : a ∈ q.under A := hqa
    rw [hq0, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero ha this
  let Q := q.map (algebraMap T U)
  have hc : Q.under T = q := IsLocalization.under_map_of_isPrime_disjoint M U inferInstance hd
  have hQ : Q ∈ minimalPrimes U := by
    have h := (IsLocalization.minimalPrimes_map M U (⊥ : Ideal T))
    rw [Ideal.map_bot] at h
    change Q ∈ (⊥ : Ideal U).minimalPrimes
    rw [h]
    change Q.under T ∈ minimalPrimes T
    rw [hc]
    exact hq
  letI : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  calc
    Algebra.trdeg L (T ⧸ q) = Algebra.trdeg L (U ⧸ Q) :=
      (localization_quotient_trdeg M q hd).symm
    _ = Algebra.trdeg K F := fieldTensor_trdeg_quotient hQ
    _ = Algebra.trdeg K A :=
      SchemeNormalCone.Algebra.trdeg_eq_of_isAlgebraic K A F

end AlgebraicGeometry.Chow.ProjectiveBaseChangeDimension
