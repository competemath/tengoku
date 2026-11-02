/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.Ideal.GoingDown
import Tengoku.Seed.RingTheory.Flat.Stability
import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Algebra
import Tengoku.Seed.RingTheory.Ideal.MinimalPrime.Localization
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.NormalCone.FiniteTypeKrullDimension
import Tengoku.Seed.RingTheory.IntegralClosure.Algebra.Basic
import Tengoku.Seed.RingTheory.Localization.BaseChange
import Tengoku.Seed.RingTheory.TensorProduct.MvPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Algebraic prerequisites for projective base-change relative dimension

Flat algebras preserve contraction of generic components. Faithfully flat
algebras also supply a generic component above every original component. These
facts are specialized to actual field scalar extensions, without finiteness or
reducedness assumptions.

For a domain of scalars, a generic component of a flat integral algebra has an
injective scalar map and preserves transcendence degree. Scalar extension of a
rational-function field is proved to be a domain of the original transcendence
degree. Its algebraic-extension generic components retain that degree.

This module does not prove PureRelDim for the projective base-change morphism.
The remaining task is to transport the rational-function calculation through a
transcendence basis and the localization of an actual finite-type fibre, then
identify coefficient-supported scheme points and convert residue transcendence
degree to their heights. General-flat all-rank Segre naturality is not asserted.
All proofs here use default elaboration budgets.
-/

universe u v

noncomputable section

open scoped TensorProduct

namespace AlgebraicGeometry.Chow.ProjectiveBaseChangeDimension

/-- A generic component of a flat algebra contracts to a generic component.-/
theorem minimalPrime_under_of_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] {q : Ideal S} (hq : q ∈ minimalPrimes S) :
    q.under R ∈ minimalPrimes R := by
  letI : q.IsPrime := hq.1.1
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  intro p hp hpq
  letI : p.IsPrime := hp.1
  obtain ⟨Q, hQq, hQprime, hQover⟩ :=
    q.exists_ideal_le_liesOver_of_le (p := p) (q := q.under R) hpq
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver p := hQover
  have hqQ : q ≤ Q := hq.2 ⟨hQprime, bot_le⟩ hQq
  have hQ : Q = q := le_antisymm hQq hqQ
  exact le_of_eq ((Q.over_def p).trans (congrArg (Ideal.under R) hQ)).symm

/-- Faithful flatness supplies a generic component over every original component.-/
theorem exists_minimalPrime_over_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {p : Ideal R} (hp : p ∈ minimalPrimes R) :
    ∃ q ∈ minimalPrimes S, q.under R = p := by
  letI : p.IsPrime := hp.1.1
  obtain ⟨Q, hQ, hQover⟩ := p.exists_isPrime_liesOver_of_faithfullyFlat (B := S)
  letI : Q.IsPrime := hQ
  letI : Q.LiesOver p := hQover
  obtain ⟨q, hq, hqQ⟩ := (⊥ : Ideal S).exists_minimalPrimes_le (J := Q) bot_le
  refine ⟨q, hq, le_antisymm ?_ ?_⟩
  · rw [Q.over_def p]
    exact Ideal.comap_mono hqQ
  · exact hp.2 (minimalPrime_under_of_flat hq).1 (by
      rw [Q.over_def p]
      exact Ideal.comap_mono hqQ)

/-- Generic components are preserved and exhaust the original components under a
faithfully flat scalar extension.-/
theorem minimalPrimes_image_under_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] :
    Ideal.under R '' minimalPrimes S = minimalPrimes R := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact minimalPrime_under_of_flat hq
  · intro hp
    obtain ⟨q, hq, hqp⟩ := exists_minimalPrime_over_of_faithfullyFlat (S := S) hp
    exact ⟨q, hq, hqp⟩

/-- The generic points of a scalar-extended algebra contract to genuine generic
points of the original algebra. No finiteness or reducedness is needed.-/
theorem fieldTensor_minimalPrime_under
    {K L A : Type*} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A] {q : Ideal (A ⊗[K] L)}
    (hq : q ∈ minimalPrimes (A ⊗[K] L)) :
    q.under A ∈ minimalPrimes A := by
  letI : Module.Free K L := Module.Free.of_divisionRing K L
  exact minimalPrime_under_of_flat hq

/-- Every generic component survives scalar extension by a field.-/
theorem fieldTensor_exists_minimalPrime_over
    {K L A : Type*} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A] {p : Ideal A} (hp : p ∈ minimalPrimes A) :
    ∃ q ∈ minimalPrimes (A ⊗[K] L), q.under A = p := by
  letI : Module.Free K L := Module.Free.of_divisionRing K L
  exact exists_minimalPrime_over_of_faithfullyFlat hp

/-- A generic component of a flat algebra over a domain contains no nonzero
scalar. This is the injectivity boundary needed before passing to fraction fields.-/
theorem algebraMap_quotient_injective_of_minimalPrime_flat
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]
    [Module.Flat R S] {q : Ideal S} (hq : q ∈ minimalPrimes S) :
    Function.Injective (algebraMap R (S ⧸ q)) := by
  have hq0 : q.under R = ⊥ := by
    have := minimalPrime_under_of_flat (R := R) hq
    simpa only [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] using this
  apply (injective_iff_map_eq_zero (algebraMap R (S ⧸ q))).mpr
  intro r hr
  have hrq : algebraMap R S r ∈ q := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [Ideal.Quotient.mk_algebraMap] using hr
  have : r ∈ q.under R := hrq
  simpa only [hq0, Ideal.mem_bot] using this

/-- A generic component of a flat integral algebra has the same transcendence
degree as the domain of scalars. Integrality is genuine algebraic input, not a
conclusion about projective relative dimension.-/
theorem trdeg_quotient_eq_of_minimalPrime_flat_integral
    {K : Type u} {R S : Type v} [Field K] [CommRing R] [CommRing S] [IsDomain R]
    [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
    [Module.Flat R S] [Algebra.IsIntegral R S]
    {q : Ideal S} (hq : q ∈ minimalPrimes S) :
    Algebra.trdeg K (S ⧸ q) = Algebra.trdeg K R := by
  letI : q.IsPrime := hq.1.1
  letI : FaithfulSMul R (S ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective R (S ⧸ q)).mpr
      (algebraMap_quotient_injective_of_minimalPrime_flat hq)
  haveI : Algebra.IsIntegral R (S ⧸ q) := Algebra.IsIntegral.trans S
  exact SchemeNormalCone.Algebra.trdeg_eq_of_isAlgebraic K R (S ⧸ q)

/-- After an algebraic field extension, every generic component of the base
change preserves the transcendence degree of a domain base. This applies to the
rational-function localization used in generic-fibre dimension arguments.-/
theorem algebraicFieldTensor_trdeg_quotient
    {K : Type u} {L F R : Type v} [Field K] [Field L] [Field F]
    [CommRing R] [IsDomain R] [Algebra K F] [Algebra K R] [Algebra L R]
    [SMulCommClass K L R] [Algebra.IsAlgebraic K F]
    {q : Ideal (R ⊗[K] F)} (hq : q ∈ minimalPrimes (R ⊗[K] F)) :
    Algebra.trdeg L ((R ⊗[K] F) ⧸ q) = Algebra.trdeg L R := by
  letI : Module.Free K F := Module.Free.of_divisionRing K F
  exact trdeg_quotient_eq_of_minimalPrime_flat_integral hq

/-- Scalar extension of a rational-function field is a domain: its denominator
set is inherited from the original polynomial ring, rather than all nonzero
polynomials over the enlarged field.-/
theorem rationalFunctionTensor_isDomain
    {K L σ : Type*} [Field K] [Field L] [Algebra K L] :
    IsDomain (L ⊗[K] FractionRing (MvPolynomial σ K)) := by
  let P := MvPolynomial σ K
  let T := L ⊗[K] P
  let F := FractionRing P
  let U := L ⊗[K] F
  let φ : T →ₐ[L] U := Algebra.TensorProduct.map (AlgHom.id L L)
    (IsScalarTower.toAlgHom K P F)
  letI : Algebra T U := φ.toRingHom.toAlgebra
  letI : IsScalarTower L T U := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  letI : IsDomain T :=
    (MvPolynomial.algebraTensorAlgEquiv K L (σ := σ)).toRingEquiv.toMulEquiv.isDomain _
  have hφ : (algebraMap T U).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap P F) := by
    apply RingHom.ext
    intro p
    change φ (1 ⊗ₜ[K] p) = 1 ⊗ₜ[K] algebraMap P F p
    rfl
  letI : IsLocalization
      ((nonZeroDivisors P).map (Algebra.TensorProduct.includeRight (R := K) (A := L))) U :=
    IsLocalization.tensorProduct_tensorProduct_right K L (nonZeroDivisors P) F hφ
  letI : Module.Free K P := Module.Free.of_divisionRing K P
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : P →ₐ[K] T) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (R := T)
    (M := (nonZeroDivisors P).map (Algebra.TensorProduct.includeRight (R := K) (A := L))) U
  rintro _ ⟨p, hp, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  simpa only [map_zero] using hinj.ne (nonZeroDivisors.ne_zero hp)

/-- A scalar extension of a rational-function field preserves its original
transcendence degree even though its ring Krull dimension can decrease.-/
theorem rationalFunctionTensor_trdeg
    {K L σ : Type u} [Field K] [Field L] [Algebra K L] :
    Algebra.trdeg L (L ⊗[K] FractionRing (MvPolynomial σ K)) = Cardinal.mk σ := by
  let P := MvPolynomial σ K
  let T := L ⊗[K] P
  let F := FractionRing P
  let U := L ⊗[K] F
  let φ : T →ₐ[L] U := Algebra.TensorProduct.map (AlgHom.id L L)
    (IsScalarTower.toAlgHom K P F)
  letI : Algebra T U := φ.toRingHom.toAlgebra
  letI : IsScalarTower L T U := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  letI : IsDomain T :=
    (MvPolynomial.algebraTensorAlgEquiv K L (σ := σ)).toRingEquiv.toMulEquiv.isDomain _
  have hφ : (algebraMap T U).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap P F) := by
    apply RingHom.ext
    intro p
    change φ (1 ⊗ₜ[K] p) = 1 ⊗ₜ[K] algebraMap P F p
    rfl
  letI : IsLocalization
      ((nonZeroDivisors P).map (Algebra.TensorProduct.includeRight (R := K) (A := L))) U :=
    IsLocalization.tensorProduct_tensorProduct_right K L (nonZeroDivisors P) F hφ
  letI : Module.Free K P := Module.Free.of_divisionRing K P
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : P →ₐ[K] T) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  have hM : (nonZeroDivisors P).map
      (Algebra.TensorProduct.includeRight (R := K) (A := L)) ≤ nonZeroDivisors T := by
    rintro _ ⟨p, hp, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    simpa only [map_zero] using hinj.ne (nonZeroDivisors.ne_zero hp)
  letI : IsDomain U := rationalFunctionTensor_isDomain (K := K) (L := L) (σ := σ)
  letI : FaithfulSMul T U := (faithfulSMul_iff_algebraMap_injective T U).mpr
    (IsLocalization.injective U hM)
  letI : Algebra.IsAlgebraic T U := IsLocalization.isAlgebraic U
    ((nonZeroDivisors P).map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
  calc
    Algebra.trdeg L U = Algebra.trdeg L T :=
      SchemeNormalCone.Algebra.trdeg_eq_of_isAlgebraic L T U
    _ = Algebra.trdeg L (MvPolynomial σ L) :=
      (MvPolynomial.algebraTensorAlgEquiv K L (σ := σ)).trdeg_eq
    _ = Cardinal.mk σ := by rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id]

local instance rationalTensor_rightAlgebra
    {K L σ : Type u} [Field K] [Field L] [Algebra K L] :
    Algebra (FractionRing (MvPolynomial σ K))
      (L ⊗[K] FractionRing (MvPolynomial σ K)) := Algebra.TensorProduct.rightAlgebra

/-- The generic components of an algebraic extension of the scalar-extended
rational-function field have exactly the original transcendence degree. This is
the field-algebra core of generic-fibre dimension stability.-/
theorem rationalFunctionTensor_algebraicExtension_trdeg
    {K L σ F : Type u} [Field K] [Field L] [Field F] [Algebra K L]
    [Algebra (FractionRing (MvPolynomial σ K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial σ K)) F]
    : let T := (L ⊗[K] FractionRing (MvPolynomial σ K))
          ⊗[FractionRing (MvPolynomial σ K)] F
      letI : CommRing T := inferInstance
      ∀ (q : Ideal T), q ∈ minimalPrimes T →
        Algebra.trdeg L (T ⧸ q) = Cardinal.mk σ := by
  intro T q hq
  letI : IsDomain (L ⊗[K] FractionRing (MvPolynomial σ K)) :=
    rationalFunctionTensor_isDomain
  rw [algebraicFieldTensor_trdeg_quotient hq, rationalFunctionTensor_trdeg]

end AlgebraicGeometry.Chow.ProjectiveBaseChangeDimension
