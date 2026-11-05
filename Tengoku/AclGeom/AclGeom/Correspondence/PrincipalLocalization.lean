/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.AlgebraicGeometry.Birational.Dominant
import Tengoku.Seed.AlgebraicGeometry.Restrict
import Tengoku.Seed.RingTheory.Localization.AsSubring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Clearing denominators on affine charts

This module spreads an injective homomorphism from a finitely generated
algebra into the fraction field of a domain to a dominant morphism defined on
one dense principal open of the source spectrum.

For a finite family `b_i` generating `B` and an embedding `φ : B → K(A)`, a
fraction presentation is chosen for every `φ(b_i)`.  The product `d` of their
nonzero denominators is nonzero, all generator images lie in `A[1/d]`, and
therefore `φ` factors injectively through that localization.  Taking spectra
gives the concrete partial map on `D(d)` needed for birational chart gluing.

This module is part of the formalization of the
Evans--Hrushovski--Gismatullin reconstruction theorem; the source of truth
is `sources/blueprint.tex`.
-/

open CategoryTheory
open AlgebraicGeometry
open scoped nonZeroDivisors

namespace AclGeom

noncomputable section

universe u v

namespace PrincipalLocalization

variable {A B : Type u} [CommRing A] [CommRing B] [IsDomain A]

/-- A ring embedding `B → A[1/d]` gives a partial map
`Spec A ⤏ Spec B` whose domain is the principal open `D(d)`.-/
def partialMap (d : A) (hd : d ≠ 0)
    (φ : B →+* Localization.Away d) (_hφ : Function.Injective φ) :
    (Spec (.of A)).PartialMap (Spec (.of B)) where
  domain := PrimeSpectrum.basicOpen d
  dense_domain := (PrimeSpectrum.basicOpen d).2.dense <| by
    apply (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp
    intro hbot
    exact hd ((PrimeSpectrum.basicOpen_eq_bot_iff d).mp hbot).eq_zero
  hom := (basicOpenIsoSpecAway (R := .of A) d).hom ≫
    Spec.map (CommRingCat.ofHom φ)

/-- The principal-open partial map attached to an injective localization map
is dominant.-/
instance partialMap_isDominant (d : A) (hd : d ≠ 0)
    (φ : B →+* Localization.Away d) (hφ : Function.Injective φ) :
    IsDominant (partialMap d hd φ hφ).hom := by
  have hspec : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    intro x hx
    have hx0 : x = 0 := hφ (by simpa using hx)
    subst x
    exact Ideal.zero_mem _
  unfold partialMap
  dsimp only
  infer_instance

/-- The principal open `D(d)` regarded as an open subscheme of `Spec A`.-/
def awayOpen (d : A) : (Spec (.of A)).Opens :=
  PrimeSpectrum.basicOpen d

/-- The standard identification of the principal open `D(d)` with
`Spec A[1/d]`.-/
def awayOpenIso (d : A) :
    (awayOpen d).toScheme ≅ Spec (.of (Localization.Away d)) :=
  basicOpenIsoSpecAway (R := CommRingCat.of A) d

/-- A nonzero principal function does not vanish at the generic point.-/
theorem genericPoint_mem_awayOpen (d : A) (hd : d ≠ 0) :
    genericPoint (Spec (.of A)) ∈ awayOpen d := by
  apply ((genericPoint_spec (Spec (.of A))).mem_open_set_iff
    (awayOpen d).2).mpr
  rw [Set.univ_inter]
  refine ⟨(⊥ : PrimeSpectrum A), ?_⟩
  change d ∉ (⊥ : Ideal A)
  simpa using hd

/-- The ring map from `A[1/d]` to the function field of `Spec A` obtained by
lifting the generic point through `D(d)`.-/
noncomputable def genericAwayMap (d : A) (hd : d ≠ 0) :
    Localization.Away d →+* (Spec (.of A)).functionField :=
  let g : Spec ((Spec (.of A)).functionField) ⟶
      Spec (.of (Localization.Away d)) := by
    exact (awayOpen d).fromSpecStalkOfMem _
        (genericPoint_mem_awayOpen d hd) ≫
      (awayOpenIso d).hom
  (Spec.preimage g).hom

/-- The generic-point map from `A[1/d]` extends the canonical map from `A`
to the function field of `Spec A`.-/
theorem genericAwayMap_comp_algebraMap (d : A) (hd : d ≠ 0) :
    (genericAwayMap d hd).comp
        (algebraMap A (Localization.Away d)) =
      (StructureSheaf.toStalk A
        (genericPoint (Spec (.of A)))).hom := by
  have hscheme :
      ((awayOpen d).fromSpecStalkOfMem _
          (genericPoint_mem_awayOpen d hd) ≫
          (awayOpenIso d).hom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap A (Localization.Away d))) =
        (Spec (.of A)).fromSpecStalk
          (genericPoint (Spec (.of A))) := by
    rw [Category.assoc]
    rw [show (awayOpenIso d).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap A (Localization.Away d))) =
        (awayOpen d).ι by
      exact basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of A) d]
    exact (awayOpen d).fromSpecStalkOfMem_ι _ _
  have hp := congrArg Spec.preimage hscheme
  rw [Spec.fromSpecStalk_eq'] at hp
  simp only [Spec.preimage_comp] at hp
  have hpre : Spec.preimage (Spec.map
      (StructureSheaf.toStalk A
        (genericPoint (Spec (.of A))))) =
      StructureSheaf.toStalk A
        (genericPoint (Spec (.of A))) :=
    Spec.preimage_map _
  have hp2 := hp.trans hpre
  have hpreAlg : Spec.preimage (Spec.map (CommRingCat.ofHom
      (algebraMap A (Localization.Away d)))) =
      CommRingCat.ofHom (algebraMap A (Localization.Away d)) :=
    Spec.preimage_map _
  have hp3 := (congrArg (fun q ↦ q ≫ Spec.preimage
      ((awayOpen d).fromSpecStalkOfMem _
        (genericPoint_mem_awayOpen d hd) ≫ (awayOpenIso d).hom))
      hpreAlg.symm).trans hp2
  have hp' := congrArg CommRingCat.Hom.hom hp3
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hp'
  unfold genericAwayMap
  exact hp'

/-- The generic-point map out of `A[1/d]` is the canonical localization map
to the function field.-/
theorem genericAwayMap_eq_mapToFractionRing (d : A) (hd : d ≠ 0) :
    letI : Algebra A (Spec (.of A)).functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
    letI : IsFractionRing A (Spec (.of A)).functionField :=
      AlgebraicGeometry.functionField_isFractionRing_of_affine (.of A)
    genericAwayMap d hd =
      (Localization.mapToFractionRing ((Spec (.of A)).functionField)
        (Submonoid.powers d) (Localization.Away d)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hd)).toRingHom := by
  letI : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  letI : IsFractionRing A (Spec (.of A)).functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine (.of A)
  apply IsLocalization.ringHom_ext (Submonoid.powers d)
  rw [genericAwayMap_comp_algebraMap]
  apply RingHom.ext
  intro z
  change algebraMap A (Spec (.of A)).functionField z = _
  exact ((Localization.mapToFractionRing ((Spec (.of A)).functionField)
    (Submonoid.powers d) (Localization.Away d)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hd))).commutes z |>.symm

-- Unfold the generic-point scheme/stalk aliases while matching the Spec maps.
set_option backward.isDefEq.respectTransparency false in
/-- The generic-point morphism of the principal-open partial map is induced
by its cleared localization homomorphism followed by the canonical map to the
source function field.-/
theorem partialMap_fromFunctionField_eq (d : A) (hd : d ≠ 0)
    (φ : B →+* Localization.Away d) (hφ : Function.Injective φ) :
    (partialMap d hd φ hφ).fromFunctionField =
      Spec.map (CommRingCat.ofHom ((genericAwayMap d hd).comp φ)) := by
  unfold Scheme.PartialMap.fromFunctionField
    Scheme.PartialMap.fromSpecStalkOfMem partialMap
  change (awayOpen d).fromSpecStalkOfMem _ _ ≫
      ((awayOpenIso d).hom ≫ Spec.map (CommRingCat.ofHom φ)) = _
  rw [← Category.assoc]
  rw [← Spec.map_preimage ((awayOpen d).fromSpecStalkOfMem _ _ ≫
    (awayOpenIso d).hom)]
  rw [← Spec.map_comp]
  congr 1

namespace CommonDenominator

variable {R K : Type u} [CommRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- A chosen numerator for an element of a fraction field.-/
noncomputable def numerator (x : K) : R :=
  (IsFractionRing.div_surjective R x).choose

/-- A chosen non-zero-divisor denominator for an element of a fraction
field.-/
noncomputable def denominator (x : K) : R :=
  (IsFractionRing.div_surjective R x).choose_spec.choose

/-- The chosen denominator is a non-zero-divisor.-/
theorem denominator_mem (x : K) : denominator (R := R) x ∈ R⁰ :=
  (IsFractionRing.div_surjective R x).choose_spec.choose_spec.1

/-- The chosen numerator and denominator represent the original element.-/
theorem fraction_eq (x : K) :
    algebraMap R K (numerator (R := R) x) /
      algebraMap R K (denominator (R := R) x) = x :=
  (IsFractionRing.div_surjective R x).choose_spec.choose_spec.2

variable {ι : Type v} [Fintype ι]

/-- One denominator for a finite family of fraction-field elements: the
product of their chosen denominators.-/
noncomputable def common (x : ι → K) : R :=
  ∏ i, denominator (R := R) (x i)

variable [IsDomain R]

/-- The common denominator of a finite family is nonzero.-/
theorem common_ne_zero (x : ι → K) : common (R := R) x ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact mem_nonZeroDivisors_iff_ne_zero.mp (denominator_mem (R := R) (x i))

/-- Every member of the finite family lies in the localization at its common
denominator.-/
theorem mem_localization (x : ι → K) (i : ι) :
    x i ∈ Localization.subalgebra.ofField K
      (Submonoid.powers (common (R := R) x))
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (common_ne_zero (R := R) x)) := by
  classical
  let q : R := ∏ j ∈ Finset.univ.erase i, denominator (R := R) (x j)
  let d := common (R := R) x
  let n := numerator (R := R) (x i)
  let s := denominator (R := R) (x i)
  have hs : s ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (denominator_mem (R := R) (x i))
  have hq : q ≠ 0 := by
    dsimp [q]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact mem_nonZeroDivisors_iff_ne_zero.mp (denominator_mem (R := R) (x j))
  have hd : d = s * q := by
    dsimp [d, s, q, common]
    symm
    exact Finset.mul_prod_erase Finset.univ
      (fun j ↦ denominator (R := R) (x j)) (Finset.mem_univ i)
  change ∃ (a t : R) (_ : t ∈ Submonoid.powers d),
    x i = algebraMap R K a * (algebraMap R K t)⁻¹
  refine ⟨n * q, d, Submonoid.mem_powers d, ?_⟩
  rw [← fraction_eq (R := R) (x i)]
  dsimp [n, s]
  rw [map_mul, hd, map_mul]
  have hsK : algebraMap R K s ≠ 0 := by
    intro h
    apply hs
    exact IsFractionRing.injective R K (by simpa using h)
  have hqK : algebraMap R K q ≠ 0 := by
    intro h
    apply hq
    exact IsFractionRing.injective R K (by simpa using h)
  field_simp [hsK, hqK]
  simp [s, hsK]

end CommonDenominator

variable {k K : Type u} {ι : Type v} [Field k] [Field K]
  [Algebra k A] [Algebra A K] [Algebra k K] [IsScalarTower k A K]
  [IsFractionRing A K] [Algebra k B] [Fintype ι]

/-- Clear one common denominator from the images of a finite algebra
generating family, obtaining an algebra homomorphism into `A[1/d]`.-/
noncomputable def awayAlgHomOfGenerators
    (b : ι → B) (hb : Algebra.adjoin k (Set.range b) = ⊤)
    (φ : B →ₐ[k] K) :
    B →ₐ[k] Localization.Away
      (CommonDenominator.common (R := A) (fun i ↦ φ (b i))) := by
  let x : ι → K := fun i ↦ φ (b i)
  let d : A := CommonDenominator.common (R := A) x
  let hd : d ≠ 0 := CommonDenominator.common_ne_zero (R := A) x
  let hS : Submonoid.powers d ≤ A⁰ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hd
  let S : Subalgebra A K :=
    Localization.subalgebra.ofField K (Submonoid.powers d) hS
  let Sk : Subalgebra k K := S.restrictScalars k
  have hgen (i : ι) : φ (b i) ∈ Sk := by
    exact CommonDenominator.mem_localization (R := A) x i
  have hall (z : B) : φ z ∈ Sk := by
    have hle : Algebra.adjoin k (Set.range b) ≤ Sk.comap φ := by
      apply Algebra.adjoin_le
      rintro z ⟨i, rfl⟩
      exact hgen i
    rw [hb] at hle
    exact hle (Set.mem_univ z)
  let ψS : B →ₐ[k] Sk := φ.codRestrict Sk hall
  let eA : Localization.Away d ≃ₐ[A] S :=
    IsLocalization.algEquiv (Submonoid.powers d) _ _
  let e : Localization.Away d ≃ₐ[k] Sk := eA.restrictScalars k
  exact e.symm.toAlgHom.comp ψS

/-- Mapping the cleared-denominator factorization back to the fraction field
recovers the original algebra homomorphism.-/
theorem awayAlgHomOfGenerators_mapToFractionRing
    (b : ι → B) (hb : Algebra.adjoin k (Set.range b) = ⊤)
    (φ : B →ₐ[k] K) (z : B) :
    let x : ι → K := fun i ↦ φ (b i)
    let d : A := CommonDenominator.common (R := A) x
    let hd : d ≠ 0 := CommonDenominator.common_ne_zero (R := A) x
    Localization.mapToFractionRing K (Submonoid.powers d)
      (Localization.Away d)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
      (awayAlgHomOfGenerators (A := A) b hb φ z) = φ z := by
  let x : ι → K := fun i ↦ φ (b i)
  let d : A := CommonDenominator.common (R := A) x
  let hd : d ≠ 0 := CommonDenominator.common_ne_zero (R := A) x
  let hS : Submonoid.powers d ≤ A⁰ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hd
  let S : Subalgebra A K :=
    Localization.subalgebra.ofField K (Submonoid.powers d) hS
  let Sk : Subalgebra k K := S.restrictScalars k
  have hall (z : B) : φ z ∈ Sk := by
    have hgen (i : ι) : φ (b i) ∈ Sk := by
      exact CommonDenominator.mem_localization (R := A) x i
    have hle : Algebra.adjoin k (Set.range b) ≤ Sk.comap φ := by
      apply Algebra.adjoin_le
      rintro z ⟨i, rfl⟩
      exact hgen i
    rw [hb] at hle
    exact hle (Set.mem_univ z)
  let ψS : B →ₐ[k] Sk := φ.codRestrict Sk hall
  let eA : Localization.Away d ≃ₐ[A] S :=
    IsLocalization.algEquiv (Submonoid.powers d) _ _
  let e : Localization.Away d ≃ₐ[k] Sk := eA.restrictScalars k
  change Localization.mapToFractionRing K (Submonoid.powers d)
      (Localization.Away d) hS (e.symm (ψS z)) = φ z
  have hmaps :
      Localization.mapToFractionRing K (Submonoid.powers d)
          (Localization.Away d) hS =
        (Subalgebra.val S).comp eA.toAlgHom :=
    (IsLocalization.algHom_subsingleton (Submonoid.powers d)).elim _ _
  rw [AlgHom.congr_fun hmaps]
  change ((e (e.symm (ψS z)) : Sk) : K) = φ z
  rw [e.apply_symm_apply]
  rfl

/-- If the original fraction-field homomorphism is injective, so is its
cleared-denominator factorization.-/
theorem awayAlgHomOfGenerators_injective
    (b : ι → B) (hb : Algebra.adjoin k (Set.range b) = ⊤)
    (φ : B →ₐ[k] K) (hφ : Function.Injective φ) :
    Function.Injective (awayAlgHomOfGenerators (A := A) b hb φ) := by
  intro z w hzw
  apply hφ
  let x : ι → K := fun i ↦ φ (b i)
  let d : A := CommonDenominator.common (R := A) x
  let hd : d ≠ 0 := CommonDenominator.common_ne_zero (R := A) x
  let F := Localization.mapToFractionRing K (Submonoid.powers d)
    (Localization.Away d)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  have h := congr_arg F hzw
  calc
    φ z = F (awayAlgHomOfGenerators (A := A) b hb φ z) := by
      exact (awayAlgHomOfGenerators_mapToFractionRing
        (A := A) b hb φ z).symm
    _ = F (awayAlgHomOfGenerators (A := A) b hb φ w) := h
    _ = φ w := by
      exact awayAlgHomOfGenerators_mapToFractionRing
        (A := A) b hb φ w

/-- An injective homomorphism from a finitely generated algebra to the
fraction field of `A` spreads to a dominant partial map on one explicit dense
principal open of `Spec A`.-/
noncomputable def partialMapOfGenerators
    (b : ι → B) (hb : Algebra.adjoin k (Set.range b) = ⊤)
    (φ : B →ₐ[k] K) (hφ : Function.Injective φ) :
    (Spec (.of A)).PartialMap (Spec (.of B)) :=
  partialMap
    (CommonDenominator.common (R := A) (fun i ↦ φ (b i)))
    (CommonDenominator.common_ne_zero (R := A) (fun i ↦ φ (b i)))
    (awayAlgHomOfGenerators (A := A) b hb φ).toRingHom
    (awayAlgHomOfGenerators_injective (A := A) b hb φ hφ)

/-- The partial map obtained by clearing the generator denominators is
dominant.-/
instance partialMapOfGenerators_isDominant
    (b : ι → B) (hb : Algebra.adjoin k (Set.range b) = ⊤)
    (φ : B →ₐ[k] K) (hφ : Function.Injective φ) :
    IsDominant (partialMapOfGenerators (A := A) b hb φ hφ).hom := by
  unfold partialMapOfGenerators
  infer_instance

end PrincipalLocalization

end

end AclGeom
