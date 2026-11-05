/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Tengoku.Seed.RingTheory.TensorProduct.Nontrivial
import Tengoku.Seed.RingTheory.Jacobson.Ring
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.RingTheory.FiniteStability
import Tengoku.Seed.RingTheory.Localization.Away.AdjoinRoot
import Tengoku.Seed.RingTheory.Spectrum.Prime.Chevalley
import Tengoku.Seed.RingTheory.Nullstellensatz

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Constructibility and Chevalley on field-valued points

`IsConstructibleOver` uses Mathlib's constructible subsets of a polynomial
prime spectrum. Its polynomial-data characterization is the usual finite
Boolean definition on points. `IsConstructibleOver.image_projection` proves
Chevalley's theorem on points over an algebraically closed ambient field.

The passage from spectral points to actual field-valued points is proved:
localize a prime quotient at the required nonvanishing, tensor with the ambient
field, and specialize a maximal quotient. Tensor nontriviality preserves the
specified base point. These results supply the constructibility foundation of
Section 9 of `sources/group_configuration_blueprint.tex`. The generic quantifier
is developed in `GroupConfig.Constructible.Generic`; the actual constructible group
and homogeneous space are proved in `GroupConfig.Constructible.CanonicalPresentation`.
The degree-only closure-membership usage claim is refuted in
`GroupConfig.ClosureCounterexample` (#31); fixed finite witness formulas use the
polynomial-data characterization and closure operations.
-/

open scoped TensorProduct

namespace GroupConfig

/-- Extend an embedding of the base to a point of a finite-type domain.
Used by the prime-lifting step in K-points Chevalley.-/
private theorem exists_algHom_of_injective_of_finiteType {A B K : Type*}
    [CommRing A] [CommRing B] [IsDomain B]
    [Field K] [IsAlgClosed K] [Algebra A B] [Algebra A K]
    [Algebra.FiniteType A B]
    (hB : Function.Injective (algebraMap A B))
    (hK : Function.Injective (algebraMap A K)) : Nonempty (B →ₐ[A] K) := by
  let : Nontrivial (K ⊗[A] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain A K B hK hB
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[A] B)
  let : m.IsMaximal := hm
  let : Field ((K ⊗[A] B) ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K ((K ⊗[A] B) ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing K ((K ⊗[A] B) ⧸ m)
  let φ : K ⊗[A] B →ₐ[K] K :=
    (IsAlgClosed.lift : ((K ⊗[A] B) ⧸ m) →ₐ[K] K).comp
      (Ideal.Quotient.mkₐ K m)
  exact ⟨(φ.restrictScalars A).comp Algebra.TensorProduct.includeRight⟩

/-- Quotient out a common kernel before applying the injective point-lifting lemma.-/
private theorem exists_ringHom_of_ker_eq {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B]
    [Field K] [IsAlgClosed K] (f : R →+* B) (g : R →+* K)
    (hf : f.FiniteType) (hker : RingHom.ker f = RingHom.ker g) :
    ∃ h : B →+* K, h.comp f = g := by
  let f' : R ⧸ RingHom.ker f →+* B := f.kerLift
  have hzero : ∀ r, r ∈ RingHom.ker f → g r = 0 := by
    intro r hr
    exact RingHom.mem_ker.mp (hker ▸ hr)
  let g' : R ⧸ RingHom.ker f →+* K := Ideal.Quotient.lift _ g hzero
  have hf' : f'.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk _)
    have hcomp : f'.comp (Ideal.Quotient.mk _) = f := by
      ext r
      exact f.kerLift_mk r
    exact hcomp.symm ▸ hf
  have hg' : Function.Injective g' :=
    RingHom.lift_injective_of_ker_le_ideal _ hzero hker.ge
  algebraize_only [f', g']
  let : Algebra.FiniteType (R ⧸ RingHom.ker f) B := hf'
  obtain ⟨h⟩ := exists_algHom_of_injective_of_finiteType (f.kerLift_injective) hg'
  refine ⟨h.toRingHom, ?_⟩
  ext r
  exact h.commutes (Ideal.Quotient.mk (RingHom.ker f) r)

/-- A prime over a specified point gives an actual point preserving a chosen nonvanishing.-/
private theorem exists_ringHom_of_prime {R S K : Type*}
    [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]
    (f : R →+* S) (g : R →+* K) (hf : f.FiniteType)
    (q : Ideal S) [q.IsPrime] (hq : q.comap f = RingHom.ker g)
    (b : S) (hb : b ∉ q) :
    ∃ h : S →+* K, h.comp f = g ∧ (∀ s ∈ q, h s = 0) ∧ h b ≠ 0 := by
  let B := Localization.Away (Ideal.Quotient.mk q b)
  have hb' : Ideal.Quotient.mk q b ≠ 0 :=
    fun h ↦ hb (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let : IsDomain B := Localization.Away.isDomain hb'
  let j : S →+* B := (algebraMap (S ⧸ q) B).comp (Ideal.Quotient.mk q)
  have hj : j.FiniteType :=
    (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective)
  have hinj : Function.Injective (algebraMap (S ⧸ q) B) :=
    IsLocalization.injective B (powers_le_nonZeroDivisors_of_noZeroDivisors hb')
  have hker : RingHom.ker (j.comp f) = RingHom.ker g := by
    rw [← hq]
    ext r
    change algebraMap (S ⧸ q) B (Ideal.Quotient.mk q (f r)) = 0 ↔ f r ∈ q
    rw [← map_zero (algebraMap (S ⧸ q) B), hinj.eq_iff, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨h, hh⟩ := exists_ringHom_of_ker_eq (j.comp f) g (hj.comp hf) hker
  refine ⟨h.comp j, ?_, ?_, ?_⟩
  · exact hh
  · intro s hs
    change h (algebraMap (S ⧸ q) B (Ideal.Quotient.mk q s)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hs, map_zero, map_zero]
  · exact ((IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk q b)).map h).ne_zero

/-- Lift a point in a constructible spectral image to an actual field-valued point.-/
private theorem exists_ringHom_of_constructible {R S K : Type*}
    [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]
    (f : R →+* S) (hf : f.FiniteType) (g : R →+* K)
    (C : Set (PrimeSpectrum S)) (hC : Topology.IsConstructible C)
    (hg : PrimeSpectrum.comap g ⟨⊥, inferInstance⟩ ∈ PrimeSpectrum.comap f '' C) :
    ∃ h : S →+* K, h.comp f = g ∧ PrimeSpectrum.comap h ⟨⊥, inferInstance⟩ ∈ C := by
  classical
  obtain ⟨q, hq, heq⟩ := hg
  obtain ⟨cells, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hC
  obtain ⟨cell, hcell, hqcell⟩ := Set.mem_iUnion₂.mp hq
  have hker : q.asIdeal.comap f = RingHom.ker g := by
    have heq' := congrArg PrimeSpectrum.asIdeal heq
    simpa only [PrimeSpectrum.comap_asIdeal, ← RingHom.ker_eq_comap_bot] using heq'
  have hn : cell.f ∉ q.asIdeal := by
    simpa only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
      using hqcell.2
  obtain ⟨h, hh, hqzero, hnzero⟩ := exists_ringHom_of_prime f g hf q.asIdeal hker cell.f hn
  refine ⟨h, hh, Set.mem_iUnion₂.mpr ⟨cell, hcell, ?_⟩⟩
  constructor
  · rw [PrimeSpectrum.mem_zeroLocus]
    rintro _ ⟨i, rfl⟩
    exact hqzero _ ((PrimeSpectrum.mem_zeroLocus q _).mp hqcell.1 ⟨i, rfl⟩)
  · simpa only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
      PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_bot] using hnzero

/-- A set of field-valued points is constructible over `k` if it is the pullback
of a constructible set in the polynomial prime spectrum.
`isConstructibleOver_iff_exists_polynomial_data` identifies this with a finite
union of polynomial equations and inequations over `k`.-/
def IsConstructibleOver (k : Type*) [Field k] {K ι : Type*} [Field K] [Algebra k K]
    (s : Set (ι → K)) : Prop :=
  ∃ C : Set (PrimeSpectrum (MvPolynomial ι k)), Topology.IsConstructible C ∧
    s = MvPolynomial.pointToPoint ⁻¹' C

/-- Constructibility over the base means a finite union of cells, each given by
finitely many polynomial equations and one polynomial inequation over that base.-/
theorem isConstructibleOver_iff_exists_polynomial_data {k K ι : Type*}
    [Field k] [Field K] [Algebra k K] {s : Set (ι → K)} :
    IsConstructibleOver k s ↔
      ∃ cells : PrimeSpectrum.ConstructibleSetData (MvPolynomial ι k),
        ∀ x, x ∈ s ↔ ∃ cell ∈ cells,
          (∀ i, MvPolynomial.aeval x (cell.g i) = 0) ∧
            MvPolynomial.aeval x cell.f ≠ 0 := by
  have hd (cells : PrimeSpectrum.ConstructibleSetData (MvPolynomial ι k)) (x : ι → K) :
      MvPolynomial.pointToPoint x ∈ cells.toSet ↔ ∃ cell ∈ cells,
        (∀ i, MvPolynomial.aeval x (cell.g i) = 0) ∧
          MvPolynomial.aeval x cell.f ≠ 0 := by
    simp [PrimeSpectrum.ConstructibleSetData.toSet,
      PrimeSpectrum.BasicConstructibleSetData.toSet, PrimeSpectrum.mem_zeroLocus,
      MvPolynomial.pointToPoint, Set.range_subset_iff, and_left_comm]
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨cells, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hC
    exact ⟨cells, hd cells⟩
  · rintro ⟨cells, hcells⟩
    exact ⟨cells.toSet, cells.isConstructible_toSet, Set.ext fun x ↦ (hcells x).trans
      (hd cells x).symm⟩

/-- The polynomial point has exactly the kernel of evaluation.-/
private theorem pointToPoint_eq_comap {k K ι : Type*} [Field k] [Field K] [Algebra k K]
    (x : ι → K) : MvPolynomial.pointToPoint (k := k) x =
      PrimeSpectrum.comap (MvPolynomial.aeval x).toRingHom ⟨⊥, inferInstance⟩ := by
  apply PrimeSpectrum.ext
  ext p
  simp [MvPolynomial.pointToPoint]

/-- `thm:chevalley`: Chevalley on field-valued points. Finite coordinate projections preserve
constructibility over an arbitrary base field when the ambient field is algebraically
closed. No transcendence-degree hypothesis is needed. This is the projection step
for constructible relations in the group-configuration blueprint.-/
theorem IsConstructibleOver.image_projection {k K ι κ : Type*}
    [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    [Finite ι] [Finite κ] {s : Set ((ι ⊕ κ) → K)} (hs : IsConstructibleOver k s) :
    IsConstructibleOver k ((fun x i ↦ x (Sum.inl i)) '' s) := by
  obtain ⟨C, hC, rfl⟩ := hs
  let f : MvPolynomial ι k →+* MvPolynomial (ι ⊕ κ) k :=
    (MvPolynomial.rename Sum.inl).toRingHom
  have hf : f.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C)
    have hc : f.comp MvPolynomial.C = MvPolynomial.C := by
      exact RingHom.ext fun c ↦ MvPolynomial.rename_C _ c
    rw [hc]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hp (x : (ι ⊕ κ) → K) : PrimeSpectrum.comap f
      (MvPolynomial.pointToPoint (k := k) x) =
      MvPolynomial.pointToPoint (k := k) (fun i ↦ x (Sum.inl i)) := by
    rw [pointToPoint_eq_comap, pointToPoint_eq_comap, ← PrimeSpectrum.comap_comp_apply]
    congr 1
    exact RingHom.ext fun p ↦ MvPolynomial.aeval_rename _ _ p
  refine ⟨PrimeSpectrum.comap f '' C,
    PrimeSpectrum.isConstructible_comap_image
      (RingHom.FinitePresentation.of_finiteType.mp hf) hC, ?_⟩
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨MvPolynomial.pointToPoint w, hw, hp w⟩
  · intro hx
    rw [Set.mem_preimage, pointToPoint_eq_comap] at hx
    obtain ⟨h, hh, hmem⟩ := exists_ringHom_of_constructible f hf
      (MvPolynomial.aeval x).toRingHom C hC hx
    let w : (ι ⊕ κ) → K := fun i ↦ h (MvPolynomial.X i)
    have hc (c : k) : h (MvPolynomial.C c) = algebraMap k K c := by
      have he := RingHom.congr_fun hh (MvPolynomial.C c)
      simpa [f] using he
    have hw : h = (MvPolynomial.aeval w).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simpa using hc c
      · intro i
        simp [w]
    refine ⟨w, ?_, ?_⟩
    · change MvPolynomial.pointToPoint w ∈ C
      rw [pointToPoint_eq_comap, ← hw]
      exact hmem
    · funext i
      have he := RingHom.congr_fun hh (MvPolynomial.X i)
      simpa [f, w] using he

end GroupConfig
