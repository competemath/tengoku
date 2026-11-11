/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.GroupTheory.CosetCover
import Tengoku.Seed.LinearAlgebra.Dimension.Free
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basis
import Tengoku.Seed.LinearAlgebra.TensorProduct.Quotient
import Tengoku.Seed.RingTheory.FiniteType
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Basic
import Tengoku.Seed.RingTheory.Nakayama
import Tengoku.Seed.RingTheory.TensorProduct.Basic
import Tengoku.Seed.RingTheory.TensorProduct.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Selecting a basis from a generating submodule over a semi-local ring

Let `R` be a local ring with infinite residue field, `S` an `R`-algebra with finitely many
maximal ideals containing the extension of the maximal ideal of `R`, and `M` a finite free
`S`-module. This file proves that an `R`-submodule spanning `M` over `S` contains an `S`-basis,
following [Stacks 03C1](https://stacks.math.columbia.edu/tag/03C1).
-/

open Submodule

section BasisOfSpan

variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

/-- A spanning family of cardinality `r` in a finite free module of rank `r` determines a basis.-/
noncomputable def basisOfSpanRangeEqTop [Nontrivial S] [Module.Free S M] [Module.Finite S M]
    {r : ℕ} (hr : Module.finrank S M = r) {y : Fin r → M}
    (hspan : Submodule.span S (Set.range y) = ⊤) : Module.Basis (Fin r) S M := by
  classical
  let φ : (Fin r → S) →ₗ[S] M := Fintype.linearCombination S y
  have hφsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspan
  have hφinj : Function.Injective φ := by
    let b : Module.Basis (Fin r) S M := (Module.finBasis S M).reindex (finCongr hr)
    have hψ : Function.Surjective (b.equivFun.toLinearMap ∘ₗ φ) :=
      b.equivFun.surjective.comp hφsurj
    have hinj := OrzechProperty.injective_of_surjective_endomorphism _ hψ
    intro a a' haa'
    exact hinj (congrArg b.equivFun haa')
  exact (Pi.basisFun S (Fin r)).map (LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩)

/-- The basis constructed by `basisOfSpanRangeEqTop` consists of the original spanning family.-/
@[simp]
theorem basisOfSpanRangeEqTop_apply [Nontrivial S] [Module.Free S M] [Module.Finite S M]
    {r : ℕ} (hr : Module.finrank S M = r) {y : Fin r → M}
    (hspan : Submodule.span S (Set.range y) = ⊤) (i : Fin r) :
    basisOfSpanRangeEqTop hr hspan i = y i := by
  classical
  set_option backward.isDefEq.respectTransparency false in
    simp only [basisOfSpanRangeEqTop, Module.Basis.map_apply, Pi.basisFun_apply,
      LinearEquiv.ofBijective_apply, Fintype.linearCombination_apply, Pi.single_apply,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end BasisOfSpan

section Nakayama

variable {S M' : Type*} [CommRing S] [AddCommGroup M'] [Module S M']

/-- A finite-family version of Nakayama's lemma for a product of ideals in the Jacobson radical.-/
theorem Submodule.eq_bot_of_forall_le_smul_of_prod_le_jacobson (Q : Submodule S M')
    (hfg : Q.FG) {s : ℕ} (n : Fin s → Ideal S) (hsmul : ∀ j, Q ≤ n j • Q)
    (hjac : (∏ j, n j) ≤ (⊥ : Ideal S).jacobson) : Q = ⊥ := by
  classical
  have hprod : ∀ t : Finset (Fin s), Q ≤ (∏ j ∈ t, n j) • Q := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty, one_smul] using (le_refl Q)
    | insert a t ha ih =>
      calc Q ≤ n a • Q := hsmul a
        _ ≤ n a • ((∏ j ∈ t, n j) • Q) := smul_mono_right _ ih
        _ = (∏ j ∈ insert a t, n j) • Q := by rw [Finset.prod_insert ha, smul_smul]
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (∏ j, n j) Q hfg
    (hprod Finset.univ) hjac

end Nakayama

section Avoidance

open IsLocalRing TensorProduct

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Every element after base change to the residue field is a pure tensor with first factor one.-/
theorem exists_one_tmul_eq_residueField {N' : Type*} [AddCommGroup N'] [Module R N']
    (x : ResidueField R ⊗[R] N') : ∃ z : N', (1 : ResidueField R) ⊗ₜ[R] z = x := by
  change ∃ z : N', (1 : R ⧸ maximalIdeal R) ⊗ₜ[R] z = x
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective
    (maximalIdeal R • (⊤ : Submodule R N'))
    (quotTensorEquivQuotSMul N' (maximalIdeal R) x)
  refine ⟨z, ?_⟩
  apply (quotTensorEquivQuotSMul N' (maximalIdeal R)).injective
  simpa only [quotTensorEquivQuotSMul_mk_one_tmul] using hz

/-- A nonzero element remains nonzero as a pure tensor when the maximal ideal kills its module.-/
theorem one_tmul_ne_zero_of_smul_top_eq_bot {T : Type*} [AddCommGroup T] [Module R T]
    (hmT : maximalIdeal R • (⊤ : Submodule R T) = ⊥) {t : T} (ht : t ≠ 0) :
    (1 : ResidueField R) ⊗ₜ[R] t ≠ (0 : ResidueField R ⊗[R] T) := by
  intro h0
  have h1 : quotTensorEquivQuotSMul T (maximalIdeal R)
      ((Ideal.Quotient.mk (maximalIdeal R) 1) ⊗ₜ[R] t) = 0 := by
    rw [show (Ideal.Quotient.mk (maximalIdeal R) 1) = (1 : R ⧸ maximalIdeal R) from map_one _]
    exact h0 ▸ map_zero _
  rw [quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero, hmT] at h1
  exact ht h1

/-- A nonzero linear map into a module killed by the maximal ideal remains nonzero after base
change.-/
theorem baseChange_ne_zero_of_ne_zero_of_smul_top_eq_bot {N' T : Type*}
    [AddCommGroup N'] [Module R N'] [AddCommGroup T] [Module R T]
    (hmT : maximalIdeal R • (⊤ : Submodule R T) = ⊥) (f : N' →ₗ[R] T) {x : N'}
    (hx : f x ≠ 0) : LinearMap.baseChange (ResidueField R) f ≠ 0 := by
  intro hzero
  refine one_tmul_ne_zero_of_smul_top_eq_bot hmT hx ?_
  rw [show ((1 : ResidueField R) ⊗ₜ[R] (f x) : ResidueField R ⊗[R] T)
      = LinearMap.baseChange (ResidueField R) f (1 ⊗ₜ[R] x) from
    (LinearMap.baseChange_tmul _ _ _).symm, hzero, LinearMap.zero_apply]

/-- Over an infinite residue field, one pure tensor simultaneously avoids finitely many kernels.-/
theorem exists_one_tmul_baseChange_ne_zero [Infinite (ResidueField R)]
    {N' : Type*} [AddCommGroup N'] [Module R N'] {s : ℕ}
    {T : Fin s → Type*} [∀ j, AddCommGroup (T j)] [∀ j, Module R (T j)]
    (h : ∀ j, N' →ₗ[R] T j)
    (hne : ∀ j, LinearMap.baseChange (ResidueField R) (h j) ≠ 0) :
    ∃ z : N', ∀ j,
      LinearMap.baseChange (ResidueField R) (h j) (1 ⊗ₜ[R] z) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hcover : ⋃ j, ((LinearMap.ker ((h j).baseChange (ResidueField R)) :
      Submodule (ResidueField R) (ResidueField R ⊗[R] N')) :
      Set (ResidueField R ⊗[R] N')) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨z, rfl⟩ := exists_one_tmul_eq_residueField x
    obtain ⟨j, hj⟩ := hcon z
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcover
  exact hne j (LinearMap.ker_eq_top.mp hj)

end Avoidance

section Semilocal

open IsLocalRing TensorProduct

variable {R : Type*} [CommRing R] [IsLocalRing R] [Infinite (ResidueField R)]
variable {S : Type*} [CommRing S] [Nontrivial S] [Algebra R S]
variable {M : Type*} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Free S M] [Module.Finite S M]

private noncomputable def fibreEval (n : Ideal S) : M →ₗ[S] (S ⧸ n) ⊗[S] M :=
  TensorProduct.mk S (S ⧸ n) M 1

end Semilocal
