/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `FiniteFamilySupportAnnihilation.lean`
in Vilin97/Clawristotle.
-/
import Tengoku.Aintlib.ModularCurves.ForMathlib.FiniteModuleSupportAnnihilation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform support annihilation over a finite family

Local support arguments on a finite family yield one common annihilating
exponent, even when the rings and modules vary with the index.
-/

noncomputable section

namespace Module

variable {ι : Type*} [Finite ι]
variable (R : ι → Type*) [∀ i, CommRing (R i)]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)]
variable [∀ i, Module (R i) (M i)]
variable (I : ∀ i, Ideal (R i))

/-- A finite family of independently annihilating powers has one common exponent.
@isnad1 id=ex.1h4v.s9.69dfecd160af from=translated src=- shape=b894c59a vocab=b3cf370a
-/
theorem exists_uniform_pow_le_annihilator
    (h : ∀ i, ∃ n : ℕ, I i ^ n ≤ Module.annihilator (R i) (M i)) :
    ∃ N : ℕ, ∀ i, I i ^ N ≤ Module.annihilator (R i) (M i) := by
  choose n hn using h
  let N : ℕ := ⨆ i, n i
  refine ⟨N, fun i ↦ ?_⟩
  exact
    (Ideal.pow_le_pow_right (le_ciSup (Finite.bddAbove_range n) i)).trans
      (hn i)

/-- Finite-family Noetherian support containment gives one common annihilating power.
@isnad1 id=ex.1h4v.s8.140a38b9938e from=translated src=- shape=a0eb0ad7 vocab=28e174dd
-/
theorem exists_uniform_pow_le_annihilator_of_support_subset_zeroLocus
    [∀ i, Module.Finite (R i) (M i)]
    [∀ i, IsNoetherianRing (R i)]
    (hsupport : ∀ i,
      Module.support (R i) (M i) ⊆ PrimeSpectrum.zeroLocus (I i)) :
    ∃ N : ℕ, ∀ i, I i ^ N ≤ Module.annihilator (R i) (M i) := by
  apply exists_uniform_pow_le_annihilator R M I
  intro i
  exact
    Module.exists_pow_le_annihilator_of_support_subset_zeroLocus
      (I i) (hsupport i)

/-- Return the common exponent as torsion-by-set witnesses.
@isnad1 id=ex.1h4v.s8.ccbadcb94342 from=translated src=- shape=aec44587 vocab=f3769639
-/
theorem exists_uniform_pow_isTorsionBySet_of_support_subset_zeroLocus
    [∀ i, Module.Finite (R i) (M i)]
    [∀ i, IsNoetherianRing (R i)]
    (hsupport : ∀ i,
      Module.support (R i) (M i) ⊆ PrimeSpectrum.zeroLocus (I i)) :
    ∃ N : ℕ, ∀ i,
      Module.IsTorsionBySet (R i) (M i)
        ((I i ^ N : Ideal (R i)) : Set (R i)) := by
  obtain ⟨N, hN⟩ :=
    exists_uniform_pow_le_annihilator_of_support_subset_zeroLocus
      R M I hsupport
  exact
    ⟨N, fun i ↦
      (Module.isTorsionBySet_iff_subset_annihilator
        (R := R i) (M := M i)).mpr (hN i)⟩

/-- Positive common exponent, preserving the support of every ideal.
@isnad1 id=ex.1h4v.s8.3a1fffbcc523 from=translated src=- shape=e8526eb7 vocab=d986bd12
-/
theorem exists_uniform_succ_pow_isTorsionBySet_of_support_subset_zeroLocus
    [∀ i, Module.Finite (R i) (M i)]
    [∀ i, IsNoetherianRing (R i)]
    (hsupport : ∀ i,
      Module.support (R i) (M i) ⊆ PrimeSpectrum.zeroLocus (I i)) :
    ∃ N : ℕ, ∀ i,
      Module.IsTorsionBySet (R i) (M i)
        ((I i ^ (N + 1) : Ideal (R i)) : Set (R i)) := by
  obtain ⟨N, hN⟩ :=
    exists_uniform_pow_isTorsionBySet_of_support_subset_zeroLocus
      R M I hsupport
  refine ⟨N, fun i ↦ ?_⟩
  apply
    (Module.isTorsionBySet_iff_subset_annihilator
      (R := R i) (M := M i)).mpr
  exact
    (Ideal.pow_le_pow_right (Nat.le_add_right N 1)).trans
      ((Module.isTorsionBySet_iff_subset_annihilator
        (R := R i) (M := M i)).mp (hN i))

end Module
