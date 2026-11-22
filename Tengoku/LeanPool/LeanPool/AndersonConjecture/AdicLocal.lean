/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import Tengoku.Seed.RingTheory.AdicCompletion.Algebra
public import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Defs
import Tengoku.Seed.RingTheory.Ideal.Quotient.Nilpotent
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Adic Completion of a Noetherian Local Ring is Local

The M-adic completion of a Noetherian local ring (R, M) is again
a local ring. The maximal ideal of the completion is the kernel
of the natural surjection onto the residue field R/M.
-/

@[expose] public section

open scoped Pointwise
open AdicCompletion Ideal Finset

variable {R : Type*} [CommRing R]

/-! ### Transition compatibility for evalₐ -/
section Compat
namespace AdicCompletion

variable (I : Ideal R)

/-- The transition ring hom `factorPow` is compatible with `evalₐ`:
`factorPow I hmn (evalₐ I n x) = evalₐ I m x`.
@isnad1 id=eq.1h5v.s11.b28f3d5ba92d from=translated src=- shape=576c93d7 vocab=a954745f
-/
lemma factorPow_comp_evalₐ {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h f =>
    rw [evalₐ_mk, evalₐ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa using (Submodule.Quotient.eq _).mp (AdicCauchySequence.mk_eq_mk hmn f)

end AdicCompletion
end Compat

/-! ### Constructing inverses from componentwise units -/
section InverseConstruction
namespace AdicCompletion

variable (I : Ideal R) [I.IsMaximal]

omit [I.IsMaximal] in
/-- If `evalOneₐ I x` is a unit (in the residue field `R ⧸ I`), then
`evalₐ I n x` is a unit in `R ⧸ I ^ n` for every `n`.
@isnad1 id=isunit.1h4v.s10.2e9324f2a0f9 from=translated src=- shape=05887312 vocab=c5a45cc9
-/
lemma evalₐ_isUnit_of_evalOneₐ_isUnit (x : AdicCompletion I R)
    (hu : IsUnit (evalOneₐ I x)) (n : ℕ) : IsUnit (evalₐ I n x) := by
  induction n with
  | zero =>
    have : Subsingleton (R ⧸ I ^ 0) := by
      simp_all
    exact isUnit_of_subsingleton _
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I 1 x)
      rw [← hr]
      rw [Quotient.isUnit_mk_pow_iff_isUnit_mk I one_ne_zero]
      convert hu using 1
      show Ideal.Quotient.mk I r = evalOneₐ I x
      simp only [evalOneₐ, AlgHom.comp_apply, ← hr]
      rfl
    · apply factorPowSucc.isUnit_of_isUnit_image (npos := Nat.zero_lt_of_ne_zero hn)
      rwa [factorPow_comp_evalₐ]

/-- Given `x` with all `evalₐ` components invertible, construct the inverse
as an element of `AdicCompletion`. -/
noncomputable def mkInverse (x : AdicCompletion I R)
    (hu : ∀ n, IsUnit (evalₐ I n x)) : AdicCompletion I R := by
  have h_smul_eq : ∀ n, (I ^ n • ⊤ : Ideal R) = I ^ n := fun n => by simp_all
  refine ⟨fun n => (Ideal.quotientEquivAlgOfEq R (h_smul_eq n)).symm
    (↑(hu n).unit⁻¹ : R ⧸ I ^ n), ?_⟩
  intro m n hmn
  apply (Ideal.quotientEquivAlgOfEq R (h_smul_eq m)).injective
  simp only [AlgEquiv.apply_symm_apply]
  have key : ∀ (y : R ⧸ I ^ n),
    (Ideal.quotientEquivAlgOfEq R (h_smul_eq m))
      (transitionMap I R hmn ((Ideal.quotientEquivAlgOfEq R (h_smul_eq n)).symm y)) =
      Quotient.factorPow I hmn y := by
    intro y
    induction y using Quotient.inductionOn' with | _ r => rfl
  rw [key]
  -- factorPow I hmn (↑u_n⁻¹) = ↑u_m⁻¹
  have h_map := factorPow_comp_evalₐ I hmn x
  have hfp : Quotient.factorPow I hmn (↑(hu n).unit⁻¹) * evalₐ I m x = 1 := by
    rw [← h_map, ← map_mul, (hu n).val_inv_mul, map_one]
  have hright : evalₐ I m x * ↑(hu m).unit⁻¹ = 1 := (hu m).mul_val_inv
  rw [← one_mul (↑(hu m).unit⁻¹ : R ⧸ I ^ m), ← hfp, mul_assoc, hright, mul_one]

omit [I.IsMaximal] in
/--
@isnad1 id=eq.1h4v.s11.ca8bd704bc68 from=translated src=- shape=9f963905 vocab=bfec610a
-/
lemma evalₐ_mkInverse (x : AdicCompletion I R) (hu : ∀ n, IsUnit (evalₐ I n x)) (n : ℕ) :
    evalₐ I n (mkInverse I x hu) = ↑(hu n).unit⁻¹ := by
  have h_eq : (I ^ n • ⊤ : Ideal R) = I ^ n := by simp_all
  have : (mkInverse I x hu).val n =
      (Ideal.quotientEquivAlgOfEq R h_eq).symm (↑(hu n).unit⁻¹) := rfl
  change (Ideal.quotientEquivAlgOfEq R h_eq) ((mkInverse I x hu).val n) = ↑(hu n).unit⁻¹
  rw [this]
  exact AlgEquiv.apply_symm_apply _ _

omit [I.IsMaximal] in
/--
@isnad1 id=eq.1h3v.s9.b27e7baa8b7c from=translated src=- shape=daaf3c48 vocab=7c4054f3
-/
lemma mkInverse_mul (x : AdicCompletion I R) (hu : ∀ n, IsUnit (evalₐ I n x)) :
    mkInverse I x hu * x = 1 := by
  apply ext_evalₐ
  intro n
  simp only [map_mul, map_one]
  rw [evalₐ_mkInverse]
  exact (hu n).val_inv_mul

omit [I.IsMaximal] in
/-- An element of the adic completion whose image under `evalOneₐ` is a unit (in the
residue field) is itself a unit.
@isnad1 id=isunit.1h3v.s8.b06b2689c41d from=translated src=- shape=af0d8aaf vocab=71170a3f
-/
lemma isUnit_of_evalOneₐ_isUnit (x : AdicCompletion I R) (hu : IsUnit (evalOneₐ I x)) :
    IsUnit x := by
  have hu_all := evalₐ_isUnit_of_evalOneₐ_isUnit I x hu
  have hmul : mkInverse I x hu_all * x = 1 := mkInverse_mul I x hu_all
  have hmul' : x * mkInverse I x hu_all = 1 := by
    apply ext_evalₐ
    intro n
    simp only [map_mul, map_one]
    rw [evalₐ_mkInverse]
    exact (hu_all n).mul_val_inv
  exact ⟨⟨x, mkInverse I x hu_all, hmul', hmul⟩, rfl⟩

end AdicCompletion
end InverseConstruction

/-! ### Main theorem -/
section Main
namespace AdicCompletion

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- Local abbreviation for the maximal ideal `IsLocalRing.maximalIdeal R`. -/
abbrev M' := IsLocalRing.maximalIdeal R

/--
@isnad1 id=nontrivi.0h1v.s5.30d0333ac96c from=translated src=- shape=4d75d831 vocab=e033d81b
-/
instance adicCompletion_nontrivial :
    Nontrivial (AdicCompletion (M' R) R) := by
  have hsurj := evalOneₐ_surjective (M' R) (R := R)
  have : Nontrivial (R ⧸ M' R) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal (R := R)).ne_top
  exact hsurj.nontrivial

omit [IsLocalRing R] in
/--
@isnad1 id=or.1h3v.s6.f565f0077adb from=translated src=- shape=3a0afded vocab=b01f6aba
-/
lemma field_isUnit_or_isUnit {K : Type*} [Field K] {a b : K} (hab : a + b = 1) :
    IsUnit a ∨ IsUnit b := by
  by_cases ha : a = 0
  · simp_all
  · exact Or.inl (IsUnit.mk0 a ha)

/--
@isnad1 id=islocalr.0h1v.s6.4e58dcf9b7a6 from=translated src=- shape=776bb47b vocab=ea550e86
-/
theorem adicCompletion_isLocalRing :
    IsLocalRing (AdicCompletion (M' R) R) := by
  let := adicCompletion_nontrivial R
  refine .of_is_unit_or_is_unit_of_add_one fun {a b} hab => ?_
  let : Field (R ⧸ M' R) := Ideal.Quotient.field (M' R)
  have hab' : evalOneₐ (M' R) a + evalOneₐ (M' R) b = 1 := by
    rw [← map_add, hab, map_one]
  rcases field_isUnit_or_isUnit hab' with hu | hu
  · left
    exact isUnit_of_evalOneₐ_isUnit _ a hu
  · right
    exact isUnit_of_evalOneₐ_isUnit _ b hu

end AdicCompletion
end Main

/--
@isnad1 id=islocalr.0h1v.s6.16fc0a4adbc5 from=translated src=- shape=776bb47b vocab=019d34ad
-/
theorem adicCompletion_isLocalRing
    (R : Type*) [CommRing R] [IsLocalRing R] :
    IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  AdicCompletion.adicCompletion_isLocalRing R
