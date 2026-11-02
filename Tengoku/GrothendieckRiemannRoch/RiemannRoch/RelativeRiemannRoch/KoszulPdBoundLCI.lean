/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.RingTheory.Regular.ProjectiveDimension
import Tengoku.Seed.RingTheory.Regular.Flat
import Tengoku.Seed.LinearAlgebra.DirectSum.Finsupp
import Tengoku.Seed.LinearAlgebra.TensorProduct.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Projective dimension bounds along a weakly regular sequence (brick G2B2)

Pure commutative algebra, no locality or Noetherian hypotheses.

For a commutative ring `R` and a list `f` which is weakly regular on `R`, write `A = R ⧸ (f)`.

* `KoszulPdBoundLCI.hasProjectiveDimensionLT_quotient_of_isWeaklyRegular` : if `f` is weakly
  regular on an `R`-module `M` and `pd_R M < n`, then `pd_R (M ⧸ (f) M) < n + |f|`.
* `KoszulPdBoundLCI.hasProjectiveDimensionLE_of_projective_quotient` : every projective
  `A`-module has `pd_R ≤ |f|`.
* `KoszulPdBoundLCI.hasProjectiveDimensionLE_quotient_ofList` : `pd_R A ≤ |f|`.
* `KoszulPdBoundLCI.hasProjectiveDimensionLE_of_quotient` (change of rings) : an `A`-module with
  `pd_A N ≤ n` has `pd_R N ≤ n + |f|`.
* `KoszulPdBoundLCI.hasProjectiveDimensionLE_of_quotSMulTop_local` : over a Noetherian local ring,
  for `t ∈ 𝔪` regular on `R` and on a finite module `F`, `pd_{R/t} (F/tF) ≤ n ⇒ pd_R F ≤ n`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Abelian RingTheory.Sequence
open scoped Pointwise

namespace KoszulPdBoundLCI

variable {R : Type u} [CommRing R]

/-- Iterating the short exact sequences `0 → M --x--> M → M/xM → 0` along a weakly regular
sequence: `pd_R (M ⧸ (f) M) < n + |f|` whenever `pd_R M < n`.-/
theorem hasProjectiveDimensionLT_quotient_of_isWeaklyRegular :
    ∀ (f : List R) (M : Type u) [AddCommGroup M] [Module R M], IsWeaklyRegular M f →
      ∀ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of R M) n →
        HasProjectiveDimensionLT
          (ModuleCat.of R (M ⧸ (Ideal.ofList f • (⊤ : Submodule R M)))) (n + f.length)
  | [], M, _, _, _, n, h => by
    have e : M ≃ₗ[R] M ⧸ (Ideal.ofList ([] : List R) • (⊤ : Submodule R M)) :=
      (Submodule.quotEquivOfEqBot _ (by rw [Ideal.ofList_nil, Submodule.bot_smul])).symm
    simpa using hasProjectiveDimensionLT_of_iso e.toModuleIso n
  | x :: f, M, _, _, reg, n, h => by
    rw [isWeaklyRegular_cons_iff] at reg
    haveI := h
    have hS := IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) reg.1
    have h₂ : HasProjectiveDimensionLT (ModuleCat.of R M) (n + 1) :=
      hasProjectiveDimensionLT_of_ge _ n (n + 1) (Nat.le_succ n)
    have h₃ := hS.hasProjectiveDimensionLT_X₃ n h h₂
    have ih := hasProjectiveDimensionLT_quotient_of_isWeaklyRegular f (QuotSMulTop x M) reg.2
      (n + 1) h₃
    have e := (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x f).symm
    haveI := ih
    rw [show n + (x :: f).length = n + 1 + f.length by simp only [List.length_cons]; omega]
    exact hasProjectiveDimensionLT_of_iso e.toModuleIso _

/-- A sequence which is weakly regular on `R` is weakly regular on every flat `R`-module.-/
theorem isWeaklyRegular_of_flat (f : List R) (hf : IsWeaklyRegular R f)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Flat R M] : IsWeaklyRegular M f :=
  ((TensorProduct.rid R M).isWeaklyRegular_congr f).mp hf.isWeaklyRegular_lTensor

/-- `(ι →₀ R ⧸ (f))` has projective dimension `≤ |f|` over `R` when `f` is weakly regular on `R`.-/
theorem hasProjectiveDimensionLE_finsupp_quotient (f : List R) (hf : IsWeaklyRegular R f)
    (ι : Type u) :
    HasProjectiveDimensionLE (ModuleCat.of R (ι →₀ R ⧸ Ideal.ofList f)) f.length := by
  classical
  haveI : Projective (ModuleCat.of R (ι →₀ R)) :=
    (IsProjective.iff_projective (ι →₀ R)).mp inferInstance
  have h := hasProjectiveDimensionLT_quotient_of_isWeaklyRegular f (ι →₀ R)
    (isWeaklyRegular_of_flat f hf (ι →₀ R)) 1 inferInstance
  let e : ((ι →₀ R) ⧸ (Ideal.ofList f • (⊤ : Submodule R (ι →₀ R)))) ≃ₗ[R]
      (ι →₀ R ⧸ Ideal.ofList f) :=
    (TensorProduct.quotTensorEquivQuotSMul (ι →₀ R) (Ideal.ofList f)).symm ≪≫ₗ
      TensorProduct.finsuppScalarRight R R (R ⧸ Ideal.ofList f) ι
  haveI := h
  rw [HasProjectiveDimensionLE, Nat.add_comm]
  exact hasProjectiveDimensionLT_of_iso e.toModuleIso _

/-- **Brick B2.** Let `f` be weakly regular on `R` and `P` a projective `R ⧸ (f)`-module. Then
`pd_R P ≤ |f|`.-/
theorem hasProjectiveDimensionLE_of_projective_quotient (f : List R) (hf : IsWeaklyRegular R f)
    (P : Type u) [AddCommGroup P] [Module (R ⧸ Ideal.ofList f) P] [Module R P]
    [IsScalarTower R (R ⧸ Ideal.ofList f) P] [Module.Projective (R ⧸ Ideal.ofList f) P] :
    HasProjectiveDimensionLE (ModuleCat.of R P) f.length := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective (R ⧸ Ideal.ofList f) P›
  haveI := hasProjectiveDimensionLE_finsupp_quotient f hf P
  let ret : Retract (ModuleCat.of R P) (ModuleCat.of R (P →₀ R ⧸ Ideal.ofList f)) :=
    { i := ModuleCat.ofHom (s.restrictScalars R)
      r := ModuleCat.ofHom ((Finsupp.linearCombination (R ⧸ Ideal.ofList f) id).restrictScalars R)
      retract := by
        ext x
        simpa using LinearMap.congr_fun hs x }
  exact ret.hasProjectiveDimensionLT _

/-- `pd_R (R ⧸ (f)) ≤ |f|` for `f` weakly regular on `R`.-/
theorem hasProjectiveDimensionLE_quotient_ofList (f : List R) (hf : IsWeaklyRegular R f) :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.ofList f)) f.length :=
  hasProjectiveDimensionLE_of_projective_quotient f hf (R ⧸ Ideal.ofList f)

/-- **Change of rings.** For `f` weakly regular on `R` and an `R ⧸ (f)`-module `N`:
`pd_{R/(f)} N ≤ n ⇒ pd_R N ≤ n + |f|`. No finiteness or locality is needed.-/
theorem hasProjectiveDimensionLE_of_quotient (f : List R) (hf : IsWeaklyRegular R f) :
    ∀ (n : ℕ) (N : Type u) [AddCommGroup N] [Module (R ⧸ Ideal.ofList f) N] [Module R N]
      [IsScalarTower R (R ⧸ Ideal.ofList f) N],
      HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.ofList f) N) n →
        HasProjectiveDimensionLE (ModuleCat.of R N) (n + f.length)
  | 0, N, _, _, _, _, h => by
    rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective] at h
    rw [Nat.zero_add]
    exact hasProjectiveDimensionLE_of_projective_quotient f hf N
  | n + 1, N, _, _, _, _, h => by
    let π := Finsupp.linearCombination (R ⧸ Ideal.ofList f) (id : N → N)
    have surj : Function.Surjective π :=
      Finsupp.linearCombination_surjective _ Function.surjective_id
    have hSA := LinearMap.shortExact_shortComplexKer surj
    haveI : Projective (ModuleCat.of (R ⧸ Ideal.ofList f) (N →₀ R ⧸ Ideal.ofList f)) :=
      (IsProjective.iff_projective _).mp inferInstance
    have hX₂ : HasProjectiveDimensionLT
        (ModuleCat.of (R ⧸ Ideal.ofList f) (N →₀ R ⧸ Ideal.ofList f)) (n + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (n + 1) (by omega)
    have hK : HasProjectiveDimensionLT
        (ModuleCat.of (R ⧸ Ideal.ofList f) (LinearMap.ker π)) (n + 1) :=
      hSA.hasProjectiveDimensionLT_X₁ (n + 1) hX₂ h
    have ihK := hasProjectiveDimensionLE_of_quotient f hf n (LinearMap.ker π) hK
    let ι : LinearMap.ker π →ₗ[R] (N →₀ R ⧸ Ideal.ofList f) :=
      (LinearMap.ker π).subtype.restrictScalars R
    let SR := ModuleCat.shortComplexOfCompEqZero (M := LinearMap.ker π) ι (π.restrictScalars R)
      (LinearMap.ext fun x => by simp [ι])
    have hSR : SR.ShortExact := ModuleCat.shortComplex_shortExact SR
      (LinearMap.exact_subtype_ker_map π) (LinearMap.ker π).injective_subtype surj
    have hX₂R : HasProjectiveDimensionLT (ModuleCat.of R (N →₀ R ⧸ Ideal.ofList f))
        (n + f.length + 1 + 1) :=
      haveI := hasProjectiveDimensionLE_finsupp_quotient f hf N
      hasProjectiveDimensionLT_of_ge _ (f.length + 1) _ (by omega)
    have := hSR.hasProjectiveDimensionLT_X₃ (n + f.length + 1) ihK hX₂R
    rw [HasProjectiveDimensionLE, show n + 1 + f.length + 1 = n + f.length + 1 + 1 by omega]
    exact this

/-- **Local change of rings for one regular element.** Let `R` be Noetherian local, `t ∈ 𝔪` a
nonzerodivisor on `R` and on a finite `R`-module `F`. Then
`pd_{R ⧸ (t)} (F ⧸ tF) ≤ n ⇒ pd_R F ≤ n`. (Without locality/finiteness this is false: see
`G2B2-status.md`.)-/
theorem hasProjectiveDimensionLE_of_quotSMulTop_local [IsLocalRing R] [IsNoetherianRing R]
    (t : R) (ht : IsSMulRegular R t) (htm : t ∈ IsLocalRing.maximalIdeal R)
    (F : Type u) [AddCommGroup F] [Module R F] [Module.Finite R F] (hF : IsSMulRegular F t)
    (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.ofList [t])
      (F ⧸ (Ideal.ofList [t] • (⊤ : Submodule R F)))) n) :
    HasProjectiveDimensionLE (ModuleCat.of R F) n := by
  have hreg : IsWeaklyRegular R [t] := (isWeaklyRegular_cons_iff R t []).mpr ⟨ht, .nil _ _⟩
  have h1 := hasProjectiveDimensionLE_of_quotient [t] hreg n _ h
  have hq : (Ideal.ofList [t] • (⊤ : Submodule R F)) = t • (⊤ : Submodule R F) := by
    rw [Ideal.ofList_cons_smul, Ideal.ofList_nil, Submodule.bot_smul, sup_bot_eq]
  let e : (F ⧸ (Ideal.ofList [t] • (⊤ : Submodule R F))) ≃ₗ[R] QuotSMulTop t F :=
    Submodule.quotEquivOfEq _ _ hq
  haveI := h1
  have h2 : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop t F)) (n + 1) :=
    hasProjectiveDimensionLT_of_iso e.toModuleIso _
  have h3 := (projectiveDimension_le_iff _ _).mpr h2
  rw [ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (ModuleCat.of R F) t hF
    htm] at h3
  rw [← projectiveDimension_le_iff]
  rw [Nat.cast_add, Nat.cast_one] at h3
  exact ENat.WithBot.add_le_add_one_right_iff.mp h3

end KoszulPdBoundLCI
