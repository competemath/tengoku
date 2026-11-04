/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.RegularLocalDomainGeneral
import Tengoku.Seed.RingTheory.LocalProperties.ProjectiveDimension
import Tengoku.Seed.RingTheory.Regular.Free
import Tengoku.Seed.RingTheory.LocalRing.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Serre's theorem: regular rings have finite global dimension

For a regular local ring `R` of embedding dimension `n` (= Krull dimension), every finitely
generated `R`-module has projective dimension `≤ n`; for a regular ring of Krull dimension
`≤ d`, every finitely generated module has projective dimension `≤ d`.  Projective dimension is
Mathlib's `HasProjectiveDimensionLE` in `ModuleCat`.

## Proof

No Tor or Koszul complex is needed.

* **Change of rings** (`RegularResolution.hasPDLE_of_quotSMulTop`).  Let `R` be noetherian local,
  `x ∈ 𝔪` an `R`-regular element and `N` a finite `R`-module on which `x` is regular.  Then
  `pd_{R/x}(N/xN) ≤ n` implies `pd_R N ≤ n`.  The proof is by induction on `n`:
  * For `n = 0`, `N/xN` is finite projective, hence free over the local ring `R/x`, so `N` is
    free by Mathlib's `Module.free_quotSMulTop_iff_free`.
  * For the step, take a presentation `0 → K → Rᵏ → N → 0`. Here `x` is `K`-regular, and
    because `x` is `N`-regular, `0 → K/x → (R/x)ᵏ → N/x → 0` stays exact.
* **Serre, local form** (`IsRegularLocalRing.hasPDLE_of_embeddingDimension_eq`).  This is an
  induction on the embedding dimension.
  * A regular local ring of dimension `0` is a field.
  * Otherwise choose `x ∈ 𝔪 \ 𝔪²`. It is regular because `R` is a domain, and `R/x` is regular
    of embedding dimension one less. The first syzygy `K` of `M` is `x`-regular, and `K/xK` has
    `pd_{R/x} ≤ n - 1` by induction. Change of rings then gives `pd_R K ≤ n - 1`.
* **Serre, global form** (`IsRegularRing.hasProjectiveDimensionLE`).  This uses Mathlib's
  `ModuleCat.hasProjectiveDimensionLE_iff_forall_primeSpectrum` together with
  `dim R_𝔭 = ht 𝔭 ≤ dim R`.
-/

noncomputable section

universe u

open CategoryTheory IsLocalRing
open scoped Pointwise

namespace RegularResolution

variable {R : Type u} [CommRing R]

/-- A projective `R`-module gives a projective object of `ModuleCat`.
@isnad1 id=hasproje.0h2v.s6.00879efeed1d from=translated src=- shape=4aecc906 vocab=4853e452
-/
theorem hasPDLE_zero_of_projective (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Projective R M] : HasProjectiveDimensionLE (ModuleCat.of R M) 0 := by
  rw [← projective_iff_hasProjectiveDimensionLE_zero]
  infer_instance

/-- Kernel step.
@isnad1 id=hasproje.2h5v.s8.ff049691c706 from=translated src=- shape=c6000abe vocab=ce01ba2a
-/
theorem hasPDLE_succ_of_ker {F N : Type u} [AddCommGroup F] [Module R F] [AddCommGroup N]
    [Module R N] [Module.Projective R F] (f : F →ₗ[R] N) (hf : Function.Surjective f) (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n) :
    HasProjectiveDimensionLE (ModuleCat.of R N) (n + 1) := by
  have hS := LinearMap.shortExact_shortComplexKer hf
  have : Projective (ModuleCat.of R F) := inferInstance
  exact hS.hasProjectiveDimensionLT_X₃ (n + 1) h inferInstance

/--
@isnad1 id=hasproje.2h5v.s8.5ca2deb6be4f from=translated src=- shape=65e29d58 vocab=ce01ba2a
-/
theorem hasPDLE_ker_of_succ {F N : Type u} [AddCommGroup F] [Module R F] [AddCommGroup N]
    [Module R N] [Module.Projective R F] (f : F →ₗ[R] N) (hf : Function.Surjective f) (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of R N) (n + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n := by
  have hS := LinearMap.shortExact_shortComplexKer hf
  have : Projective (ModuleCat.of R F) := inferInstance
  exact hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance h

/-- `x` is regular on a finite free module `Fin k → R` when it is regular on `R`.
@isnad1 id=issmulre.1h3v.s5.e94310649863 from=translated src=- shape=3e821ba5 vocab=a7601764
-/
theorem isSMulRegular_pi {x : R} (hx : IsSMulRegular R x) (k : ℕ) :
    IsSMulRegular (Fin k → R) x := by
  intro a b hab
  funext i
  exact hx (congrFun hab i)

/-- Regularity passes to submodules.
@isnad1 id=issmulre.1h4v.s7.a247992cb72d from=translated src=- shape=7cf863dd vocab=f6f4d800
-/
theorem isSMulRegular_submodule {F : Type u} [AddCommGroup F] [Module R F] {x : R}
    (hx : IsSMulRegular F x) (K : Submodule R F) : IsSMulRegular K x := by
  intro a b hab
  exact Subtype.ext (hx (congrArg Subtype.val hab))

/-- Reduction modulo an `N`-regular element keeps the kernel inclusion injective.
@isnad1 id=injectiv.1h5v.s16.3f5c0fbe9777 from=translated src=- shape=ee299a2a vocab=90a49b65
-/
theorem quotSMulTop_map_ker_subtype_injective {F N : Type u} [AddCommGroup F] [Module R F]
    [AddCommGroup N] [Module R N] (f : F →ₗ[R] N) {x : R} (hN : IsSMulRegular N x) :
    Function.Injective (QuotSMulTop.map x (LinearMap.ker f).subtype) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  induction a using Submodule.Quotient.induction_on with
  | H k =>
    rw [QuotSMulTop.map_apply_mk] at ha
    have hk : (k : F) ∈ x • (⊤ : Submodule R F) := (Submodule.Quotient.mk_eq_zero _).mp ha
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hk
    have hfy : f y = 0 := by
      apply hN
      change x • f y = x • 0
      rw [← map_smul, hy, smul_zero]
      exact k.2
    have hk' : k = x • (⟨y, hfy⟩ : LinearMap.ker f) := Subtype.ext hy.symm
    rw [hk']
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.smul_mem_pointwise_smul _ x _ Submodule.mem_top)

variable [IsNoetherianRing R]

/-- **Change of rings.** Over a noetherian local ring, if `x ∈ 𝔪` is `R`-regular and `N`-regular,
then `pd_R N ≤ pd_{R/x} (N/xN)`.
@isnad1 id=hasproje.4h4v.s9.5c41d936accf from=translated src=- shape=fe370fed vocab=21db67f1
-/
theorem hasPDLE_of_quotSMulTop [IsLocalRing R] {x : R} (hxm : x ∈ maximalIdeal R)
    (hx : IsSMulRegular R x) :
    ∀ (n : ℕ) (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      IsSMulRegular N x →
      HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x N)) n →
      HasProjectiveDimensionLE (ModuleCat.of R N) n
  | 0, N, _, _, _, hN, h => by
      letI := ModuleCat.quotientSpanIsLocalRing R x hxm
      rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective] at h
      haveI := Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) (QuotSMulTop x N)
      haveI : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x N) :=
        Module.free_of_flat_of_isLocalRing
      haveI := Module.finitePresentation_of_finite R N
      have hjac : x ∈ (⊥ : Ideal R).jacobson := by
        rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact hxm
      haveI : Module.Free R N := (Module.free_quotSMulTop_iff_free R N hjac hN).mp inferInstance
      exact hasPDLE_zero_of_projective N
  | n + 1, N, _, _, _, hN, h => by
      obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R N
      let K := LinearMap.ker f
      have hK : IsSMulRegular K x := isSMulRegular_submodule (isSMulRegular_pi hx k) K
      have hsurj : Function.Surjective (algebraMap R (R ⧸ Ideal.span {x})) :=
        Ideal.Quotient.mk_surjective
      let ι : QuotSMulTop x K →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x (Fin k → R) :=
        LinearMap.extendScalarsOfSurjective hsurj (QuotSMulTop.map x K.subtype)
      let π : QuotSMulTop x (Fin k → R) →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x N :=
        LinearMap.extendScalarsOfSurjective hsurj (QuotSMulTop.map x f)
      have hex : Function.Exact (QuotSMulTop.map x K.subtype) (QuotSMulTop.map x f) :=
        QuotSMulTop.map_exact x (LinearMap.exact_subtype_ker_map f) hf
      have hιc : ⇑ι = ⇑(QuotSMulTop.map x K.subtype) := rfl
      have hπc : ⇑π = ⇑(QuotSMulTop.map x f) := rfl
      have hexι : Function.Exact ι π := by rw [hιc, hπc]; exact hex
      have hinj : Function.Injective ι := by
        rw [hιc]; exact quotSMulTop_map_ker_subtype_injective f hN
      have hsur : Function.Surjective π := by rw [hπc]; exact QuotSMulTop.map_surjective x hf
      have h0 : π.comp ι = 0 := LinearMap.ext fun y => hexι.apply_apply_eq_zero y
      have hS := ModuleCat.shortComplex_shortExact
        (ModuleCat.shortComplexOfCompEqZero ι π h0) hexι hinj hsur
      have hK' : HasProjectiveDimensionLE
          (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x K)) n :=
        hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance h
      exact hasPDLE_succ_of_ker f hf n (hasPDLE_of_quotSMulTop hxm hx n K hK hK')

end RegularResolution

namespace IsRegularLocalRing

open RegularResolution

/-- **Serre (local form).** A finitely generated module over a regular local ring of embedding
dimension `n` has projective dimension at most `n`.
@isnad1 id=hasproje.1h3v.s6.c102798e69ab from=translated src=- shape=1381f844 vocab=a40586a1
-/
theorem hasPDLE_of_embeddingDimension_eq :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R], embeddingDimension R = n →
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
        HasProjectiveDimensionLE (ModuleCat.of R M) n
  | 0, R, _, _, hn, M, _, _, _ => by
      have hdim : ringKrullDim R = 0 := by
        rw [← coe_embeddingDimension_eq_ringKrullDim, hn]; rfl
      letI := (isField_of_ringKrullDim_eq_zero hdim).toField
      haveI : Module.Free R M := Module.Free.of_divisionRing R M
      exact hasPDLE_zero_of_projective M
  | n + 1, R, _, _, hn, M, _, _, _ => by
      classical
      have hdim : ringKrullDim R ≠ 0 := by
        rw [← coe_embeddingDimension_eq_ringKrullDim, hn]
        exact_mod_cast (Nat.succ_ne_zero n)
      obtain ⟨x, hxm, hx2⟩ := exists_mem_maximalIdeal_notMem_sq hdim
      haveI := isDomain_of_isRegularLocalRing R
      have hx : IsSMulRegular R x := isSMulRegular_of_notMem_sq_of_isDomain hx2
      letI := quotient_span_singleton_isRegularLocalRing hxm hx2
      have hn' : embeddingDimension (R ⧸ Ideal.span {x}) = n := by
        have := embeddingDimension_quotient_span_singleton hxm hx2
        rw [this, hn]; rfl
      obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
      let K := LinearMap.ker f
      have hK : IsSMulRegular K x := isSMulRegular_submodule (isSMulRegular_pi hx k) K
      haveI := Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) (QuotSMulTop x K)
      have hbar := hasPDLE_of_embeddingDimension_eq n (R ⧸ Ideal.span {x}) hn' (QuotSMulTop x K)
      exact hasPDLE_succ_of_ker f hf n (hasPDLE_of_quotSMulTop hxm hx n K hK hbar)

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/--
@isnad1 id=hasproje.0h2v.s6.519aadfa3b7c from=translated src=- shape=a8af8ac6 vocab=98b9eeb1
-/
theorem hasProjectiveDimensionLE_embeddingDimension (M : ModuleCat.{u} R) [Module.Finite R M] :
    HasProjectiveDimensionLE M (embeddingDimension R) :=
  hasPDLE_of_embeddingDimension_eq _ R rfl M

/--
@isnad1 id=hasproje.1h3v.s6.a77692d627aa from=translated src=- shape=d15f83f1 vocab=1dd78f43
-/
theorem hasProjectiveDimensionLE_of_ringKrullDim_le (M : ModuleCat.{u} R) [Module.Finite R M]
    (d : ℕ) (hd : ringKrullDim R ≤ d) : HasProjectiveDimensionLE M d := by
  have h := hasProjectiveDimensionLE_embeddingDimension M
  have hle : embeddingDimension R ≤ d := by
    rw [← coe_embeddingDimension_eq_ringKrullDim] at hd
    exact_mod_cast hd
  exact hasProjectiveDimensionLT_of_ge M (embeddingDimension R + 1) (d + 1) (by omega)

end IsRegularLocalRing

namespace IsRegularRing

variable {R : Type u} [CommRing R] [IsRegularRing R]

/-- **Serre (global form).** Over a regular ring of Krull dimension `≤ d`, every finitely
generated module has projective dimension `≤ d`.
@isnad1 id=hasproje.1h3v.s6.92f1312ee5f3 from=translated src=- shape=77ca3efd vocab=9674d50b
-/
theorem hasProjectiveDimensionLE (d : ℕ) (hd : ringKrullDim R ≤ d)
    (M : ModuleCat.{u} R) [Module.Finite R M] : HasProjectiveDimensionLE M d := by
  rw [ModuleCat.hasProjectiveDimensionLE_iff_forall_primeSpectrum]
  intro p
  haveI : IsRegularLocalRing (Localization.AtPrime p.1) := inferInstance
  haveI : Module.Finite (Localization.AtPrime p.1) (M.localizedModule p.1.primeCompl) :=
    Module.Finite.of_isLocalizedModule p.1.primeCompl (M.localizedModuleMkLinearMap p.1.primeCompl)
  apply IsRegularLocalRing.hasProjectiveDimensionLE_of_ringKrullDim_le _ d
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.1]
  exact (Ideal.height_le_ringKrullDim_of_ne_top p.2.ne_top).trans hd

end IsRegularRing
