/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Meromorphic.Order

/-!
# Meromorphic API for the Logarithmic Derivative
-/

@[expose] public section

open Filter Function Set Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f g : 𝕜 → 𝕜'} {x : 𝕜} {U : Set 𝕜}

/-!
## Arithmetic on Codiscrete Sets

The pointwise lemma `logDeriv_mul` requires differentiability and nonvanishing of the factors at the
point in question. For meromorphic functions whose order is nowhere `⊤`, both conditions hold away
from a codiscrete set, turning the pointwise arithmetic into arithmetic of codiscrete equivalence
classes.
-/

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a product of two meromorphic functions is the sum of the logarithmic
derivatives.
@isnad1 id=eventual.4h5v.s8.3394aaf33ece from=seed src=0 shape=c7982b62 vocab=43a4139c
-/
@[to_fun MeromorphicOn.logDeriv_fun_mul_eventuallyEq]
theorem MeromorphicOn.logDeriv_mul_eventuallyEq (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (h'f : ∀ x ∈ U, meromorphicOrderAt f x ≠ ⊤) (h'g : ∀ x ∈ U, meromorphicOrderAt g x ≠ ⊤) :
    logDeriv (f * g) =ᶠ[codiscreteWithin U] logDeriv f + logDeriv g := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, hg.analyticAt_mem_codiscreteWithin,
    hf.eventually_codiscreteWithin_apply_ne_zero h'f,
    hg.eventually_codiscreteWithin_apply_ne_zero h'g]
    with y h₁y h₂y h₃y h₄y
  rw [Pi.add_apply]
  exact logDeriv_mul y h₃y h₄y h₁y.differentiableAt h₂y.differentiableAt

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a product of two meromorphic functions is the sum of the logarithmic
derivatives.
@isnad1 id=eventual.4h4v.s8.d165555786d4 from=seed src=0 shape=ebdde995 vocab=00133301
-/
@[to_fun Meromorphic.logDeriv_fun_mul_eventuallyEq]
theorem Meromorphic.logDeriv_mul_eventuallyEq (hf : Meromorphic f) (hg : Meromorphic g)
    (h'f : ∀ x, meromorphicOrderAt f x ≠ ⊤) (h'g : ∀ x, meromorphicOrderAt g x ≠ ⊤) :
    logDeriv (f * g) =ᶠ[codiscrete 𝕜] logDeriv f + logDeriv g :=
  (meromorphicOn_univ.2 hf).logDeriv_mul_eventuallyEq (meromorphicOn_univ.2 hg)
    (fun x _ ↦ h'f x) (fun x _ ↦ h'g x)

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
@isnad1 id=eventual.2h6v.s7.d918b67144f4 from=seed src=0 shape=520a65bb vocab=319c4c3b
-/
@[to_fun MeromorphicOn.logDeriv_fun_prod_eventuallyEq]
theorem MeromorphicOn.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'}
    (h : ∀ i ∈ s, MeromorphicOn (F i) U)
    (h' : ∀ i ∈ s, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ i ∈ s, F i) =ᶠ[codiscreteWithin U] ∑ i ∈ s, logDeriv (F i) := by
  have hA : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ s, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset s).2 fun i hi ↦ (h i hi).analyticAt_mem_codiscreteWithin
  have hN : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ s, F i y ≠ 0 :=
    (eventually_all_finset s).2 fun i hi ↦ (h i hi).eventually_codiscreteWithin_apply_ne_zero
      (h' i hi)
  filter_upwards [hA, hN] with y h₁y h₂y
  rw [Finset.sum_apply]
  exact logDeriv_prod h₂y fun i hi ↦ (h₁y i hi).differentiableAt

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
@isnad1 id=eventual.2h5v.s7.fa38cfac0406 from=seed src=0 shape=9af35405 vocab=39d61f7b
-/
@[to_fun Meromorphic.logDeriv_fun_prod_eventuallyEq]
theorem Meromorphic.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'}
    (h : ∀ i ∈ s, Meromorphic (F i)) (h' : ∀ i ∈ s, ∀ x, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ i ∈ s, F i) =ᶠ[codiscrete 𝕜] ∑ i ∈ s, logDeriv (F i) := by
  apply MeromorphicOn.logDeriv_prod_eventuallyEq (fun i hi ↦ meromorphicOn_univ.mpr (h i hi))
  aesop

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
@isnad1 id=eventual.3h5v.s7.349c9ec05613 from=seed src=0 shape=0a59164b vocab=c3219a51
-/
theorem MeromorphicOn.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'}
    (hF : (mulSupport F).Finite) (h : ∀ i, MeromorphicOn (F i) U)
    (h' : ∀ i, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i) =ᶠ[codiscreteWithin U] ∑ᶠ i, logDeriv (F i) := by
  have hsub : support (fun i ↦ logDeriv (F i)) ⊆ hF.toFinset := by
    simp +contextual [Set.subset_def, not_imp_not, Pi.one_def]
  rw [finprod_eq_prod_of_mulSupport_subset F (s := hF.toFinset) (by simp),
    finsum_eq_sum_of_support_subset _ hsub]
  exact logDeriv_prod_eventuallyEq (fun i _ ↦ h i) (fun i _ ↦ h' i)

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
@isnad1 id=eventual.3h4v.s7.75df5775f22c from=seed src=0 shape=9e650bca vocab=fcbd6044
-/
theorem Meromorphic.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'}
    (hF : (mulSupport F).Finite) (h : ∀ i, Meromorphic (F i))
    (h' : ∀ i x, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i) =ᶠ[codiscrete 𝕜] ∑ᶠ i, logDeriv (F i) := by
  apply MeromorphicOn.logDeriv_finprod_eventuallyEq hF (fun i ↦ meromorphicOn_univ.mpr (h i))
  aesop

/--
Away from a codiscrete subset of `U`, the logarithmic derivative of the `n`-th power of a
meromorphic function is `n` times the logarithmic derivative.
@isnad1 id=eventual.1h5v.s7.eff9a12caca8 from=seed src=0 shape=27234549 vocab=3296ab4d
-/
@[to_fun MeromorphicOn.logDeriv_fun_zpow_eventuallyEq]
theorem MeromorphicOn.logDeriv_zpow_eventuallyEq (hf : MeromorphicOn f U) (n : ℤ) :
    logDeriv (f ^ n) =ᶠ[codiscreteWithin U] n • logDeriv f := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with y hy
  rw [Pi.smul_apply, zsmul_eq_mul, show f ^ n = (f · ^ n) from rfl]
  exact logDeriv_fun_zpow hy.differentiableAt n

/--
Away from a codiscrete subset of `𝕜`, the logarithmic derivative of the `n`-th power of a
meromorphic function is `n` times the logarithmic derivative.
@isnad1 id=eventual.1h4v.s7.c658611bdd3a from=seed src=0 shape=ac73c8a2 vocab=2f968c0a
-/
@[to_fun Meromorphic.logDeriv_fun_zpow_eventuallyEq]
theorem Meromorphic.logDeriv_zpow_eventuallyEq (hf : Meromorphic f) (n : ℤ) :
    logDeriv (f ^ n) =ᶠ[codiscrete 𝕜] n • logDeriv f := by
  apply MeromorphicOn.logDeriv_zpow_eventuallyEq (meromorphicOn_univ.mpr hf)


/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of integer powers of meromorphic functions is the
corresponding weighted sum of logarithmic derivatives. This is the shape of statement used in the
differentiated Poisson–Jensen formula, where the exponents are given by a divisor.
@isnad1 id=eventual.3h6v.s8.274dbbac5115 from=seed src=0 shape=1b6633ae vocab=df620d5d
-/
theorem MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'} {d : ι → ℤ}
    (hd : (support d).Finite) (h : ∀ i, MeromorphicOn (F i) U)
    (h' : ∀ i, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i ^ d i)
      =ᶠ[codiscreteWithin U] fun z ↦ ∑ᶠ i, d i • logDeriv (F i) z := by
  have hA : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ hd.toFinset, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset hd.toFinset).2 fun i _ ↦ (h i).analyticAt_mem_codiscreteWithin
  have hN : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ hd.toFinset, F i y ≠ 0 :=
    (eventually_all_finset hd.toFinset).2 fun i _ ↦ (h i).eventually_codiscreteWithin_apply_ne_zero
      (h' i)
  filter_upwards [hA, hN] with y h₁y h₂y
  have h₀ : ∏ᶠ i, F i ^ d i = ∏ i ∈ hd.toFinset, F i ^ d i :=
    finprod_eq_prod_of_mulSupport_subset _ <| by simp +contextual [Set.subset_def, not_imp_not]
  have hsub : support (fun i ↦ d i • logDeriv (F i) y) ⊆ hd.toFinset := by
    simp +contextual [-support_mul, -mul_eq_zero, Set.subset_def, not_imp_not]
  calc logDeriv (∏ᶠ i, F i ^ d i) y
      = logDeriv (∏ i ∈ hd.toFinset, F i ^ d i) y := by rw [h₀]
    _ = ∑ i ∈ hd.toFinset, logDeriv (F i ^ d i) y :=
        logDeriv_prod (fun i hi ↦ zpow_ne_zero _ (h₂y i hi))
          (fun i hi ↦ ((h₁y i hi).zpow (h₂y i hi)).differentiableAt)
    _ = ∑ i ∈ hd.toFinset, d i • logDeriv (F i) y := by
        congr! with i hi
        rw [zsmul_eq_mul, Pi.pow_def]
        exact logDeriv_fun_zpow (h₁y i hi).differentiableAt (d i)
    _ = ∑ᶠ i, d i • logDeriv (F i) y := (finsum_eq_sum_of_support_subset _ hsub).symm

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a finite product of integer powers of meromorphic functions is the
corresponding weighted sum of logarithmic derivatives. This is the shape of statement used in the
differentiated Poisson–Jensen formula, where the exponents are given by a divisor.
@isnad1 id=eventual.3h5v.s8.16a17f700399 from=seed src=0 shape=d3503df4 vocab=70efdb82
-/
theorem Meromorphic.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'} {d : ι → ℤ}
    (hd : (support d).Finite) (h : ∀ i, Meromorphic (F i))
    (h' : ∀ i x, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i ^ d i)
      =ᶠ[codiscrete 𝕜] fun z ↦ ∑ᶠ i, d i • logDeriv (F i) z := by
  apply MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq hd (fun i ↦ meromorphicOn_univ.mpr (h i))
  aesop
