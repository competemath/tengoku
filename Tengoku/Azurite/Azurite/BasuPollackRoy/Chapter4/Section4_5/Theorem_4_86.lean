/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_88
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_90
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_91
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Definitions
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Definition_4_89
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_72
import Tengoku.Seed.RingTheory.Nullstellensatz
import Tengoku.Seed.RingTheory.IntegralClosure.IsIntegral.Basic
import Tengoku.Seed.RingTheory.IntegralClosure.Algebra.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Finrank
import Tengoku.Seed.LinearAlgebra.Dimension.StrongRankCondition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.5, Theorem 4.86: finiteness characterization of zero-dimensional systems

Let `K` be a field of characteristic zero, `C` an algebraically closed field extension of `K`,
and `𝒫` a finite subset of `K[X₁, …, X_k]`. Then `A = K[X]/Ideal(𝒫, K)` is a finite-dimensional
`K`-vector space of positive dimension if and only if the system `𝒫` is zero-dimensional (i.e.
`Zer(𝒫, Cᵏ)` is a non-empty finite set). Moreover the number of solutions is at most `dim_K A`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- **Bridge B1.** `Zer(𝒫, Cᵏ) = zeroLocus C (Ideal(𝒫, C))`.
@isnad1 id=eq.0h4v.s6.7928c6bbba2c from=translated src=- shape=68f51309 vocab=f64433f0
-/
theorem zerOfFinset_eq_zeroLocus (C : Type*) [Field C] [Algebra K C]
    (Ps : Finset (MvPolynomial (Fin k) K)) :
    zerOfFinset C Ps = MvPolynomial.zeroLocus C (idealOfPolysExt C Ps) := by
  classical
  ext x
  rw [MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro hx p hp
    refine aeval_eq_zero_of_mem_idealOfPolys hp x fun q hq => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
    rw [MvPolynomial.aeval_map_algebraMap]
    exact hx P hP
  · intro hx P hP
    have hmem : MvPolynomial.map (algebraMap K C) P ∈ idealOfPolysExt C Ps :=
      Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hP))
    have := hx _ hmem
    rwa [MvPolynomial.aeval_map_algebraMap] at this

section Ext

variable (C : Type*) [Field C] [Algebra K C]

/-- Image of a variable under the quotient map `C[X] → Ā`.-/
noncomputable def xiExt (Ps : Finset (MvPolynomial (Fin k) K)) (i : Fin k) : quotPolysExt C Ps :=
  Ideal.Quotient.mk (idealOfPolysExt C Ps) (X i)

/--
@isnad1 id=eq.0h5v.s10.cdd8bd60f146 from=translated src=- shape=d64be9d3 vocab=59661515
-/
theorem mkₐ_X (Ps : Finset (MvPolynomial (Fin k) K)) (i : Fin k) :
    (Ideal.Quotient.mkₐ C (idealOfPolysExt C Ps)) (X i) = xiExt C Ps i := by
  rw [xiExt, Ideal.Quotient.mkₐ_eq_mk]

/-- **Bridge B3.** The images of the variables generate `Ā` as a `C`-algebra.
@isnad1 id=eq.0h4v.s11.f8d4f8a5b4d2 from=translated src=- shape=1e78badb vocab=6e9a3139
-/
theorem adjoin_range_xiExt (Ps : Finset (MvPolynomial (Fin k) K)) :
    Algebra.adjoin C (Set.range (fun i => xiExt C Ps i)) = ⊤ := by
  have hxi : Set.range (fun i => xiExt C Ps i)
      = (Ideal.Quotient.mkₐ C (idealOfPolysExt C Ps)) '' (Set.range X) := by
    rw [← Set.range_comp]
    congr 1
  rw [hxi, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
  exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective C (idealOfPolysExt C Ps))

/-- **Bridge B4.** `Ā` is finite-dimensional over `C` iff every variable image is integral.
@isnad1 id=iff.0h4v.s8.261198e62553 from=translated src=- shape=0c5fa851 vocab=b2c20c81
-/
theorem finiteDimensional_ext_iff_isIntegral (Ps : Finset (MvPolynomial (Fin k) K)) :
    FiniteDimensional C (quotPolysExt C Ps) ↔ ∀ i, IsIntegral C (xiExt C Ps i) := by
  constructor
  · intro hfd i
    have : Module.Finite C (quotPolysExt C Ps) := hfd
    exact IsIntegral.of_finite C _
  · intro hint
    have hfin : Module.Finite C (Algebra.adjoin C (Set.range (fun i => xiExt C Ps i))) :=
      Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _)
        (fun z hz => by obtain ⟨i, rfl⟩ := hz; exact hint i)
    rw [adjoin_range_xiExt] at hfin
    exact Module.Finite.equiv (Subalgebra.topEquiv.toLinearEquiv)

end Ext

/-- Naturality: an `AlgHom` `f : C[X] →ₐ B` commutes with substituting `X i` into a univariate
polynomial.
@isnad1 id=eq.0h6v.s9.8c8010d4fbd8 from=translated src=- shape=95b6f59d vocab=70e66a95
-/
theorem algHom_aeval_X {C : Type*} [CommRing C] {B : Type*} [CommRing B] [Algebra C B]
    (f : MvPolynomial (Fin k) C →ₐ[C] B) (i : Fin k) (Q : Polynomial C) :
    f (Polynomial.aeval (X i) Q) = Polynomial.aeval (f (X i)) Q :=
  (Polynomial.aeval_algHom_apply f (X i) Q).symm

section IntegralFinite

variable (C : Type*) [Field C] [IsAlgClosed C] [Algebra K C]

/-- **Bridge B5.** Every variable image is integral over `C` iff `Zer(𝒫, Cᵏ)` is finite.
@isnad1 id=iff.0h4v.s7.39696d7978f5 from=translated src=- shape=fc17c90a vocab=48f70cb1
-/
theorem isIntegral_iff_finite [CharZero K] (Ps : Finset (MvPolynomial (Fin k) K)) :
    (∀ i, IsIntegral C (xiExt C Ps i)) ↔ (zerOfFinset C Ps).Finite := by
  classical
  constructor
  · -- integral ⟹ finite
    intro hint
    -- choose for each `i` a monic `Q i` annihilating `xiExt C Ps i`
    choose Q hQmonic hQzero using hint
    -- the substituted multivariate poly lies in J, so vanishes on Zer
    have hroot : ∀ i, ∀ x ∈ zerOfFinset C Ps, (Q i).eval (x i) = 0 := by
      intro i x hx
      -- `Polynomial.aeval (X i) (Q i)` lies in J
      have hqJ : Polynomial.aeval (X i) (Q i) ∈ idealOfPolysExt C Ps := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        have hh : (Ideal.Quotient.mkₐ C (idealOfPolysExt C Ps)) (Polynomial.aeval (X i) (Q i))
            = Polynomial.aeval (xiExt C Ps i) (Q i) := by
          rw [algHom_aeval_X, mkₐ_X]
        rw [Ideal.Quotient.mkₐ_eq_mk] at hh
        rw [hh]
        exact hQzero i
      rw [zerOfFinset_eq_zeroLocus, MvPolynomial.mem_zeroLocus_iff] at hx
      have hax := hx _ hqJ
      rw [algHom_aeval_X (MvPolynomial.aeval x) i (Q i), MvPolynomial.aeval_X,
        Polynomial.coe_aeval_eq_eval] at hax
      exact hax
    -- Zer ⊆ {x | ∀ i, x i ∈ (Q i).roots.toFinset}, which injects into a finite product
    refine Set.Finite.subset (Set.Finite.pi (fun i => (Q i).roots.toFinset.finite_toSet)) ?_
    intro x hx i _
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    exact Polynomial.mem_roots'.mpr ⟨(hQmonic i).ne_zero, hroot i x hx⟩
  · -- finite ⟹ integral
    intro hfin i
    -- monic univariate poly vanishing at all `x i`
    set Qi : Polynomial C := ∏ x ∈ hfin.toFinset, (Polynomial.X - Polynomial.C (x i)) with hQi
    have hQimonic : Qi.Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C (x i))
    -- its multivariate substitution
    set pi : MvPolynomial (Fin k) C := Polynomial.aeval (X i) Qi with hpi
    -- `pi` vanishes on `Zer(𝒫, Cᵏ)`
    have hpivanish : ∀ y ∈ zerOfFinset C Ps, MvPolynomial.aeval y pi = 0 := by
      intro y hy
      rw [hpi, algHom_aeval_X (MvPolynomial.aeval y) i Qi, MvPolynomial.aeval_X,
        Polynomial.coe_aeval_eq_eval, hQi, Polynomial.eval_prod]
      refine Finset.prod_eq_zero (hfin.mem_toFinset.mpr hy) ?_
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
    -- so `pi ∈ J.radical`, i.e. `pi^m ∈ J`
    have hpirad : pi ∈ (idealOfPolysExt C Ps).radical := by
      have : pi ∈ MvPolynomial.vanishingIdeal C (zerOfFinset C Ps) :=
        MvPolynomial.mem_vanishingIdeal_iff.mpr hpivanish
      rw [zerOfFinset_eq_zeroLocus,
        MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at this
      exact this
    obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hpirad
    -- the integral witness is `Qi ^ m`
    refine ⟨Qi ^ m, hQimonic.pow m, ?_⟩
    -- `aeval (xiExt) (Qi^m) = mk (pi^m) = 0`
    have hkey : Polynomial.aeval (xiExt C Ps i) (Qi ^ m)
        = Ideal.Quotient.mk (idealOfPolysExt C Ps) (pi ^ m) := by
      rw [← mkₐ_X C Ps i,
        ← algHom_aeval_X (Ideal.Quotient.mkₐ C (idealOfPolysExt C Ps)) i (Qi ^ m),
        Ideal.Quotient.mkₐ_eq_mk, hpi, map_pow]
    show Polynomial.aeval (xiExt C Ps i) (Qi ^ m) = 0
    rw [hkey, Ideal.Quotient.eq_zero_iff_mem]
    exact hm

end IntegralFinite

end Azurite.BPR.Chapter4
