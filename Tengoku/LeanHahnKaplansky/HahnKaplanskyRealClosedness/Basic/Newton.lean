/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanHahnKaplansky.HahnKaplanskyRealClosedness.Basic.Cluster

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local Hahn-Newton step estimates for cluster polynomials
-/

namespace HahnKaplanskyRealClosedness

open Polynomial
open HahnSeries

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- A unit of the valuation subring has valuation zero.
@isnad1 id=eq.1h3v.s10.080067594593 from=translated src=- shape=94579bde vocab=2ef3f6b3
-/
theorem addVal_eq_zero_of_isUnit (x : valuationSubring k Γ) (hx : IsUnit x) :
    addVal k Γ (x : HahnField k Γ) = 0 := by
  have hxnonneg : (0 : WithTop Γ) ≤ addVal k Γ (x : HahnField k Γ) := x.property
  by_contra hne
  have hpos : (0 : WithTop Γ) < addVal k Γ (x : HahnField k Γ) :=
    lt_of_le_of_ne hxnonneg (fun h => hne h.symm)
  exact (IsLocalRing.notMem_maximalIdeal.mpr hx)
    ((mem_maximalIdeal_iff_pos_addVal k Γ x).mpr hpos)

/-- For elements of the valuation subring, being a unit is equivalent to having valuation zero.
@isnad1 id=iff.0h3v.s10.2d87a9736bb5 from=translated src=- shape=5891a4bf vocab=2ef3f6b3
-/
theorem isUnit_iff_addVal_eq_zero (x : valuationSubring k Γ) :
    IsUnit x ↔ addVal k Γ (x : HahnField k Γ) = 0 :=
  ⟨addVal_eq_zero_of_isUnit k Γ x, fun hx => isUnit_of_addVal_eq_zero k Γ hx⟩

/-- A unit coefficient has valuation zero.
@isnad1 id=eq.1h4v.s11.af9fcb85ede6 from=translated src=- shape=51ccc78c vocab=4772425c
-/
theorem addVal_coeff_eq_zero_of_isUnit {F : (valuationSubring k Γ)[X]} {i : ℕ}
    (hunit : IsUnit (F.coeff i)) :
    addVal k Γ (F.coeff i : HahnField k Γ) = 0 :=
  addVal_eq_zero_of_isUnit k Γ (F.coeff i) hunit

/-- The constant coefficient of a positive cluster lies in the maximal ideal.
@isnad1 id=mem.2h4v.s13.96f4081ce590 from=translated src=- shape=03cbfcf9 vocab=28cd3bc5
-/
theorem coeff_zero_mem_maximalIdeal_of_cluster_pos {F : (valuationSubring k Γ)[X]} {m : ℕ}
    (hsmall : ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hm : 0 < m) :
    F.coeff 0 ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  hsmall 0 hm

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- If every summand has positive valuation, so does the finite sum.
@isnad1 id=lt.1h5v.s9.426235d45dd9 from=translated src=- shape=528202f0 vocab=26174669
-/
theorem addVal_sum_pos_of_forall_pos {ι : Type*} {s : Finset ι}
    {f : ι → HahnField k Γ}
    (hf : ∀ i ∈ s, (0 : WithTop Γ) < addVal k Γ (f i)) :
    (0 : WithTop Γ) < addVal k Γ (∑ i ∈ s, f i) :=
  (addVal k Γ).map_lt_sum' (by simp) hf

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- If every summand has valuation strictly above a finite bound, so does the finite sum.
@isnad1 id=lt.1h6v.s9.4030202bac95 from=translated src=- shape=5c034e5b vocab=15370930
-/
theorem addVal_sum_gt_of_forall_gt {ι : Type*} {s : Finset ι}
    {f : ι → HahnField k Γ} {γ : Γ}
    (hf : ∀ i ∈ s, (γ : WithTop Γ) < addVal k Γ (f i)) :
    (γ : WithTop Γ) < addVal k Γ (∑ i ∈ s, f i) :=
  (addVal k Γ).map_lt_sum' (WithTop.coe_lt_top γ) hf

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- If two Hahn-field elements both have valuation above a finite bound, so does their sum.
@isnad1 id=lt.2h5v.s9.3b6a83503de4 from=translated src=- shape=609e5355 vocab=96541d67
-/
theorem addVal_add_gt_of_forall_gt {x y : HahnField k Γ} {γ : Γ}
    (hx : (γ : WithTop Γ) < addVal k Γ x) (hy : (γ : WithTop Γ) < addVal k Γ y) :
    (γ : WithTop Γ) < addVal k Γ (x + y) :=
  (addVal k Γ).map_lt_add hx hy

/-- A positive cluster maps the maximal ideal into itself.
@isnad1 id=mem.3h5v.s14.465b71368bcd from=translated src=- shape=3fa6ea52 vocab=ca04ce0f
-/
theorem eval_mem_maximalIdeal_of_cluster_pos
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {y : valuationSubring k Γ}
    (hsmall : ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hm : 0 < m) (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    F.eval y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  rw [Polynomial.eval_eq_sum_range]
  apply Ideal.sum_mem
  intro i _hi
  by_cases hi0 : i = 0
  · subst i
    simpa using coeff_zero_mem_maximalIdeal_of_cluster_pos k Γ hsmall hm
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    exact (IsLocalRing.maximalIdeal (valuationSubring k Γ)).mul_mem_left (F.coeff i)
      ((IsLocalRing.maximalIdeal (valuationSubring k Γ)).pow_mem_of_mem hy i hipos)

/-- A unit coefficient bounds the polynomial degree from below.
@isnad1 id=le.1h4v.s11.f61b1cf2d4b5 from=translated src=- shape=dd3e181b vocab=75f42730
-/
theorem le_natDegree_of_unit_coeff {F : (valuationSubring k Γ)[X]} {m : ℕ}
    (hunit : IsUnit (F.coeff m)) :
    m ≤ F.natDegree :=
  Polynomial.le_natDegree_of_ne_zero hunit.ne_zero

/-- A Hahn monomial of nonnegative exponent, viewed in the valuation subring.-/
def singleOfNonneg (γ : Γ) (c : k) (hγ : 0 ≤ γ) : valuationSubring k Γ :=
  ⟨toLex (HahnSeries.single γ c), by
    change (0 : WithTop Γ) ≤ addVal k Γ (toLex (HahnSeries.single γ c))
    by_cases hc : c = 0
    · subst c
      simp [HahnSeries.single_eq_zero]
    · rw [addVal_single_of_ne (k := k) (Γ := Γ) hc]
      simpa using hγ⟩

/--
@isnad1 id=eq.1h4v.s9.80bb7dfbdfed from=translated src=- shape=c1b0b525 vocab=c3ab3c6f
-/
@[simp]
theorem singleOfNonneg_coe (γ : Γ) (c : k) (hγ : 0 ≤ γ) :
    (singleOfNonneg k Γ γ c hγ : HahnField k Γ) =
      toLex (HahnSeries.single γ c) :=
  rfl

/-- The valuation of a nonzero nonnegative Hahn monomial.
@isnad1 id=eq.2h4v.s9.f2ce9133e530 from=translated src=- shape=e52e7c07 vocab=3d0f6af7
-/
theorem addVal_singleOfNonneg_of_ne {γ : Γ} {c : k} (hγ : 0 ≤ γ) (hc : c ≠ 0) :
    addVal k Γ (singleOfNonneg k Γ γ c hγ : HahnField k Γ) = (γ : WithTop Γ) := by
  rw [singleOfNonneg_coe, addVal_single_of_ne (k := k) (Γ := Γ) hc]

/-- The valuation of a power of a nonzero nonnegative Hahn monomial.
@isnad1 id=eq.2h5v.s9.627797b83b6c from=translated src=- shape=fe6b2c88 vocab=b3b74d3f
-/
theorem addVal_singleOfNonneg_pow_of_ne {γ : Γ} {c : k} (hγ : 0 ≤ γ) (hc : c ≠ 0)
    (n : ℕ) :
    addVal k Γ ((singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ n) =
      (n • γ : WithTop Γ) := by
  rw [AddValuation.map_pow, addVal_singleOfNonneg_of_ne (k := k) (Γ := Γ) hγ hc]

/-- The valuation of one summand after substituting a nonzero nonnegative Hahn monomial.
@isnad1 id=eq.2h6v.s11.b10362f97c7b from=translated src=- shape=78b14cc6 vocab=d42094d3
-/
theorem addVal_coeff_mul_singleOfNonneg_pow_of_ne
    {F : (valuationSubring k Γ)[X]} {γ : Γ} {c : k}
    (hγ : 0 ≤ γ) (hc : c ≠ 0) (i : ℕ) :
    addVal k Γ ((F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ i) =
      addVal k Γ (F.coeff i : HahnField k Γ) + (i • γ : WithTop Γ) := by
  rw [AddValuation.map_mul, addVal_singleOfNonneg_pow_of_ne (k := k) (Γ := Γ) hγ hc]

/-- The main cluster summand has valuation `m • γ` after substituting a nonzero nonnegative
Hahn monomial.
@isnad1 id=eq.3h6v.s12.af9dd025b0ef from=translated src=- shape=8366a981 vocab=1fe12a93
-/
theorem addVal_cluster_main_summand_singleOfNonneg
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {γ : Γ} {c : k}
    (hunit : IsUnit (F.coeff m)) (hγ : 0 ≤ γ) (hc : c ≠ 0) :
    addVal k Γ ((F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ m) =
      (m • γ : WithTop Γ) := by
  rw [addVal_coeff_mul_singleOfNonneg_pow_of_ne (k := k) (Γ := Γ) hγ hc,
    addVal_coeff_eq_zero_of_isUnit k Γ hunit, zero_add]

/-- If the substituted exponent is chosen so that `m • δ = γ`, the main cluster summand has
valuation exactly `γ`.
@isnad1 id=eq.4h7v.s12.adaa8c2d0c19 from=translated src=- shape=abbf0761 vocab=1fe12a93
-/
theorem addVal_cluster_main_summand_singleOfNonneg_eq_of_nsmul_eq
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {δ γ : Γ} {c : k}
    (hunit : IsUnit (F.coeff m)) (hδ_nonneg : 0 ≤ δ) (hc : c ≠ 0)
    (hδ : m • δ = γ) :
    addVal k Γ ((F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m) =
      (γ : WithTop Γ) := by
  rw [addVal_cluster_main_summand_singleOfNonneg (k := k) (Γ := Γ)
    hunit hδ_nonneg hc]
  rw [← WithTop.coe_nsmul, hδ]

/-- The coefficient at the main valuation of the main cluster summand after monomial
substitution.
@isnad1 id=eq.2h7v.s12.e733ecaf448f from=translated src=- shape=67318da4 vocab=0daef536
-/
theorem coeff_cluster_main_summand_singleOfNonneg_of_nsmul_eq
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {δ γ : Γ} {c : k}
    (hδ_nonneg : 0 ≤ δ) (hδ : m • δ = γ) :
    (ofLex ((F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m)).coeff γ =
      constantCoeffRingHom k Γ (F.coeff m) * c ^ m := by
  change ((ofLex (F.coeff m : HahnField k Γ)) *
      (HahnSeries.single δ c) ^ m).coeff γ =
    constantCoeffRingHom k Γ (F.coeff m) * c ^ m
  rw [HahnSeries.single_pow, hδ, HahnSeries.coeff_mul_single]
  simp [constantCoeffRingHom_apply]

/-- At the target valuation, adding the main correction changes the error coefficient by
`residue(F_m) * c^m`.
@isnad1 id=eq.3h9v.s12.430216ffc185 from=translated src=- shape=c142887c vocab=88430de4
-/
theorem coeff_error_add_cluster_main_summand_singleOfNonneg
    {e : valuationSubring k Γ} {F : (valuationSubring k Γ)[X]} {m : ℕ}
    {δ γ : Γ} {b c : k}
    (hecoeff : (ofLex (e : HahnField k Γ)).coeff γ = b)
    (hδ_nonneg : 0 ≤ δ) (hδ : m • δ = γ) :
    (ofLex ((e : HahnField k Γ) + (F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m)).coeff γ =
      b + constantCoeffRingHom k Γ (F.coeff m) * c ^ m := by
  change ((ofLex (e : HahnField k Γ)) +
      ofLex ((F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m)).coeff γ =
    b + constantCoeffRingHom k Γ (F.coeff m) * c ^ m
  rw [HahnSeries.coeff_add, hecoeff,
    coeff_cluster_main_summand_singleOfNonneg_of_nsmul_eq (k := k) (Γ := Γ)
      (F := F) (m := m) hδ_nonneg hδ]

/-- If the residue-side cancellation equation holds, the target coefficient of the corrected
leading error is zero.
@isnad1 id=eq.4h9v.s12.d58a47df1914 from=translated src=- shape=c92ada45 vocab=88430de4
-/
theorem coeff_error_add_cluster_main_summand_singleOfNonneg_eq_zero
    {e : valuationSubring k Γ} {F : (valuationSubring k Γ)[X]} {m : ℕ}
    {δ γ : Γ} {b c : k}
    (hecoeff : (ofLex (e : HahnField k Γ)).coeff γ = b)
    (hδ_nonneg : 0 ≤ δ) (hδ : m • δ = γ)
    (hcancel : b + constantCoeffRingHom k Γ (F.coeff m) * c ^ m = 0) :
    (ofLex ((e : HahnField k Γ) + (F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m)).coeff γ = 0 := by
  rw [coeff_error_add_cluster_main_summand_singleOfNonneg
    (k := k) (Γ := Γ) (F := F) (m := m) hecoeff hδ_nonneg hδ, hcancel]

/-- If the main correction coefficient cancels the leading error coefficient, then the valuation of
`error + main correction` strictly improves.
@isnad1 id=lt.7h9v.s13.9f841152e27b from=translated src=- shape=bb0ff05e vocab=50650864
-/
theorem lt_addVal_error_add_cluster_main_summand_singleOfNonneg
    {e : valuationSubring k Γ} {F : (valuationSubring k Γ)[X]} {m : ℕ}
    {δ γ : Γ} {b c : k}
    (heval : addVal k Γ (e : HahnField k Γ) = (γ : WithTop Γ))
    (hecoeff : (ofLex (e : HahnField k Γ)).coeff γ = b)
    (hunit : IsUnit (F.coeff m)) (hδ_nonneg : 0 ≤ δ) (hc : c ≠ 0)
    (hδ : m • δ = γ)
    (hcancel : b + constantCoeffRingHom k Γ (F.coeff m) * c ^ m = 0) :
    (γ : WithTop Γ) <
      addVal k Γ ((e : HahnField k Γ) + (F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m) := by
  apply lt_addVal_of_le_addVal_of_coeff_eq_zero k Γ
  · apply le_addVal_add_of_le_addVal k Γ
    · exact le_of_eq heval.symm
    · exact le_of_eq (addVal_cluster_main_summand_singleOfNonneg_eq_of_nsmul_eq
        k Γ hunit hδ_nonneg hc hδ).symm
  · exact coeff_error_add_cluster_main_summand_singleOfNonneg_eq_zero
      k Γ hecoeff hδ_nonneg hδ hcancel

/-- Terms above the cluster degree have valuation strictly larger than the target value
`m • δ` when substituting a nonzero positive Hahn monomial of exponent `δ`.
@isnad1 id=lt.4h8v.s11.ea25d1ff54ef from=translated src=- shape=2eda78ac vocab=9278c9ac
-/
theorem lt_addVal_cluster_high_summand_singleOfNonneg_of_nsmul_eq
    {F : (valuationSubring k Γ)[X]} {m i : ℕ} {δ γ : Γ} {c : k}
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ) (hmi : m < i) :
    (γ : WithTop Γ) <
      addVal k Γ ((F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ i) := by
  rw [addVal_coeff_mul_singleOfNonneg_pow_of_ne
    (k := k) (Γ := Γ) (le_of_lt hδpos) hc]
  rw [← hδ, ← WithTop.coe_nsmul]
  have hcoeff_nonneg :
      (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i : HahnField k Γ) :=
    (F.coeff i).property
  have hpow_lt : (m • δ : WithTop Γ) < (i • δ : WithTop Γ) := by
    exact_mod_cast nsmul_lt_nsmul_left hδpos hmi
  exact lt_of_lt_of_le hpow_lt (le_add_of_nonneg_left hcoeff_nonneg)

/-- Lower cluster terms are also above the target valuation when their coefficients are above the
corresponding first-slope bound.
@isnad1 id=lt.5h8v.s11.adf92b37b98c from=translated src=- shape=99e497b0 vocab=ade0dc37
-/
theorem lt_addVal_cluster_lower_summand_singleOfNonneg_of_coeff_bound
    {F : (valuationSubring k Γ)[X]} {m i : ℕ} {δ γ : Γ} {c : k}
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ) (hi : i < m)
    (hcoeff : (((m - i) • δ : Γ) : WithTop Γ) <
      addVal k Γ (F.coeff i : HahnField k Γ)) :
    (γ : WithTop Γ) <
      addVal k Γ ((F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ i) := by
  rw [addVal_coeff_mul_singleOfNonneg_pow_of_ne
    (k := k) (Γ := Γ) (le_of_lt hδpos) hc]
  by_cases hzero : (F.coeff i : HahnField k Γ) = 0
  · simp [hzero]
  · let η : Γ := (addVal k Γ (F.coeff i : HahnField k Γ)).untop
        (by simpa [AddValuation.ne_top_iff] using hzero)
    have hη :
        addVal k Γ (F.coeff i : HahnField k Γ) = (η : WithTop Γ) :=
      (WithTop.coe_untop _ _).symm
    have hη_gt : (m - i) • δ < η := by
      apply WithTop.coe_lt_coe.mp
      simpa [hη] using hcoeff
    rw [hη, ← hδ, ← WithTop.coe_nsmul, ← WithTop.coe_add]
    apply WithTop.coe_lt_coe.mpr
    have hsplit : m • δ = (m - i) • δ + i • δ := by
      rw [← add_nsmul, Nat.sub_add_cancel hi.le]
    rw [hsplit]
    simpa [add_comm, add_left_comm, add_assoc] using add_lt_add_right hη_gt (i • δ)

/-- Every non-constant, non-main term is above the target valuation under the positive-degree
lower first-slope bounds. The constant term is handled together with the current error.
@isnad1 id=lt.6h8v.s11.d56aeea7acc9 from=translated src=- shape=0aaceadc vocab=ade0dc37
-/
theorem lt_addVal_cluster_nonconstant_nonmain_summand_singleOfNonneg_of_nsmul_eq
    {F : (valuationSubring k Γ)[X]} {m i : ℕ} {δ γ : Γ} {c : k}
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ)
    (hlower : ∀ j, 0 < j → j < m → (((m - j) • δ : Γ) : WithTop Γ) <
      addVal k Γ (F.coeff j : HahnField k Γ))
    (hi0 : i ≠ 0) (hi : i ≠ m) :
    (γ : WithTop Γ) <
      addVal k Γ ((F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ i) := by
  rcases lt_or_gt_of_ne hi with him | hmi
  · exact lt_addVal_cluster_lower_summand_singleOfNonneg_of_coeff_bound
      k Γ hδpos hc hδ him (hlower i (Nat.pos_of_ne_zero hi0) him)
  · exact lt_addVal_cluster_high_summand_singleOfNonneg_of_nsmul_eq
      k Γ hδpos hc hδ hmi

/-- A finite sum of non-constant, non-main cluster correction terms is above the target valuation
under the positive-degree lower first-slope bounds.
@isnad1 id=lt.6h8v.s11.3b2958cfd309 from=translated src=- shape=1cfbe853 vocab=1bee7fd4
-/
theorem lt_addVal_sum_cluster_nonconstant_nonmain_summands_singleOfNonneg_of_nsmul_eq
    {F : (valuationSubring k Γ)[X]} {s : Finset ℕ} {m : ℕ} {δ γ : Γ} {c : k}
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ)
    (hlower : ∀ j, 0 < j → j < m → (((m - j) • δ : Γ) : WithTop Γ) <
      addVal k Γ (F.coeff j : HahnField k Γ))
    (hs0 : ∀ i ∈ s, i ≠ 0) (hsm : ∀ i ∈ s, i ≠ m) :
    (γ : WithTop Γ) <
      addVal k Γ (∑ i ∈ s, (F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ i) := by
  apply addVal_sum_gt_of_forall_gt k Γ
  intro i hi
  exact lt_addVal_cluster_nonconstant_nonmain_summand_singleOfNonneg_of_nsmul_eq
    k Γ hδpos hc hδ hlower (hs0 i hi) (hsm i hi)

/-- A nonzero Hahn monomial of positive exponent lies in the maximal ideal.
@isnad1 id=mem.2h4v.s12.bac8407e86da from=translated src=- shape=b5cb000a vocab=6c905380
-/
theorem singleOfNonneg_mem_maximalIdeal_of_pos {γ : Γ} {c : k}
    (hγ : 0 < γ) (hc : c ≠ 0) :
    singleOfNonneg k Γ γ c (le_of_lt hγ) ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  rw [mem_maximalIdeal_iff_pos_addVal]
  rw [addVal_singleOfNonneg_of_ne (k := k) (Γ := Γ) (le_of_lt hγ) hc]
  simpa using hγ

/-- Adding a nonzero positive Hahn monomial to an element of the maximal ideal stays in the
maximal ideal.
@isnad1 id=mem.3h5v.s13.ed641f0748ae from=translated src=- shape=584c3621 vocab=5abb41f4
-/
theorem add_singleOfNonneg_mem_maximalIdeal_of_mem_of_pos
    {y : valuationSubring k Γ} {γ : Γ} {c : k}
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hγ : 0 < γ) (hc : c ≠ 0) :
    y + singleOfNonneg k Γ γ c (le_of_lt hγ) ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  (IsLocalRing.maximalIdeal (valuationSubring k Γ)).add_mem hy
    (singleOfNonneg_mem_maximalIdeal_of_pos k Γ hγ hc)

/-- A Hahn monomial of positive exponent has zero residue.
@isnad1 id=eq.1h4v.s11.5bec68ff1f95 from=translated src=- shape=7dcce1a2 vocab=48c9ed9d
-/
theorem constantCoeffRingHom_singleOfNonneg_pos {γ : Γ} (hγ : 0 < γ) (c : k) :
    constantCoeffRingHom k Γ (singleOfNonneg k Γ γ c (le_of_lt hγ)) = 0 := by
  rw [constantCoeffRingHom_apply, singleOfNonneg_coe]
  change (HahnSeries.single γ c).coeff 0 = 0
  exact HahnSeries.coeff_single_of_ne (ne_of_lt hγ)

/-- Adding a positive-exponent Hahn monomial does not change the residue.
@isnad1 id=eq.1h5v.s12.673c110f0761 from=translated src=- shape=21d99b22 vocab=5ead5985
-/
theorem constantCoeffRingHom_add_singleOfNonneg_pos
    (y : valuationSubring k Γ) {γ : Γ} (hγ : 0 < γ) (c : k) :
    constantCoeffRingHom k Γ (y + singleOfNonneg k Γ γ c (le_of_lt hγ)) =
      constantCoeffRingHom k Γ y := by
  rw [map_add, constantCoeffRingHom_singleOfNonneg_pos (k := k) (Γ := Γ) hγ c, add_zero]

/-- Taking the residue of a valuation-subring polynomial evaluation agrees with evaluating the
residue polynomial at the residue of the point.
@isnad1 id=eq.0h4v.s12.e8b4f5a3a7c1 from=translated src=- shape=169a3ca5 vocab=28f503e9
-/
theorem constantCoeffRingHom_eval_eq_eval_map
    (F : (valuationSubring k Γ)[X]) (y : valuationSubring k Γ) :
    constantCoeffRingHom k Γ (F.eval y) =
      (F.map (constantCoeffRingHom k Γ)).eval (constantCoeffRingHom k Γ y) :=
  (Polynomial.eval_map_apply
    (f := constantCoeffRingHom k Γ) (p := F) (x := y)).symm

/-- Evaluating over the valuation subring and then embedding into the Hahn field agrees with
evaluating the mapped polynomial over the Hahn field.
@isnad1 id=eq.0h4v.s11.b1de0a70e546 from=translated src=- shape=b825b43d vocab=38624388
-/
theorem eval_map_algebraMap_eq_coe_eval
    (F : (valuationSubring k Γ)[X]) (x : valuationSubring k Γ) :
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (x : HahnField k Γ) =
      ((F.eval x : valuationSubring k Γ) : HahnField k Γ) := by
  simpa only [Algebra.algebraMap_ofSubsemiring_apply] using Polynomial.eval_map_apply
    (f := algebraMap (valuationSubring k Γ) (HahnField k Γ)) (p := F) (x := x)

/-- Specialization of `eval_map_algebraMap_eq_coe_eval` to nonnegative Hahn monomials.
@isnad1 id=eq.1h5v.s11.718ffe526cc5 from=translated src=- shape=fcd7b6c5 vocab=c9736c10
-/
theorem eval_map_algebraMap_singleOfNonneg
    (F : (valuationSubring k Γ)[X]) {γ : Γ} (c : k) (hγ : 0 ≤ γ) :
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ) =
      ((F.eval (singleOfNonneg k Γ γ c hγ) : valuationSubring k Γ) : HahnField k Γ) :=
  eval_map_algebraMap_eq_coe_eval k Γ F (singleOfNonneg k Γ γ c hγ)

/-- Finite-sum expansion of a valuation-subring polynomial evaluated after mapping to the Hahn
field.
@isnad1 id=eq.0h4v.s12.21fa3011c917 from=translated src=- shape=c16b5a68 vocab=83dd62de
-/
theorem eval_map_algebraMap_eq_sum_range
    (F : (valuationSubring k Γ)[X]) (x : HahnField k Γ) :
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval x =
      ∑ i ∈ Finset.range (F.natDegree + 1),
        (F.coeff i : HahnField k Γ) * x ^ i := by
  rw [Polynomial.eval_eq_sum_range,
    Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (algebraMap (valuationSubring k Γ) (HahnField k Γ)) from
        fun a b h => Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.coeff_map]
  change ((F.coeff i : valuationSubring k Γ) : HahnField k Γ) * x ^ i =
    ((F.coeff i : valuationSubring k Γ) : HahnField k Γ) * x ^ i
  rfl

/-- Finite-sum expansion after substituting a nonnegative Hahn monomial.
@isnad1 id=eq.1h5v.s12.62d4e968245a from=translated src=- shape=4464376e vocab=ee055e20
-/
theorem eval_map_algebraMap_singleOfNonneg_eq_sum_range
    (F : (valuationSubring k Γ)[X]) {γ : Γ} (c : k) (hγ : 0 ≤ γ) :
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ) =
      ∑ i ∈ Finset.range (F.natDegree + 1),
        (F.coeff i : HahnField k Γ) *
          (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ i :=
  eval_map_algebraMap_eq_sum_range k Γ F (singleOfNonneg k Γ γ c hγ)

/-- Split a monomial substitution evaluation into its constant term, the degree-`m` summand, and
the remaining summands.
@isnad1 id=eq.3h6v.s13.218f39ca053e from=translated src=- shape=487e87b2 vocab=7bf32480
-/
theorem eval_map_algebraMap_singleOfNonneg_eq_const_add_main_add_nonmain
    (F : (valuationSubring k Γ)[X]) {m : ℕ} {γ : Γ} (c : k) (hγ : 0 ≤ γ)
    (hm_pos : 0 < m) (hmdeg : m ≤ F.natDegree) :
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ) =
      (F.coeff 0 : HahnField k Γ) +
        ((F.coeff m : HahnField k Γ) *
            (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ m +
          ∑ i ∈ ((Finset.range (F.natDegree + 1)).erase 0).erase m,
            (F.coeff i : HahnField k Γ) *
              (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ i) := by
  let s : Finset ℕ := Finset.range (F.natDegree + 1)
  let t : valuationSubring k Γ := singleOfNonneg k Γ γ c hγ
  let f : ℕ → HahnField k Γ := fun i => (F.coeff i : HahnField k Γ) * (t : HahnField k Γ) ^ i
  have h0mem : 0 ∈ s := by
    dsimp [s]
    exact Finset.mem_range.mpr (Nat.succ_pos _)
  have hmmem : m ∈ s.erase 0 := by
    rw [Finset.mem_erase]
    exact ⟨hm_pos.ne', by
      dsimp [s]
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hmdeg)⟩
  calc
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ)
        = ∑ i ∈ s, f i := by
          dsimp [s, f, t]
          exact eval_map_algebraMap_singleOfNonneg_eq_sum_range k Γ F c hγ
    _ = f 0 + ∑ i ∈ s.erase 0, f i := by
          exact (Finset.add_sum_erase s f h0mem).symm
    _ = f 0 + (f m + ∑ i ∈ (s.erase 0).erase m, f i) := by
          rw [(Finset.add_sum_erase (s.erase 0) f hmmem).symm]
    _ = (F.coeff 0 : HahnField k Γ) +
        ((F.coeff m : HahnField k Γ) *
            (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ m +
          ∑ i ∈ ((Finset.range (F.natDegree + 1)).erase 0).erase m,
            (F.coeff i : HahnField k Γ) *
              (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ i) := by
          simp [s, f, t]

/-- If the constant term plus the main correction improves, and every other correction term is
above the target valuation, then the whole monomial-substitution evaluation improves.
@isnad1 id=lt.7h7v.s13.d1ddddd988c9 from=translated src=- shape=b8d5e91d vocab=52e216a1
-/
theorem lt_addVal_eval_map_singleOfNonneg_of_const_main_improves
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {δ γ : Γ} {c : k}
    (hm_pos : 0 < m) (hunit : IsUnit (F.coeff m))
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ)
    (hlower : ∀ j, 0 < j → j < m → (((m - j) • δ : Γ) : WithTop Γ) <
      addVal k Γ (F.coeff j : HahnField k Γ))
    (hmain : (γ : WithTop Γ) <
      addVal k Γ ((F.coeff 0 : HahnField k Γ) + (F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ m)) :
    (γ : WithTop Γ) <
      addVal k Γ ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ)) := by
  let rest : HahnField k Γ :=
    ∑ i ∈ ((Finset.range (F.natDegree + 1)).erase 0).erase m,
      (F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ i
  have hrest : (γ : WithTop Γ) < addVal k Γ rest := by
    dsimp [rest]
    exact lt_addVal_sum_cluster_nonconstant_nonmain_summands_singleOfNonneg_of_nsmul_eq
      k Γ hδpos hc hδ hlower
      (by
        intro i hi
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1)
      (by
        intro i hi
        exact (Finset.mem_erase.mp hi).1)
  have heval :
      (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) =
        (F.coeff 0 : HahnField k Γ) +
          ((F.coeff m : HahnField k Γ) *
              (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ m + rest) := by
    dsimp [rest]
    exact eval_map_algebraMap_singleOfNonneg_eq_const_add_main_add_nonmain
      k Γ F c (le_of_lt hδpos) hm_pos (le_natDegree_of_unit_coeff k Γ hunit)
  rw [heval, ← add_assoc]
  exact addVal_add_gt_of_forall_gt k Γ hmain hrest

/-- A unit in the valuation subring has nonzero residue.
@isnad1 id=ne.1h3v.s11.573b243206b9 from=translated src=- shape=270cdf2c vocab=30b17718
-/
theorem constantCoeffRingHom_ne_zero_of_isUnit {x : valuationSubring k Γ} (hx : IsUnit x) :
    constantCoeffRingHom k Γ x ≠ 0 := by
  intro hzero
  have hmem : x ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
    rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k) (Γ := Γ), RingHom.mem_ker]
    exact hzero
  exact (IsLocalRing.notMem_maximalIdeal.mpr hx) hmem

/-- A coefficient whose residue is zero lies in the maximal ideal.
@isnad1 id=mem.1h4v.s12.c230e66a86f7 from=translated src=- shape=bc03ce39 vocab=3e3ee731
-/
theorem coeff_mem_maximalIdeal_of_map_constantCoeff_coeff_eq_zero
    {g : (valuationSubring k Γ)[X]} {n : ℕ}
    (h : (g.map (constantCoeffRingHom k Γ)).coeff n = 0) :
    g.coeff n ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k) (Γ := Γ), RingHom.mem_ker]
  simpa [Polynomial.coeff_map] using h

/-- A coefficient with nonzero residue is a unit.
@isnad1 id=isunit.1h4v.s11.79394ba4952a from=translated src=- shape=87883dee vocab=dad58716
-/
theorem isUnit_coeff_of_map_constantCoeff_coeff_ne_zero
    {g : (valuationSubring k Γ)[X]} {n : ℕ}
    (h : (g.map (constantCoeffRingHom k Γ)).coeff n ≠ 0) :
    IsUnit (g.coeff n) := by
  apply isUnit_of_constantCoeffRingHom_ne_zero k Γ
  simpa [Polynomial.coeff_map] using h

/-- A unit coefficient remains nonzero in the residue polynomial.
@isnad1 id=ne.1h4v.s11.6ca265723c94 from=translated src=- shape=2a30414b vocab=dad58716
-/
theorem coeff_map_constantCoeff_ne_zero_of_unit_coeff {g : (valuationSubring k Γ)[X]}
    {n : ℕ} (hunit : IsUnit (g.coeff n)) :
    (g.map (constantCoeffRingHom k Γ)).coeff n ≠ 0 := by
  rw [Polynomial.coeff_map]
  exact constantCoeffRingHom_ne_zero_of_isUnit k Γ hunit

/-- Lower cluster coefficients vanish in the residue polynomial.
@isnad1 id=eq.2h5v.s12.0ef90c937119 from=translated src=- shape=cacbfcf7 vocab=0115ff46
-/
theorem coeff_map_constantCoeff_eq_zero_of_cluster_lt
    {F : (valuationSubring k Γ)[X]} {m i : ℕ}
    (hsmall : ∀ j, j < m → F.coeff j ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hi : i < m) :
    (F.map (constantCoeffRingHom k Γ)).coeff i = 0 := by
  rw [Polynomial.coeff_map]
  have hmem := hsmall i hi
  rwa [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k) (Γ := Γ), RingHom.mem_ker] at hmem

/-- The main cluster coefficient is nonzero in the residue polynomial.
@isnad1 id=ne.1h4v.s11.6ca265723c94 from=translated src=- shape=2a30414b vocab=dad58716
-/
theorem coeff_map_constantCoeff_ne_zero_of_cluster_unit
    {F : (valuationSubring k Γ)[X]} {m : ℕ}
    (hunit : IsUnit (F.coeff m)) :
    (F.map (constantCoeffRingHom k Γ)).coeff m ≠ 0 :=
  coeff_map_constantCoeff_ne_zero_of_unit_coeff k Γ hunit

/-- If the target is nonzero, the cluster main coefficient can cancel it with a nonzero odd-power
coefficient.
@isnad1 id=ex.3h5v.s12.a1fa94d3fe85 from=translated src=- shape=9d0267ef vocab=d5f810e6
-/
theorem exists_nonzero_cancel_cluster_main_residue_pow_of_odd
    [IsRealClosed k] {F : (valuationSubring k Γ)[X]} {m : ℕ}
    (hm : Odd m) (hunit : IsUnit (F.coeff m)) {b : k} (hb : b ≠ 0) :
    ∃ c : k, c ≠ 0 ∧ b + constantCoeffRingHom k Γ (F.coeff m) * c ^ m = 0 :=
  exists_nonzero_cancel_add_mul_pow_of_odd hm
    (constantCoeffRingHom_ne_zero_of_isUnit k Γ hunit) hb

/-- Given a nonzero maximal-ideal error, choose a Hahn monomial main correction together with the
exact valuation of the current error and a strict improvement after correction.
@isnad1 id=ex.5h5v.s13.b59ef0560270 from=translated src=- shape=dbf61bd0 vocab=9ff06485
-/
theorem exists_main_correction_improves_error_with_value
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {e : valuationSubring k Γ} {F : (valuationSubring k Γ)[X]} {m : ℕ}
    (hm_pos : 0 < m) (hm_odd : Odd m) (hunit : IsUnit (F.coeff m))
    (hemem : e ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hene : e ≠ 0) :
    ∃ γ : Γ, ∃ δ : Γ, ∃ c : k,
      ∃ hδpos : 0 < δ, 0 < γ ∧ c ≠ 0 ∧ m • δ = γ ∧
        addVal k Γ (e : HahnField k Γ) = (γ : WithTop Γ) ∧
          (γ : WithTop Γ) <
            addVal k Γ ((e : HahnField k Γ) + (F.coeff m : HahnField k Γ) *
              (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ m) := by
  rcases exists_pos_addVal_leading_coeff_of_mem_maximalIdeal k Γ hemem hene with
    ⟨γ, b, hγpos, hbne, heval, hecoeff⟩
  rcases exists_pos_nsmul_eq (Γ := Γ) hm_pos hγpos with ⟨δ, hδpos, hδ⟩
  rcases exists_nonzero_cancel_cluster_main_residue_pow_of_odd k Γ hm_odd hunit hbne with
    ⟨c, hcne, hcancel⟩
  refine ⟨γ, δ, c, hδpos, hγpos, hcne, hδ, heval, ?_⟩
  exact lt_addVal_error_add_cluster_main_summand_singleOfNonneg
    k Γ heval hecoeff hunit (le_of_lt hδpos) hcne hδ hcancel

/-- Translating a valuation-subring polynomial commutes with passing to the residue polynomial.
@isnad1 id=eq.0h4v.s14.0dd645eb24e5 from=translated src=- shape=c5e4a2af vocab=243a0c9e
-/
theorem map_constantCoeff_comp_X_add_C {g : (valuationSubring k Γ)[X]}
    (A : valuationSubring k Γ) :
    ((g.comp (Polynomial.X + Polynomial.C A)).map (constantCoeffRingHom k Γ)) =
      (g.map (constantCoeffRingHom k Γ)).comp
        (Polynomial.X + Polynomial.C (constantCoeffRingHom k Γ A)) := by
  rw [Polynomial.map_comp]
  simp

/-- Coefficient form of `map_constantCoeff_comp_X_add_C`.
@isnad1 id=eq.0h5v.s14.fdc9a7658eb6 from=translated src=- shape=ce81cef7 vocab=aacb0fa7
-/
theorem coeff_map_constantCoeff_comp_X_add_C {g : (valuationSubring k Γ)[X]}
    (A : valuationSubring k Γ) (n : ℕ) :
    ((g.comp (Polynomial.X + Polynomial.C A)).map (constantCoeffRingHom k Γ)).coeff n =
      ((g.map (constantCoeffRingHom k Γ)).comp
        (Polynomial.X + Polynomial.C (constantCoeffRingHom k Γ A))).coeff n := by
  rw [map_constantCoeff_comp_X_add_C]

/-- A root of the translated polynomial `g(X + A)` gives a root of `g`.
@isnad1 id=isroot.1h5v.s14.cb10a0e7720e from=translated src=- shape=8b09adec vocab=430aec2f
-/
theorem isRoot_add_of_isRoot_comp_X_add_C
    {g : (valuationSubring k Γ)[X]} {A y : valuationSubring k Γ}
    (hroot : (g.comp (Polynomial.X + Polynomial.C A)).IsRoot y) :
    g.IsRoot (y + A) := by
  rw [Polynomial.IsRoot] at hroot ⊢
  simpa [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    using hroot

/-- Evaluating the translated polynomial `g(X + A)` at `y` is evaluating `g` at `y + A`.
@isnad1 id=eq.0h5v.s14.c4e6c6db2d5f from=translated src=- shape=35049067 vocab=316c35c5
-/
theorem eval_comp_X_add_C
    (g : (valuationSubring k Γ)[X]) (A y : valuationSubring k Γ) :
    (g.comp (Polynomial.X + Polynomial.C A)).eval y = g.eval (y + A) := by
  simp [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- Lift a Hahn-field polynomial with nonnegative coefficient valuations to the natural
valuation subring, coefficient by coefficient.-/
noncomputable def polynomialIntegralLift (S : Polynomial (HahnField k Γ))
    (hS : ∀ i, (0 : WithTop Γ) ≤ addVal k Γ (S.coeff i)) :
    Polynomial (valuationSubring k Γ) :=
  S.support.sum fun i => Polynomial.monomial i ⟨S.coeff i, hS i⟩

/-- A Newton-scaled root transports back while preserving an arbitrary property stable under
translation by the residue term and multiplication by the Newton monomial.
@isnad1 id=ex.1h9v.s11.d83f5c50b6e5 from=translated src=- shape=75aba499 vocab=83877460
-/
theorem exists_root_of_scalePolynomial_comp_single_zero_with_property
    (G : Polynomial (HahnField k Γ)) {δ μ : Γ} (a : k)
    (P : HahnField k Γ → Prop)
    (hP_add : ∀ y, P y → P (y + toLex (HahnSeries.single 0 a)))
    (hP_mul : ∀ y, P y → P (hahnMonomial k Γ δ * y))
    (hroot : ∃ y : HahnField k Γ,
      (0 : WithTop Γ) < addVal k Γ y ∧
        P y ∧
          ((scalePolynomial k Γ G δ μ).comp
            (Polynomial.X + Polynomial.C (toLex (HahnSeries.single 0 a)))).IsRoot y) :
    ∃ z : HahnField k Γ,
      (δ : WithTop Γ) ≤ addVal k Γ z ∧ P z ∧ G.IsRoot z := by
  rcases hroot with ⟨y, hypos, hyP, hyroot⟩
  let aH : HahnField k Γ := toLex (HahnSeries.single 0 a)
  let yA : HahnField k Γ := y + aH
  have ha_nonneg : (0 : WithTop Γ) ≤ addVal k Γ aH := by
    by_cases ha : a = 0
    · simp [aH, ha]
    · rw [show aH = toLex (HahnSeries.single (0 : Γ) a) by rfl,
        addVal_single_of_ne (k := k) (Γ := Γ) ha]
      exact le_rfl
  have hyA_nonneg : (0 : WithTop Γ) ≤ addVal k Γ yA :=
    le_addVal_add_of_le_addVal k Γ (le_of_lt hypos) ha_nonneg
  have hyAroot : (scalePolynomial k Γ G δ μ).IsRoot yA := by
    rw [Polynomial.IsRoot] at hyroot ⊢
    simpa [yA, aH, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C] using hyroot
  let z : HahnField k Γ := hahnMonomial k Γ δ * yA
  have hzlower : (δ : WithTop Γ) ≤ addVal k Γ z := by
    rw [show z = hahnMonomial k Γ δ * yA by rfl, AddValuation.map_mul,
      addVal_hahnMonomial]
    exact le_add_of_nonneg_right hyA_nonneg
  have hzP : P z := by
    exact hP_mul yA (by simpa [yA, aH] using hP_add y hyP)
  exact ⟨z, hzlower, hzP, isRoot_of_scalePolynomial_isRoot k Γ hyAroot⟩

/-- Translating a cluster by a maximal-ideal element preserves the lower coefficient condition.
@isnad1 id=mem.3h6v.s14.a7523a9307b0 from=translated src=- shape=61d01c81 vocab=c303f5d2
-/
theorem coeff_comp_X_add_C_mem_maximalIdeal_of_cluster_of_mem_maximalIdeal
    {F : (valuationSubring k Γ)[X]} {m i : ℕ} {y : valuationSubring k Γ}
    (hsmall : ∀ j, j < m → F.coeff j ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hi : i < m) :
    (F.comp (Polynomial.X + Polynomial.C y)).coeff i ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  apply coeff_mem_maximalIdeal_of_map_constantCoeff_coeff_eq_zero k Γ
  rw [coeff_map_constantCoeff_comp_X_add_C]
  have hy0 : constantCoeffRingHom k Γ y = 0 := by
    rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k) (Γ := Γ)] at hy
    exact RingHom.mem_ker.mp hy
  simpa [hy0] using coeff_map_constantCoeff_eq_zero_of_cluster_lt k Γ hsmall hi

/-- Translating a cluster by a maximal-ideal element preserves the unit main coefficient.
@isnad1 id=isunit.2h5v.s14.9a74493b5992 from=translated src=- shape=7fd63979 vocab=6ea7e1bb
-/
theorem isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {y : valuationSubring k Γ}
    (hunit : IsUnit (F.coeff m))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    IsUnit ((F.comp (Polynomial.X + Polynomial.C y)).coeff m) := by
  apply isUnit_coeff_of_map_constantCoeff_coeff_ne_zero k Γ
  rw [coeff_map_constantCoeff_comp_X_add_C]
  have hy0 : constantCoeffRingHom k Γ y = 0 := by
    rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k) (Γ := Γ)] at hy
    exact RingHom.mem_ker.mp hy
  simpa [hy0] using coeff_map_constantCoeff_ne_zero_of_cluster_unit k Γ hunit

/-- Translating a cluster by a maximal-ideal element preserves the cluster coefficient
conditions.
@isnad1 id=and.3h5v.s15.d1ab4fb80ed0 from=translated src=- shape=e348f386 vocab=1a5a00e1
-/
theorem cluster_coeffs_comp_X_add_C_of_mem_maximalIdeal
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {y : valuationSubring k Γ}
    (hsmall : ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff m))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    (∀ i, i < m → (F.comp (Polynomial.X + Polynomial.C y)).coeff i ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ)) ∧
      IsUnit ((F.comp (Polynomial.X + Polynomial.C y)).coeff m) := by
  constructor
  · intro i hi
    exact coeff_comp_X_add_C_mem_maximalIdeal_of_cluster_of_mem_maximalIdeal
      k Γ hsmall hy hi
  · exact isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal k Γ hunit hy

/-- At a non-root maximal-ideal approximation, choose the main cluster correction together with
the exact current evaluation valuation and the resulting strict main-term improvement.
@isnad1 id=ex.6h5v.s14.591ca44289e1 from=translated src=- shape=8b3a36a2 vocab=bf690ada
-/
theorem exists_main_correction_improves_eval_at_of_cluster_with_value
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {y : valuationSubring k Γ}
    (hm_pos : 0 < m) (hm_odd : Odd m)
    (hsmall : ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff m))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hne : F.eval y ≠ 0) :
    ∃ γ : Γ, ∃ δ : Γ, ∃ c : k,
      ∃ hδpos : 0 < δ, 0 < γ ∧ c ≠ 0 ∧ m • δ = γ ∧
        addVal k Γ ((F.eval y : valuationSubring k Γ) : HahnField k Γ) =
          (γ : WithTop Γ) ∧
          (γ : WithTop Γ) <
            addVal k Γ (((F.eval y : valuationSubring k Γ) : HahnField k Γ) +
              ((F.comp (Polynomial.X + Polynomial.C y)).coeff m : HahnField k Γ) *
                (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ m) := by
  have hunit' : IsUnit ((F.comp (Polynomial.X + Polynomial.C y)).coeff m) :=
    isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal k Γ hunit hy
  have hemem : F.eval y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
    eval_mem_maximalIdeal_of_cluster_pos k Γ hsmall hm_pos hy
  exact exists_main_correction_improves_error_with_value
    k Γ (F := F.comp (Polynomial.X + Polynomial.C y)) (e := F.eval y)
    hm_pos hm_odd hunit' hemem hne

/-- Version of the one-step estimate around a maximal-ideal approximation `y`, expressed back in
the original polynomial. The hypotheses on lower coefficients are for the translated polynomial
`F(X + y)`.
@isnad1 id=lt.7h8v.s15.53b25f39a45c from=translated src=- shape=579395e4 vocab=6a03884e
-/
theorem lt_addVal_eval_add_singleOfNonneg_of_translated_const_main_improves
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {y : valuationSubring k Γ}
    {δ γ : Γ} {c : k}
    (hm_pos : 0 < m)
    (hunit : IsUnit ((F.comp (Polynomial.X + Polynomial.C y)).coeff m))
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ)
    (hlower : ∀ j, 0 < j → j < m → (((m - j) • δ : Γ) : WithTop Γ) <
      addVal k Γ ((F.comp (Polynomial.X + Polynomial.C y)).coeff j : HahnField k Γ))
    (hmain : (γ : WithTop Γ) <
      addVal k Γ (((F.eval y : valuationSubring k Γ) : HahnField k Γ) +
        ((F.comp (Polynomial.X + Polynomial.C y)).coeff m : HahnField k Γ) *
          (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ m)) :
    (γ : WithTop Γ) <
      addVal k Γ (((F.eval (singleOfNonneg k Γ δ c (le_of_lt hδpos) + y) :
        valuationSubring k Γ) : HahnField k Γ)) := by
  let G : (valuationSubring k Γ)[X] := F.comp (Polynomial.X + Polynomial.C y)
  let t : valuationSubring k Γ := singleOfNonneg k Γ δ c (le_of_lt hδpos)
  have hcoeff0 : G.coeff 0 = F.eval y := by
    dsimp [G]
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_comp_X_add_C]
    simp
  have hcoeff0' : (F.comp (Polynomial.X + Polynomial.C y)).coeff 0 = F.eval y := by
    simpa [G] using hcoeff0
  have hmain' : (γ : WithTop Γ) <
      addVal k Γ ((G.coeff 0 : HahnField k Γ) + (G.coeff m : HahnField k Γ) *
        (t : HahnField k Γ) ^ m) := by
    dsimp [G, t]
    simpa [hcoeff0'] using hmain
  have hG : (γ : WithTop Γ) <
      addVal k Γ ((G.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (t : HahnField k Γ)) := by
    exact lt_addVal_eval_map_singleOfNonneg_of_const_main_improves
      k Γ (F := G) (m := m) (δ := δ) (γ := γ) (c := c)
      hm_pos hunit hδpos hc hδ (by
        intro j hjpos hjm
        dsimp [G] at hlower ⊢
        exact hlower j hjpos hjm) hmain'
  have hmap :
      (G.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          (t : HahnField k Γ) =
        ((G.eval t : valuationSubring k Γ) : HahnField k Γ) :=
    eval_map_algebraMap_eq_coe_eval k Γ G t
  have htranslate : G.eval t = F.eval (t + y) := by
    dsimp [G, t]
    exact eval_comp_X_add_C k Γ F y (singleOfNonneg k Γ δ c (le_of_lt hδpos))
  rw [hmap, htranslate] at hG
  simpa [t] using hG

/-- In the simple-cluster case, choose a one-term correction together with the exact current
evaluation valuation and the resulting strict improvement.
@isnad1 id=ex.4h4v.s14.c79474cc0316 from=translated src=- shape=3e8821e2 vocab=8122156b
-/
theorem exists_correction_improves_eval_at_of_one_cluster_with_value
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : (valuationSubring k Γ)[X]} {y : valuationSubring k Γ}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hne : F.eval y ≠ 0) :
    ∃ γ : Γ, ∃ δ : Γ, ∃ c : k,
      ∃ hδpos : 0 < δ, 0 < γ ∧ c ≠ 0 ∧ δ = γ ∧
        addVal k Γ ((F.eval y : valuationSubring k Γ) : HahnField k Γ) =
          (γ : WithTop Γ) ∧
          (γ : WithTop Γ) <
            addVal k Γ (((F.eval (singleOfNonneg k Γ δ c (le_of_lt hδpos) + y) :
              valuationSubring k Γ) : HahnField k Γ)) := by
  rcases exists_main_correction_improves_eval_at_of_cluster_with_value
    (k := k) (Γ := Γ) (F := F) (m := 1) (y := y)
    (by norm_num) (by norm_num) hsmall hunit hy hne with
    ⟨γ, δ, c, hδpos, hγpos, hcne, hδ, hval, hmain⟩
  have hunit' : IsUnit ((F.comp (Polynomial.X + Polynomial.C y)).coeff 1) :=
    isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal k Γ hunit hy
  have himprove : (γ : WithTop Γ) <
      addVal k Γ (((F.eval (singleOfNonneg k Γ δ c (le_of_lt hδpos) + y) :
        valuationSubring k Γ) : HahnField k Γ)) := by
    exact lt_addVal_eval_add_singleOfNonneg_of_translated_const_main_improves
      (k := k) (Γ := Γ) (F := F) (m := 1) (y := y)
      (by norm_num) hunit' hδpos hcne hδ (by
        intro j hjpos hjlt
        omega) hmain
  refine ⟨γ, δ, c, hδpos, hγpos, hcne, ?_, hval, himprove⟩
  simpa using hδ

/-- A non-root simple-cluster approximation has a corrected maximal-ideal approximation together
with the current evaluation value and the valuation of the correction step.
@isnad1 id=ex.4h4v.s14.41de19ea10a2 from=translated src=- shape=adef98c9 vocab=c76b21e0
-/
theorem exists_next_approx_improves_eval_at_of_one_cluster_with_values
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : (valuationSubring k Γ)[X]} {y : valuationSubring k Γ}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hne : F.eval y ≠ 0) :
    ∃ y' : valuationSubring k Γ,
      y' ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧
        ∃ γ : Γ, ∃ δ : Γ, ∃ c : k,
          ∃ hδpos : 0 < δ, 0 < γ ∧ c ≠ 0 ∧ δ = γ ∧
            y' = singleOfNonneg k Γ δ c (le_of_lt hδpos) + y ∧
              addVal k Γ ((F.eval y : valuationSubring k Γ) : HahnField k Γ) =
                (γ : WithTop Γ) ∧
                addVal k Γ ((y' - y : valuationSubring k Γ) : HahnField k Γ) =
                  (δ : WithTop Γ) ∧
                  (γ : WithTop Γ) <
                    addVal k Γ (((F.eval y' : valuationSubring k Γ) : HahnField k Γ)) := by
  rcases exists_correction_improves_eval_at_of_one_cluster_with_value
    k Γ hsmall hunit hy hne with
    ⟨γ, δ, c, hδpos, hγpos, hcne, hδ, hval, himprove⟩
  let y' : valuationSubring k Γ := singleOfNonneg k Γ δ c (le_of_lt hδpos) + y
  have hy' : y' ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
    dsimp [y']
    simpa [add_comm] using add_singleOfNonneg_mem_maximalIdeal_of_mem_of_pos
      k Γ hy hδpos hcne
  have hstep : addVal k Γ ((y' - y : valuationSubring k Γ) : HahnField k Γ) =
      (δ : WithTop Γ) := by
    have hsub : (y' - y : valuationSubring k Γ) =
        singleOfNonneg k Γ δ c (le_of_lt hδpos) := by
      dsimp [y']
      abel
    rw [hsub]
    exact addVal_singleOfNonneg_of_ne k Γ (le_of_lt hδpos) hcne
  refine ⟨y', hy', γ, δ, c, hδpos, hγpos, hcne, hδ, rfl, hval, hstep, ?_⟩
  simpa [y'] using himprove

end HahnField

end

end HahnKaplanskyRealClosedness
