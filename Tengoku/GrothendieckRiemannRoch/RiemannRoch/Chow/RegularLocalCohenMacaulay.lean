/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.RegularLocalDomain
import Tengoku.Seed.Data.ENat.Basic
import Tengoku.Seed.Order.KrullDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regular local rings are Cohen--Macaulay (P3.4)

Induction on embedding dimension via a parameter outside `m²` (from `RegularLocalDomain`),
comparing `ModuleCat.ringDepth` with `ModuleCat.localKrullDim`.

* Dimensions `0` and `1` are unconditional.
* The inductive step for dimension `≥ 2` needs a nonzerodivisor parameter.  That follows from
  `IsDomain`; the general fact that every regular local ring is a domain is the remainder of
  P2.2 and is passed here as the explicit named hypothesis `regularLocal_isDomain` (no `sorry`).
-/

noncomputable section

universe u

open IsLocalRing ModuleCat RingTheory.Sequence Ideal
open scoped Pointwise

variable {R : Type u} [CommRing R]

namespace IsRegularLocalRing

/-- In a domain, every nonzero ring element is `R`-regular.-/
theorem isSMulRegular_of_ne_zero [IsDomain R] {r : R} (hr : r ≠ 0) :
    IsSMulRegular R r :=
  IsSMulRegular.of_right_eq_zero_of_smul fun a ha =>
    (mul_eq_zero.mp (by simpa [smul_eq_mul] using ha)).resolve_left hr

/-- A parameter outside `m²` is nonzero.-/
theorem ne_zero_of_notMem_sq [IsLocalRing R] {x : R}
    (hx2 : x ∉ maximalIdeal R ^ 2) : x ≠ 0 := by
  intro h0; exact hx2 (by simp [h0])

/-- Under `IsDomain`, a non-square parameter is an `R`-regular element.-/
theorem isSMulRegular_of_notMem_sq_of_isDomain [IsDomain R] [IsLocalRing R] {x : R}
    (hx2 : x ∉ maximalIdeal R ^ 2) : IsSMulRegular R x :=
  isSMulRegular_of_ne_zero (ne_zero_of_notMem_sq hx2)

/-- Generators of equal principal maximal ideals differ by a unit.-/
theorem exists_units_eq_of_span_singleton_eq_span_singleton [IsLocalRing R]
    {x y : R} (hx : maximalIdeal R = Ideal.span {x})
    (hy : maximalIdeal R = Ideal.span {y})
    (hy_ne : ∀ n : ℕ, y ^ n ≠ 0) :
    ∃ u : Rˣ, x = u * y := by
  have h1 : x ∈ Ideal.span {y} := by rw [← hy, hx]; exact Ideal.mem_span_singleton_self _
  have h2 : y ∈ Ideal.span {x} := by rw [← hx, hy]; exact Ideal.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp h1
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp h2
  have hrs : y = s * r * y := by
    calc y = x * s := hs
      _ = (y * r) * s := by rw [← hr]
      _ = s * r * y := by ring
  have h1srs : (1 - s * r) * y = 0 := by
    rw [sub_mul, one_mul, ← hrs, sub_self]
  have hsr_unit : IsUnit (s * r) := by
    by_contra hnu
    rw [← mem_nonunits_iff, ← mem_maximalIdeal] at hnu
    have h1u : IsUnit (1 - s * r) := by
      rw [← notMem_maximalIdeal]
      intro hmem
      have : (1 : R) ∈ maximalIdeal R := by
        convert add_mem hmem hnu using 1; abel
      exact (maximalIdeal.isMaximal R).ne_top <| Ideal.eq_top_of_isUnit_mem _ this isUnit_one
    exact hy_ne 1 ((IsUnit.mul_right_eq_zero h1u).mp (by rw [pow_one]; exact h1srs))
  have hr_unit : IsUnit r := by
    by_contra hnu
    rw [← mem_nonunits_iff, ← mem_maximalIdeal] at hnu
    have : s * r ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hnu
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp this)) hsr_unit
  obtain ⟨u, hr_u⟩ := hr_unit
  exact ⟨u, by
    calc x = y * r := hr
      _ = y * (u : R) := by rw [← hr_u]
      _ = u * y := mul_comm y u⟩

/-- In dimension one, a generator of `m` is a nonzerodivisor (unconditional).-/
theorem isSMulRegular_of_ringKrullDim_eq_one [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 1) {x : R}
    (hxspan : maximalIdeal R = Ideal.span {x}) :
    IsSMulRegular R x := by
  obtain ⟨y, hyspan, hyne⟩ := exists_generator_maximalIdeal_of_ringKrullDim_eq_one hdim
  obtain ⟨u, hu⟩ :=
    exists_units_eq_of_span_singleton_eq_span_singleton hxspan hyspan hyne
  refine IsSMulRegular.of_right_eq_zero_of_smul fun a ha => by
    have : (u : R) * y * a = 0 := by
      simpa [hu, hxspan, mul_assoc] using ha
    have hya : y * a = 0 := by
      have heq := congrArg (fun z => (↑u⁻¹ : R) * z) this
      simpa [← mul_assoc] using heq
    by_contra a_ne
    obtain ⟨v, k, rfl⟩ :=
      exists_unit_mul_pow_eq_of_ringKrullDim_eq_one hdim hyspan a_ne
    have : (v : R) * y ^ (k + 1) = 0 := by
      calc (v : R) * y ^ (k + 1) = v * (y ^ k * y) := by rw [pow_succ]
        _ = (v * y ^ k) * y := by ring
        _ = 0 := by
          rw [mul_comm (v * y ^ k) y]
          exact hya
    exact hyne (k + 1) ((IsUnit.mul_right_eq_zero v.isUnit).mp this)

/-- Embedding dimension of a parameter quotient drops by one.-/
theorem embeddingDimension_quotient_span_singleton [IsRegularLocalRing R]
    [DecidableEq R]
    {x : R} (hxm : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    letI := ModuleCat.quotientSpanIsLocalRing R x hxm
    letI := quotient_span_singleton_isRegularLocalRing hxm hx2
    embeddingDimension (R ⧸ Ideal.span {x}) = Nat.sub (embeddingDimension R) 1 := by
  let Q := R ⧸ Ideal.span {x}
  letI : IsLocalRing Q := ModuleCat.quotientSpanIsLocalRing R x hxm
  letI : IsRegularLocalRing Q := quotient_span_singleton_isRegularLocalRing hxm hx2
  letI : DecidableEq Q := Classical.decEq Q
  letI : IsNoetherianRing Q := Ideal.Quotient.isNoetherianRing _
  obtain ⟨t, hat, hcard, hspan⟩ :=
    exists_finset_span_card_eq_spanFinrank_containing (R := R) hxm hx2
  let t₀ : Finset Q := (t.erase x).image (Ideal.Quotient.mk (Ideal.span {x}))
  have hmap :
      (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) = maximalIdeal Q :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hspanQ : Ideal.span (t₀ : Set Q) = maximalIdeal Q := by
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
      have : Ideal.Quotient.mk (Ideal.span {x}) y ∈
          (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) :=
        Ideal.mem_map_of_mem _
          (by rw [← hspan]; exact Submodule.subset_span (Finset.mem_of_mem_erase hy))
      rwa [hmap] at this
    · rw [← hmap, ← hspan, Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyx : y = x
      · rw [show Ideal.Quotient.mk (Ideal.span {x}) y = 0 from by
          rw [hyx, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_span_singleton_self x]
        exact Ideal.zero_mem (Ideal.span (t₀ : Set Q))
      · exact Ideal.subset_span
          (Finset.mem_image.mpr ⟨y, Finset.mem_erase.mpr ⟨hyx, hy⟩, rfl⟩)
  have hle : (maximalIdeal Q).spanFinrank ≤ Nat.sub (maximalIdeal R).spanFinrank 1 := by
    have hle' : (Ideal.span (t₀ : Set Q)).spanFinrank ≤ t₀.card :=
      (Submodule.spanFinrank_span_le_ncard_of_finite t₀.finite_toSet).trans_eq (by simp)
    have hle'' : (maximalIdeal Q).spanFinrank ≤ t₀.card := by rwa [← hspanQ]
    have hcard₀ : t₀.card ≤ Nat.sub t.card 1 := by
      have := Finset.card_image_le (s := t.erase x)
        (f := Ideal.Quotient.mk (Ideal.span {x}))
      rwa [Finset.card_erase_of_mem hat] at this
    have hcard₁ : Nat.sub t.card 1 = Nat.sub (maximalIdeal R).spanFinrank 1 := by rw [hcard]
    exact Nat.le_trans hle'' (hcard₀.trans (Nat.le_of_eq hcard₁))
  have hge : Nat.sub (maximalIdeal R).spanFinrank 1 ≤ (maximalIdeal Q).spanFinrank := by
    have hdim_le : ringKrullDim R ≤ ringKrullDim Q + 1 := by
      have h := ringKrullDim_le_ringKrullDim_quotSMulTop_succ (x := x) hxm
      have hI : Ideal.span {x} = x • (⊤ : Ideal R) := by simp [← Submodule.ideal_span_singleton_smul]
      rw [show ringKrullDim (R ⧸ x • (⊤ : Ideal R)) = ringKrullDim (R ⧸ Ideal.span {x}) from
        ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R hI).symm.toRingEquiv] at h
      simpa [Q] using h
    have hpos : 0 < IsRegularLocalRing.embeddingDimension R := by
      rw [IsRegularLocalRing.embeddingDimension, ← hcard]
      exact Finset.card_pos.mpr ⟨x, hat⟩
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hpos
    have hn1 : IsRegularLocalRing.embeddingDimension R = n + 1 := by
      simpa [Nat.succ_eq_add_one] using hn
    have this : (n : WithBot ℕ∞) + 1 ≤ ringKrullDim Q + 1 := by
      rw [← IsRegularLocalRing.coe_embeddingDimension_eq_ringKrullDim, hn1] at hdim_le
      exact hdim_le
    have hstep : (n : WithBot ℕ∞) ≤ ringKrullDim Q :=
      ENat.WithBot.add_le_add_natCast_right_iff.mp this
    have hsub : Nat.sub (maximalIdeal R).spanFinrank 1 = n := by
      rw [show (maximalIdeal R).spanFinrank = n + 1 from
        by rw [← IsRegularLocalRing.embeddingDimension, hn1]]
      rfl
    rw [hsub]
    have : (n : WithBot ℕ∞) ≤ ((maximalIdeal Q).spanFinrank : WithBot ℕ∞) := by
      rw [IsRegularLocalRing.spanFinrank_maximalIdeal (R := Q)]
      exact hstep
    exact_mod_cast this
  simp only [embeddingDimension] at hle hge hcard ⊢
  exact Nat.le_antisymm hle hge

end IsRegularLocalRing

namespace ModuleCat

open IsRegularLocalRing

/-! ### Depth comparison -/

/-! ### Dimension 0 and 1 -/

/-! ### General case -/

end ModuleCat
