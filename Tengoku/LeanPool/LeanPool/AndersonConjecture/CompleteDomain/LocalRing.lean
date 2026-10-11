/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.AndersonConjecture.CompleteDomain.Domain

/-!
# The Complete Domain T -- Local Ring Properties

T = C[[x,y,z]]/(x^2 - yz) is a Noetherian complete local domain
whose residue field has the cardinality of C.
-/

@[expose] public section

noncomputable section

-- T is local since it's a quotient of a local ring by a proper ideal
instance T_isLocalRing : IsLocalRing T := by
  have : Nontrivial T := Ideal.Quotient.nontrivial_iff.mpr conjI_ne_top
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk conjI) Ideal.Quotient.mk_surjective

lemma Finsupp.cons_add' {n : ℕ} {a b : ℕ} {s t : Fin n →₀ ℕ} :
    Finsupp.cons (a + b) (s + t) = Finsupp.cons a s + Finsupp.cons b t := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Finsupp.cons_zero]
  · simp [Finsupp.cons_succ]

lemma Finsupp.tail_add' {n : ℕ} (s t : Fin (n + 1) →₀ ℕ) :
    Finsupp.tail (s + t) = Finsupp.tail s + Finsupp.tail t := by
  ext i
  simp [Finsupp.tail_apply, Finsupp.add_apply]

lemma Finsupp.add_cons_zero {n : ℕ} (s t : Fin (n + 1) →₀ ℕ) :
    (s + t) 0 = s 0 + t 0 := by simp [Finsupp.add_apply]

/-- The ring equivalence `MvPowerSeries (Fin 0) R ≃+* R` given by taking the
constant coefficient (its inverse is the constant-series embedding). -/
noncomputable def mvPowerSeriesFin0RingEquiv (R : Type*) [CommSemiring R] :
    MvPowerSeries (Fin 0) R ≃+* R where
  toFun := MvPowerSeries.constantCoeff
  invFun := MvPowerSeries.C
  left_inv f := by
    have huniq : ∀ (m : Fin 0 →₀ ℕ), m = 0 := fun m => by ext i
                                                          exact Fin.elim0 i
    ext m
    simp [huniq m, MvPowerSeries.coeff_C]
  right_inv r := MvPowerSeries.constantCoeff_C r
  map_mul' := map_mul _
  map_add' := map_add _

section MvPowerSeriesFinSuccEquiv

variable {n : ℕ} {R : Type*} [CommSemiring R]

lemma fin1_finsupp_eq {u : Fin 1 →₀ ℕ} : u = Finsupp.single 0 (u 0) := by
  refine Finsupp.ext_iff.mpr (fun i => ?_)
  have : i = (0 : Fin 1) := Subsingleton.elim i 0
  subst this
  simp [Finsupp.single_eq_same]

end MvPowerSeriesFinSuccEquiv

section AdicComplete

open MvPowerSeries Finset Finsupp

/-- Local abbreviation for the maximal ideal of `ℂ[[x,y,z]] = MvPowerSeries (Fin 3) ℂ`. -/
abbrev MPS := IsLocalRing.maximalIdeal (MvPowerSeries (Fin 3) ℂ)

/-- Total degree of a monomial exponent vector `d : Fin 3 →₀ ℕ`. -/
abbrev tdeg (d : Fin 3 →₀ ℕ) : ℕ := d.sum fun _ k => k

lemma tdeg_add (a b : Fin 3 →₀ ℕ) :
    tdeg (a + b) = tdeg a + tdeg b := by
  simp [tdeg, Finsupp.sum_add_index']

lemma constantCoeff_eq_zero_of_mem_MPS
    {m : MvPowerSeries (Fin 3) ℂ}
    (hm : m ∈ MPS) :
    MvPowerSeries.constantCoeff (σ := Fin 3) (R := ℂ) m = 0 := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff] at hm
  by_contra h
  exact hm (IsUnit.mk0 _ h)

-- If f ∈ MPS^n then all coefficients at degree < n vanish

private lemma mvPowerSeries_eq_sum_X_mul {k : Type*} [CommRing k]
    (f : MvPowerSeries (Fin 3) k) (hf : MvPowerSeries.constantCoeff f = 0) :
    f = X 0 * (show MvPowerSeries (Fin 3) k from fun m => coeff (m + single 0 1) f) +
      X 1 * (show MvPowerSeries (Fin 3) k from fun m =>
        if m 0 = 0 then coeff (m + single 1 1) f else 0) +
      X 2 * (show MvPowerSeries (Fin 3) k from fun m =>
        if m 0 = 0 ∧ m 1 = 0 then coeff (m + single 2 1) f else 0) := by
  let g₀ : MvPowerSeries (Fin 3) k := fun m => coeff (m + single 0 1) f
  let g₁ : MvPowerSeries (Fin 3) k := fun m =>
    if m 0 = 0 then coeff (m + single 1 1) f else 0
  let g₂ : MvPowerSeries (Fin 3) k := fun m =>
    if m 0 = 0 ∧ m 1 = 0 then coeff (m + single 2 1) f else 0
  change f = X 0 * g₀ + X 1 * g₁ + X 2 * g₂
  ext m
  have step (s : Fin 3) (g : MvPowerSeries (Fin 3) k) :
      coeff m (X s * g) = if single s 1 ≤ m then g (m - single s 1) else 0 := by
    change coeff m (monomial (single s 1) 1 * g) = _
    rw [coeff_monomial_mul, one_mul, coeff_apply]
  simp only [map_add, coeff_apply, step]
  have tsub_val (s j : Fin 3) :
      (m - single s 1 : Fin 3 →₀ ℕ) j = m j - (single s 1 : Fin 3 →₀ ℕ) j :=
    Finsupp.tsub_apply _ _ _
  have h_g1_van (d : Fin 3 →₀ ℕ) (hd : d 0 ≠ 0) : g₁ d = 0 := ite_eq_right hd
  have h_g2_van_0 (d : Fin 3 →₀ ℕ) (hd : d 0 ≠ 0) : g₂ d = 0 :=
    ite_eq_right (not_and_of_not_left _ hd)
  have h_g2_van_1 (d : Fin 3 →₀ ℕ) (hd : d 1 ≠ 0) : g₂ d = 0 :=
    ite_eq_right (not_and_of_not_right _ hd)
  by_cases hm0 : single (0 : Fin 3) 1 ≤ m
  · rw [ite_eq_left hm0]
    set d₀ := m - single (0 : Fin 3) 1
    have hd₀_add : d₀ + single 0 1 = m := tsub_add_cancel_of_le hm0
    have hm0v := single_le_iff.mp hm0
    change f m = coeff (d₀ + single 0 1) f + _ + _
    rw [hd₀_add, coeff_apply]
    have h0_ne (s : Fin 3) (hs : s ≠ 0) :
        (m - single s 1 : Fin 3 →₀ ℕ) 0 ≠ 0 := by
      rw [tsub_val s 0, single_apply, ite_eq_right hs]
      simpa only [tsub_zero] using Nat.ne_of_gt hm0v
    have t1 : g₁ (m - single (1 : Fin 3) 1) = 0 := h_g1_van _ (h0_ne 1 (by decide))
    have t2 : g₂ (m - single (2 : Fin 3) 1) = 0 := h_g2_van_0 _ (h0_ne 2 (by decide))
    simp only [t1, t2, ite_self, add_zero]
  · rw [ite_eq_right hm0, zero_add]
    have hm0v : m 0 = 0 := by simp [single_le_iff] at hm0
                              omega
    by_cases hm1 : single (1 : Fin 3) 1 ≤ m
    · rw [ite_eq_left hm1]
      set d₁ := m - single (1 : Fin 3) 1
      have hd₁_add : d₁ + single 1 1 = m := tsub_add_cancel_of_le hm1
      have hm1v := single_le_iff.mp hm1
      have hd₁_0 : d₁ 0 = 0 := by
        change (m - single (1 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 = 0
        rw [tsub_val 1 0, single_apply]
        simpa only [Fin.isValue, one_ne_zero, ↓reduceIte, tsub_zero] using hm0v
      change f m = (if d₁ 0 = 0 then coeff (d₁ + single 1 1) f else 0) + _
      rw [ite_eq_left hd₁_0, hd₁_add, coeff_apply]
      have h1_ne : (m - single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 1 ≠ 0 := by
        rw [tsub_val 2 1, single_apply, ite_eq_right (by decide : (2 : Fin 3) ≠ 1)]
        simpa only [tsub_zero] using Nat.ne_of_gt hm1v
      simp only [h_g2_van_1 _ h1_ne, ite_self, add_zero]
    · rw [ite_eq_right hm1, zero_add]
      have hm1v : m 1 = 0 := by simp [single_le_iff] at hm1
                                omega
      by_cases hm2 : single (2 : Fin 3) 1 ≤ m
      · rw [ite_eq_left hm2]
        set d₂ := m - single (2 : Fin 3) 1
        have hd₂_add : d₂ + single 2 1 = m := tsub_add_cancel_of_le hm2
        have hd₂_0 : d₂ 0 = 0 := by
          change (m - single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 = 0
          rw [tsub_val 2 0, single_apply]
          simpa only [Fin.isValue, Fin.reduceEq, ↓reduceIte, tsub_zero] using hm0v
        have hd₂_1 : d₂ 1 = 0 := by
          change (m - single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 1 = 0
          rw [tsub_val 2 1, single_apply]
          simpa only [Fin.isValue, Fin.reduceEq, ↓reduceIte, tsub_zero] using hm1v
        change f m = if d₂ 0 = 0 ∧ d₂ 1 = 0 then coeff (d₂ + single 2 1) f else 0
        rw [ite_eq_left ⟨hd₂_0, hd₂_1⟩, hd₂_add, coeff_apply]
      · rw [ite_eq_right hm2]
        have hm2v : m 2 = 0 := by simp [single_le_iff] at hm2
                                  omega
        have : m = 0 := by ext i
                           fin_cases i <;> assumption
        subst this
        exact hf

-- Converse: vanishing coefficients at degree < n implies f ∈ MPS^n
lemma mem_MPS_pow_of_coeff_vanish
    (f : MvPowerSeries (Fin 3) ℂ) (n : ℕ)
    (hf : ∀ d : Fin 3 →₀ ℕ, tdeg d < n → coeff d f = 0) :
    f ∈ MPS ^ n := by
  induction n generalizing f with
  | zero => simp [pow_zero]
  | succ n ih =>
    -- Decompose f = X₀g₀ + X₁g₁ + X₂g₂ where g_i ∈ MPS^n by induction
    have hconst : MvPowerSeries.constantCoeff (σ := Fin 3) (R := ℂ) f = 0 :=
      hf 0 (by simp [tdeg, Finsupp.sum])
    let g₀ : MvPowerSeries (Fin 3) ℂ := fun m => coeff (m + single 0 1) f
    let g₁ : MvPowerSeries (Fin 3) ℂ := fun m =>
      if m 0 = 0 then coeff (m + single 1 1) f else 0
    let g₂ : MvPowerSeries (Fin 3) ℂ := fun m =>
      if m 0 = 0 ∧ m 1 = 0 then coeff (m + single 2 1) f else 0
    have hg₀ : g₀ ∈ MPS ^ n := ih _ fun d hd => by
      change coeff (d + single 0 1) f = 0
      exact hf _ (by
                    rw [tdeg_add]
                    simp [tdeg, Finsupp.sum_single_index]
                    omega)
    have hg₁ : g₁ ∈ MPS ^ n := ih _ fun d hd => by
      change (if d 0 = 0 then coeff (d + single 1 1) f else 0) = 0
      split
      · exact hf _ (by
                      rw [tdeg_add]
                      simp [tdeg, Finsupp.sum_single_index]
                      omega)
      · rfl
    have hg₂ : g₂ ∈ MPS ^ n := ih _ fun d hd => by
      change (if d 0 = 0 ∧ d 1 = 0 then coeff (d + single 2 1) f else 0) = 0
      split
      · exact hf _ (by
                      rw [tdeg_add]
                      simp [tdeg, Finsupp.sum_single_index]
                      omega)
      · rfl
    -- Decompose f = X₀g₀ + X₁g₁ + X₂g₂; each X_i*g_i ∈ MPS^(n+1)
    suffices hdecomp : f = X 0 * g₀ + X 1 * g₁ + X 2 * g₂ by
      rw [hdecomp]
      have hX : ∀ (i : Fin 3), X i ∈ MPS := fun i => by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff,
            constantCoeff_X]
        exact not_isUnit_zero
      have key : ∀ (i : Fin 3) (g : MvPowerSeries (Fin 3) ℂ), g ∈ MPS ^ n →
          X i * g ∈ MPS ^ (n + 1) := fun i g hg => by
        have := Ideal.mul_mem_mul (hX i) hg
        rwa [show MPS * MPS ^ n = MPS ^ (n + 1) from
          (Ideal.IsTwoSided.pow_succ (I := MPS) n).symm] at this
      exact Ideal.add_mem _
        (Ideal.add_mem _ (key 0 g₀ hg₀) (key 1 g₁ hg₁)) (key 2 g₂ hg₂)
    exact mvPowerSeries_eq_sum_X_mul f hconst

-- Precompleteness: coefficients stabilize, so define limit coefficientwise

end AdicComplete

open MvPowerSeries Finsupp in
lemma mvPS_mem_span_X_of_constantCoeff_zero {k : Type*} [CommRing k]
    (f : MvPowerSeries (Fin 3) k) (hf : MvPowerSeries.constantCoeff f = 0) :
    f ∈ Ideal.span ({(X 0 : MvPowerSeries (Fin 3) k), X 1, X 2} : Set _) := by
  let I := Ideal.span ({(X 0 : MvPowerSeries (Fin 3) k), X 1, X 2} : Set _)
  let g₀ : MvPowerSeries (Fin 3) k := fun m => coeff (m + single 0 1) f
  let g₁ : MvPowerSeries (Fin 3) k := fun m =>
    if m 0 = 0 then coeff (m + single 1 1) f else 0
  let g₂ : MvPowerSeries (Fin 3) k := fun m =>
    if m 0 = 0 ∧ m 1 = 0 then coeff (m + single 2 1) f else 0
  have hX0 : X 0 * g₀ ∈ I := I.mul_mem_right _ (Ideal.subset_span (by simp))
  have hX1 : X 1 * g₁ ∈ I := I.mul_mem_right _ (Ideal.subset_span (by simp))
  have hX2 : X 2 * g₂ ∈ I := I.mul_mem_right _ (Ideal.subset_span (by simp))
  suffices hkey : f = X 0 * g₀ + X 1 * g₁ + X 2 * g₂ by
    rw [hkey]
    exact I.add_mem (I.add_mem hX0 hX1) hX2
  exact mvPowerSeries_eq_sum_X_mul f hf

-- maximalIdeal = span{X₀, X₁, X₂}: ⊆ by decomposition, ⊇ since each X_i has zero constant term
open MvPowerSeries in
lemma mvPS_maximalIdeal_eq_span_X :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin 3) ℂ) =
    Ideal.span ({(X 0 : MvPowerSeries (Fin 3) ℂ), X 1, X 2} : Set _) := by
  apply le_antisymm
  · intro f hf
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at hf
    exact mvPS_mem_span_X_of_constantCoeff_zero f (by
                                                     by_contra h
                                                     exact hf (IsUnit.mk0 _ h))
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    rcases hx with rfl | rfl | rfl <;>
      simp [MvPowerSeries.constantCoeff_X]

-- dim ≤ 3 by Krull's height theorem: maxIdeal is 3-generated
open MvPowerSeries nonZeroDivisors in
lemma gen_mem_nonZeroDivisors :
    (X 0 : MvPowerSeries (Fin 3) ℂ) ^ 2 - X 1 * X 2 ∈ (MvPowerSeries (Fin 3) ℂ)⁰ :=
  mem_nonZeroDivisors_of_ne_zero anderson_gen_ne_zero

open MvPowerSeries in
lemma gen_mem_maximalIdeal :
    (X 0 : MvPowerSeries (Fin 3) ℂ) ^ 2 - X 1 * X 2 ∈
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin 3) ℂ) := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]
  simp [map_sub, map_pow, map_mul, constantCoeff_X]

-- Injectivity of ℂ → MvPowerSeries → T: gen has zero constant term
open MvPowerSeries in
lemma cToT_injective : Function.Injective
    ((Ideal.Quotient.mk conjI).comp (MvPowerSeries.C (σ := Fin 3) (R := ℂ))) := by
  intro a b hab
  simp only [RingHom.comp_apply] at hab
  have hmem : C (σ := Fin 3) a - C (σ := Fin 3) b ∈ conjI := Ideal.Quotient.eq.mp hab
  rw [← map_sub, conjI, Ideal.mem_span_singleton] at hmem
  obtain ⟨q, hq⟩ := hmem
  have h1 := congr_arg (constantCoeff (σ := Fin 3) (R := ℂ)) hq
  simp only [MvPowerSeries.constantCoeff_C, map_mul, map_sub, map_pow,
    constantCoeff_X, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, sub_zero, zero_mul] at h1
  exact sub_eq_zero.mp h1

-- |Fin 3 →₀ ℕ| = ℵ₀ and |ℂ| = continuum, so |(Fin 3 →₀ ℕ) → ℂ| = |ℂ|
lemma mvPS_card_eq : Cardinal.mk (MvPowerSeries (Fin 3) ℂ) = Cardinal.mk ℂ := by
  change Cardinal.mk ((Fin 3 →₀ ℕ) → ℂ) = Cardinal.mk ℂ
  rw [Cardinal.mk_arrow]
  simp only [Cardinal.lift_id]
  rw [Cardinal.mk_complex]
  rw [le_antisymm Cardinal.mk_le_aleph0 (Cardinal.aleph0_le_mk_iff.mpr (Infinite.of_injective
    (fun n => Finsupp.single (0 : Fin 3) n) (Finsupp.single_injective _)))]
  exact Cardinal.continuum_power_aleph0

/-- |T| = |ℂ| (a power series ring over ℂ in finitely many vars has cardinality |ℂ|). -/
theorem T_card_eq : Cardinal.mk T = Cardinal.mk ℂ :=
  le_antisymm
    ((Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans mvPS_card_eq.le)
    (Cardinal.mk_le_of_injective cToT_injective)

-- If mk(g) is a unit in T, then constantCoeff g is a unit in ℂ
lemma unit_of_mk_unit_T (g : MvPowerSeries (Fin 3) ℂ)
    (h : IsUnit (Ideal.Quotient.mk conjI g)) : IsUnit (MvPowerSeries.constantCoeff g) := by
  obtain ⟨⟨u, v, huv, hvu⟩, hu⟩ := h
  obtain ⟨f₁, rfl⟩ := Ideal.Quotient.mk_surjective v
  have h1 : g * f₁ - 1 ∈ conjI := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one]
    exact sub_eq_zero.mpr (hu ▸ huv)
  have hcc_I : ∀ x ∈ conjI, MvPowerSeries.constantCoeff (σ := Fin 3) (R := ℂ) x = 0 := by
    intro x hx
    rw [conjI, Ideal.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    simp [map_mul, map_sub, map_pow, MvPowerSeries.constantCoeff_X]
  have hcc := hcc_I _ h1
  simp only [map_sub, map_mul, map_one] at hcc
  exact IsUnit.of_mul_eq_one (MvPowerSeries.constantCoeff f₁) (sub_eq_zero.mp hcc)

open MvPowerSeries in
lemma mk_sub_C_mem_maxIdeal_T (f : MvPowerSeries (Fin 3) ℂ) :
    Ideal.Quotient.mk conjI (f - MvPowerSeries.C (σ := Fin 3) (constantCoeff f)) ∈
    IsLocalRing.maximalIdeal T := by
  rw [IsLocalRing.mem_maximalIdeal]
  intro hu
  have hcc := unit_of_mk_unit_T _ hu
  have : constantCoeff (f - MvPowerSeries.C (σ := Fin 3) (constantCoeff f)) = 0 := by
    simp [map_sub, MvPowerSeries.constantCoeff_C]
  rw [this] at hcc
  exact (not_isUnit_zero hcc).elim

open MvPowerSeries in
/-- The composite `ℂ →[C] MvPowerSeries (Fin 3) ℂ →[mk] T →[residue] T/M` from `ℂ` to the
residue field of `T`. -/
noncomputable def cToResT : ℂ →+* IsLocalRing.ResidueField T :=
  (IsLocalRing.residue T).comp ((Ideal.Quotient.mk conjI).comp (C (σ := Fin 3)))

-- Surjectivity: every class in T/M has a constant representative
open MvPowerSeries in
lemma cToResT_surjective : Function.Surjective cToResT := by
  intro x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective t
  use constantCoeff f
  change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T))
      ((Ideal.Quotient.mk conjI) (C (constantCoeff f))) =
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T))
      ((Ideal.Quotient.mk conjI) f)
  rw [Ideal.Quotient.eq, ← map_sub]
  have : C (σ := Fin 3) (constantCoeff f) - f = -(f - C (constantCoeff f)) := by ring
  rw [this, map_neg]
  exact neg_mem (mk_sub_C_mem_maxIdeal_T f)

-- Injectivity: distinct constants map to distinct residue classes
open MvPowerSeries in
lemma cToResT_injective : Function.Injective cToResT := by
  intro a b hab
  by_contra h
  change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T))
      ((Ideal.Quotient.mk conjI) (C (σ := Fin 3) a)) =
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T))
      ((Ideal.Quotient.mk conjI) (C (σ := Fin 3) b)) at hab
  rw [Ideal.Quotient.eq, ← map_sub, ← map_sub] at hab
  rw [IsLocalRing.mem_maximalIdeal] at hab
  apply hab
  apply (Ideal.Quotient.mk conjI).isUnit_map
  rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C]
  exact IsUnit.mk0 _ (sub_ne_zero.mpr h)

/-- |T/M| = |ℂ| (the residue field is ℂ). -/
theorem T_residueField_card :
    Cardinal.mk (IsLocalRing.ResidueField T) = Cardinal.mk ℂ :=
  le_antisymm
    (Cardinal.mk_le_of_surjective cToResT_surjective)
    (Cardinal.mk_le_of_injective cToResT_injective)
