/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanHahnKaplansky.HahnKaplanskyRealClosedness.Basic.HahnField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residue, local-ring, and square-part infrastructure for Hahn fields
-/

namespace HahnKaplanskyRealClosedness

open Polynomial
open HahnSeries

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The constant coefficient map on the natural valuation subring.-/
def constantCoeff : valuationSubring k Γ →+ k where
  toFun x := (ofLex (x : HahnField k Γ)).coeff 0
  map_zero' := by simp
  map_add' x y := by simp

@[simp]
theorem constantCoeff_apply (x : valuationSubring k Γ) :
    constantCoeff k Γ x = (ofLex (x : HahnField k Γ)).coeff 0 :=
  rfl

@[simp]
theorem constantCoeff_one :
    constantCoeff k Γ (1 : valuationSubring k Γ) = 1 := by
  change (ofLex ((1 : valuationSubring k Γ) : HahnField k Γ)).coeff 0 = 1
  simp

theorem constantCoeff_surjective : Function.Surjective (constantCoeff k Γ) := by
  intro r
  refine ⟨⟨toLex (HahnSeries.single 0 r), ?_⟩, ?_⟩
  · change (0 : WithTop Γ) ≤ addVal k Γ (toLex (HahnSeries.single 0 r))
    by_cases hr : r = 0
    · simp [hr]
    · simp [addVal_single_of_ne (k := k) (Γ := Γ) hr]
  · change (ofLex (toLex (HahnSeries.single 0 r))).coeff 0 = r
    simp

/-- The constant coefficient of a product of two elements of the valuation subring is the product
of their constant coefficients.-/
theorem constantCoeff_mul (x y : valuationSubring k Γ) :
    constantCoeff k Γ (x * y) = constantCoeff k Γ x * constantCoeff k Γ y := by
  change (ofLex ((x : HahnField k Γ) * (y : HahnField k Γ))).coeff 0 =
    (ofLex (x : HahnField k Γ)).coeff 0 * (ofLex (y : HahnField k Γ)).coeff 0
  change ((ofLex (x : HahnField k Γ)) * (ofLex (y : HahnField k Γ))).coeff 0 =
    (ofLex (x : HahnField k Γ)).coeff 0 * (ofLex (y : HahnField k Γ)).coeff 0
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_single (0, 0) ?_ ?_
  · intro ij hij hij_ne
    rw [Finset.mem_antidiagonal] at hij
    by_cases hxij : (ofLex (x : HahnField k Γ)).coeff ij.1 = 0
    · simp [hxij]
    by_cases hyij : (ofLex (y : HahnField k Γ)).coeff ij.2 = 0
    · simp [hyij]
    exfalso
    have hnonneg_left : 0 ≤ ij.1 :=
      nonneg_of_mem_valuationSubring_coeff_ne_zero k Γ x.property hxij
    have hnonneg_right : 0 ≤ ij.2 :=
      nonneg_of_mem_valuationSubring_coeff_ne_zero k Γ y.property hyij
    have hij_zero : ij.1 = 0 ∧ ij.2 = 0 :=
      (add_eq_zero_iff_of_nonneg hnonneg_left hnonneg_right).mp hij.2.2
    exact hij_ne (Prod.ext hij_zero.1 hij_zero.2)
  · intro hnot
    rw [Finset.mem_antidiagonal] at hnot
    simp only [HahnSeries.mem_support, ne_eq, zero_add, and_true] at hnot
    by_cases hx0 : (ofLex (x : HahnField k Γ)).coeff 0 = 0
    · simp [hx0]
    · have hy0 : (ofLex (y : HahnField k Γ)).coeff 0 = 0 := by
        by_contra hy0
        exact hnot ⟨hx0, hy0⟩
      simp [hy0]

/-- The constant coefficient as a ring homomorphism from the natural valuation subring.-/
def constantCoeffRingHom : valuationSubring k Γ →+* k where
  toFun := constantCoeff k Γ
  map_zero' := by simp
  map_one' := constantCoeff_one k Γ
  map_add' x y := by simp
  map_mul' := constantCoeff_mul k Γ

@[simp]
theorem constantCoeffRingHom_apply (x : valuationSubring k Γ) :
    constantCoeffRingHom k Γ x = (ofLex (x : HahnField k Γ)).coeff 0 :=
  rfl

theorem constantCoeffRingHom_surjective :
    Function.Surjective (constantCoeffRingHom k Γ) :=
  constantCoeff_surjective k Γ

/-- Inside the natural valuation subring, reducing to zero is the same as having positive
valuation.-/
theorem constantCoeffRingHom_eq_zero_iff_pos_addVal (x : valuationSubring k Γ) :
    constantCoeffRingHom k Γ x = 0 ↔
      (0 : WithTop Γ) < addVal k Γ (x : HahnField k Γ) := by
  constructor
  · intro hx0
    by_contra hpos
    have hle : addVal k Γ (x : HahnField k Γ) ≤ 0 := le_of_not_gt hpos
    have hge : (0 : WithTop Γ) ≤ addVal k Γ (x : HahnField k Γ) := x.property
    have hval : addVal k Γ (x : HahnField k Γ) = 0 := le_antisymm hle hge
    have hcoeff : (ofLex (x : HahnField k Γ)).coeff 0 ≠ 0 := by
      exact HahnSeries.coeff_orderTop_ne (by simpa [addVal_apply] using hval)
    exact hcoeff (by simpa only [constantCoeffRingHom_apply] using hx0)
  · intro hpos
    change (ofLex (x : HahnField k Γ)).coeff 0 = 0
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop (by simpa [addVal_apply] using hpos)

theorem addVal_eq_zero_of_mem_valuationSubring_of_constantCoeff_ne_zero
    {x : HahnField k Γ} (hx : x ∈ valuationSubring k Γ)
    (h0 : (ofLex x).coeff 0 ≠ 0) :
    addVal k Γ x = 0 := by
  exact le_antisymm (by simpa [addVal_apply] using HahnSeries.orderTop_le_of_coeff_ne_zero h0) hx

/-- A valuation-subring element of value zero has sign determined by its constant coefficient.-/
theorem pos_iff_constantCoeff_pos_of_addVal_eq_zero (x : valuationSubring k Γ)
    (hx : addVal k Γ (x : HahnField k Γ) = 0) :
    0 < (x : HahnField k Γ) ↔ 0 < constantCoeff k Γ x := by
  rw [← HahnSeries.leadingCoeff_pos_iff, constantCoeff_apply,
    leadingCoeff_eq_coeff_zero_of_addVal_eq_zero k Γ hx]

/-- The sign of any finite-value Hahn series can be read from the constant coefficient after
positive monomial normalization.-/
theorem pos_iff_constantCoeff_pos_of_normalized_monomial {x : HahnField k Γ} {γ : Γ}
    (hx : addVal k Γ x = (γ : WithTop Γ)) :
    let y : valuationSubring k Γ :=
      ⟨toLex (HahnSeries.single (-γ) (1 : k)) * x, by
        change (0 : WithTop Γ) ≤
          addVal k Γ (toLex (HahnSeries.single (-γ) (1 : k)) * x)
        rw [addVal_single_neg_mul_of_addVal_eq k Γ hx]⟩
    0 < x ↔ 0 < constantCoeff k Γ y := by
  dsimp only
  let y : valuationSubring k Γ :=
    ⟨toLex (HahnSeries.single (-γ) (1 : k)) * x, by
      change (0 : WithTop Γ) ≤
        addVal k Γ (toLex (HahnSeries.single (-γ) (1 : k)) * x)
      rw [addVal_single_neg_mul_of_addVal_eq k Γ hx]⟩
  calc
    0 < x ↔ 0 < (y : HahnField k Γ) := by
      change 0 < x ↔ 0 < toLex (HahnSeries.single (-γ) (1 : k)) * x
      exact (normalized_monomial_mul_pos_iff k Γ γ x).symm
    _ ↔ 0 < constantCoeff k Γ y :=
      pos_iff_constantCoeff_pos_of_addVal_eq_zero k Γ y
        (addVal_single_neg_mul_of_addVal_eq k Γ hx)

/-- The binomial half-power squares to the original `1`-unit.-/
theorem orderTopSubOnePos_sq_pow_half (u : HahnSeries.orderTopSubOnePos Γ k) :
    (u ^ ((1 : k) / 2)) * (u ^ ((1 : k) / 2)) = u := by
  rw [← HahnSeries.pow_add]
  rw [show (1 : k) / 2 + (1 : k) / 2 = 1 by ring]
  apply Subtype.ext
  apply Units.ext
  rw [HahnSeries.binomial_power]
  change PowerSeries.heval (u.val.val - 1) (PowerSeries.binomialSeries k (1 : k)) = u.val.val
  have hb := PowerSeries.binomialSeries_nat (R := k) (A := k) 1
  norm_num at hb
  rw [hb]
  change PowerSeries.heval (u.val.val - 1) (1 + PowerSeries.X) = u.val.val
  rw [map_add, PowerSeries.heval_X (u.val.val - 1) u.property]
  change PowerSeries.heval (u.val.val - 1) 1 + (u.val.val - 1) = u.val.val
  rw [map_one]
  simp

/-- A Hahn-field element congruent to `1` modulo positive valuation has a square root given by
the binomial series.-/
theorem exists_square_root_of_orderTop_sub_one_pos {x : HahnField k Γ}
    (hx : 0 < (ofLex x - 1).orderTop) : ∃ z : HahnField k Γ, x = z * z := by
  let u : HahnSeries.orderTopSubOnePos Γ k := HahnSeries.toOrderTopSubOnePos hx
  let r : HahnSeries.orderTopSubOnePos Γ k := u ^ ((1 : k) / 2)
  have hs : r * r = u := by
    change (u ^ ((1 : k) / 2)) * (u ^ ((1 : k) / 2)) = u
    exact orderTopSubOnePos_sq_pow_half k Γ u
  have hval := congrArg (fun u : HahnSeries.orderTopSubOnePos Γ k => u.val.val) hs
  refine ⟨toLex r.val.val, ?_⟩
  change x = toLex (r.val.val * r.val.val)
  simpa [u] using (congrArg toLex hval.symm)

theorem isUnit_of_constantCoeffRingHom_ne_zero (x : valuationSubring k Γ)
    (hx0 : constantCoeffRingHom k Γ x ≠ 0) : IsUnit x := by
  let x' : HahnField k Γ := x
  have hxval : addVal k Γ x' = 0 :=
    addVal_eq_zero_of_mem_valuationSubring_of_constantCoeff_ne_zero k Γ x.property hx0
  have hxne : x' ≠ 0 := by
    intro h
    apply hx0
    rw [constantCoeffRingHom_apply]
    change (ofLex x').coeff 0 = 0
    simp [h]
  have hinv_mem : x'⁻¹ ∈ valuationSubring k Γ := by
    change (0 : WithTop Γ) ≤ addVal k Γ x'⁻¹
    have hmul := AddValuation.map_mul (addVal k Γ) x' x'⁻¹
    rw [mul_inv_cancel₀ hxne, AddValuation.map_one, hxval, zero_add] at hmul
    exact le_of_eq hmul
  refine ⟨⟨x, ⟨x'⁻¹, hinv_mem⟩, ?_, ?_⟩, rfl⟩
  · ext
    exact mul_inv_cancel₀ hxne
  · ext
    exact inv_mul_cancel₀ hxne

/-- An element of the natural valuation subring with value zero is a unit.-/
theorem isUnit_of_addVal_eq_zero {x : HahnField k Γ} (hx : addVal k Γ x = 0) :
    IsUnit (⟨x, by change (0 : WithTop Γ) ≤ addVal k Γ x; rw [hx]⟩ :
      valuationSubring k Γ) := by
  apply isUnit_of_constantCoeffRingHom_ne_zero k Γ
  intro hzero
  have hpos := (constantCoeffRingHom_eq_zero_iff_pos_addVal k Γ _).mp hzero
  rw [hx] at hpos
  exact (lt_irrefl (0 : WithTop Γ)) hpos

/-- The monomial-normalized form of a finite-value Hahn series is a unit of the natural valuation
subring.-/
theorem isUnit_normalized_monomial {x : HahnField k Γ} {γ : Γ}
    (hx : addVal k Γ x = (γ : WithTop Γ)) :
    IsUnit (⟨toLex (HahnSeries.single (-γ) (1 : k)) * x, by
      change (0 : WithTop Γ) ≤ addVal k Γ (toLex (HahnSeries.single (-γ) (1 : k)) * x)
      rw [addVal_single_neg_mul_of_addVal_eq k Γ hx]⟩ : valuationSubring k Γ) := by
  apply isUnit_of_addVal_eq_zero k Γ
  exact addVal_single_neg_mul_of_addVal_eq k Γ hx

omit [IsStrictOrderedRing k] in
private theorem exists_leadingTerm_decomposition_of_pos {x : HahnField k Γ} (hx : 0 < x) :
    ∃ γ : Γ, ∃ c : k, ∃ w : HahnField k Γ,
      0 < c ∧ 0 < (ofLex w).orderTop ∧
        x = toLex (HahnSeries.single γ c) * (1 + w) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  let γ : Γ := (addVal k Γ x).untop (by simpa [AddValuation.ne_top_iff] using hxne)
  have hxγ : addVal k Γ x = (γ : WithTop Γ) := (WithTop.coe_untop _ _).symm
  let c : k := (ofLex x).leadingCoeff
  have hc : 0 < c := by
    dsimp [c]
    exact HahnSeries.leadingCoeff_pos_iff.mpr hx
  let u : HahnField k Γ := toLex (HahnSeries.single (-γ) c⁻¹) * x
  have hval_u : addVal k Γ u = 0 := by
    change addVal k Γ (toLex (HahnSeries.single (-γ) c⁻¹) * x) = 0
    rw [AddValuation.map_mul, addVal_single_of_ne (k := k) (Γ := Γ)
      (inv_ne_zero (ne_of_gt hc)), hxγ]
    simp
  have hlead_u : (ofLex u).leadingCoeff = 1 := by
    rw [leadingCoeff_eq_coeff_zero_of_addVal_eq_zero k Γ hval_u]
    dsimp [u]
    rw [HahnSeries.coeff_single_mul]
    rw [show (0 : Γ) - -γ = γ by abel]
    have hcoeffγ : (ofLex x).coeff γ = c := by
      rw [← leadingCoeff_eq_coeff_of_addVal_eq k Γ hxγ]
    rw [hcoeffγ]
    field_simp [ne_of_gt hc]
  have hclose : 0 < (ofLex u - 1).orderTop := by
    rw [HahnSeries.orderTop_self_sub_one_pos_iff]
    exact ⟨by simpa [addVal_apply] using hval_u, hlead_u⟩
  have hdenorm : x = toLex (HahnSeries.single γ c) * u := by
    dsimp [u]
    rw [← mul_assoc]
    change x = toLex (HahnSeries.single γ c * HahnSeries.single (-γ) c⁻¹) * x
    rw [HahnSeries.single_mul_single]
    simp [ne_of_gt hc]
  refine ⟨γ, c, u - 1, hc, ?_, ?_⟩
  · simpa using hclose
  · rw [show (1 : HahnField k Γ) + (u - 1) = u by ring]
    exact hdenorm

/-- Over a real closed coefficient field and a divisible value group, every nonnegative Hahn-field
element is a square.-/
theorem isSquare_of_nonneg [IsRealClosed k] [DivisibleBy Γ ℕ] {x : HahnField k Γ}
    (hx : 0 ≤ x) : IsSquare x := by
  rcases lt_or_eq_of_le hx with hxpos | rfl
  · rcases exists_leadingTerm_decomposition_of_pos k Γ hxpos with
      ⟨γ, c, w, hc, hw, hxdec⟩
    rcases IsRealClosed.exists_eq_pow_of_nonneg hc.le (n := 2) (by decide) with ⟨d, hd⟩
    have hclose : 0 < (ofLex (1 + w) - 1).orderTop := by simpa using hw
    rcases exists_square_root_of_orderTop_sub_one_pos k Γ hclose with ⟨s, hs⟩
    let m : HahnField k Γ := toLex (HahnSeries.single (DivisibleBy.div γ 2) d)
    have hm : m ^ 2 = toLex (HahnSeries.single γ c) := by
      dsimp [m]
      change toLex (HahnSeries.single (DivisibleBy.div γ 2) d ^ 2) =
        toLex (HahnSeries.single γ c)
      rw [HahnSeries.single_pow, DivisibleBy.div_cancel γ (by decide : 2 ≠ 0), ← hd]
    refine ⟨m * s, ?_⟩
    calc
      x = toLex (HahnSeries.single γ c) * (1 + w) := hxdec
      _ = m ^ 2 * (s * s) := by rw [hm, hs]
      _ = (m * s) ^ 2 := by rw [pow_two]; ring
      _ = (m * s) * (m * s) := by rw [pow_two]
  · exact ⟨0, by simp⟩

/-- A sharper Hahn-field real-closedness criterion after proving the square part by binomial
Hahn-series expansion.

The remaining hard input is the existence of roots for odd-degree polynomials.-/
theorem isRealClosed_of_odd_roots [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hodd : ∀ {f : (HahnField k Γ)[X]}, Odd f.natDegree → ∃ x, f.IsRoot x) :
    IsRealClosed (HahnField k Γ) := by
  apply IsRealClosed.of_linearOrderedField
  · intro x hx
    exact isSquare_of_nonneg k Γ hx
  · exact hodd

theorem constantCoeffRingHom_ker_isMaximal :
    (RingHom.ker (constantCoeffRingHom k Γ)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (constantCoeffRingHom k Γ)
    (constantCoeffRingHom_surjective k Γ)

theorem le_constantCoeffRingHom_ker_of_isMaximal
    (I : Ideal (valuationSubring k Γ)) (hI : I.IsMaximal) :
    I ≤ RingHom.ker (constantCoeffRingHom k Γ) := by
  intro x hxI
  rw [RingHom.mem_ker]
  by_contra hx0
  exact hI.ne_top (I.eq_top_of_isUnit_mem hxI
    (isUnit_of_constantCoeffRingHom_ne_zero k Γ x hx0))

instance instIsLocalRingValuationSubring : IsLocalRing (valuationSubring k Γ) := by
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨RingHom.ker (constantCoeffRingHom k Γ), constantCoeffRingHom_ker_isMaximal k Γ, ?_⟩
  intro I hI
  exact hI.eq_of_le (constantCoeffRingHom_ker_isMaximal k Γ).ne_top
    (le_constantCoeffRingHom_ker_of_isMaximal k Γ I hI)

/-- The maximal ideal of the natural valuation subring is the kernel of the residue map.-/
theorem constantCoeffRingHom_ker_eq_maximalIdeal :
    RingHom.ker (constantCoeffRingHom k Γ) =
      IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  IsLocalRing.ker_eq_maximalIdeal (constantCoeffRingHom k Γ)
    (constantCoeffRingHom_surjective k Γ)

/-- The maximal ideal of the natural valuation subring consists of elements with positive
valuation.-/
theorem mem_maximalIdeal_iff_pos_addVal (x : valuationSubring k Γ) :
    x ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ↔
      (0 : WithTop Γ) < addVal k Γ (x : HahnField k Γ) := by
  rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k) (Γ := Γ), RingHom.mem_ker,
    constantCoeffRingHom_eq_zero_iff_pos_addVal]

/-- A nonzero maximal-ideal element has a finite positive valuation and nonzero leading
coefficient.-/
theorem exists_pos_addVal_coeff_ne_zero_of_mem_maximalIdeal
    {x : valuationSubring k Γ}
    (hxmem : x ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hxne : x ≠ 0) :
    ∃ γ : Γ, 0 < γ ∧ addVal k Γ (x : HahnField k Γ) = (γ : WithTop Γ) ∧
      (ofLex (x : HahnField k Γ)).coeff γ ≠ 0 := by
  have hxne' : (x : HahnField k Γ) ≠ 0 := by
    intro hzero
    exact hxne (Subtype.ext hzero)
  let γ : Γ := (addVal k Γ (x : HahnField k Γ)).untop
    (by simpa [AddValuation.ne_top_iff] using hxne')
  have hγ : addVal k Γ (x : HahnField k Γ) = (γ : WithTop Γ) :=
    (WithTop.coe_untop _ _).symm
  have hposVal : (0 : WithTop Γ) < addVal k Γ (x : HahnField k Γ) :=
    (mem_maximalIdeal_iff_pos_addVal k Γ x).mp hxmem
  have hγpos : 0 < γ := by
    apply WithTop.coe_lt_coe.mp
    simpa [hγ] using hposVal
  refine ⟨γ, hγpos, hγ, ?_⟩
  exact HahnSeries.coeff_orderTop_ne (by simpa [addVal_apply] using hγ)

/-- A nonzero maximal-ideal element has a finite positive valuation and a named nonzero leading
coefficient.-/
theorem exists_pos_addVal_leading_coeff_of_mem_maximalIdeal
    {x : valuationSubring k Γ}
    (hxmem : x ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hxne : x ≠ 0) :
    ∃ γ : Γ, ∃ b : k, 0 < γ ∧ b ≠ 0 ∧
      addVal k Γ (x : HahnField k Γ) = (γ : WithTop Γ) ∧
        (ofLex (x : HahnField k Γ)).coeff γ = b := by
  rcases exists_pos_addVal_coeff_ne_zero_of_mem_maximalIdeal k Γ hxmem hxne with
    ⟨γ, hγpos, hγ, hcoeff⟩
  exact ⟨γ, (ofLex (x : HahnField k Γ)).coeff γ, hγpos, hcoeff, hγ, rfl⟩

/-- The new `K[X]`-level odd-cluster root statement.

This avoids first lifting a polynomial to `(valuationSubring k Γ)[X]`.  The coefficient
conditions are stated directly with the Hahn valuation: all coefficients are integral, lower
coefficients are in the maximal ideal, and the `m`-th coefficient is a unit.-/
def KOddClusterRootHypothesis : Prop :=
  ∀ {F : (HahnField k Γ)[X]} {m : ℕ},
    0 < m → Odd m →
    (∀ i, (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i)) →
    (∀ i, i < m → (0 : WithTop Γ) < addVal k Γ (F.coeff i)) →
    addVal k Γ (F.coeff m) = 0 →
    ∃ y : HahnField k Γ,
      (0 : WithTop Γ) < addVal k Γ y ∧ F.IsRoot y

/-- A Hahn-field root with positive valuation.-/
abbrev PositiveHahnRoot (F : (HahnField k Γ)[X]) : Prop :=
  ∃ y : HahnField k Γ, (0 : WithTop Γ) < addVal k Γ y ∧ F.IsRoot y

/-- A positive-valuation root after mapping a valuation-subring polynomial to the Hahn field.-/
abbrev PositiveHahnRootInMap (F : (valuationSubring k Γ)[X]) : Prop :=
  PositiveHahnRoot k Γ
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ)))

omit [LinearOrder k] [IsStrictOrderedRing k] in
noncomputable def PositiveHahnRoot.some {F : (HahnField k Γ)[X]}
    (h : PositiveHahnRoot k Γ F) : HahnField k Γ :=
  Classical.choose h

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem PositiveHahnRoot.pos {F : (HahnField k Γ)[X]}
    (h : PositiveHahnRoot k Γ F) :
    (0 : WithTop Γ) < addVal k Γ (PositiveHahnRoot.some k Γ h) :=
  (Classical.choose_spec h).1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem PositiveHahnRoot.isRoot {F : (HahnField k Γ)[X]}
    (h : PositiveHahnRoot k Γ F) :
    F.IsRoot (PositiveHahnRoot.some k Γ h) :=
  (Classical.choose_spec h).2

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem PositiveHahnRoot.of_dvd {F G : (HahnField k Γ)[X]}
    (hroot : PositiveHahnRoot k Γ G) (hdiv : G ∣ F) :
    PositiveHahnRoot k Γ F := by
  rcases hroot with ⟨y, hypos, hyroot⟩
  rcases hdiv with ⟨H, hFH⟩
  refine ⟨y, hypos, ?_⟩
  rw [Polynomial.IsRoot] at hyroot ⊢
  rw [hFH, Polynomial.eval_mul, hyroot, zero_mul]

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem PositiveHahnRoot.of_mul_left {F G H : (HahnField k Γ)[X]}
    (hroot : PositiveHahnRoot k Γ G) (hF : F = G * H) :
    PositiveHahnRoot k Γ F :=
  PositiveHahnRoot.of_dvd k Γ hroot ⟨H, hF⟩

end HahnField

end

end HahnKaplanskyRealClosedness
