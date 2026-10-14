/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.BruhatTits.Utils.Misc

/-!
# LeanPool.BruhatTits.Utils.ValuationRings
-/

@[expose] public section

open Module

section

variable {K : Type*} [Field K] (R : Subring K)

variable {R} in
open Pointwise in
/--
@isnad1 id=eq.1h5v.s13.bb2f41579d40 from=translated src=- shape=c7b0294e vocab=ee8de66c
-/
lemma maximalIdeal_smul_eq_uniformizer_smul [IsDiscreteValuationRing R] {ι : Type*}
    (M : Submodule R (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal R • M = ϖ • M := by
  rw [hϖ.maximalIdeal_eq]
  exact Submodule.ideal_span_singleton_smul ϖ M

/--
@isnad1 id=eq.0h4v.s10.e94520f3f349 from=translated src=- shape=b75fdaef vocab=1d2c7290
-/
@[simp]
lemma Subring.coe_zpow (a : Rˣ) (n : ℤ) :
    (a ^ n).val.val = a.val.val ^ n := by
  change (Units.map R.subtype (a ^ n) : Kˣ).val = (Units.map R.subtype a).val ^ n
  simp

end

variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]

variable (ϖ : R) (hϖ : Irreducible ϖ)

local notation "v" => ValuationRing.valuation R K

/--
@isnad1 id=iff.0h3v.s10.31d4274c75ee from=translated src=- shape=734f939c vocab=0bfb314e
-/
lemma mem_subring_iff_integer (x : K) : x ∈ R ↔ v x ≤ 1 := by
  rw [← Valuation.mem_integer_iff, ValuationRing.mem_integer_iff, ← Set.mem_range]
  change x ∈ R ↔ x ∈ R.subtype.range
  rw [Subring.range_subtype]

omit [ValuationRing ↥R] [IsFractionRing (↥R) K] in
/--
@isnad1 id=eq.0h3v.s9.b40654cb1528 from=translated src=- shape=7ef914ec vocab=a985171f
-/
lemma coe_inv_eq_inv_coe (u : Rˣ) : (u : K)⁻¹ = u⁻¹ := by
  symm
  apply eq_inv_of_mul_eq_one_right
  change ((u : R) : K) * ((u⁻¹ : Rˣ) : R) = 1
  rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]

/--
@isnad1 id=or.0h3v.s8.19621f70c545 from=translated src=- shape=d31b6949 vocab=72fdbe8b
-/
lemma mem_or_inv_mem (x : K) : x ∈ R ∨ x⁻¹ ∈ R := by
  rw [mem_subring_iff_integer, mem_subring_iff_integer]
  by_cases h : v x ≤ 1
  · exact Or.inl h
  · apply Or.inr
    have hx : x ≠ 0 := by
      rintro rfl
      simp at h
    have hvx : 1 < v x := not_le.mp h
    rw [Valuation.one_lt_val_iff v hx] at hvx
    exact le_of_lt hvx

include hϖ in
lemma eq_unit_mul_pow_irreducible [IsDiscreteValuationRing R] (x : K) (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : Rˣ), x = u * ϖ ^ n := by
  cases mem_or_inv_mem (R := R) x
  · next h =>
    let x' : R := ⟨x, h⟩
    have hx' : x' ≠ 0 := Subtype.coe_ne_coe.mp hx
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' hϖ
    use n, u
    simpa using congrArg Subtype.val hu
  · next h =>
    let x' : R := ⟨x⁻¹, h⟩
    have hx' : x' ≠ 0 := (Subtype.coe_ne_coe).mp (inv_ne_zero hx)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' hϖ
    have : x = x'.val⁻¹ := by simp [x']
    use -n, u⁻¹
    rw [this, hu, mul_comm]
    ring_nf
    simp [coe_inv_eq_inv_coe]

lemma eq_unit_mul_pow_irreducible' [IsDiscreteValuationRing R] (x : Kˣ) :
    ∃ (n : ℤ) (u : Rˣ), x = Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ n := by
  have hx : x.val ≠ 0 := x.ne_zero
  obtain ⟨n, u, h⟩ := eq_unit_mul_pow_irreducible ϖ hϖ x.val hx
  use n, u
  ext
  simp_all

/-
NOTE: The following lemmas are mostly copied from the analogous lemmas for `ValuationSubring`s.
It could be advisable to change our setup, started a Zulip discussion for that.
-/

/--
@isnad1 id=iff.0h4v.s11.830ea36b5ffc from=translated src=- shape=d14abe84 vocab=bea6f6f6
-/
theorem valuation_eq_iff (x y : K) :
    v x = v y ↔ ∃ (a : Rˣ), a * y = x :=
  Quotient.eq''

/--
@isnad1 id=eq.0h3v.s10.e3a4633c17dd from=translated src=- shape=7b2ebf31 vocab=bffde15f
-/
theorem valuation_unit (a : Rˣ) : v a = 1 := by
  rw [← Valuation.map_one v, valuation_eq_iff]; use a; simp

/--
@isnad1 id=eq.1h3v.s10.336f0707ec59 from=translated src=- shape=9f3ca1e4 vocab=a1bfc78a
-/
lemma valuation_isUnit (a : R) (ha : IsUnit a) : v a = 1 :=
  valuation_unit ha.unit

/--
@isnad1 id=iff.0h3v.s10.8e6c95c879cf from=translated src=- shape=16f87574 vocab=a1bfc78a
-/
lemma valuation_eq_one_iff (a : R) : IsUnit a ↔ v a = 1 :=
  ⟨fun h => valuation_unit h.unit, fun h => by
    have ha : (a : K) ≠ 0 := by
      intro c
      simp_all
    have ha' : (a : K)⁻¹ ∈ R := by rw [mem_subring_iff_integer, map_inv₀, h, inv_one]
    apply IsUnit.of_mul_eq_one ⟨(a : K)⁻¹, ha'⟩
    ext
    simp_all⟩

/--
@isnad1 id=eq.0h3v.s10.e3a4633c17dd from=translated src=- shape=7b2ebf31 vocab=bffde15f
-/
lemma valuation_unit_eq_one (x : Rˣ) : v x = 1 :=
  valuation_unit x

include hϖ in
/--
@isnad1 id=lt.1h3v.s11.7ea2f84d4840 from=translated src=- shape=9f3ca1e4 vocab=d652f0c8
-/
lemma valuation_lt_one_of_irreducible : v ϖ < 1 := by
  by_contra h
  apply hϖ.not_isUnit
  rw [valuation_eq_one_iff]
  apply le_antisymm
  · simp [← mem_subring_iff_integer]
  · simpa using h

variable [IsDiscreteValuationRing R]

/-- The exponent of a unit relative to a chosen irreducible element. -/
noncomputable def zaddVal' (x : Kˣ) : ℤ :=
  (eq_unit_mul_pow_irreducible' ϖ hϖ x).choose

/-- The exponent of a unit relative to an arbitrary chosen irreducible element of the DVR. -/
noncomputable def zaddVal (x : Kˣ) : ℤ :=
  zaddVal'
    (IsDiscreteValuationRing.exists_irreducible R).choose
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec
    x

/--
@isnad1 id=ex.1h4v.s11.e828e8e0a5c5 from=translated src=- shape=60023314 vocab=7633ee76
-/
lemma zaddVal'_spec (x : Kˣ) : ∃ (u : Rˣ),
    x = Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ (zaddVal' ϖ hϖ x) :=
  (eq_unit_mul_pow_irreducible' ϖ hϖ x).choose_spec

/--
@isnad1 id=ex.0h3v.s9.67f47d14a646 from=translated src=- shape=63e825ce vocab=b67400e2
-/
lemma zaddVal_spec' (x : Kˣ) : ∃ (ϖ : R) (hϖ : Irreducible ϖ),
    zaddVal (R := R) x = zaddVal' ϖ hϖ x := by
  use (IsDiscreteValuationRing.exists_irreducible R).choose
  use (IsDiscreteValuationRing.exists_irreducible R).choose_spec
  rfl

/--
@isnad1 id=ex.0h3v.s11.211ff3003b88 from=translated src=- shape=ba4e107a vocab=f065438e
-/
lemma zaddVal_spec (x : Kˣ) : ∃ (ϖ : R) (hϖ : Irreducible ϖ)
    (u : Rˣ),
    x = Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ (zaddVal (R := R) x) := by
  obtain ⟨ϖ, hϖ, h⟩ := zaddVal_spec' (R := R) x
  use ϖ, hϖ
  obtain ⟨u, hu⟩ := zaddVal'_spec ϖ hϖ x
  use u
  rwa [h]

include hϖ in
/--
@isnad1 id=eq.2h7v.s10.9199d5505694 from=translated src=- shape=e9471c67 vocab=bfa7f1c1
-/
lemma unit_mul_zpow_congr_zpow' (a b : Rˣ) (m n : ℤ) (h : a * ϖ.val ^ m = b * ϖ.val ^ n) :
    m = n := by
  wlog hmn : m ≤ n
  · simp only [not_le] at hmn
    symm
    exact this ϖ hϖ b a n m h.symm (le_of_lt hmn)
  have h' : a * ϖ.val ^ m * ϖ.val ^ (-m) = b * ϖ.val ^ n * ϖ.val ^ (-m) :=
    congrFun (congrArg HMul.hMul h) (ϖ.val ^ (-m))
  rw [mul_assoc, mul_assoc, ← zpow_add₀ (by simpa using hϖ.ne_zero),
    ← zpow_add₀ (by simpa using hϖ.ne_zero)] at h'
  ring_nf at h'
  simp only [zpow_zero, mul_one] at h'
  rw [add_comm] at h'
  have : a * ϖ ^ 0 = b * ϖ ^ (Int.toNat (n - m)) := by
    ext
    simp only [pow_zero, mul_one, Subring.coe_mul, SubmonoidClass.coe_pow]
    rw [h', ← sub_eq_add_neg, ← Int.toNat_sub_of_le hmn]
    norm_cast
  have : 0 = Int.toNat (n - m) :=
    IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ a b 0 (Int.toNat (n - m)) this
  rw [← Nat.cast_inj (R := ℤ)] at this
  simp only [CharP.cast_eq_zero, Int.ofNat_toNat, right_eq_sup, tsub_le_iff_right, zero_add] at this
  symm
  exact Int.le_antisymm this hmn

/--
@isnad1 id=eq.3h8v.s10.265d71c15ef3 from=translated src=- shape=d6c89b2e vocab=bfa7f1c1
-/
lemma unit_mul_zpow_congr_zpow {p q : R} (hp : Irreducible p) (hq : Irreducible q)
    (a b : Rˣ) (m n : ℤ) (h : a * p.val ^ m = b * q.val ^ n) :
    m = n := by
  obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible R hp hq
  simp only [Subring.coe_mul] at h
  rw [mul_zpow] at h
  nth_rw 3 [mul_comm] at h
  have : (b * u ^ n).val.val = b.val.val * u.val.val ^ n := by simp
  rw [← mul_assoc, ← this] at h
  apply unit_mul_zpow_congr_zpow' _ hp
  exact h

include hϖ in
omit [IsDiscreteValuationRing R] in
/--
@isnad1 id=iff.1h4v.s10.64ac99632e00 from=translated src=- shape=3b9293d2 vocab=4bd68fbe
-/
lemma valuation_irreducible_zpow_eq_one_iff (n : ℤ) : v (ϖ.val ^ n) = 1 ↔ n = 0 := by
  constructor
  · intro h
    rw [map_zpow₀] at h
    have : v ϖ < 1 := valuation_lt_one_of_irreducible ϖ hϖ
    exact exp_zero_of_zpow_eq_one this h
  · simp_all

include hϖ in
omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K] in
/--
@isnad1 id=not.1h3v.s8.ff109583021e from=translated src=- shape=b151602e vocab=60061e6d
-/
lemma inv_irreducible_not_mem_subring : ϖ.val⁻¹ ∉ R := by
  by_contra h
  apply hϖ.not_isUnit
  have hϖnzero : ϖ.val ≠ 0 := by simpa using hϖ.ne_zero
  let x : Rˣ :=
    ⟨ϖ, ⟨ϖ.val⁻¹, h⟩,
      by
        ext
        simp_all,
      by
        ext
        simp_all⟩
  use x

include hϖ in
omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K] in
/--
@isnad1 id=not.2h4v.s8.3c7df5886cc2 from=translated src=- shape=76f4fbb5 vocab=5beb3d46
-/
lemma neg_pow_not_mem_subring (n : ℕ) (hn : n > 0) : ϖ.val ^ (- n : ℤ) ∉ R := by
  induction n with
  | zero => contradiction
  | succ n ih =>
      have hϖnzero : ϖ.val ≠ 0 := by simpa using hϖ.ne_zero
      simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg]
      rw [zpow_add₀ hϖnzero]
      simp only [Int.reduceNeg, zpow_neg, zpow_one, zpow_natCast]
      simp only [gt_iff_lt, zpow_neg, zpow_natCast] at ih
      by_cases hnz : n = 0
      · subst hnz
        simpa only [pow_zero, inv_one, mul_one] using
          inv_irreducible_not_mem_subring ϖ hϖ
      · have : (ϖ.val ^ n)⁻¹ ∉ R := by
          apply ih
          exact Nat.zero_lt_of_ne_zero hnz
        contrapose! this
        have : ϖ.val * ϖ.val⁻¹ * (ϖ.val ^ n)⁻¹ = (ϖ.val ^ n)⁻¹ := by field_simp
        rw [← this, mul_assoc]
        apply Subring.mul_mem
        · exact ϖ.property
        · assumption

omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K] in
include hϖ in
/--
@isnad1 id=iff.1h4v.s8.34e2bb2882ac from=translated src=- shape=97c9ebaa vocab=a80ab009
-/
lemma irreducible_zpow_mem_subring_iff (n : ℤ) : ϖ.val ^ n ∈ R ↔ n ≥ 0 := by
  constructor
  · intro h
    contrapose! h
    have hn : - n ≥ 0 := by
      simpa only [ge_iff_le, Left.nonneg_neg_iff] using Int.le_of_lt h
    convert_to (ϖ.val ^ (- (- n).toNat : ℤ)) ∉ R
    · simp_all
    · apply neg_pow_not_mem_subring _ (-n).toNat (hϖ := hϖ)
      simpa
  · intro hn
    convert_to (ϖ ^ n.toNat).val ∈ R
    · rw [SubmonoidClass.coe_pow, ← zpow_natCast, Int.toNat_of_nonneg hn]
    · exact SetLike.coe_mem (ϖ ^ n.toNat)

/--
@isnad1 id=iff.1h5v.s11.ba5fdab8c571 from=translated src=- shape=bb34fb19 vocab=f065438e
-/
lemma zaddVal_eq_iff (n : ℤ) (x : Kˣ) :
    zaddVal (R := R) x = n ↔ ∃ (u : Rˣ), Units.map R.subtype u *
      (Units.mk0 ϖ.val (by simpa using hϖ.ne_zero)) ^ n = x := by
  constructor
  · intro h
    obtain ⟨p, hp, y, hy⟩ := zaddVal_spec (R := R) x
    rw [h] at hy
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ hp
    use y * a ^ n
    ext
    simp [hy, mul_zpow]
    group
  · rintro ⟨u, hu⟩
    obtain ⟨p, hp, y, hy⟩ := zaddVal_spec (R := R) x
    nth_rw 1 [← hu] at hy
    rw [Units.ext_iff] at hy
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Subring.coe_subtype,
      Units.val_zpow_eq_zpow_val, Units.val_mk0] at hy
    apply unit_mul_zpow_congr_zpow hp hϖ y u
    exact hy.symm

include hϖ in
/--
@isnad1 id=iff.1h5v.s9.df66d38d60d1 from=translated src=- shape=9f2546d7 vocab=4a769cdc
-/
lemma zaddVal_eq_iff' (n : ℤ) (x : Kˣ) :
    zaddVal (R := R) x = n ↔ ∃ (u : Rˣ), u * ϖ.val ^ n = x := by
  rw [zaddVal_eq_iff ϖ hϖ]
  simp [Units.ext_iff]

include hϖ in
lemma eq_unit_mul_zpow_zaddVal (x : Kˣ) :
    ∃ (u : Rˣ), u * ϖ.val ^ zaddVal (R := R) x = x :=
  (zaddVal_eq_iff' ϖ hϖ (zaddVal (R := R) x) x).mp rfl

/--
@isnad1 id=eq.0h4v.s8.eee1008bff77 from=translated src=- shape=704ee111 vocab=e69197f5
-/
@[simp]
lemma zaddVal_mul (x y : Kˣ) :
    zaddVal (R := R) (x * y) = zaddVal (R := R) x + zaddVal (R := R) y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ux, hux⟩ := eq_unit_mul_zpow_zaddVal ϖ hϖ x
  obtain ⟨uy, huy⟩ := eq_unit_mul_zpow_zaddVal ϖ hϖ y
  rw [zaddVal_eq_iff' ϖ hϖ]
  use ux * uy
  simp only [Units.val_mul, Subring.coe_mul]
  rw [zpow_add₀ (by simpa using hϖ.ne_zero), ← hux, ← huy]
  ring

/--
@isnad1 id=eq.0h3v.s11.650c059a518a from=translated src=- shape=c14f76c0 vocab=2e1369e1
-/
@[simp]
lemma zaddVal_units_map (x : Rˣ) :
    zaddVal (R := R) (Units.map R.subtype x) = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [zaddVal_eq_iff' ϖ hϖ]
  simp_all
