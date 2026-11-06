import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve

def tateB (d : ℕ) : ℤ := (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12

def tateA4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3)

def tateA6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => -∑ d ∈ n.divisors, tateB d

def eisenstein6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

/--
@isnad1 id=eq.0h1v.s7.df80f333eafd from=translated src=- shape=cc8181d1 vocab=8b760981
-/
theorem coeff_tateA4 (n : ℕ) :
    PowerSeries.coeff n tateA4 = -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3) :=
  PowerSeries.coeff_mk n _

/--
@isnad1 id=eq.0h1v.s6.abc93eddea5a from=translated src=- shape=9fc61bb6 vocab=2c9a2a90
-/
theorem coeff_tateA6 (n : ℕ) :
    PowerSeries.coeff n tateA6 = -∑ d ∈ n.divisors, tateB d :=
  PowerSeries.coeff_mk n _

/--
@isnad1 id=eq.0h0v.s6.92e2f73d14bd from=translated src=- shape=c0fd5483 vocab=80cddc15
-/
theorem coeff_zero_tateA4 : PowerSeries.coeff 0 tateA4 = 0 := by
  rw [coeff_tateA4, Nat.divisors_zero, Finset.sum_empty, neg_zero]

/--
@isnad1 id=eq.0h0v.s6.d55a990ba0f1 from=translated src=- shape=c0fd5483 vocab=966d0f5b
-/
theorem coeff_zero_tateA6 : PowerSeries.coeff 0 tateA6 = 0 := by
  rw [coeff_tateA6, Nat.divisors_zero, Finset.sum_empty, neg_zero]

/--
@isnad1 id=eq.0h0v.s5.8e658d38c8fd from=translated src=- shape=8b3e5d3e vocab=28cb7e96
-/
theorem constantCoeff_tateA4 : PowerSeries.constantCoeff tateA4 = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_tateA4

/--
@isnad1 id=eq.0h0v.s5.be7f9f8242cb from=translated src=- shape=8b3e5d3e vocab=4271da35
-/
theorem constantCoeff_tateA6 : PowerSeries.constantCoeff tateA6 = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_tateA6

/--
@isnad1 id=eq.0h0v.s6.b87f0a1ec1d2 from=translated src=- shape=972ef9b2 vocab=40d30ebe
-/
theorem coeff_one_tateA6 : PowerSeries.coeff 1 tateA6 = -1 := by
  have h : tateB 1 = 1 := by norm_num [tateB]
  rw [coeff_tateA6, Nat.divisors_one, Finset.sum_singleton, h]

def tatePowerSeries : WeierstrassCurve (PowerSeries ℤ) := ⟨1, 0, 0, tateA4, tateA6⟩

/--
@isnad1 id=eq.0h0v.s4.ddbf0a0ea6ae from=translated src=- shape=aa786730 vocab=6c3a94ff
-/
@[simp] theorem tatePowerSeries_a₁ : tatePowerSeries.a₁ = 1 := rfl
/--
@isnad1 id=eq.0h0v.s4.e47b0c506b51 from=translated src=- shape=aa786730 vocab=a9e34cd9
-/
@[simp] theorem tatePowerSeries_a₂ : tatePowerSeries.a₂ = 0 := rfl
/--
@isnad1 id=eq.0h0v.s4.842c9c610403 from=translated src=- shape=aa786730 vocab=34d93b92
-/
@[simp] theorem tatePowerSeries_a₃ : tatePowerSeries.a₃ = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.dc9a6b6f6d72 from=translated src=- shape=844a12b5 vocab=9a214fe6
-/
@[simp] theorem tatePowerSeries_a₄ : tatePowerSeries.a₄ = tateA4 := rfl
/--
@isnad1 id=eq.0h0v.s3.6bc1f20c8096 from=translated src=- shape=844a12b5 vocab=22a2798e
-/
@[simp] theorem tatePowerSeries_a₆ : tatePowerSeries.a₆ = tateA6 := rfl

def laurentOfInt (K : Type*) [CommRing K] : PowerSeries ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map (Int.castRingHom K))

/--
@isnad1 id=eq.0h2v.s8.bea49a1d8f00 from=translated src=- shape=296504ef vocab=2a25942c
-/
theorem laurentOfInt_apply (K : Type*) [CommRing K] (f : PowerSeries ℤ) :
    laurentOfInt K f = HahnSeries.ofPowerSeries ℤ K (f.map (Int.castRingHom K)) := rfl

def tateLaurent (K : Type*) [CommRing K] : WeierstrassCurve (LaurentSeries K) :=
  tatePowerSeries.map (laurentOfInt K)

/--
@isnad1 id=eq.0h1v.s7.0d65e07a42c5 from=translated src=- shape=86ae884b vocab=7659c716
-/
@[simp] theorem tateLaurent_a₄ (K : Type*) [CommRing K] :
    (tateLaurent K).a₄ = laurentOfInt K tateA4 := rfl

/--
@isnad1 id=eq.0h1v.s7.395de42c0d01 from=translated src=- shape=86ae884b vocab=65902a8d
-/
@[simp] theorem tateLaurent_a₆ (K : Type*) [CommRing K] :
    (tateLaurent K).a₆ = laurentOfInt K tateA6 := rfl

/--
@isnad1 id=isellipt.0h1v.s4.3d0892aed081 from=translated src=- shape=aa7e0af4 vocab=aa36bfb4
-/
instance instIsElliptic_tateLaurent (K : Type*) [CommRing K] : (tateLaurent K).IsElliptic := by
  constructor
  have hΔeq : tatePowerSeries.Δ =
      -tateA6 + tateA4 ^ 2 - PowerSeries.C 64 * tateA4 ^ 3 - PowerSeries.C 432 * tateA6 ^ 2
        + PowerSeries.C 72 * (tateA4 * tateA6) := by
    rw [show (PowerSeries.C (64 : ℤ)) = (64 : PowerSeries ℤ) from map_ofNat _ 64,
      show (PowerSeries.C (432 : ℤ)) = (432 : PowerSeries ℤ) from map_ofNat _ 432,
      show (PowerSeries.C (72 : ℤ)) = (72 : PowerSeries ℤ) from map_ofNat _ 72]
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, tatePowerSeries_a₁, tatePowerSeries_a₂, tatePowerSeries_a₃,
      tatePowerSeries_a₄, tatePowerSeries_a₆]
    ring
  have hc0 : PowerSeries.constantCoeff tatePowerSeries.Δ = 0 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, map_mul, map_pow, PowerSeries.constantCoeff_C,
      constantCoeff_tateA4, constantCoeff_tateA6]
    ring
  have hmul1 : ∀ f g : PowerSeries ℤ, PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
    intro f g
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h420 : PowerSeries.coeff 0 (tateA4 ^ 2) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_tateA4]
    norm_num
  have hsq4 : PowerSeries.coeff 1 (tateA4 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA4]
    norm_num
  have hsq6 : PowerSeries.coeff 1 (tateA6 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA6]
    norm_num
  have hcb4 : PowerSeries.coeff 1 (tateA4 ^ 3) = 0 := by
    rw [show tateA4 ^ 3 = tateA4 ^ 2 * tateA4 from pow_succ tateA4 2, hmul1, h420, hsq4,
      coeff_zero_tateA4]
    norm_num
  have hprod : PowerSeries.coeff 1 (tateA4 * tateA6) = 0 := by
    rw [hmul1, coeff_zero_tateA4, coeff_zero_tateA6]
    norm_num
  have hc1 : PowerSeries.coeff 1 tatePowerSeries.Δ = 1 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, hsq4, hsq6, hcb4, hprod,
      coeff_one_tateA6]
    norm_num
  obtain ⟨u, hXu⟩ : (PowerSeries.X : PowerSeries ℤ) ∣ tatePowerSeries.Δ :=
    PowerSeries.X_dvd_iff.mpr hc0
  have h1u : PowerSeries.coeff 1 tatePowerSeries.Δ = PowerSeries.constantCoeff u := by
    rw [hXu, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul]
  have hu : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← h1u, hc1]
    exact isUnit_one
  have hΔL : (tateLaurent K).Δ = laurentOfInt K tatePowerSeries.Δ := by
    rw [tateLaurent, WeierstrassCurve.map_Δ]
  rw [hΔL, hXu, map_mul]
  refine IsUnit.mul ?_ (hu.map (laurentOfInt K))
  have hX : laurentOfInt K PowerSeries.X = HahnSeries.single (1 : ℤ) 1 := by
    rw [laurentOfInt_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  rw [hX]
  exact ⟨⟨HahnSeries.single (1 : ℤ) 1, HahnSeries.single (-1 : ℤ) 1,
    by simp [HahnSeries.single_mul_single], by simp [HahnSeries.single_mul_single]⟩, rfl⟩

end ModularCurve

end
