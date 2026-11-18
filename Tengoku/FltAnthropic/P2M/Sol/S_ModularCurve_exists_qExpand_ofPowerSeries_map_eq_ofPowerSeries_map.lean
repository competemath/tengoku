import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_qExpand_ofPowerSeries_map_eq_ofPowerSeries_map.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_qExpand_ofPowerSeries_map_eq_ofPowerSeries_map

set_option autoImplicit false

namespace ModularCurve
export _root_.ModularCurve (qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd)
namespace BetaGauss
open _root_.ModularCurve

open PowerSeries

variable {A : Type*} [CommRing A]

noncomputable def expandPS (N : ℕ) (x : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => if N ∣ n then PowerSeries.coeff (n / N) x else 0

theorem coeff_expandPS (N : ℕ) (x : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (expandPS N x) = if N ∣ n then PowerSeries.coeff (n / N) x else 0 := by
  rw [expandPS, PowerSeries.coeff_mk]

theorem coeff_expandPS_mul (N : ℕ) [NeZero N] (x : PowerSeries A) (m : ℕ) :
    PowerSeries.coeff (N * m) (expandPS N x) = PowerSeries.coeff m x := by
  rw [coeff_expandPS, ite_eq_left (dvd_mul_right N m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (NeZero.ne N))]

theorem map_expandPS {B : Type*} [CommRing B] (φ : A →+* B) (N : ℕ) (x : PowerSeries A) :
    (expandPS N x).map φ = expandPS N (x.map φ) := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_expandPS]
  split_ifs <;> simp

theorem expandPS_eq_zero_iff (N : ℕ) [NeZero N] (x : PowerSeries A) : expandPS N x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext m
    have := congrArg (PowerSeries.coeff (N * m)) h
    rwa [coeff_expandPS_mul, map_zero] at this
  · rintro rfl
    ext n
    rw [coeff_expandPS]
    split_ifs <;> simp

theorem coeff_ofPowerSeries {R : Type*} [CommRing R] (y : PowerSeries R) (k : ℤ) :
    (HahnSeries.ofPowerSeries ℤ R y).coeff k = if 0 ≤ k then PowerSeries.coeff k.toNat y else 0 := by
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [Int.toNat_natCast]
    exact HahnSeries.ofPowerSeries_apply_coeff y n
  · apply HahnSeries.embDomain_of_notMem_range
    rintro ⟨n, hn⟩
    apply hk
    have : (n : ℤ) = k := by simpa using hn
    omega

theorem qExpand_ofPowerSeries {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (y : PowerSeries R) :
    ModularCurve.qExpand R N (HahnSeries.ofPowerSeries ℤ R y) = HahnSeries.ofPowerSeries ℤ R (expandPS N y) := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.qExpand_coeff_mul, coeff_ofPowerSeries, coeff_ofPowerSeries]
    by_cases hm : 0 ≤ m
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      have htn : ((N : ℤ) * (n : ℤ)).toNat = N * n := by rw [← Nat.cast_mul, Int.toNat_natCast]
      rw [ite_eq_left hm, ite_eq_left (by positivity), Int.toNat_natCast, htn, coeff_expandPS_mul]
    · rw [ite_eq_right hm, ite_eq_right]
      intro h
      exact hm ((mul_nonneg_iff_of_pos_left hN).mp h)
  · rw [ModularCurve.qExpand_coeff_of_not_dvd N _ hk, coeff_ofPowerSeries]
    split_ifs with h0
    · rw [coeff_expandPS, ite_eq_right]
      intro hd
      apply hk
      obtain ⟨c, hc⟩ := hd
      refine ⟨c, ?_⟩
      have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg h0
      rw [← this, hc]; push_cast; ring
    · rfl

end ModularCurve.BetaGauss

theorem solution
    (A : Type*) [CommRing A] (L : Type*) [Field L] [Algebra A L] (N : ℕ) [NeZero N] (x : PowerSeries A) :
    ∃ x' : PowerSeries A,
      (∀ n : ℕ, PowerSeries.coeff n x' = if N ∣ n then PowerSeries.coeff (n / N) x else 0) ∧
      ModularCurve.qExpand L N (HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) =
        HahnSeries.ofPowerSeries ℤ L (x'.map (algebraMap A L)) ∧
      ∀ (B : Type*) [CommRing B] (φ : A →+* B), x'.map φ = 0 ↔ x.map φ = 0 := by
  refine ⟨ModularCurve.BetaGauss.expandPS N x, ModularCurve.BetaGauss.coeff_expandPS N x, ?_, ?_⟩
  · rw [ModularCurve.BetaGauss.qExpand_ofPowerSeries, ModularCurve.BetaGauss.map_expandPS]
  · intro B _ φ
    rw [ModularCurve.BetaGauss.map_expandPS, ModularCurve.BetaGauss.expandPS_eq_zero_iff]
