import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Seed.Data.Nat.Choose.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_StarBank_onePoint.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_StarBank_onePoint

set_option autoImplicit false

open _root_.Polynomial open _root_.HahnSeries open _root_.ModularCurve

namespace ModularCurve
export _root_.ModularCurve (jqModC etaProd)
namespace W1
open _root_.ModularCurve

section OnePointKit

variable {K : Type*} [Field K]

/--
@isnad1 id=eq.0h2v.s8.991b0e6b8b70 from=translated src=- shape=0782e67a vocab=2962618f
-/
theorem algebraMap_laurent_eq_single (K' : Type*) [CommRing K'] (c : K') :
    algebraMap K' (LaurentSeries K') c = HahnSeries.single (0 : ℤ) c := by
  have h1 : algebraMap K' (PowerSeries K') c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

/--
@isnad1 id=eq.0h3v.s7.93f06269cd0a from=translated src=- shape=e7ce0de1 vocab=75fbd2f7
-/
theorem leadingCoeff_laurent_pow (x : LaurentSeries K) (n : ℕ) :
    (x ^ n).leadingCoeff = x.leadingCoeff ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, HahnSeries.leadingCoeff_eq, HahnSeries.order_one,
      ← HahnSeries.single_zero_one, HahnSeries.coeff_single, ite_eq_left rfl]
  | succ n ih =>
    rw [pow_succ, pow_succ, HahnSeries.leadingCoeff_mul, ih]

/--
@isnad1 id=eq.1h3v.s7.50b31244b32c from=translated src=- shape=29cf5b97 vocab=f575f06d
-/
theorem order_laurent_pow {x : LaurentSeries K} (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).order = n • x.order := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul, HahnSeries.order_one]
  | succ n ih =>
    have hlc : (x ^ n).leadingCoeff * x.leadingCoeff ≠ 0 := by
      rw [leadingCoeff_laurent_pow]
      exact mul_ne_zero (pow_ne_zero _ (HahnSeries.leadingCoeff_ne_zero.mpr hx))
        (HahnSeries.leadingCoeff_ne_zero.mpr hx)
    rw [pow_succ, HahnSeries.order_mul_of_ne_zero hlc, ih, succ_nsmul]

/--
@isnad1 id=eq.0h4v.s8.6f982dff66f9 from=translated src=- shape=85166969 vocab=84aa2910
-/
theorem coeff_C_mul (c : K) (y : LaurentSeries K) (g : ℤ) :
    (HahnSeries.C c * y).coeff g = c * y.coeff g := by
  rw [show (HahnSeries.C c : LaurentSeries K) = HahnSeries.single 0 c from rfl,
    HahnSeries.coeff_single_mul, sub_zero]

/--
@isnad1 id=eq.1h3v.s7.be0c9be1325c from=translated src=- shape=935ec0e5 vocab=c3870633
-/
theorem coeff_C_of_ne (c : K) {g : ℤ} (hg : g ≠ 0) :
    (HahnSeries.C c : LaurentSeries K).coeff g = 0 := by
  rw [show (HahnSeries.C c : LaurentSeries K) = HahnSeries.single 0 c from rfl,
    HahnSeries.coeff_single, ite_eq_right hg]

theorem eq_C_of_pow_eq_C {x : LaurentSeries K} {γ₀ : K} {M : ℕ}
    (hM : (M : K) ≠ 0) (hγ₀ : γ₀ ≠ 0) (hx : x ^ M = HahnSeries.C γ₀) :
    ∃ γ : K, γ ≠ 0 ∧ x = HahnSeries.C γ := by
  have hM0 : M ≠ 0 := fun h => hM (by rw [h, Nat.cast_zero])
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM0] at hx
    apply hγ₀
    have h1 := congrArg (fun z : LaurentSeries K => z.coeff 0) hx.symm
    rw [show (HahnSeries.C γ₀ : LaurentSeries K) = HahnSeries.single 0 γ₀ from rfl,
      HahnSeries.coeff_single, ite_eq_left rfl] at h1
    exact h1.trans rfl

  have horder : x.order = 0 := by
    have h2 := order_laurent_pow hx0 M
    rw [hx, HahnSeries.order_C] at h2
    have h3 : (M : ℤ) * x.order = 0 := by rw [← nsmul_eq_mul]; exact h2.symm
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (Int.natCast_ne_zero.mpr hM0)
    · exact h4
  set γ : K := x.coeff 0 with hγdef
  have hγ : γ ≠ 0 := by
    rw [hγdef, ← horder]
    exact fun h => hx0 (HahnSeries.coeff_order_eq_zero.mp h)
  refine ⟨γ, hγ, ?_⟩
  by_contra hne
  have hy0 : x - HahnSeries.C γ ≠ 0 := fun h => hne (by rwa [sub_eq_zero] at h)
  set y : LaurentSeries K := x - HahnSeries.C γ with hydef
  set r : ℤ := y.order with hrdef
  have hyr : y.coeff r ≠ 0 := fun h => hy0 (HahnSeries.coeff_order_eq_zero.mp h)

  have hylow : ∀ k : ℤ, k ≤ 0 → y.coeff k = 0 := by
    intro k hk
    rcases lt_or_eq_of_le hk with hk0 | hk0
    · rw [hydef, HahnSeries.coeff_sub,
        HahnSeries.coeff_eq_zero_of_lt_order (by rw [horder]; exact hk0),
        coeff_C_of_ne γ (ne_of_lt hk0), sub_zero]
    · rw [hydef, HahnSeries.coeff_sub, hk0,
        show (HahnSeries.C γ : LaurentSeries K) = HahnSeries.single 0 γ from rfl,
        HahnSeries.coeff_single, ite_eq_left rfl, ← hγdef, sub_self]
  have hr1 : 1 ≤ r := by
    by_contra hr0
    exact hyr (hylow r (by omega))
  have hrne : r ≠ 0 := by omega

  have hxsplit : x = HahnSeries.C γ + y := by rw [hydef]; ring
  have hch : M.choose (M - 1) = M := by
    have h3 := Nat.choose_symm (show M - 1 ≤ M by omega)
    rw [show M - (M - 1) = 1 from by omega] at h3
    rw [← h3, Nat.choose_one_right]
  have hcoeffM : (x ^ M).coeff r = γ ^ (M - 1) * (M : K) * y.coeff r := by
    rw [hxsplit, add_pow, HahnSeries.coeff_sum]
    rw [Finset.sum_eq_single_of_mem (M - 1) (Finset.mem_range.mpr (by omega))
      (fun b hb hbne => ?_)]
    ·
      have h1 : M - (M - 1) = 1 := by omega
      have hC : (HahnSeries.C γ : LaurentSeries K) ^ (M - 1) * y ^ (M - (M - 1))
            * ((M.choose (M - 1) : ℕ) : LaurentSeries K)
          = HahnSeries.C (γ ^ (M - 1) * (M : K)) * y := by
        rw [h1, pow_one, hch, ← map_pow, ← map_natCast (HahnSeries.C (Γ := ℤ) (R := K)) M,
          mul_right_comm, ← map_mul]
      rw [hC, coeff_C_mul]
    ·
      have hbM : b ≤ M := by
        have := Finset.mem_range.mp hb
        omega
      rcases eq_or_ne b M with hbeq | hbM'
      ·
        subst hbeq
        rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one,
          ← map_pow, coeff_C_of_ne _ hrne]
      ·
        have hb2 : 2 ≤ M - b := by omega
        have hCb : (HahnSeries.C γ : LaurentSeries K) ^ b * y ^ (M - b)
              * ((M.choose b : ℕ) : LaurentSeries K)
            = HahnSeries.C (γ ^ b * (M.choose b : K)) * y ^ (M - b) := by
          rw [← map_pow, ← map_natCast (HahnSeries.C (Γ := ℤ) (R := K)) (M.choose b),
            mul_right_comm, ← map_mul]
        have hyb : (y ^ (M - b)).coeff r = 0 := by
          apply HahnSeries.coeff_eq_zero_of_lt_order
          rw [order_laurent_pow hy0, nsmul_eq_mul]
          have h2b : (2 : ℤ) ≤ ((M - b : ℕ) : ℤ) := by exact_mod_cast hb2
          nlinarith
        rw [hCb, coeff_C_mul, hyb, mul_zero]
  rw [hx] at hcoeffM
  rw [coeff_C_of_ne _ hrne] at hcoeffM
  exact absurd hcoeffM.symm
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hγ) hM) hyr)

end OnePointKit

end ModularCurve.W1

namespace ModularCurve export _root_.ModularCurve (jqModC etaProd) namespace StarBank end ModularCurve.StarBank
open scoped _root_.ModularCurve in

private theorem ModularCurve.StarBank.onePoint {K : Type*} [Field K] {M : ℕ}
    (hM : (M : K) ≠ 0) {c : K} (hc : c ≠ 0) {β₀ : K}
    (hstar : Polynomial.aeval (ModularCurve.jqModC K)
          (Polynomial.C c * (Polynomial.X - Polynomial.C β₀) ^ M)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24) ^ M
        = 1) :
    ∃ γ : K, γ ≠ 0 ∧
      (ModularCurve.jqModC K - HahnSeries.C β₀)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24)
        = HahnSeries.C γ := by
  set D : LaurentSeries K := HahnSeries.single (1 : ℤ) 1
    * HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24 with hD

  have haeval : Polynomial.aeval (jqModC K) (Polynomial.C c * (Polynomial.X - Polynomial.C β₀) ^ M)
      = HahnSeries.C c * (jqModC K - HahnSeries.C β₀) ^ M := by
    rw [map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C,
      ModularCurve.W1.algebraMap_laurent_eq_single K c,
      ModularCurve.W1.algebraMap_laurent_eq_single K β₀]
    rfl
  rw [haeval] at hstar

  have hgroup : HahnSeries.C c * ((jqModC K - HahnSeries.C β₀) * D) ^ M = 1 := by
    rw [mul_pow, ← mul_assoc]
    exact hstar

  have hpow : ((jqModC K - HahnSeries.C β₀) * D) ^ M = HahnSeries.C c⁻¹ := by
    have h2 := congrArg (fun z : LaurentSeries K => HahnSeries.C c⁻¹ * z) hgroup
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul, mul_one] at h2
    exact h2
  obtain ⟨γ, hγ, hxC⟩ := ModularCurve.W1.eq_C_of_pow_eq_C hM (inv_ne_zero hc) hpow
  exact ⟨γ, hγ, hxC⟩

open Polynomial HahnSeries _root_.ModularCurve _root_.P2MW.S_ModularCurve_StarBank_onePoint.ModularCurve in

/--
@isnad1 id=ex.3h4v.s11.eeb04ae63008 from=translated src=- shape=4b1cec7e vocab=a4412575
-/
theorem solution {K : Type*} [Field K] {M : ℕ}
    (hM : (M : K) ≠ 0) {c : K} (hc : c ≠ 0) {β₀ : K}
    (hstar : Polynomial.aeval (ModularCurve.jqModC K)
          (Polynomial.C c * (Polynomial.X - Polynomial.C β₀) ^ M)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24) ^ M
        = 1) :
    ∃ γ : K, γ ≠ 0 ∧
      (ModularCurve.jqModC K - HahnSeries.C β₀)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24)
        = HahnSeries.C γ :=
  ModularCurve.StarBank.onePoint hM hc hstar

