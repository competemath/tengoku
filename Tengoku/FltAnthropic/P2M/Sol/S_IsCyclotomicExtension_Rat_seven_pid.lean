import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.PID
import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Ideal
import Tengoku.Seed.Analysis.Real.Pi.Bounds
import Tengoku.Seed.Tactic.IntervalCases
import Tengoku.Seed.Tactic.NormNum.Prime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`, 1 `p2m_open_scoped`, 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsCyclotomicExtension_Rat_seven_pid

namespace SevenPidPort

open _root_.NumberField open _root_.Module open _root_.NumberField.InfinitePlace open _root_.Nat open _root_.Real open _root_.RingOfIntegers open _root_.NumberField.RingOfIntegers open _root_.Finset open _root_.IsCyclotomicExtension.Rat open _root_.Polynomial open _root_.Real.Polynomial open _root_.Polynomial.cyclotomic open _root_.Ideal open _root_.NumberField.Ideal

open scoped _root_.NumberField _root_.NumberField.InfinitePlace.NumberField

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

scoped instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

lemma floor_minkowskiBound_seven : ⌊(4 / π) ^ 3 * (6! / 6 ^ 6 * √16807)⌋₊ = 4 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 3 * (6! / 6 ^ 6 * √16807) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 3 * (6! / 6 ^ 6 * 129) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 4 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 3 * (6! / 6 ^ 6 * √16807) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 3 * (6! / 6 ^ 6 * 130) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ _ := by norm_num

variable [IsCyclotomicExtension {7} ℚ K]

theorem floor_M_seven : ⌊(M K)⌋₊ = 4 := by
  rw [discr_prime 7 K, IsCyclotomicExtension.finrank (n := 7) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 7, totient_prime
      (by norm_num)]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact floor_minkowskiBound_seven

lemma orderOf_two_zmod_seven : orderOf ((2 : ℕ) : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm' ↦ ?_⟩
  interval_cases m <;> decide

lemma orderOf_three_zmod_seven : orderOf ((3 : ℕ) : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm' ↦ ?_⟩
  interval_cases m <;> decide

variable (K) in

theorem seven_pid : IsPrincipalIdealRing (𝓞 K) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (fun p hple hp P hPmem hle ↦ ?_)
  exfalso
  rw [floor_M_seven] at hple hle
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : P.IsPrime := hPmem.1
  haveI : P.LiesOver (span {(p : ℤ)}) := hPmem.2
  obtain ⟨hp1, hp4⟩ := Finset.mem_Icc.mp hple
  interval_cases p
  · exact Nat.not_prime_one hp
  · rw [inertiaDeg_eq_of_not_dvd 2 K P (m := 7) (by norm_num),
      orderOf_two_zmod_seven] at hle
    norm_num at hle
  · rw [inertiaDeg_eq_of_not_dvd 3 K P (m := 7) (by norm_num),
      orderOf_three_zmod_seven] at hle
    norm_num at hle
  · norm_num at hp

end SevenPidPort
open scoped _root_.P2MW.S_IsCyclotomicExtension_Rat_seven_pid.SevenPidPort

open scoped NumberField in
theorem solution (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K] :
    IsPrincipalIdealRing (𝓞 K) :=
  SevenPidPort.seven_pid K
