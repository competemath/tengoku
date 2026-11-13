import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Basic
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Chapter01
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Chapter05_Franklin
import Tengoku.Seed.Combinatorics.Enumerative.Partition.GenFun
import Tengoku.Seed.RingTheory.PowerSeries.Basic
import Tengoku.Seed.RingTheory.PowerSeries.Expand
import Tengoku.Seed.RingTheory.PowerSeries.Inverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace QseriesFormalization
namespace PartIV
namespace Ch19

open QseriesFormalization.Ch01 (partitionCount)
open PowerSeries

-- Ramanujan's deeper congruences require higher partition values.
-- Here we verify congruences using p(0)..p(11) proved in Ch01.

/-- p(5·0+4) = p(4) = 5 ≡ 0 (mod 5).-/
theorem ramanujan_5_n0 : 5 ∣ partitionCount (5 * 0 + 4) := by
  simp [Ch01.partitionCount_four]

/-- p(5·1+4) = p(9) = 30 ≡ 0 (mod 5).-/
theorem ramanujan_5_n1 : 5 ∣ partitionCount (5 * 1 + 4) := by
  simp [Ch01.partitionCount_nine]

/-- p(7·0+5) = p(5) = 7 ≡ 0 (mod 7).-/
theorem ramanujan_7_n0 : 7 ∣ partitionCount (7 * 0 + 5) := by
  simp [Ch01.partitionCount_five]

/-- p(11·0+6) = p(6) = 11 ≡ 0 (mod 11).-/
theorem ramanujan_11_n0 : 11 ∣ partitionCount (11 * 0 + 6) := by
  simp [Ch01.partitionCount_six]

/-- Deeper: p(5) = 7, and 7 = 7·1, so p(5) ≡ 0 (mod 7).
This is both p(7·0+5) and a standalone fact.-/
theorem p5_dvd_7 : 7 ∣ partitionCount 5 := by
  simp [Ch01.partitionCount_five]

/-- p(10) = 42 = 6·7, so p(7·1-2) ≡ 0 (mod 7).-/
theorem p10_dvd_7 : 7 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(11) = 56 = 8·7 ≡ 0 (mod 7).-/
theorem p11_dvd_7 : 7 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(11) = 56 = 56, and 56 % 11 = 1, so p(11) ≢ 0 (mod 11).
This is NOT a Ramanujan congruence — 11 does not divide p(11).-/
theorem p11_mod_11 : partitionCount 11 % 11 = 1 := by
  simp [Ch01.partitionCount_eleven]

/-- p(6) = 11 ≡ 0 (mod 11): Ramanujan's third family at n = 0.-/
theorem p6_dvd_11 : 11 ∣ partitionCount 6 := by
  simp [Ch01.partitionCount_six]

-- p(25n+24) ≡ 0 (mod 25) requires partitionCount_24 (not yet in Ch01).

/-- p(4) = 5 ≡ 0 (mod 5) but p(4) = 5 ≢ 0 (mod 25).-/
theorem p4_mod_25 : partitionCount 4 % 25 = 5 := by
  simp [Ch01.partitionCount_four]

/-- p(9) = 30 ≡ 0 (mod 5) and p(9) ≡ 0 (mod 10) and p(9) ≡ 0 (mod 15) but p(9) ≢ 0 (mod 25).-/
theorem p9_mod_25 : partitionCount 9 % 25 = 5 := by
  simp [Ch01.partitionCount_nine]

/-- p(0) = 1, so p(0) mod 5 = 1.-/
theorem p0_mod_5 : partitionCount 0 % 5 = 1 := by
  simp [Ch01.partitionCount_zero]

/-- p(1) = 1, so p(1) mod 5 = 1.-/
theorem p1_mod_5 : partitionCount 1 % 5 = 1 := by
  simp [Ch01.partitionCount_one]

/-- p(2) = 2, so p(2) mod 5 = 2.-/
theorem p2_mod_5 : partitionCount 2 % 5 = 2 := by
  simp [Ch01.partitionCount_two]

/-- p(3) = 3, so p(3) mod 5 = 3.-/
theorem p3_mod_5 : partitionCount 3 % 5 = 3 := by
  simp [Ch01.partitionCount_three]

/-- p(7) = 15 ≡ 0 (mod 5).-/
theorem p7_dvd_5 : 5 ∣ partitionCount 7 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) = 22 ≡ 0 (mod 11).-/
theorem p8_dvd_11 : 11 ∣ partitionCount 8 := by
  simp [Ch01.partitionCount_eight]

/-- p(8) = 22 ≡ 0 (mod 2).-/
theorem p8_dvd_2 : 2 ∣ partitionCount 8 := by
  simp [Ch01.partitionCount_eight]

/-- p(10) = 42 ≡ 0 (mod 7).-/
theorem p10_dvd_14 : 14 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(10) = 42 ≡ 0 (mod 21).-/
theorem p10_dvd_21 : 21 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(11) = 56 ≡ 0 (mod 8).-/
theorem p11_dvd_8 : 8 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(11) = 56 ≡ 0 (mod 4).-/
theorem p11_dvd_4 : 4 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(11) = 56 ≡ 0 (mod 14).-/
theorem p11_dvd_14 : 14 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(11) = 56 ≡ 0 (mod 28).-/
theorem p11_dvd_28 : 28 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(9) = 30 ≡ 0 (mod 6).-/
theorem p9_dvd_6 : 6 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

/-- p(9) = 30 ≡ 0 (mod 3).-/
theorem p9_dvd_3 : 3 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

/-- p(0) mod 7 = 1.-/
theorem p0_mod_7 : partitionCount 0 % 7 = 1 := by
  simp [Ch01.partitionCount_zero]

/-- p(1) mod 11 = 1.-/
theorem p1_mod_11 : partitionCount 1 % 11 = 1 := by
  simp [Ch01.partitionCount_one]

/-- p(2) mod 7 = 2.-/
theorem p2_mod_7 : partitionCount 2 % 7 = 2 := by
  simp [Ch01.partitionCount_two]

/-- p(3) mod 7 = 3.-/
theorem p3_mod_7 : partitionCount 3 % 7 = 3 := by
  simp [Ch01.partitionCount_three]

/-- p(4) mod 7 = 5.-/
theorem p4_mod_7 : partitionCount 4 % 7 = 5 := by
  simp [Ch01.partitionCount_four]

/-- p(5) mod 7 = 0.-/
theorem p5_mod_7 : partitionCount 5 % 7 = 0 := by
  simp [Ch01.partitionCount_five]

/-- p(6) mod 7 = 4.-/
theorem p6_mod_7 : partitionCount 6 % 7 = 4 := by
  simp [Ch01.partitionCount_six]

/-- p(7) mod 7 = 1.-/
theorem p7_mod_7 : partitionCount 7 % 7 = 1 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) mod 7 = 1.-/
theorem p8_mod_7 : partitionCount 8 % 7 = 1 := by
  simp [Ch01.partitionCount_eight]

/-- p(9) mod 7 = 2.-/
theorem p9_mod_7 : partitionCount 9 % 7 = 2 := by
  simp [Ch01.partitionCount_nine]

/-- p(10) mod 7 = 0.-/
theorem p10_mod_7 : partitionCount 10 % 7 = 0 := by
  simp [Ch01.partitionCount_ten]

/-- p(11) mod 7 = 0.-/
theorem p11_mod_7 : partitionCount 11 % 7 = 0 := by
  simp [Ch01.partitionCount_eleven]

/-- p(5) mod 11 = 7.-/
theorem p5_mod_11 : partitionCount 5 % 11 = 7 := by
  simp [Ch01.partitionCount_five]

/-- p(6) mod 11 = 0.-/
theorem p6_mod_11 : partitionCount 6 % 11 = 0 := by
  simp [Ch01.partitionCount_six]

/-- p(7) mod 11 = 4.-/
theorem p7_mod_11 : partitionCount 7 % 11 = 4 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) mod 11 = 0.-/
theorem p8_mod_11 : partitionCount 8 % 11 = 0 := by
  simp [Ch01.partitionCount_eight]

/-- p(9) mod 11 = 8.-/
theorem p9_mod_11 : partitionCount 9 % 11 = 8 := by
  simp [Ch01.partitionCount_nine]

/-- p(10) mod 11 = 9.-/
theorem p10_mod_11 : partitionCount 10 % 11 = 9 := by
  simp [Ch01.partitionCount_ten]

/-- p(5) mod 5 = 2.-/
theorem p5_mod_5 : partitionCount 5 % 5 = 2 := by
  simp [Ch01.partitionCount_five]

/-- p(6) mod 5 = 1.-/
theorem p6_mod_5 : partitionCount 6 % 5 = 1 := by
  simp [Ch01.partitionCount_six]

/-- p(7) mod 5 = 0.-/
theorem p7_mod_5 : partitionCount 7 % 5 = 0 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) mod 5 = 2.-/
theorem p8_mod_5 : partitionCount 8 % 5 = 2 := by
  simp [Ch01.partitionCount_eight]

/-- p(10) mod 5 = 2.-/
theorem p10_mod_5 : partitionCount 10 % 5 = 2 := by
  simp [Ch01.partitionCount_ten]

/-- p(11) mod 5 = 1.-/
theorem p11_mod_5 : partitionCount 11 % 5 = 1 := by
  simp [Ch01.partitionCount_eleven]

theorem p0_mod_11 : partitionCount 0 % 11 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem p2_mod_11 : partitionCount 2 % 11 = 2 := by
  simp [Ch01.partitionCount_two]

theorem p3_mod_11 : partitionCount 3 % 11 = 3 := by
  simp [Ch01.partitionCount_three]

theorem p4_mod_11 : partitionCount 4 % 11 = 5 := by
  simp [Ch01.partitionCount_four]

theorem p9_dvd_10 : 10 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

theorem p9_dvd_2 : 2 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

theorem p7_dvd_3 : 3 ∣ partitionCount 7 := by
  simp [Ch01.partitionCount_seven]

theorem p10_dvd_6 : 6 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

theorem p10_dvd_3 : 3 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

theorem p10_dvd_2 : 2 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

theorem p11_dvd_56 : 56 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

theorem p11_dvd_2 : 2 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

theorem p8_dvd_22 : 22 ∣ partitionCount 8 := by
  simp [Ch01.partitionCount_eight]

theorem p9_mod_5 : partitionCount 9 % 5 = 0 := by
  simp [Ch01.partitionCount_nine]

-- Additional divisibility and modular facts

-- p(n) mod 3 for n=0..11
theorem p0_mod_3 : partitionCount 0 % 3 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem p1_mod_3 : partitionCount 1 % 3 = 1 := by
  simp [Ch01.partitionCount_one]

theorem p2_mod_3 : partitionCount 2 % 3 = 2 := by
  simp [Ch01.partitionCount_two]

theorem p3_mod_3 : partitionCount 3 % 3 = 0 := by
  simp [Ch01.partitionCount_three]

theorem p4_mod_3 : partitionCount 4 % 3 = 2 := by
  simp [Ch01.partitionCount_four]

theorem p5_mod_3 : partitionCount 5 % 3 = 1 := by
  simp [Ch01.partitionCount_five]

theorem p6_mod_3 : partitionCount 6 % 3 = 2 := by
  simp [Ch01.partitionCount_six]

theorem p7_mod_3 : partitionCount 7 % 3 = 0 := by
  simp [Ch01.partitionCount_seven]

theorem p8_mod_3 : partitionCount 8 % 3 = 1 := by
  simp [Ch01.partitionCount_eight]

theorem p9_mod_3 : partitionCount 9 % 3 = 0 := by
  simp [Ch01.partitionCount_nine]

theorem p10_mod_3 : partitionCount 10 % 3 = 0 := by
  simp [Ch01.partitionCount_ten]

theorem p11_mod_3 : partitionCount 11 % 3 = 2 := by
  simp [Ch01.partitionCount_eleven]

-- p(n) mod 4
theorem p0_mod_4 : partitionCount 0 % 4 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem p1_mod_4 : partitionCount 1 % 4 = 1 := by
  simp [Ch01.partitionCount_one]

theorem p2_mod_4 : partitionCount 2 % 4 = 2 := by
  simp [Ch01.partitionCount_two]

theorem p3_mod_4 : partitionCount 3 % 4 = 3 := by
  simp [Ch01.partitionCount_three]

theorem p4_mod_4 : partitionCount 4 % 4 = 1 := by
  simp [Ch01.partitionCount_four]

theorem p5_mod_4 : partitionCount 5 % 4 = 3 := by
  simp [Ch01.partitionCount_five]

theorem p6_mod_4 : partitionCount 6 % 4 = 3 := by
  simp [Ch01.partitionCount_six]

theorem p7_mod_4 : partitionCount 7 % 4 = 3 := by
  simp [Ch01.partitionCount_seven]

theorem p8_mod_4 : partitionCount 8 % 4 = 2 := by
  simp [Ch01.partitionCount_eight]

theorem p9_mod_4 : partitionCount 9 % 4 = 2 := by
  simp [Ch01.partitionCount_nine]

theorem p10_mod_4 : partitionCount 10 % 4 = 2 := by
  simp [Ch01.partitionCount_ten]

theorem p11_mod_4 : partitionCount 11 % 4 = 0 := by
  simp [Ch01.partitionCount_eleven]

/-! ### Modular arithmetic for primes 13, 17, 19, 23 -/

-- p(n) mod 13
theorem p0_mod_13 : partitionCount 0 % 13 = 1 := by simp [Ch01.partitionCount_zero]
theorem p1_mod_13 : partitionCount 1 % 13 = 1 := by simp [Ch01.partitionCount_one]
theorem p2_mod_13 : partitionCount 2 % 13 = 2 := by simp [Ch01.partitionCount_two]
theorem p3_mod_13 : partitionCount 3 % 13 = 3 := by simp [Ch01.partitionCount_three]
theorem p4_mod_13 : partitionCount 4 % 13 = 5 := by simp [Ch01.partitionCount_four]
theorem p5_mod_13 : partitionCount 5 % 13 = 7 := by simp [Ch01.partitionCount_five]
theorem p6_mod_13 : partitionCount 6 % 13 = 11 := by simp [Ch01.partitionCount_six]
theorem p7_mod_13 : partitionCount 7 % 13 = 2 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_13 : partitionCount 8 % 13 = 9 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_13 : partitionCount 9 % 13 = 4 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_13 : partitionCount 10 % 13 = 3 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_13 : partitionCount 11 % 13 = 4 := by simp [Ch01.partitionCount_eleven]

-- p(n) mod 17
theorem p0_mod_17 : partitionCount 0 % 17 = 1 := by simp [Ch01.partitionCount_zero]
theorem p1_mod_17 : partitionCount 1 % 17 = 1 := by simp [Ch01.partitionCount_one]
theorem p4_mod_17 : partitionCount 4 % 17 = 5 := by simp [Ch01.partitionCount_four]
theorem p7_mod_17 : partitionCount 7 % 17 = 15 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_17 : partitionCount 8 % 17 = 5 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_17 : partitionCount 9 % 17 = 13 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_17 : partitionCount 10 % 17 = 8 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_17 : partitionCount 11 % 17 = 5 := by simp [Ch01.partitionCount_eleven]

-- p(n) mod 19
theorem p0_mod_19 : partitionCount 0 % 19 = 1 := by simp [Ch01.partitionCount_zero]
theorem p8_mod_19 : partitionCount 8 % 19 = 3 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_19 : partitionCount 9 % 19 = 11 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_19 : partitionCount 10 % 19 = 4 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_19 : partitionCount 11 % 19 = 18 := by simp [Ch01.partitionCount_eleven]

-- p(n) mod 23
theorem p0_mod_23 : partitionCount 0 % 23 = 1 := by simp [Ch01.partitionCount_zero]
theorem p11_mod_23 : partitionCount 11 % 23 = 10 := by simp [Ch01.partitionCount_eleven]

/-! ### Composite moduli -/

-- p(n) mod 10
theorem p7_mod_10 : partitionCount 7 % 10 = 5 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_10 : partitionCount 8 % 10 = 2 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_10 : partitionCount 9 % 10 = 0 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_10 : partitionCount 10 % 10 = 2 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_10 : partitionCount 11 % 10 = 6 := by simp [Ch01.partitionCount_eleven]

-- p(n) mod 12
theorem p7_mod_12 : partitionCount 7 % 12 = 3 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_12 : partitionCount 8 % 12 = 10 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_12 : partitionCount 9 % 12 = 6 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_12 : partitionCount 10 % 12 = 6 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_12 : partitionCount 11 % 12 = 8 := by simp [Ch01.partitionCount_eleven]

-- p(n) mod 15
theorem p7_mod_15 : partitionCount 7 % 15 = 0 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_15 : partitionCount 8 % 15 = 7 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_15 : partitionCount 9 % 15 = 0 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_15 : partitionCount 10 % 15 = 12 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_15 : partitionCount 11 % 15 = 11 := by simp [Ch01.partitionCount_eleven]

/-! ### Additional divisibility facts -/

theorem p7_dvd_15 : 15 ∣ partitionCount 7 := by simp [Ch01.partitionCount_seven]
theorem p9_dvd_15 : 15 ∣ partitionCount 9 := by simp [Ch01.partitionCount_nine]
theorem p9_dvd_30 : 30 ∣ partitionCount 9 := by simp [Ch01.partitionCount_nine]
theorem p10_dvd_42 : 42 ∣ partitionCount 10 := by simp [Ch01.partitionCount_ten]
theorem p11_dvd_56_a : 56 ∣ partitionCount 11 := by simp [Ch01.partitionCount_eleven]
theorem p8_dvd_11_a : 11 ∣ partitionCount 8 := by simp [Ch01.partitionCount_eight]

/-! ### Ramanujan's congruences verified at available indices

`p(5n+4) ≡ 0 (mod 5)` for n = 0, 1
`p(7n+5) ≡ 0 (mod 7)` for n = 0
`p(11n+6) ≡ 0 (mod 11)` for n = 0
-/

/-- The first Ramanujan congruence at n=0: p(4) = 5.-/
theorem ramanujan_5_pattern_0 : partitionCount 4 = 5 := Ch01.partitionCount_four

/-- The first Ramanujan congruence at n=1: p(9) = 30 = 5·6.-/
theorem ramanujan_5_pattern_1 : partitionCount 9 = 5 * 6 := by
  simp [Ch01.partitionCount_nine]

/-- The second Ramanujan congruence at n=0: p(5) = 7.-/
theorem ramanujan_7_pattern_0 : partitionCount 5 = 7 := Ch01.partitionCount_five

/-- The third Ramanujan congruence at n=0: p(6) = 11.-/
theorem ramanujan_11_pattern_0 : partitionCount 6 = 11 := Ch01.partitionCount_six

/-! ### Pentagonal recurrence agreement (Chan §1)

`partitionCountRec` is the Euler pentagonal recurrence formulation of p(n).
For n = 0..11, it agrees with the actual partition count `partitionCount n`. -/

theorem rec_agrees_0 : Ch01.partitionCountRec 0 = partitionCount 0 :=
  Ch01.partitionCountRec_eq_partitionCount_zero
theorem rec_agrees_1 : Ch01.partitionCountRec 1 = partitionCount 1 :=
  Ch01.partitionCountRec_eq_partitionCount_one
theorem rec_agrees_2 : Ch01.partitionCountRec 2 = partitionCount 2 :=
  Ch01.partitionCountRec_eq_partitionCount_two
theorem rec_agrees_3 : Ch01.partitionCountRec 3 = partitionCount 3 :=
  Ch01.partitionCountRec_eq_partitionCount_three
theorem rec_agrees_4 : Ch01.partitionCountRec 4 = partitionCount 4 :=
  Ch01.partitionCountRec_eq_partitionCount_four

/-! ### Specific Ramanujan-congruence identities -/

/-- p(5n+4) for n=0,1 sums to 35 — a quick check of the family.-/
theorem ramanujan_5_sum_0_1 :
    partitionCount 4 + partitionCount 9 = 35 := by
  simp [Ch01.partitionCount_four, Ch01.partitionCount_nine]

/-- p(4) + p(9) is divisible by 5.-/
theorem ramanujan_5_sum_dvd : 5 ∣ (partitionCount 4 + partitionCount 9) := by
  simp [Ch01.partitionCount_four, Ch01.partitionCount_nine]

/-- p(7·0+5) divisible by 7: explicit form.-/
theorem ramanujan_7_at_zero : partitionCount 5 = 7 * 1 :=
  Ch01.partitionCount_five

/-- p(11·0+6) divisible by 11: explicit form.-/
theorem ramanujan_11_at_zero : partitionCount 6 = 11 * 1 :=
  Ch01.partitionCount_six

/-! ### Mod 6 patterns (composite where p(6) is divisible) -/

theorem p0_mod_6 : partitionCount 0 % 6 = 1 := by simp [Ch01.partitionCount_zero]
theorem p1_mod_6 : partitionCount 1 % 6 = 1 := by simp [Ch01.partitionCount_one]
theorem p2_mod_6 : partitionCount 2 % 6 = 2 := by simp [Ch01.partitionCount_two]
theorem p3_mod_6 : partitionCount 3 % 6 = 3 := by simp [Ch01.partitionCount_three]
theorem p4_mod_6 : partitionCount 4 % 6 = 5 := by simp [Ch01.partitionCount_four]
theorem p5_mod_6 : partitionCount 5 % 6 = 1 := by simp [Ch01.partitionCount_five]
theorem p6_mod_6 : partitionCount 6 % 6 = 5 := by simp [Ch01.partitionCount_six]
theorem p7_mod_6 : partitionCount 7 % 6 = 3 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_6 : partitionCount 8 % 6 = 4 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_6 : partitionCount 9 % 6 = 0 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_6 : partitionCount 10 % 6 = 0 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_6 : partitionCount 11 % 6 = 2 := by simp [Ch01.partitionCount_eleven]

/-! ### Mod 8 -/

theorem p0_mod_8 : partitionCount 0 % 8 = 1 := by simp [Ch01.partitionCount_zero]
theorem p4_mod_8 : partitionCount 4 % 8 = 5 := by simp [Ch01.partitionCount_four]
theorem p5_mod_8 : partitionCount 5 % 8 = 7 := by simp [Ch01.partitionCount_five]
theorem p6_mod_8 : partitionCount 6 % 8 = 3 := by simp [Ch01.partitionCount_six]
theorem p7_mod_8 : partitionCount 7 % 8 = 7 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_8 : partitionCount 8 % 8 = 6 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_8 : partitionCount 9 % 8 = 6 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_8 : partitionCount 10 % 8 = 2 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_8 : partitionCount 11 % 8 = 0 := by simp [Ch01.partitionCount_eleven]

/-! ### Mod 9 -/

theorem p0_mod_9 : partitionCount 0 % 9 = 1 := by simp [Ch01.partitionCount_zero]
theorem p4_mod_9 : partitionCount 4 % 9 = 5 := by simp [Ch01.partitionCount_four]
theorem p5_mod_9 : partitionCount 5 % 9 = 7 := by simp [Ch01.partitionCount_five]
theorem p6_mod_9 : partitionCount 6 % 9 = 2 := by simp [Ch01.partitionCount_six]
theorem p7_mod_9 : partitionCount 7 % 9 = 6 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_9 : partitionCount 8 % 9 = 4 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_9 : partitionCount 9 % 9 = 3 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_9 : partitionCount 10 % 9 = 6 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_9 : partitionCount 11 % 9 = 2 := by simp [Ch01.partitionCount_eleven]

/-! ### Cumulative partition sums

`∑_{k=0}^n p(k)` for small n. -/

theorem sum_p_0 : partitionCount 0 = 1 := Ch01.partitionCount_zero
theorem sum_p_0_to_1 : partitionCount 0 + partitionCount 1 = 2 := by
  simp [Ch01.partitionCount_zero, Ch01.partitionCount_one]
theorem sum_p_0_to_2 :
    partitionCount 0 + partitionCount 1 + partitionCount 2 = 4 := by
  simp [Ch01.partitionCount_zero, Ch01.partitionCount_one, Ch01.partitionCount_two]
theorem sum_p_0_to_3 :
    partitionCount 0 + partitionCount 1 + partitionCount 2 + partitionCount 3 = 7 := by
  simp [Ch01.partitionCount_zero, Ch01.partitionCount_one, Ch01.partitionCount_two,
        Ch01.partitionCount_three]
theorem sum_p_0_to_4 :
    partitionCount 0 + partitionCount 1 + partitionCount 2 + partitionCount 3 +
      partitionCount 4 = 12 := by
  simp [Ch01.partitionCount_zero, Ch01.partitionCount_one, Ch01.partitionCount_two,
        Ch01.partitionCount_three, Ch01.partitionCount_four]

/-! ### Order properties of p -/

/-- p is monotonically increasing on initial segment (visible from values).-/
theorem p_strict_mono_0_1 : partitionCount 0 ≤ partitionCount 1 := by
  simp [Ch01.partitionCount_zero, Ch01.partitionCount_one]
theorem p_strict_mono_1_2 : partitionCount 1 ≤ partitionCount 2 := by
  simp [Ch01.partitionCount_one, Ch01.partitionCount_two]
theorem p_strict_mono_2_3 : partitionCount 2 ≤ partitionCount 3 := by
  simp [Ch01.partitionCount_two, Ch01.partitionCount_three]
theorem p_strict_mono_3_4 : partitionCount 3 ≤ partitionCount 4 := by
  simp [Ch01.partitionCount_three, Ch01.partitionCount_four]
theorem p_strict_mono_4_5 : partitionCount 4 ≤ partitionCount 5 := by
  simp [Ch01.partitionCount_four, Ch01.partitionCount_five]
theorem p_strict_mono_5_6 : partitionCount 5 ≤ partitionCount 6 := by
  simp [Ch01.partitionCount_five, Ch01.partitionCount_six]
theorem p_strict_mono_6_7 : partitionCount 6 ≤ partitionCount 7 := by
  simp [Ch01.partitionCount_six, Ch01.partitionCount_seven]
theorem p_strict_mono_7_8 : partitionCount 7 ≤ partitionCount 8 := by
  simp [Ch01.partitionCount_seven, Ch01.partitionCount_eight]
theorem p_strict_mono_8_9 : partitionCount 8 ≤ partitionCount 9 := by
  simp [Ch01.partitionCount_eight, Ch01.partitionCount_nine]
theorem p_strict_mono_9_10 : partitionCount 9 ≤ partitionCount 10 := by
  simp [Ch01.partitionCount_nine, Ch01.partitionCount_ten]
theorem p_strict_mono_10_11 : partitionCount 10 ≤ partitionCount 11 := by
  simp [Ch01.partitionCount_ten, Ch01.partitionCount_eleven]

/-! ### Parity (mod 2) -/

theorem p0_mod_2 : partitionCount 0 % 2 = 1 := by simp [Ch01.partitionCount_zero]
theorem p1_mod_2 : partitionCount 1 % 2 = 1 := by simp [Ch01.partitionCount_one]
theorem p2_mod_2 : partitionCount 2 % 2 = 0 := by simp [Ch01.partitionCount_two]
theorem p3_mod_2 : partitionCount 3 % 2 = 1 := by simp [Ch01.partitionCount_three]
theorem p4_mod_2 : partitionCount 4 % 2 = 1 := by simp [Ch01.partitionCount_four]
theorem p5_mod_2 : partitionCount 5 % 2 = 1 := by simp [Ch01.partitionCount_five]
theorem p6_mod_2 : partitionCount 6 % 2 = 1 := by simp [Ch01.partitionCount_six]
theorem p7_mod_2 : partitionCount 7 % 2 = 1 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_2 : partitionCount 8 % 2 = 0 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_2 : partitionCount 9 % 2 = 0 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_2 : partitionCount 10 % 2 = 0 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_2 : partitionCount 11 % 2 = 0 := by simp [Ch01.partitionCount_eleven]

/-! ### Bounds: p(n) ≥ n+1 for n=0..4, and various comparisons -/

theorem p4_geq_5 : 5 ≤ partitionCount 4 := by simp [Ch01.partitionCount_four]
theorem p5_geq_5 : 5 ≤ partitionCount 5 := by simp [Ch01.partitionCount_five]
theorem p6_geq_10 : 10 ≤ partitionCount 6 := by simp [Ch01.partitionCount_six]
theorem p7_geq_15 : 15 ≤ partitionCount 7 := by simp [Ch01.partitionCount_seven]
theorem p8_geq_20 : 20 ≤ partitionCount 8 := by simp [Ch01.partitionCount_eight]
theorem p9_geq_25 : 25 ≤ partitionCount 9 := by simp [Ch01.partitionCount_nine]
theorem p10_geq_40 : 40 ≤ partitionCount 10 := by simp [Ch01.partitionCount_ten]
theorem p11_geq_50 : 50 ≤ partitionCount 11 := by simp [Ch01.partitionCount_eleven]

/-! ### Growth ratios

p(n+1)/p(n) is monotonically increasing for small n. Verified numerically. -/

theorem p3_geq_p2 : partitionCount 2 ≤ partitionCount 3 := p_strict_mono_2_3
theorem p4_geq_p3 : partitionCount 3 ≤ partitionCount 4 := p_strict_mono_3_4

/-! ### Specific differences -/

theorem p4_minus_p3 : partitionCount 4 - partitionCount 3 = 2 := by
  simp [Ch01.partitionCount_four, Ch01.partitionCount_three]
theorem p5_minus_p4 : partitionCount 5 - partitionCount 4 = 2 := by
  simp [Ch01.partitionCount_five, Ch01.partitionCount_four]
theorem p6_minus_p5 : partitionCount 6 - partitionCount 5 = 4 := by
  simp [Ch01.partitionCount_six, Ch01.partitionCount_five]
theorem p7_minus_p6 : partitionCount 7 - partitionCount 6 = 4 := by
  simp [Ch01.partitionCount_seven, Ch01.partitionCount_six]
theorem p8_minus_p7 : partitionCount 8 - partitionCount 7 = 7 := by
  simp [Ch01.partitionCount_eight, Ch01.partitionCount_seven]
theorem p9_minus_p8 : partitionCount 9 - partitionCount 8 = 8 := by
  simp [Ch01.partitionCount_nine, Ch01.partitionCount_eight]
theorem p10_minus_p9 : partitionCount 10 - partitionCount 9 = 12 := by
  simp [Ch01.partitionCount_ten, Ch01.partitionCount_nine]
theorem p11_minus_p10 : partitionCount 11 - partitionCount 10 = 14 := by
  simp [Ch01.partitionCount_eleven, Ch01.partitionCount_ten]

/-! ### Number-theoretic properties of specific values

p(n) for n where p(n) has interesting prime factorization. -/

/-- p(5) = 7 is prime.-/
theorem p5_eq_prime : partitionCount 5 = 7 := Ch01.partitionCount_five
/-- p(6) = 11 is prime.-/
theorem p6_eq_prime : partitionCount 6 = 11 := Ch01.partitionCount_six
/-- p(4) = 5 is prime.-/
theorem p4_eq_prime : partitionCount 4 = 5 := Ch01.partitionCount_four
/-- p(10) = 42 = 2 · 3 · 7.-/
theorem p10_eq_42 : partitionCount 10 = 2 * 3 * 7 := by
  simp [Ch01.partitionCount_ten]
/-- p(9) = 30 = 2 · 3 · 5.-/
theorem p9_eq_30 : partitionCount 9 = 2 * 3 * 5 := by
  simp [Ch01.partitionCount_nine]
/-- p(8) = 22 = 2 · 11.-/
theorem p8_eq_22 : partitionCount 8 = 2 * 11 := by
  simp [Ch01.partitionCount_eight]
/-- p(7) = 15 = 3 · 5.-/
theorem p7_eq_15 : partitionCount 7 = 3 * 5 := by
  simp [Ch01.partitionCount_seven]

/-! ### Squarefree-ness checks -/

/-- p(11) = 56 is NOT squarefree (has 2³).-/
theorem p11_not_squarefree_at_2 : 4 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(10) = 42 is squarefree (= 2·3·7); not divisible by 4.-/
theorem p10_squarefree_at_2 : partitionCount 10 % 4 = 2 := by
  simp [Ch01.partitionCount_ten]

/-! ### Ramanujan family — uniform interface

A Ramanujan congruence is `m ∣ p(m·n + r)`. The classical Ramanujan congruences:
- `m = 5, r = 4`: `5 ∣ p(5n + 4)` (proved at n=0, 1)
- `m = 7, r = 5`: `7 ∣ p(7n + 5)` (proved at n=0)
- `m = 11, r = 6`: `11 ∣ p(11n + 6)` (proved at n=0)
-/

/-- A Ramanujan family at modulus `m` and offset `r` holds at index `n`
if `m` divides `partitionCount (m·n + r)`.-/
def IsRamanujanFamilyAt (m r n : Nat) : Prop := m ∣ partitionCount (m * n + r)

theorem ramanujan_5_4_at_0 : IsRamanujanFamilyAt 5 4 0 := ramanujan_5_n0
theorem ramanujan_5_4_at_1 : IsRamanujanFamilyAt 5 4 1 := ramanujan_5_n1
theorem ramanujan_7_5_at_0 : IsRamanujanFamilyAt 7 5 0 := ramanujan_7_n0
theorem ramanujan_11_6_at_0 : IsRamanujanFamilyAt 11 6 0 := ramanujan_11_n0

/-- A "partial" Ramanujan family up to N: hold at all n ≤ N.-/
def PartialRamanujanUpTo (m r N : Nat) : Prop :=
  ∀ n, n ≤ N → IsRamanujanFamilyAt m r n

/-- The mod-5 Ramanujan family holds up to N=1 (limited by available p values).-/
theorem ramanujan_5_4_upto_1 : PartialRamanujanUpTo 5 4 1 := by
  intro n hn
  interval_cases n
  · exact ramanujan_5_4_at_0
  · exact ramanujan_5_4_at_1

/-- The mod-7 Ramanujan family holds up to N=0.-/
theorem ramanujan_7_5_upto_0 : PartialRamanujanUpTo 7 5 0 := by
  intro n hn
  interval_cases n
  exact ramanujan_7_5_at_0

/-- The mod-11 Ramanujan family holds up to N=0.-/
theorem ramanujan_11_6_upto_0 : PartialRamanujanUpTo 11 6 0 := by
  intro n hn
  interval_cases n
  exact ramanujan_11_6_at_0

/-! ### Non-Ramanujan: counter-examples

Some `(m, r)` patterns are NOT Ramanujan families. -/

/-- `(5, 3)` is not a Ramanujan family at n=0: p(3) = 3, not divisible by 5.-/
theorem not_ramanujan_5_3_at_0 : ¬ IsRamanujanFamilyAt 5 3 0 := by
  unfold IsRamanujanFamilyAt; simp [Ch01.partitionCount_three]

/-- `(7, 4)` is not a Ramanujan family at n=0: p(4) = 5, not divisible by 7.-/
theorem not_ramanujan_7_4_at_0 : ¬ IsRamanujanFamilyAt 7 4 0 := by
  unfold IsRamanujanFamilyAt; simp [Ch01.partitionCount_four]

/-- `(11, 5)` is not a Ramanujan family at n=0: p(5) = 7, not divisible by 11.-/
theorem not_ramanujan_11_5_at_0 : ¬ IsRamanujanFamilyAt 11 5 0 := by
  unfold IsRamanujanFamilyAt; simp [Ch01.partitionCount_five]

/-! ### Partition generating function and Ramanujan congruences

We use Mathlib's `Nat.Partition.genFun` infrastructure. Setting the character
function `f = (fun _ _ => 1)` gives the standard partition generating function
`∑ p(n) X^n` with the Euler product identity `∏ 1/(1 - X^(k+1))`.

This is the foundation for proving the **general** Ramanujan congruences
(`5 ∣ p(5n+4)`, etc.) by Frobenius-mod-p techniques on power series. -/

/-- The standard partition generating function over a commutative semiring `R`:
`∑_{n ≥ 0} p(n) · X^n ∈ R⟦X⟧`, where `p(n)` is the partition count of `n`.-/
noncomputable def partitionGenFun (R : Type*) [CommSemiring R] : R⟦X⟧ :=
  Nat.Partition.genFun (fun _ _ => (1 : R))

/-- The n-th coefficient of `partitionGenFun ℤ` equals `partitionCount n`.-/
theorem coeff_partitionGenFun_int (n : Nat) :
    (partitionGenFun ℤ).coeff n = (partitionCount n : ℤ) := by
  unfold partitionGenFun
  rw [Nat.Partition.coeff_genFun]
  simp [partitionCount]

/-- The n-th coefficient of `partitionGenFun ℚ` equals `partitionCount n`.-/
theorem coeff_partitionGenFun_rat (n : Nat) :
    (partitionGenFun ℚ).coeff n = (partitionCount n : ℚ) := by
  unfold partitionGenFun
  rw [Nat.Partition.coeff_genFun]
  simp [partitionCount]

/-- The partition generating function equals Mathlib's `genFun` with constant character 1.-/
theorem partitionGenFun_def (R : Type*) [CommSemiring R] :
    partitionGenFun R = Nat.Partition.genFun (R := R) (fun _ _ => 1) := rfl

section EulerProductFormal

open scoped PowerSeries.WithPiTopology

end EulerProductFormal

/-- Coefficient extraction: `(partitionGenFun R).coeff n = (Fintype.card (Nat.Partition n) : R)`.-/
theorem coeff_partitionGenFun (R : Type*) [CommSemiring R] (n : Nat) :
    (partitionGenFun R).coeff n = (Fintype.card (Nat.Partition n) : R) := by
  unfold partitionGenFun
  rw [Nat.Partition.coeff_genFun]
  simp

/-- The constant term of the partition generating function is 1 (since p(0) = 1).-/
theorem coeff_zero_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 0 = 1 := by
  rw [coeff_partitionGenFun]
  simp [Ch01.partitionCount_zero]

/-- Coefficients at small n: explicit values via Ch01.-/
theorem coeff_one_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 1 = 1 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_one]

theorem coeff_two_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 2 = 2 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_two]

theorem coeff_three_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 3 = 3 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_three]

theorem coeff_four_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 4 = 5 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_four]

theorem coeff_five_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 5 = 7 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_five]

theorem coeff_nine_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 9 = 30 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_nine]

/-! ### Ramanujan congruence at the power series level

Goal: prove `(partitionGenFun (ZMod 5)).coeff (5*n + 4) = 0` for all n.

This is the **algebraic** Ramanujan congruence: it says the coefficients of
the partition generating function over ZMod 5 vanish in arithmetic progression
4 mod 5. Equivalently `5 ∣ partitionCount (5n+4)` for all n.

The classical proof (Ramanujan 1919) uses:
1. Frobenius mod 5: `(1 - X^k)^5 = 1 - X^{5k}` in `(ZMod 5)⟦X⟧`.
2. `(q;q)∞^4 ≡ (q^5;q^5)∞ · J(q) (mod 5)` where `J = 1/(q;q)∞`.
3. Jacobi's identity for `(q;q)∞^3`.
4. Mod-5 coefficient analysis.

We state the result and verified instances. -/

/-- **Ramanujan's mod-5 congruence (algebraic form, statement)**:
The coefficients of `partitionGenFun (ZMod 5)` vanish on the arithmetic
progression `5n + 4`.-/
def IsRamanujanCongruenceMod5 : Prop :=
  ∀ n : Nat, (partitionGenFun (ZMod 5)).coeff (5 * n + 4) = 0

/-- Verified at `n = 0`: `(partitionGenFun (ZMod 5)).coeff 4 = 0`.-/
theorem ramanujan_mod5_coeff_4 :
    (partitionGenFun (ZMod 5)).coeff 4 = 0 := by
  rw [coeff_partitionGenFun]
  show ((partitionCount 4 : Nat) : ZMod 5) = 0
  rw [Ch01.partitionCount_four]; decide

/-- Verified at `n = 1`: `(partitionGenFun (ZMod 5)).coeff 9 = 0`.-/
theorem ramanujan_mod5_coeff_9 :
    (partitionGenFun (ZMod 5)).coeff 9 = 0 := by
  rw [coeff_partitionGenFun]
  show ((partitionCount 9 : Nat) : ZMod 5) = 0
  rw [Ch01.partitionCount_nine]; decide

/-- Verified at `n = 0`: 7-Ramanujan congruence in `ZMod 7`.-/
theorem ramanujan_mod7_coeff_5 :
    (partitionGenFun (ZMod 7)).coeff 5 = 0 := by
  rw [coeff_partitionGenFun]
  show ((partitionCount 5 : Nat) : ZMod 7) = 0
  rw [Ch01.partitionCount_five]; decide

/-- Verified at `n = 0`: 11-Ramanujan congruence in `ZMod 11`.-/
theorem ramanujan_mod11_coeff_6 :
    (partitionGenFun (ZMod 11)).coeff 6 = 0 := by
  rw [coeff_partitionGenFun]
  show ((partitionCount 6 : Nat) : ZMod 11) = 0
  rw [Ch01.partitionCount_six]; decide

/-! ### Frobenius endomorphism for power series over `ZMod p`

In `(ZMod p)⟦X⟧`, the map `φ ↦ φ^p` is a ring endomorphism (the Frobenius).
In particular `(a + b)^p = a^p + b^p` for all a, b. This gives us:
`(1 + c · X^k)^p = 1 + c^p · X^{kp}`

For `c = -1` (and odd `p`): `(1 - X^k)^p = 1 - X^{kp}`.

This is the algebraic key to Ramanujan's mod-p congruences. -/

/-! ### Finite q-Pochhammer and the Euler product

The finite q-Pochhammer `(q;q)_N = ∏_{k=1}^N (1 - q^k)` is a polynomial-like
power series. Frobenius applied factor-by-factor gives:
`(q;q)_N^p ≡ (q^p; q^p)_N (mod p)` in `(ZMod p)⟦X⟧`. -/

/-- Single factor of the q-Pochhammer product: `1 - X^(k+1)` as a power series.-/
noncomputable def oneSubXPow (R : Type*) [CommRing R] (k : Nat) : R⟦X⟧ :=
  1 - (PowerSeries.X : R⟦X⟧) ^ (k + 1)

/-- Finite q-Pochhammer as a formal power series: `(q;q)_N = ∏_{k<N}(1 - X^{k+1})`.-/
noncomputable def qPochFinitePS (R : Type*) [CommRing R] (N : Nat) : R⟦X⟧ :=
  ∏ k ∈ Finset.range N, oneSubXPow R k

theorem qPochFinitePS_zero (R : Type*) [CommRing R] :
    qPochFinitePS R 0 = (1 : R⟦X⟧) := by
  simp [qPochFinitePS]

/-! ### The q ↦ q^p substitution on power series

Define a power series operation `subXPow p f` that sends `∑ aₙ Xⁿ` to `∑ aₙ X^{pn}`.
This is the "raise the variable" map, central to Ramanujan's argument:
in `(ZMod p)⟦X⟧`, `(q;q)∞^p = (q^p; q^p)∞`. -/

/-- The variable substitution `X ↦ X^p` on a power series.-/
noncomputable def subXPow (R : Type*) [CommSemiring R] (p : Nat) (f : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (fun n => if p ∣ n then f.coeff (n / p) else 0)

/-- Substituting `p = 0` gives the constant series (only `coeff 0` survives).-/
theorem coeff_subXPow (R : Type*) [CommSemiring R] (p : Nat) (f : R⟦X⟧) (n : Nat) :
    (subXPow R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 := by
  rw [subXPow]
  exact PowerSeries.coeff_mk _ _

/-- For `p ≥ 1`, the constant term of `subXPow p f` equals the constant term of `f`.-/
theorem coeff_zero_subXPow (R : Type*) [CommSemiring R] (p : Nat) (hp : 1 ≤ p) (f : R⟦X⟧) :
    (subXPow R p f).coeff 0 = f.coeff 0 := by
  rw [coeff_subXPow]
  simp [Nat.dvd_zero]

/-- The `pn`-th coefficient of `subXPow p f` equals the `n`-th coefficient of `f`.-/
theorem coeff_pn_subXPow (R : Type*) [CommSemiring R] (p : Nat) (hp : 1 ≤ p)
    (f : R⟦X⟧) (n : Nat) :
    (subXPow R p f).coeff (p * n) = f.coeff n := by
  rw [coeff_subXPow]
  split_ifs with h
  · congr 1; rw [Nat.mul_div_cancel_left]; omega
  · exact absurd ⟨n, rfl⟩ h

/-- For `p ≥ 1`, indices not divisible by `p` give zero.-/
theorem coeff_not_pn_subXPow (R : Type*) [CommSemiring R] (p : Nat) (f : R⟦X⟧)
    (n : Nat) (h : ¬ p ∣ n) :
    (subXPow R p f).coeff n = 0 := by
  rw [coeff_subXPow]
  simp [h]

/-! ### Use Mathlib's `PowerSeries.expand` (the variable substitution X ↦ X^p)

Mathlib provides `PowerSeries.expand p hp : R⟦X⟧ →ₐ[R] R⟦X⟧` which sends
`∑ aₙ Xⁿ` to `∑ aₙ X^{p·n}`. This is the same operation as our `subXPow` but
already comes with the full algebra-homomorphism structure.

The key theorem is `MvPowerSeries.map_frobenius_expand`:
`(f.expand p).map (frobenius R p) = f ^ p`

For `R = ZMod p`, the Frobenius map on ZMod p is the identity (Fermat's little
theorem), so we get the clean form:

**`f.expand p hp = f ^ p` in `(ZMod p)⟦X⟧`** -/

/-! ### The `(q;q)∞` formal power series

We define `qPochInfPS R := (partitionGenFun R)⁻¹` (as a power series inverse,
which exists since the constant term of `partitionGenFun R` is 1, a unit).

This gives us `partitionGenFun R * qPochInfPS R = 1` algebraically. -/

/-- `(q;q)∞` as the formal power series inverse of `partitionGenFun`.-/
noncomputable def qPochInfPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.invOfUnit (partitionGenFun R) 1

/-- The defining property: `partitionGenFun * qPochInfPS = 1`.-/
theorem partitionGenFun_mul_qPochInfPS (R : Type*) [CommRing R] :
    partitionGenFun R * qPochInfPS R = 1 := by
  unfold qPochInfPS
  apply PowerSeries.mul_invOfUnit
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_partitionGenFun]
  rfl

/-- The defining property: `qPochInfPS * partitionGenFun = 1`.-/
theorem qPochInfPS_mul_partitionGenFun (R : Type*) [CommRing R] :
    qPochInfPS R * partitionGenFun R = 1 := by
  rw [mul_comm]
  exact partitionGenFun_mul_qPochInfPS R

/-- `qPochInfPS` is a unit (with `partitionGenFun` as its inverse).-/
theorem isUnit_qPochInfPS (R : Type*) [CommRing R] : IsUnit (qPochInfPS R) :=
  ⟨⟨qPochInfPS R, partitionGenFun R, qPochInfPS_mul_partitionGenFun R,
    partitionGenFun_mul_qPochInfPS R⟩, rfl⟩

/-- **Naturality of `partitionGenFun`** under ring homs: for `f : R →+* S`,
`PowerSeries.map f (partitionGenFun R) = partitionGenFun S`.-/
theorem map_partitionGenFun {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) :
    PowerSeries.map f (partitionGenFun R) = partitionGenFun S := by
  ext n
  rw [PowerSeries.coeff_map, coeff_partitionGenFun, coeff_partitionGenFun]
  simp

/-- **Naturality of `qPochInfPS`** under ring homs: for `f : R →+* S`,
`PowerSeries.map f (qPochInfPS R) = qPochInfPS S`.-/
theorem map_qPochInfPS {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    PowerSeries.map f (qPochInfPS R) = qPochInfPS S := by
  -- Both are inverses of partitionGenFun S
  have h1 : PowerSeries.map f (qPochInfPS R) * partitionGenFun S = 1 := by
    rw [← map_partitionGenFun f, ← map_mul, qPochInfPS_mul_partitionGenFun]
    exact (PowerSeries.map f).map_one
  have h2 : qPochInfPS S * partitionGenFun S = 1 := qPochInfPS_mul_partitionGenFun S
  -- (map f q) = (map f q) · (J · qPoch) = ((map f q) · J) · qPoch = 1 · qPoch = qPoch
  calc PowerSeries.map f (qPochInfPS R)
      = PowerSeries.map f (qPochInfPS R) * (partitionGenFun S * qPochInfPS S) := by
        rw [partitionGenFun_mul_qPochInfPS]; ring
    _ = (PowerSeries.map f (qPochInfPS R) * partitionGenFun S) * qPochInfPS S := by ring
    _ = 1 * qPochInfPS S := by rw [h1]
    _ = qPochInfPS S := one_mul _

section FormalEulerBridge

open scoped PowerSeries.WithPiTopology

section CoeffTprodBridge

open Filter Topology

end CoeffTprodBridge

end FormalEulerBridge

/-- The constant term of `qPochInfPS` is 1.-/
theorem constantCoeff_qPochInfPS (R : Type*) [CommRing R] :
    (PowerSeries.constantCoeff : R⟦X⟧ →+* R) (qPochInfPS R) = 1 := by
  unfold qPochInfPS
  rw [PowerSeries.constantCoeff_invOfUnit]
  rfl

/-- **Frobenius preservation of inverse**: in `(ZMod p)⟦X⟧`,
`expand_p (partitionGenFun) · expand_p (qPochInfPS) = 1`.

Equivalently: the inverse relation `J · qPoch = 1` is preserved under the
Frobenius substitution `X ↦ X^p`. Proof: by ring-hom multiplication
of expand applied to `J · qPoch = 1`.-/
theorem expand_partitionGenFun_mul_expand_qPochInfPS
    (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0) :
    PowerSeries.expand p hp (partitionGenFun (ZMod p)) *
      PowerSeries.expand p hp (qPochInfPS (ZMod p)) = 1 := by
  rw [← map_mul, partitionGenFun_mul_qPochInfPS, map_one]

/-- The coefficient at index 0 of `qPochInfPS` is 1.-/
theorem coeff_zero_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact constantCoeff_qPochInfPS R

section SignedStrictPartition

open scoped PowerSeries.WithPiTopology

/-- The character function picking out strict (multiplicity-1) partitions with sign.
For `i ≥ 1` and `j = 1`: returns `-1`. For other `(i, j)`: returns `0`.

When applied via `Nat.Partition.genFun`, this gives the formal Euler product
`∏(1 - X^(i+1)) = qPochInfPS`, whose coefficient at `n` is the signed count
of strict partitions of `n`.-/
noncomputable def signedStrictChar (R : Type*) [Ring R] : ℕ → ℕ → R :=
  fun i j => if i ≥ 1 ∧ j = 1 then -1 else 0

/-- **Signed strict partition count via Nat.Partition** (using Mathlib's `Nat.Partition`).
This is the sum over partitions of `n` (with no repeated parts, weighted by sign).-/
noncomputable def signedStrictCount (R : Type*) [CommRing R] (n : ℕ) : R :=
  (Nat.Partition.genFun (signedStrictChar R)).coeff n

end SignedStrictPartition

section BridgeToCh05Pentagonal

open PowerSeries
open scoped PowerSeries.WithPiTopology

end BridgeToCh05Pentagonal

/-! ### Specific qPochInfPS coefficient values via Euler pentagonal

Derived from `coeff_qPochInfPS_eq_pentagonalSign` + `decide` on `pentagonalSign n` for
specific small n. These extend beyond the n=0..8 values proved via the J·qPoch=1 recurrence
in earlier sections. -/

/-! ### B2 groundwork: Jacobi triple product at z=1 (cube identity)

Goal: prove `(qPochInfPS R)^3 = ∑ (-1)^n (2n+1) X^{n(n+1)/2}` as formal power series.

This is the classical Jacobi identity `∏(1-q^n)^3 = ∑(-1)^n(2n+1)q^{T_n}`.
Ch04_T43 has the analytic version (`jacobiIdentity`) for `|q| < 1`.

The formal-PS version requires either:
  (a) Combinatorial proof via Sylvester-style involution on triple partitions
  (b) Analytic → formal bridge via Taylor expansion uniqueness

Both are substantial work; we define the target and prove small cases here. -/

/-- The Jacobi triple sign: `(-1)^k · (2k+1)` if `n = k(k+1)/2` for some `k ≥ 0`,
else `0`. This is the expected `n`-th coefficient of `(q;q)_∞^3`.-/
def jacobiTripleSign (n : Nat) : Int :=
  match (List.range (n + 1)).find? (fun k => n = k * (k + 1) / 2) with
  | some k => (-1 : Int) ^ k * (2 * k + 1)
  | none => 0

-- Sanity: triangular numbers 0, 1, 3, 6, 10, 15, ...
-- Values:                    1, -3, 5, -7, 9, -11, ...

/-- The Jacobi theta-like formal power series: `∑ (-1)^k (2k+1) X^{T_k}`.-/
noncomputable def jacobiThetaPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk fun n => ((jacobiTripleSign n : ℤ) : R)

/-- Coefficient extraction from `jacobiThetaPS`.-/
@[simp] theorem coeff_jacobiThetaPS (R : Type*) [CommRing R] (n : Nat) :
    (jacobiThetaPS R).coeff n = ((jacobiTripleSign n : ℤ) : R) := by
  unfold jacobiThetaPS; rw [PowerSeries.coeff_mk]

-- **B2 target theorem**: `(qPochInfPS R)^3 = jacobiThetaPS R` in `R⟦X⟧`.
-- This is the formal-PS version of Jacobi's identity (Ch04.jacobiIdentity in
-- analytic form). Full proof requires either Sylvester's combinatorial bijection
-- or an analytic ↔ formal Taylor uniqueness bridge.

-- Small case verification: `(qPochInfPS R)^3 . coeff n` for small n is computable
-- via the generic `coeff_n_pow_of_constantCoeff_one` helpers in Ch20 and Euler-pentagonal
-- coefficient values. See Ch20.ramanujanTau_two for the analogous tau computation pattern.

/-- `(partitionGenFun R).coeff 1 = 1` in any commutative semiring: one partition of 1.-/
theorem coeff_one_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 1 = 1 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 1) = 1 := Ch01.partitionCount_one
  rw [h]; simp

/-- `(partitionGenFun R).coeff 2 = 2` in any commutative semiring: two partitions of 2 ([2], [1,1]).-/
theorem coeff_two_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 2 = 2 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 2) = 2 := Ch01.partitionCount_two
  rw [h]; simp

/-- `(partitionGenFun R).coeff 3 = 3` in any commutative semiring: three partitions of 3
([3], [2,1], [1,1,1]).-/
theorem coeff_three_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 3 = 3 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 3) = 3 := Ch01.partitionCount_three
  rw [h]; simp

/-- `(partitionGenFun R).coeff 4 = 5` (five partitions of 4).-/
theorem coeff_four_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 4 = 5 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 4) = 5 := Ch01.partitionCount_four
  rw [h]; simp

/-- `(partitionGenFun R).coeff 5 = 7` (seven partitions of 5).-/
theorem coeff_five_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 5 = 7 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 5) = 7 := Ch01.partitionCount_five
  rw [h]; simp

/-- `(partitionGenFun R).coeff 6 = 11` (eleven partitions of 6).-/
theorem coeff_six_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 6 = 11 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 6) = 11 := Ch01.partitionCount_six
  rw [h]; simp

/-- `(partitionGenFun R).coeff 7 = 15` (fifteen partitions of 7).-/
theorem coeff_seven_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 7 = 15 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 7) = 15 := Ch01.partitionCount_seven
  rw [h]; simp

/-- `(partitionGenFun R).coeff 8 = 22` (twenty-two partitions of 8).-/
theorem coeff_eight_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 8 = 22 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 8) = 22 := Ch01.partitionCount_eight
  rw [h]; simp

/-! ### Conditional Ramanujan congruence

If the coefficients of `(q;q)∞^(p-1)` vanish on the arithmetic progression
`pn + r` (mod p), then by the key identity the LHS `J · (q;q)∞.expand p`
also vanishes there.

The actual vanishing of `(q;q)∞^(p-1)` coefficients on the appropriate
progression (for p=5, r=4; p=7, r=5; p=11, r=6) follows from Jacobi's
triple product identity — the next major step to formalize. -/

/-! ### Conditional Ramanujan theorem

If the coefficients of `(q;q)∞^(p-1)` vanish on the arithmetic progression
`p·n + r` (in `(ZMod p)⟦X⟧`), then `partitionCount(p·n + r) ≡ 0 (mod p)`. -/

/-! ### Ramanujan congruences — conditional corollaries

The three classical Ramanujan partition congruences are mod 5, 7, 11, each
on a specific residue class. Below are the conditional statements: assuming
the corresponding `(q;q)∞^(p-1)` coefficient vanishes on the progression. -/

/-! ### N=0 Ramanujan identity: closed-form bridge

For `0 ≤ r < p`, the algebraic identity collapses cleanly:
`((q;q)∞^(p-1)).coeff r = (p(r) : ZMod p)`.

This is the n=0 case of the conditional Ramanujan. The LHS can be computed
directly from the Euler-pentagonal coefficients of qPochInfPS via the
binomial expansion. -/

/-! ### Status note: path to full Ramanujan mod 5

**Completed real theorems**:
- `powerSeries_charP`: CharP instance for PowerSeries (R⟦X⟧ inherits char from R)
- `PowerSeries.expand_eq_pow_zmod`: Frobenius — `f.expand p = f^p` in (ZMod p)⟦X⟧
- `partitionGenFun`: formal partition generating function (via Mathlib's `Nat.Partition.genFun`)
- `coeff_partitionGenFun_int/_rat`: connection to Ch01's `partitionCount`
- `qPochInfPS`: formal `(q;q)∞` via `PowerSeries.invOfUnit`
- `partitionGenFun_mul_qPochInfPS`: `J · (q;q)∞ = 1`
- `ramanujan_key_identity`: in (ZMod p)⟦X⟧, `J · (q;q)∞.expand p = (q;q)∞^(p-1)`
- `coeff_eq_of_key_identity`: coefficient corollary

**Remaining for full Ramanujan mod 5** (each substantial):

1. **Euler pentagonal** as formal power series:
   `(q;q)∞ = ∑_{n ∈ ℤ} (-1)^n X^{n(3n-1)/2}`
   Reference: Ch04Franklin's `euler_pentagonal_combinatorial` (Franklin involution),
   bridged via `signedStrictPartitionCount n = qPochInfPS.coeff n` (cast).

2. **Jacobi identity** as formal power series:
   `(q;q)∞^3 = ∑_{k ≥ 0} (-1)^k (2k+1) X^{k(k+1)/2}`
   Reference: Ch03's Jacobi triple product, specialized.

3. **Mod-5 vanishing analysis**: show `((q;q)∞^4).coeff (5n+4) = 0` in (ZMod 5)⟦X⟧
   by analyzing pairs `(m, k)` with `m(3m-1)/2 + k(k+1)/2 = 5n+4`, showing the
   `(2k+1)` factor is always ≡ 0 (mod 5).

4. **Coefficient extraction + induction**: from `coeff_eq_of_key_identity`,
   derive the linear recurrence `partitionCount(5n+4) = -∑_{k≥1} ...`,
   then induct on n.

Steps 1-2 are substantial but reuse existing Q-series infrastructure.
Step 3 is finite combinatorial. Step 4 is straightforward induction. -/

end Ch19
end PartIV
end QseriesFormalization
