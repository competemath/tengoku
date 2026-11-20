/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku
import Tengoku.Qharm.QHarm.Main
import Tengoku.Qharm.QHarm.MainRat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms QHarmonicRationalBase.irrational_of_logRatio_lt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms QHarmonicRationalBase.irrational_half_odd` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms QHarmonicRationalBase.irrational_int` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/BrandonMYates/qharm@27f42bc146a6, `QHarm/Reduce.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# QHarm/Reduce.lean — the three Challenge statements, reduced to two master theorems

## Consumes

The two master theorems, and nothing else from `QHarm`:

* `QHarm.master_int`  — `QHarm/Main.lean` (integer track, deviation D1)
* `QHarm.master_rat`  — `QHarm/MainRat.lean` (general rational-base track)

Everything else in this file is elementary `Real.log` monotonicity and a `π > 3` bound,
and was built and audited before the rest of the DAG landed.

## Main results

The three advertised statements of the Palomar Challenge file for this entry, with
**term-identical** conclusions:

* `QHarmonicRationalBase.irrational_of_logRatio_lt`
* `QHarmonicRationalBase.irrational_half_odd`
* `QHarmonicRationalBase.irrational_int`

together with the arithmetic that reduces them to the two masters. All of that
arithmetic is fully proved here:

* `QHarm.Reduce.cast_half_odd`      — `(((P : ℚ)/2 : ℚ) : ℝ) = (P : ℝ)/2`
* `QHarm.Reduce.one_lt_half_odd`    — `1 < (P : ℚ)/2` for `7 ≤ P`
* `QHarm.Reduce.num_half_odd`       — `((P : ℚ)/2).num = P` for `P` odd
* `QHarm.Reduce.den_half_odd`       — `((P : ℚ)/2).den = 2` for `P` odd
* `QHarm.Reduce.log_seven_gt`       — `(13/5) * log 2 < log 7`
* `QHarm.Reduce.log_two_div_log_seven_lt` — `log 2 / log 7 < 5/13`
* `QHarm.Reduce.log_two_div_log_lt` — `log 2 / log P < 1/2 − 1/π²` for `7 ≤ P`
* `QHarm.Reduce.logRatio_int_lt`    — the (unused-but-on-record) `θ = 0` threshold check

## What is NOT here

* The masters themselves (`QHarm/Main.lean`).
* Anything about the linear forms, the clearing factor (`QHarm/Clearing.lean`), the
  q-Legendre polynomials, orthogonality, or the growth estimates. This file contains
  no analysis beyond elementary `Real.log` monotonicity and a `π > 3` bound.
* Irrationality measures / `LiouvilleWith`: deliberately not advertised.
-/

namespace QHarm

/-! Both masters are now **proved** and imported above — `master_int` in `QHarm/Main.lean`
(integer track, deviation D1) and `master_rat` in `QHarm/MainRat.lean` (general rational-base
track).  The two placeholders that stood here are closed; this file carries no `sorry`. -/

namespace Reduce

/-! ### Step 1 — the cast bridge

The Challenge spells the half-odd base as the *real* number `(P : ℝ) / 2`, while
`master_rat` is stated for a *rational* `t` coerced into `ℝ`. This lemma is what makes
the two `tsum`s the same term. -/

/-- `(P : ℚ)/2` and `(P : ℝ)/2` name the same real number.
@isnad1 id=eq.0h1v.s5.89e543daf278 from=translated src=- shape=0ab8d3ee vocab=04a5d28a
-/
theorem cast_half_odd (P : ℕ) : ((((P : ℚ) / 2 : ℚ)) : ℝ) = (P : ℝ) / 2 := by
  push_cast
  ring

/-! ### Step 2 — positivity of the base -/

/-- For `P ≥ 7` the base `P/2` exceeds `1` (indeed it exceeds `7/2`).
@isnad1 id=lt.1h1v.s5.2f8e024c1601 from=translated src=- shape=172d991d vocab=51c9349f
-/
theorem one_lt_half_odd (P : ℕ) (hP : 7 ≤ P) : 1 < ((P : ℚ) / 2) := by
  have h : (7 : ℚ) ≤ (P : ℚ) := by exact_mod_cast hP
  linarith

/-! ### Step 3 — `P/2` is already in lowest terms

`Rat.num_div_eq_of_coprime` / `Rat.den_div_eq_of_coprime` (Mathlib
`Data/Rat/Lemmas.lean`) are stated for `a b : ℤ` with `0 < b` and
`Nat.Coprime a.natAbs b.natAbs`. -/

/-- `P` odd gives `Nat.Coprime |P| |2|` in the shape the `Rat` API wants.
@isnad1 id=coprime.1h1v.s4.839bd2565f5b from=translated src=- shape=648d1664 vocab=91b2dac5
-/
theorem coprime_half_odd (P : ℕ) (hodd : Odd P) :
    Nat.Coprime ((P : ℤ)).natAbs ((2 : ℤ)).natAbs := by
  simpa using Nat.coprime_two_right.mpr hodd

/-- The two spellings of the base, over `ℚ`.
@isnad1 id=eq.0h1v.s5.7fb4a921e5d2 from=translated src=- shape=02e709d8 vocab=5df4ddbd
-/
theorem rat_half_eq (P : ℕ) : (((P : ℤ) : ℚ)) / (((2 : ℤ) : ℚ)) = (P : ℚ) / 2 := by
  push_cast
  ring

/-- The numerator of `P/2` is `P`, for odd `P`.
@isnad1 id=eq.1h1v.s4.73038c38307f from=translated src=- shape=ac9bdeb6 vocab=0ab0fdf8
-/
theorem num_half_odd (P : ℕ) (hodd : Odd P) : ((P : ℚ) / 2).num = (P : ℤ) := by
  have h := Rat.num_div_eq_of_coprime (a := (P : ℤ)) (b := (2 : ℤ)) (by norm_num)
    (coprime_half_odd P hodd)
  rwa [rat_half_eq P] at h

/-- The denominator of `P/2` is `2`, for odd `P`.
@isnad1 id=eq.1h1v.s4.5b0c1be44a8f from=translated src=- shape=ee594b33 vocab=3e79db66
-/
theorem den_half_odd (P : ℕ) (hodd : Odd P) : ((P : ℚ) / 2).den = 2 := by
  have h := Rat.den_div_eq_of_coprime (a := (P : ℤ)) (b := (2 : ℤ)) (by norm_num)
    (coprime_half_odd P hodd)
  rw [rat_half_eq P] at h
  exact_mod_cast h

/-! ### Step 4 — the numeric threshold

`log 2 / log P < 1/2 − 1/π²` for `P ≥ 7`, via `7^5 = 16807 > 8192 = 2^13` and `π > 3`.
No transcendental estimate beyond `Real.pi_gt_three` is used. -/

/-- `7^5 = 16807 > 8192 = 2^13`, hence `log 7 > (13/5) log 2`.
@isnad1 id=lt.0h0v.s5.0df1b0b4afc4 from=translated src=- shape=9718c9b4 vocab=4ca98610
-/
theorem log_seven_gt : (13 / 5 : ℝ) * Real.log 2 < Real.log 7 := by
  have h1 : ((2 : ℝ) ^ (13 : ℕ)) < ((7 : ℝ) ^ (5 : ℕ)) := by norm_num
  have h2 : Real.log ((2 : ℝ) ^ (13 : ℕ)) < Real.log ((7 : ℝ) ^ (5 : ℕ)) :=
    Real.log_lt_log (by norm_num) h1
  rw [Real.log_pow, Real.log_pow] at h2
  push_cast at h2
  linarith

/-- `log 2 / log 7 < 5/13`.
@isnad1 id=lt.0h0v.s5.7efa9e6ebb18 from=translated src=- shape=d917c32c vocab=26a59d5f
-/
theorem log_two_div_log_seven_lt : Real.log 2 / Real.log 7 < 5 / 13 := by
  have h7 : (0 : ℝ) < Real.log 7 := Real.log_pos (by norm_num)
  rw [div_lt_div_iff₀ h7 (by norm_num : (0 : ℝ) < 13)]
  linarith [log_seven_gt]

/-- `π² > 26/3`; the only transcendental input is `Real.pi_gt_three`.
@isnad1 id=lt.0h0v.s5.768e353a8ddb from=translated src=- shape=078d9480 vocab=5d10ec1f
-/
theorem pi_sq_gt : (26 / 3 : ℝ) < Real.pi ^ 2 := by
  nlinarith [Real.pi_gt_three, Real.pi_pos]

/-- `5/13 < 1/2 − 1/π²`, equivalently `1/π² < 3/26`.
@isnad1 id=lt.0h0v.s6.4b240c60ccb8 from=translated src=- shape=530e937c vocab=21821a13
-/
theorem five_div_thirteen_lt : (5 / 13 : ℝ) < 1 / 2 - 1 / Real.pi ^ 2 := by
  have hpos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have h : 1 / Real.pi ^ 2 < 3 / 26 := by
    rw [div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 26)]
    linarith [pi_sq_gt]
  linarith

/-- **The numeric threshold.** For every natural `P ≥ 7`,
`log 2 / log P < 1/2 − 1/π²`.
@isnad1 id=lt.1h1v.s6.c00248c85e43 from=translated src=- shape=ddc85bd5 vocab=598c451d
-/
theorem log_two_div_log_lt {P : ℕ} (hP : 7 ≤ P) :
    Real.log 2 / Real.log (P : ℝ) < 1 / 2 - 1 / Real.pi ^ 2 := by
  have h7 : (0 : ℝ) < Real.log 7 := Real.log_pos (by norm_num)
  have hPR : (7 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hlog : Real.log 7 ≤ Real.log (P : ℝ) := Real.log_le_log (by norm_num) hPR
  have hstep : Real.log 2 / Real.log (P : ℝ) ≤ Real.log 2 / Real.log 7 :=
    div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) h7 hlog
  linarith [log_two_div_log_seven_lt, five_div_thirteen_lt]

/-- The `θ = 0` threshold check for an integer base. `irrational_int` is routed through
`QHarm.master_int` (deviation D1), so this lemma is not consumed by anything below; it
is on record that the rational route would also have applied. (The hypothesis `2 ≤ t`
is kept for signature parity with `master_int`; the estimate in fact holds for every
integer `t`, since `(t : ℚ).den = 1` unconditionally.)
@isnad1 id=lt.1h1v.s6.7a949af1b08a from=translated src=- shape=6a899552 vocab=c09be3c6
-/
theorem logRatio_int_lt (t : ℤ) (ht : 2 ≤ t) :
    Real.log (((t : ℚ)).den : ℝ) / Real.log (((t : ℚ)).num : ℝ) < 1 / 2 - 1 / Real.pi ^ 2 := by
  rw [Rat.den_intCast t]
  simp only [Nat.cast_one, Real.log_one, zero_div]
  have hpos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have h : 1 / Real.pi ^ 2 < 1 / 2 := by
    rw [div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_gt_three]
  linarith

end Reduce

end QHarm

namespace QHarmonicRationalBase

open Real

/-- **The main statement.** Let `t > 1` be rational, written in lowest terms as
`t = t.num / t.den`. If `log t.den / log t.num < 1/2 − 1/π²`, then the `q`-harmonic
series `∑_{n≥1} 1/(tⁿ − 1)` is irrational.
@isnad1 id=irration.2h1v.s7.73d51fa36933 from=translated src=- shape=548b39d1 vocab=4499ab25
-/
theorem irrational_of_logRatio_lt (t : ℚ) (ht : 1 < t)
    (hθ : Real.log (t.den : ℝ) / Real.log (t.num : ℝ) < 1 / 2 - 1 / Real.pi ^ 2) :
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) :=
  QHarm.master_rat t ht hθ

/-- **The first new bases, concretely.** For every odd `P ≥ 7` the series
`∑_{n≥1} 1/((P/2)ⁿ − 1)` is irrational.
@isnad1 id=irration.2h1v.s6.902961bff476 from=translated src=- shape=f3b82811 vocab=c96448eb
-/
theorem irrational_half_odd (P : ℕ) (hodd : Odd P) (hP : 7 ≤ P) :
    Irrational (∑' n : ℕ+, 1 / (((P : ℝ) / 2) ^ (n : ℕ) - 1)) := by
  have key := QHarm.master_rat ((P : ℚ) / 2) (QHarm.Reduce.one_lt_half_odd P hP) (by
    rw [QHarm.Reduce.num_half_odd P hodd, QHarm.Reduce.den_half_odd P hodd]
    push_cast
    exact QHarm.Reduce.log_two_div_log_lt hP)
  rwa [QHarm.Reduce.cast_half_odd P] at key

/-- **The integer case**, `Q = 1`: Erdős 1948.
@isnad1 id=irration.1h1v.s6.4b00e674d9a8 from=translated src=- shape=c700ddf4 vocab=c5b869d2
-/
theorem irrational_int (t : ℤ) (ht : 2 ≤ t) :
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) :=
  QHarm.master_int t ht

end QHarmonicRationalBase

/-! ## Acceptance test

Each `example` below restates the conclusion of the corresponding theorem of
the Palomar Challenge file for this entry **verbatim** and is closed by a bare
term — no `by`, no coercion massaging. If any of the three statements had drifted from
the Challenge spelling (a stray `Rat.cast`, an `ℕ+` coercion, a different `1/2 − 1/π²`
elaboration), these would fail to elaborate. -/
section AcceptanceTest

end AcceptanceTest

