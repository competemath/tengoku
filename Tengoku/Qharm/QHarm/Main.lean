/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Qharm.QHarm.Basic
import Tengoku.Qharm.QHarm.Legendre
import Tengoku.Qharm.QHarm.Clearing
import Tengoku.Qharm.QHarm.Pade
import Tengoku.Qharm.QHarm.Integrality
import Tengoku.Qharm.QHarm.Forms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms QHarm.master_int` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# QHarm/Main.lean — the assembly

This file contains **no mathematics of its own**: it is the
composition step that turns the finished component files into `master_int`, the integer-base
master theorem that `QHarm/Reduce.lean` uses to discharge
`QHarmonicRationalBase.irrational_int` (Erdős 1948).

## Consumes

`QHarm/Basic.lean` (`S`, `irrational_of_linear_forms`), `QHarm/Legendre.lean` (the little
q-Legendre objects), `QHarm/Clearing.lean` (`Dr`, `Dz`). The remaining inputs are declared
below, each with the file that supplies it.

## Main results

`master_int : 2 ≤ t → Irrational (∑' n : ℕ+, 1/((t:ℝ)^(n:ℕ) - 1))`.

## What is NOT here

The orthogonality (`QHarm/Orthogonality.lean`), the Padé identity (`QHarm/Pade.lean`), the
integrality of the forms (`QHarm/Integrality.lean`), the size bounds (`QHarm/CoefBound.lean`),
and the whole general rational-base track (`Cyclotomic`/`Mertens`/`Growth`), which is not
needed for the integer case — see design decision D1 of the build notes.

## The balance being realised here

`|B_n S - A_n| = clr t n * |rem t n| ≤ 2 t^{-n} √(h_n/(1-q))`, with `clr t n ≤ t^{n²}` and
`|rem t n| ≤ 2 t^{-n²-n} √(h_n/(1-q))`. Nonvanishing is separate and comes from the
sum-of-squares identity, which needs only the vanishing half of orthogonality.
-/

namespace QHarm

open Filter

/-- The full clearing factor `t^{M_n} · D_n`.-/
noncomputable def clr (t : ℝ) (n : ℕ) : ℝ := t ^ Mexp n * Dr t n

/-! ### Inputs from the component files

Every input this file once declared as a placeholder is now closed. `pade` comes from
`QHarm/Pade.lean`;
`sumsq`, `sumsq_pos` and `clr_mul_rem_tendsto_zero` from `QHarm/Forms.lean`; the two
integrality facts from `QHarm/Integrality.lean`. -/

/-- `clr` is `QHarm/Forms.lean`'s `clrF` — definitionally identical.
@isnad1 id=eq.0h2v.s3.5d7bdaf6af34 from=translated src=- shape=6456e7f0 vocab=3234a3ed
-/
theorem clr_eq_clrF (t : ℝ) (n : ℕ) : clr t n = clrF t n := rfl

/-- Closed by `QHarm/Integrality.lean`.
@isnad1 id=ex.1h2v.s5.d82ed2d57072 from=translated src=- shape=7931f8d9 vocab=776c5442
-/
theorem clr_mul_legVal_isInt {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    ∃ b : ℤ, clr (t : ℝ) n * legVal (t : ℝ) n = (b : ℝ) :=
  tM_Dr_mul_legVal_isInt ht n

/-- Closed by `QHarm/Integrality.lean`.
@isnad1 id=ex.1h2v.s6.3bf20c6bc9f2 from=translated src=- shape=4e351085 vocab=1dcf7914
-/
theorem clr_mul_form_isInt {t : ℤ} (ht : 2 ≤ t) (n : ℕ) :
    ∃ a : ℤ, clr (t : ℝ) n * legQval (t : ℝ) n
        + clr (t : ℝ) n * legVal (t : ℝ) n * headSum (t : ℝ) n = (a : ℝ) := by
  obtain ⟨a, ha⟩ := tM_Dr_mul_Aform_isInt ht n
  exact ⟨a, by rw [← ha]; unfold clr; ring⟩

/-! ### Assembly -/

/-- The linear form, in the shape `QHarm/Basic.lean`'s criterion consumes.
@isnad1 id=eq.2h2v.s6.d84fd50a417b from=translated src=- shape=9152b570 vocab=ebb3d339
-/
theorem form_eq {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) :
    (clr t n * legVal t n) * S t
        - (clr t n * legQval t n + clr t n * legVal t n * headSum t n)
      = clr t n * rem t n := by
  have h := pade ht hn
  linear_combination clr t n * h

/-- `clr` is positive, so it never destroys nonvanishing.
@isnad1 id=lt.1h2v.s4.172fa8431544 from=translated src=- shape=9141f3a7 vocab=a6170c0b
-/
theorem clr_pos {t : ℝ} (ht : 1 < t) (n : ℕ) : 0 < clr t n := by
  have h1 : (0 : ℝ) < t ^ Mexp n := pow_pos (lt_trans zero_lt_one ht) _
  exact mul_pos h1 (Clearing.Dr_pos ht n)

/-- `legVal t n ≠ 0` and `rem t n ≠ 0`, both at once, from the sum-of-squares form. This is
the whole content of "nonvanishing" — no zero-localisation argument is used anywhere.
@isnad1 id=ne.2h2v.s5.12bc7e4eeced from=translated src=- shape=cf5864d0 vocab=9c096aa4
-/
theorem rem_ne_zero {t : ℝ} (ht : 1 < t) {n : ℕ} (hn : 1 ≤ n) : rem t n ≠ 0 := by
  intro h
  have hp := sumsq_pos ht hn
  rw [← sumsq ht hn, h, mul_zero] at hp
  exact lt_irrefl 0 hp

/-- **The integer master theorem.** Erdős 1948, by the Van Assche route.
@isnad1 id=irration.1h1v.s6.4b00e674d9a8 from=translated src=- shape=c700ddf4 vocab=c5b869d2
-/
theorem master_int (t : ℤ) (ht : 2 ≤ t) :
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) := by
  have ht1 : (1 : ℝ) < (t : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two ht
  show Irrational (S (t : ℝ))
  choose B hB using clr_mul_legVal_isInt ht
  choose A hA using clr_mul_form_isInt ht
  refine irrational_of_linear_forms_tendsto A B ?_ ?_
  · intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0
      rw [← hB 0, ← hA 0]
      simp only [legVal_zero, legQval_zero, headSum_zero, mul_zero, mul_one, add_zero,
        sub_zero]
      exact ne_of_gt (mul_pos (clr_pos ht1 0) (S_pos ht1))
    · rw [← hB n, ← hA n, form_eq ht1 hn]
      exact mul_ne_zero (ne_of_gt (clr_pos ht1 n)) (rem_ne_zero ht1 hn)
  · have : ∀ n : ℕ, 1 ≤ n →
        |(B n : ℝ) * S (t : ℝ) - (A n : ℝ)| = |clr (t : ℝ) n * rem (t : ℝ) n| := by
      intro n hn; rw [← hB n, ← hA n, form_eq ht1 hn]
    refine Tendsto.congr' ?_ (clr_mul_rem_tendsto_zero ht1)
    filter_upwards [eventually_ge_atTop 1] with n hn using (this n hn).symm

end QHarm
