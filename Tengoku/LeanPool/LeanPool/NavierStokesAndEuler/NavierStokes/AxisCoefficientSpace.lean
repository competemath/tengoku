/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Defs
public import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Basic
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Lemmas
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Tengoku
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Defs
public import Tengoku.Seed.Data.Finset.NatAntidiagonal
import Tengoku.Seed.Data.Nat.Choose.Vandermonde
import Tengoku.Seed.Tactic.FieldSimp
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool
namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A complete coefficient space with compatible actual derivatives

Normalized bounded continuous jets are restricted by closed, linear
fundamental-theorem-of-calculus identities. Thus a point of the resulting
Banach space determines genuine smooth coefficient functions, not unrelated
arrays masquerading as their derivatives.
-/

section

/-!
# Concrete coefficient estimates for the natural-axis norm

Products are actual
finite coefficient convolutions with the Leibniz binomial factors. In particular,
the mixed derivative estimate is proved after the radial inverse; no boundedness
of either differentiation operator on its own is assumed.
-/

@[expose] public section

namespace NavierStokes.AxisWeightEstimates

open scoped BigOperators
open Finset Finset.Nat

noncomputable section

/-- The exact coefficient weight printed in the candidate manuscript. -/
def weight (ε : ℝ) (n m : ℕ) : ℝ :=
  (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * (m.factorial : ℝ) * ((n + m).choose m : ℝ) /
    (((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2)

/-- The analytic part of the weight, before the two square-decay factors. -/
def coreWeight (ε : ℝ) (n m : ℕ) : ℝ :=
  (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * (m.factorial : ℝ) * ((n + m).choose m : ℝ)

/-- Square decay, given by `1 / ((n : ℝ) + 1) ^ 2`. -/
def squareDecay (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 2

/--
@isnad1 id=eq.0h3v.s5.98a774c76df2 from=translated src=- shape=52db3875 vocab=b70427b1
-/
theorem weight_eq_core_decay (ε : ℝ) (n m : ℕ) :
    weight ε n m = coreWeight ε n m * squareDecay n * squareDecay m := by
  unfold weight coreWeight squareDecay
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/--
@isnad1 id=lt.0h1v.s3.16c54f928e78 from=translated src=- shape=b9369acb vocab=93871959
-/
theorem squareDecay_pos (n : ℕ) : 0 < squareDecay n := by
  unfold squareDecay
  positivity

/--
@isnad1 id=lt.1h3v.s4.e15e3ea3995a from=translated src=- shape=f4002352 vocab=d64ca407
-/
theorem coreWeight_pos {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    0 < coreWeight ε n m := by
  unfold coreWeight
  have hc : 0 < ((n + m).choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : m ≤ n + m)
  positivity

/--
@isnad1 id=lt.1h3v.s4.602103a7c487 from=translated src=- shape=f4002352 vocab=4eb1498e
-/
theorem weight_pos {ε : ℝ} (hε : 0 < ε) (n m : ℕ) : 0 < weight ε n m := by
  rw [weight_eq_core_decay]
  exact mul_pos (mul_pos (coreWeight_pos hε n m) (squareDecay_pos n)) (squareDecay_pos m)

/--
@isnad1 id=le.0h1v.s4.c5fb684dc5b3 from=translated src=- shape=490b3ecf vocab=8c7740ce
-/
theorem squareDecay_succ_le (n : ℕ) : squareDecay (n + 1) ≤ squareDecay n := by
  unfold squareDecay
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  linarith [show (0 : ℝ) ≤ n by positivity]

/--
@isnad1 id=le.0h1v.s5.e784ef5ed447 from=translated src=- shape=8d73523d vocab=35795a5c
-/
theorem squareDecay_le_four_succ (n : ℕ) : squareDecay n ≤ 4 * squareDecay (n + 1) := by
  unfold squareDecay
  have hn : (0 : ℝ) ≤ n := by positivity
  have h₁ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h₂ : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
  rw [show 4 * (1 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2) =
    4 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 by ring]
  rw [div_le_div_iff₀ (sq_pos_of_pos h₁) (sq_pos_of_pos h₂)]
  push_cast
  nlinarith

/-- Elementary telescoping majorant for the square summability estimate.
@isnad1 id=le.1h1v.s6.ec932e29155f from=translated src=- shape=f3a9c139 vocab=075a0716
-/
theorem reciprocal_square_telescope (x : ℝ) (hx : 1 ≤ x) :
    1 / x ^ 2 ≤ 2 / x - 2 / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hid : 2 / x - 2 / (x + 1) = 2 / (x * (x + 1)) := by
    field_simp; ring
  rw [hid, div_le_div_iff₀ (sq_pos_of_pos hx0) (mul_pos hx0 hx1)]
  nlinarith

/--
@isnad1 id=le.0h1v.s6.e4e31b875c8c from=translated src=- shape=4b1eecaf vocab=750e298e
-/
theorem sum_squareDecay_le (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), squareDecay i) ≤ 2 - 2 / ((n : ℝ) + 2) := by
  induction n with
  | zero => norm_num [squareDecay]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn : (0 : ℝ) ≤ n := by positivity
      have htel := reciprocal_square_telescope ((n : ℝ) + 2) (by linarith)
      have hid : squareDecay (n + 1) = 1 / ((n : ℝ) + 2) ^ 2 := by
        simp [squareDecay, Nat.cast_add, Nat.cast_one]
        ring
      rw [hid]
      push_cast
      ring_nf at ih htel ⊢
      linarith

/--
@isnad1 id=le.0h1v.s5.2f3a82e206cb from=translated src=- shape=45684c87 vocab=cf743395
-/
theorem sum_squareDecay_le_two (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), squareDecay i) ≤ 2 := by
  have h := sum_squareDecay_le n
  have hp : 0 ≤ 2 / ((n : ℝ) + 2) := by positivity
  linarith

/--
@isnad1 id=le.0h2v.s5.55054e5b767a from=translated src=- shape=9a8974e4 vocab=35795a5c
-/
theorem squareDecay_product_le (i j : ℕ) :
    squareDecay i * squareDecay j ≤
      2 * squareDecay (i + j) * (squareDecay i + squareDecay j) := by
  have hi : 0 < (i : ℝ) + 1 := by positivity
  have hj : 0 < (j : ℝ) + 1 := by positivity
  have hij : 0 < ((i + j : ℕ) : ℝ) + 1 := by positivity
  have hpoly : (((i + j : ℕ) : ℝ) + 1) ^ 2 ≤
      2 * (((i : ℝ) + 1) ^ 2 + ((j : ℝ) + 1) ^ 2) := by
    push_cast
    linarith [sq_nonneg ((i : ℝ) - (j : ℝ))]
  have hh := div_le_div_of_nonneg_right hpoly (le_of_lt
    (mul_pos (mul_pos (sq_pos_of_pos hi) (sq_pos_of_pos hj)) (sq_pos_of_pos hij)))
  convert! hh using 1 <;> unfold squareDecay <;>
    field_simp [ne_of_gt hi, ne_of_gt hj, ne_of_gt hij]
  ring

/-- The one-dimensional convolution constant is at most eight.
@isnad1 id=le.0h1v.s5.c7ca572eb4d1 from=translated src=- shape=344434f8 vocab=42cda2c7
-/
theorem squareDecay_convolution_le (n : ℕ) :
    (∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) ≤ 8 * squareDecay n := by
  have hsum : (∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) ≤
      ∑ ij ∈ antidiagonal n, 2 * squareDecay n * (squareDecay ij.1 + squareDecay ij.2) := by
    apply Finset.sum_le_sum
    intro ij hij
    have h := squareDecay_product_le ij.1 ij.2
    rw [mem_antidiagonal.mp hij] at h
    exact h
  have hfirst : (∑ ij ∈ antidiagonal n, squareDecay ij.1) ≤ 2 := by
    rw [sum_antidiagonal_eq_sum_range_succ_mk]
    exact sum_squareDecay_le_two n
  have hsecond : (∑ ij ∈ antidiagonal n, squareDecay ij.2) ≤ 2 := by
    have heq : (∑ ij ∈ antidiagonal n, squareDecay ij.2) =
        ∑ ij ∈ antidiagonal n, squareDecay ij.1 := by
      simpa only [Prod.fst_swap] using
        (sum_antidiagonal_swap (n := n) (f := fun ij => squareDecay ij.1))
    rw [heq]
    exact hfirst
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hd := (squareDecay_pos n).le
  nlinarith

/-- A term of Vandermonde's sum gives the binomial estimate used in the norm.
@isnad1 id=le.0h4v.s6.9e7553e62f9c from=translated src=- shape=ceae2026 vocab=6e3d1898
-/
theorem choose_product_le (i j k l : ℕ) :
    (i + k).choose k * (j + l).choose l ≤ ((i + j) + (k + l)).choose (k + l) := by
  have h := Finset.single_le_sum (fun p (_ : p ∈ antidiagonal (k + l)) =>
    Nat.zero_le ((i + k).choose p.1 * (j + l).choose p.2))
    (show (k, l) ∈ antidiagonal (k + l) from mem_antidiagonal.mpr rfl)
  rw [← Nat.add_choose_eq] at h
  have hindex : i + k + (j + l) = i + j + (k + l) := by omega
  rw [hindex] at h
  exact h

/--
@isnad1 id=eq.0h2v.s5.ccbd5f471323 from=translated src=- shape=d760f63f vocab=517e7d58
-/
theorem choose_factorials (k l : ℕ) :
    ((k + l).choose k : ℝ) * (k.factorial : ℝ) * (l.factorial : ℝ) =
      ((k + l).factorial : ℝ) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial l k
  rw [Nat.add_comm l k, Nat.mul_right_comm] at h
  exact_mod_cast h

/-- The analytic factors respect the Leibniz convolution with constant one.
@isnad1 id=le.1h5v.s6.9d2d05eed3f4 from=translated src=- shape=1c89f78f vocab=317b9250
-/
theorem coreWeight_product_le {ε : ℝ} (hε : 0 < ε) (i j k l : ℕ) :
    ((k + l).choose k : ℝ) * coreWeight ε i k * coreWeight ε j l ≤
      coreWeight ε (i + j) (k + l) := by
  have hc : ((i + k).choose k : ℝ) * ((j + l).choose l : ℝ) ≤
      (((i + j) + (k + l)).choose (k + l) : ℝ) := by
    exact_mod_cast choose_product_le i j k l
  have hfac := choose_factorials k l
  have hnonneg : 0 ≤ (1 / 20 : ℝ) ^ (i + j) * (ε⁻¹) ^ (k + l) *
      ((k + l).factorial : ℝ) := by positivity
  calc
    _ = ((1 / 20 : ℝ) ^ (i + j) * (ε⁻¹) ^ (k + l) * ((k + l).factorial : ℝ)) *
        (((i + k).choose k : ℝ) * ((j + l).choose l : ℝ)) := by
      rw [← hfac]
      unfold coreWeight
      rw [pow_add, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hnonneg

/-- Factorial form used only to prove the exact shift identities.
@isnad1 id=eq.0h3v.s6.762829467024 from=translated src=- shape=191f2a98 vocab=eeab4f36
-/
theorem coreWeight_factorial (ε : ℝ) (n m : ℕ) :
    coreWeight ε n m =
      (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * ((n + m).factorial : ℝ) / (n.factorial : ℝ) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hf : (m.factorial : ℝ) * ((n + m).choose m : ℝ) * (n.factorial : ℝ) =
      ((n + m).factorial : ℝ) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial n m
    exact_mod_cast (by simpa only [mul_comm, mul_left_comm, mul_assoc] using h)
  apply (eq_div_iff hn).2
  unfold coreWeight
  calc
    _ = (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m *
        ((m.factorial : ℝ) * ((n + m).choose m : ℝ) * (n.factorial : ℝ)) := by ring
    _ = _ := by rw [hf]

/--
@isnad1 id=eq.1h3v.s6.37e2d158cfe0 from=translated src=- shape=d15a0088 vocab=5d7b01fd
-/
theorem coreWeight_radial_identity {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    coreWeight ε n m * ((n : ℝ) + m + 1) =
      20 * ((n : ℝ) + 1) * coreWeight ε (n + 1) m := by
  rw [coreWeight_factorial, coreWeight_factorial]
  have hindex : n + 1 + m = (n + m) + 1 := by omega
  rw [hindex, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
  push_cast
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [ne_of_gt hε, hn, hn1]

/--
@isnad1 id=le.1h3v.s5.b064ad84ff38 from=translated src=- shape=88e8008c vocab=f8b2d241
-/
theorem coreWeight_radial_le {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    coreWeight ε n m ≤ 20 * coreWeight ε (n + 1) m := by
  have hp : 0 < (n : ℝ) + 1 := by positivity
  apply (mul_le_mul_iff_left₀ hp).mp
  calc
    coreWeight ε n m * ((n : ℝ) + 1) ≤
        coreWeight ε n m * ((n : ℝ) + m + 1) := by
      exact mul_le_mul_of_nonneg_left (by
        have hm : (0 : ℝ) ≤ m := by positivity
        linarith)
        (coreWeight_pos hε n m).le
    _ = 20 * coreWeight ε (n + 1) m * ((n : ℝ) + 1) := by
      rw [coreWeight_radial_identity hε]
      ring

/--
@isnad1 id=eq.1h3v.s6.c4cb4801522d from=translated src=- shape=7e29a580 vocab=cf6298a4
-/
theorem coreWeight_parameter_shift {ε : ℝ} (hε : 0 < ε) (i k : ℕ) :
    coreWeight ε i (k + 1) =
      (20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k := by
  rw [coreWeight_factorial, coreWeight_factorial]
  have hindex : i + 1 + k = i + (k + 1) := by omega
  rw [hindex, Nat.factorial_succ, pow_succ, pow_succ]
  push_cast
  have hi : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hi1 : (i : ℝ) + 1 ≠ 0 := by positivity
  have he := ne_of_gt hε
  field_simp

/-- A radial shift costs at most the printed factor `4 * 20 = 80`.
@isnad1 id=le.1h3v.s5.95eed4dba5e6 from=translated src=- shape=88e8008c vocab=d087e62b
-/
theorem weight_radial_shift {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    weight ε n m ≤ 80 * weight ε (n + 1) m := by
  rw [weight_eq_core_decay, weight_eq_core_decay]
  calc
    _ ≤ (20 * coreWeight ε (n + 1) m) * (4 * squareDecay (n + 1)) * squareDecay m := by
      apply mul_le_mul_of_nonneg_right _ (squareDecay_pos m).le
      exact mul_le_mul (coreWeight_radial_le hε n m) (squareDecay_le_four_succ n)
        (squareDecay_pos n).le (mul_nonneg (by norm_num) (coreWeight_pos hε (n + 1) m).le)
    _ = _ := by ring

/--
@isnad1 id=le.1h3v.s5.b98e6c27977b from=translated src=- shape=37bdd930 vocab=25357e85
-/
theorem weight_radial_shift_ratio {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    weight ε n m / weight ε (n + 1) m ≤ 80 := by
  exact (div_le_iff₀ (weight_pos hε (n + 1) m)).2 (weight_radial_shift hε n m)

/-- Assigning the output radial shift to a parameter-differentiated factor.
@isnad1 id=le.1h3v.s6.ffd45810f06e from=translated src=- shape=7e29a580 vocab=c468c218
-/
theorem weight_parameter_radial_shift {ε : ℝ} (hε : 0 < ε) (i k : ℕ) :
    weight ε i (k + 1) ≤ (80 / ε) * ((i : ℝ) + 1) * weight ε (i + 1) k := by
  have hc : 0 ≤ (20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k := by
    have hcpos := coreWeight_pos hε (i + 1) k
    positivity
  have hd := mul_le_mul (squareDecay_le_four_succ i) (squareDecay_succ_le k)
    (squareDecay_pos (k + 1)).le (mul_nonneg (by norm_num) (squareDecay_pos (i + 1)).le)
  rw [weight_eq_core_decay, coreWeight_parameter_shift hε, weight_eq_core_decay]
  calc
    _ = ((20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k) *
        (squareDecay i * squareDecay (k + 1)) := by ring
    _ ≤ ((20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k) *
        (4 * squareDecay (i + 1) * squareDecay k) := mul_le_mul_of_nonneg_left hd hc
    _ = _ := by ring

/--
@isnad1 id=le.1h3v.s6.e3e6ba3f2115 from=translated src=- shape=58b3aa8a vocab=c468c218
-/
theorem weight_parameter_radial_shift_ratio {ε : ℝ} (hε : 0 < ε) (i k : ℕ) :
    weight ε i (k + 1) / weight ε (i + 1) k ≤ (80 / ε) * ((i : ℝ) + 1) := by
  exact (div_le_iff₀ (weight_pos hε (i + 1) k)).2 (weight_parameter_radial_shift hε i k)

/-- The finite weight convolution associated with radial multiplication and
the parameter Leibniz rule. -/
def productWeightSum (ε : ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (m.choose kl.1 : ℝ) * weight ε ij.1 kl.1 * weight ε ij.2 kl.2

/--
@isnad1 id=le.1h5v.s6.ede98cf8d7a5 from=translated src=- shape=3bb66e7c vocab=143a075c
-/
theorem weight_product_term_le {ε : ℝ} (hε : 0 < ε) (i j k l : ℕ) :
    ((k + l).choose k : ℝ) * weight ε i k * weight ε j l ≤
      coreWeight ε (i + j) (k + l) * (squareDecay i * squareDecay j) *
        (squareDecay k * squareDecay l) := by
  have hd : 0 ≤ squareDecay i * squareDecay j * squareDecay k * squareDecay l := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (squareDecay_pos i).le
      (squareDecay_pos j).le) (squareDecay_pos k).le) (squareDecay_pos l).le
  calc
    _ = (((k + l).choose k : ℝ) * coreWeight ε i k * coreWeight ε j l) *
        (squareDecay i * squareDecay j * squareDecay k * squareDecay l) := by
      rw [weight_eq_core_decay, weight_eq_core_decay]
      ring
    _ ≤ coreWeight ε (i + j) (k + l) *
        (squareDecay i * squareDecay j * squareDecay k * squareDecay l) :=
      mul_le_mul_of_nonneg_right (coreWeight_product_le hε i j k l) hd
    _ = _ := by ring

/-- The manuscript's uniform algebra constant `64`, with actual finite sums.
@isnad1 id=le.1h3v.s5.7a6a56890000 from=translated src=- shape=3a2eff7f vocab=b947d384
-/
theorem productWeightSum_le {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    productWeightSum ε n m ≤ 64 * weight ε n m := by
  have hsum : productWeightSum ε n m ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        coreWeight ε n m * (squareDecay ij.1 * squareDecay ij.2) *
          (squareDecay kl.1 * squareDecay kl.2) := by
    apply Finset.sum_le_sum
    intro ij hij
    apply Finset.sum_le_sum
    intro kl hkl
    have h := weight_product_term_le hε ij.1 ij.2 kl.1 kl.2
    rw [mem_antidiagonal.mp hij, mem_antidiagonal.mp hkl] at h
    exact h
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        coreWeight ε n m * (squareDecay ij.1 * squareDecay ij.2) *
          (squareDecay kl.1 * squareDecay kl.2)) =
      coreWeight ε n m *
        (∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) *
        (∑ kl ∈ antidiagonal m, squareDecay kl.1 * squareDecay kl.2) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hfactor] at hsum
  have hn0 : 0 ≤ ∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2 :=
    Finset.sum_nonneg (fun ij _ => mul_nonneg (squareDecay_pos _).le (squareDecay_pos _).le)
  have hm0 : 0 ≤ ∑ kl ∈ antidiagonal m, squareDecay kl.1 * squareDecay kl.2 :=
    Finset.sum_nonneg (fun kl _ => mul_nonneg (squareDecay_pos _).le (squareDecay_pos _).le)
  have hprod := mul_le_mul (squareDecay_convolution_le n) (squareDecay_convolution_le m)
    hm0 (mul_nonneg (by norm_num) (squareDecay_pos n).le)
  calc
    _ ≤ coreWeight ε n m *
        ((∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) *
        (∑ kl ∈ antidiagonal m, squareDecay kl.1 * squareDecay kl.2)) := by
      simpa only [mul_assoc] using hsum
    _ ≤ coreWeight ε n m * ((8 * squareDecay n) * (8 * squareDecay m)) :=
      mul_le_mul_of_nonneg_left hprod (coreWeight_pos hε n m).le
    _ = _ := by rw [weight_eq_core_decay]; ring

/-- Actual radial convolution with the parameter Leibniz coefficients. -/
def jetProduct (f g : ℕ → ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (m.choose kl.1 : ℝ) * f ij.1 kl.1 * g ij.2 kl.2

/--
@isnad1 id=le.7h7v.s7.020caf77bbef from=translated src=- shape=9b56ef88 vocab=d96afd66
-/
theorem abs_bilinear_term_le (a x y wx wy F G : ℝ)
    (ha : 0 ≤ a) (hF : 0 ≤ F) (_hG : 0 ≤ G) (hwx : 0 ≤ wx) (_hwy : 0 ≤ wy)
    (hx : |x| ≤ F * wx) (hy : |y| ≤ G * wy) :
    |a * x * y| ≤ (F * G) * (a * wx * wy) := by
  rw [abs_mul, abs_mul, abs_of_nonneg ha]
  calc
    a * |x| * |y| = a * (|x| * |y|) := by ring
    _ ≤ a * ((F * wx) * (G * wy)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hx hy (abs_nonneg y) (mul_nonneg hF hwx)) ha
    _ = _ := by ring

/--
@isnad1 id=le.1h6v.s6.ed792bc8d68a from=translated src=- shape=5a95886e vocab=b12c75ee
-/
theorem abs_double_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f M : ι → κ → ℝ) (h : ∀ i ∈ s, ∀ k ∈ t, |f i k| ≤ M i k) :
    |∑ i ∈ s, ∑ k ∈ t, f i k| ≤ ∑ i ∈ s, ∑ k ∈ t, M i k := by
  calc
    _ ≤ ∑ i ∈ s, |∑ k ∈ t, f i k| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      exact (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (h i hi))

/-- Uniform coefficient product bound, requiring only the actual coefficient
bounds on the two input arrays.
@isnad1 id=le.5h7v.s7.891a2d174d4a from=translated src=- shape=7da15dde vocab=4e3d01e1
-/
theorem jetProduct_bound {ε F G : ℝ} (hε : 0 < ε) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (f g : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m)
    (hg : ∀ n m, |g n m| ≤ G * weight ε n m) (n m : ℕ) :
    |jetProduct f g n m| ≤ 64 * F * G * weight ε n m := by
  have hsum : |jetProduct f g n m| ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((m.choose kl.1 : ℝ) * weight ε ij.1 kl.1 * weight ε ij.2 kl.2) := by
    apply abs_double_sum_le
    intro ij hij kl hkl
    exact abs_bilinear_term_le _ _ _ _ _ _ _ (Nat.cast_nonneg _) hF hG
      (weight_pos hε _ _).le (weight_pos hε _ _).le (hf _ _) (hg _ _)
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((m.choose kl.1 : ℝ) * weight ε ij.1 kl.1 * weight ε ij.2 kl.2)) =
      (F * G) * productWeightSum ε n m := by
    simp only [productWeightSum, Finset.mul_sum]
  rw [hfactor] at hsum
  calc
    _ ≤ (F * G) * productWeightSum ε n m := hsum
    _ ≤ (F * G) * (64 * weight ε n m) :=
      mul_le_mul_of_nonneg_left (productWeightSum_le hε n m) (mul_nonneg hF hG)
    _ = _ := by ring

/-- Radial divisor, given by `((n : ℝ) + 1) * ((n : ℝ) + r)`. -/
def radialDivisor (r n : ℕ) : ℝ := ((n : ℝ) + 1) * ((n : ℝ) + r)

/--
@isnad1 id=lt.1h2v.s4.bba4b6767305 from=translated src=- shape=c62f519e vocab=2880e4fb
-/
theorem radialDivisor_pos {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : 0 < radialDivisor r n := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  unfold radialDivisor
  positivity

/-- The extra parameter and dot factors fit inside the regular radial divisor.
@isnad1 id=le.2h4v.s6.7488338f2158 from=translated src=- shape=75d4eb5e vocab=8089f6d7
-/
theorem mixed_factors_le_divisor {r n i j : ℕ} (hr : 1 ≤ r) (hij : i + j = n) :
    ((i : ℝ) + 1) * (j : ℝ) ≤ radialDivisor r n := by
  have hi : i + 1 ≤ n + 1 := by omega
  have hj : j ≤ n + r := by omega
  unfold radialDivisor
  exact_mod_cast Nat.mul_le_mul hi hj

/-- Shifted product weight sum, given by `∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
(m.choose kl.1 : ℝ) * weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2`. -/
def shiftedProductWeightSum (ε : ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (m.choose kl.1 : ℝ) * weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2

/--
@isnad1 id=le.1h3v.s5.3084f05c2cdd from=translated src=- shape=f2e59857 vocab=e16c13ea
-/
theorem shiftedProductWeightSum_le {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    shiftedProductWeightSum ε n m ≤ 64 * weight ε (n + 1) m := by
  have hsub : shiftedProductWeightSum ε n m ≤ productWeightSum ε (n + 1) m := by
    unfold productWeightSum
    rw [sum_antidiagonal_succ]
    change shiftedProductWeightSum ε n m ≤ _ + shiftedProductWeightSum ε n m
    apply le_add_of_nonneg_left
    apply Finset.sum_nonneg
    intro kl hkl
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (weight_pos hε _ _).le)
      (weight_pos hε _ _).le
  exact hsub.trans (productWeightSum_le hε (n + 1) m)

/-- A single mixed term after applying the inverse radial divisor.
@isnad1 id=le.3h8v.s7.b416912ce72b from=translated src=- shape=4de43da4 vocab=5c16e653
-/
theorem mixed_weight_term_le {ε : ℝ} (hε : 0 < ε) {r n i j : ℕ}
    (hr : 1 ≤ r) (hij : i + j = n) (m k l : ℕ) :
    (((m.choose k : ℝ) * j) / radialDivisor r n) * weight ε i (k + 1) * weight ε j l ≤
      (80 / ε) * ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l) := by
  have hD := radialDivisor_pos hr n
  have hcoef : 0 ≤ ((m.choose k : ℝ) * j) / radialDivisor r n := by positivity
  have hfactor : (((i : ℝ) + 1) * j) / radialDivisor r n ≤ 1 := by
    apply (div_le_iff₀ hD).2
    simpa only [one_mul] using mixed_factors_le_divisor hr hij
  have hnonneg : 0 ≤ (80 / ε) *
      ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l) := by
    exact mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (weight_pos hε _ _).le) (weight_pos hε _ _).le)
  calc
    _ ≤ (((m.choose k : ℝ) * j) / radialDivisor r n) *
        ((80 / ε) * ((i : ℝ) + 1) * weight ε (i + 1) k) * weight ε j l := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (weight_parameter_radial_shift hε i k) hcoef)
        (weight_pos hε _ _).le
    _ = ((80 / ε) * ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l)) *
        ((((i : ℝ) + 1) * j) / radialDivisor r n) := by ring
    _ ≤ ((80 / ε) * ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l)) * 1 :=
      mul_le_mul_of_nonneg_left hfactor hnonneg
    _ = _ := mul_one _

/-- Mixed weight sum, choosing the witness provided by `kl.1`. -/
def mixedWeightSum (ε : ℝ) (r n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
      weight ε ij.1 (kl.1 + 1) * weight ε ij.2 kl.2

/--
@isnad1 id=le.2h4v.s6.197dc3cd2a0b from=translated src=- shape=1a8b2f3a vocab=9a8e9f0c
-/
theorem mixedWeightSum_le {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : 1 ≤ r) (n m : ℕ) :
    mixedWeightSum ε r n m ≤ (5120 / ε) * weight ε (n + 1) m := by
  have hsum : mixedWeightSum ε r n m ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (80 / ε) * ((m.choose kl.1 : ℝ) * weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2) := by
    apply Finset.sum_le_sum
    intro ij hij
    apply Finset.sum_le_sum
    intro kl hkl
    exact mixed_weight_term_le hε hr (mem_antidiagonal.mp hij) m kl.1 kl.2
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (80 / ε) * ((m.choose kl.1 : ℝ) * weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2)) =
      (80 / ε) * shiftedProductWeightSum ε n m := by
    simp only [shiftedProductWeightSum, Finset.mul_sum]
  rw [hfactor] at hsum
  calc
    _ ≤ (80 / ε) * shiftedProductWeightSum ε n m := hsum
    _ ≤ (80 / ε) * (64 * weight ε (n + 1) m) :=
      mul_le_mul_of_nonneg_left (shiftedProductWeightSum_le hε n m) (by positivity)
    _ = _ := by ring

/-- The coefficient at radial degree n+1 of J_r((∂η f) D_Y g).
The radial divisor is distributed over its finite convolution sum. -/
def inverseMixedJet (r : ℕ) (f g : ℕ → ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
      f ij.1 (kl.1 + 1) * g ij.2 kl.2

/-- The mixed derivative is bounded after radial inversion, with explicit
constant 5120/ε. Neither individual derivative is assumed bounded.
@isnad1 id=le.6h8v.s7.0c48720b36c7 from=translated src=- shape=2356167d vocab=b65c212c
-/
theorem inverseMixedJet_bound {ε F G : ℝ} (hε : 0 < ε) (hF : 0 ≤ F) (hG : 0 ≤ G)
    {r : ℕ} (hr : 1 ≤ r) (f g : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m)
    (hg : ∀ n m, |g n m| ≤ G * weight ε n m) (n m : ℕ) :
    |inverseMixedJet r f g n m| ≤ (5120 / ε) * F * G * weight ε (n + 1) m := by
  have hD := radialDivisor_pos hr n
  have hsum : |inverseMixedJet r f g n m| ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
          weight ε ij.1 (kl.1 + 1) * weight ε ij.2 kl.2) := by
    apply abs_double_sum_le
    intro ij hij kl hkl
    exact abs_bilinear_term_le _ _ _ _ _ _ _ (by positivity) hF hG
      (weight_pos hε _ _).le (weight_pos hε _ _).le (hf _ _) (hg _ _)
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
          weight ε ij.1 (kl.1 + 1) * weight ε ij.2 kl.2)) =
      (F * G) * mixedWeightSum ε r n m := by
    simp only [mixedWeightSum, Finset.mul_sum]
  rw [hfactor] at hsum
  calc
    _ ≤ (F * G) * mixedWeightSum ε r n m := hsum
    _ ≤ (F * G) * ((5120 / ε) * weight ε (n + 1) m) :=
      mul_le_mul_of_nonneg_left (mixedWeightSum_le hε hr n m) (mul_nonneg hF hG)
    _ = _ := by ring

/-- Coefficients of the radial averaging operator `Bf(Y)=∫₀¹ f(tY)dt`. -/
def averageJet (f : ℕ → ℕ → ℝ) (n m : ℕ) : ℝ := f n m / ((n : ℝ) + 1)

/-- Coefficients of the zero-datum primitive. -/
def primitiveJet (f : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => f n m / ((n : ℝ) + 1)

/-- Coefficients of the regular zero-datum inverse of `Y f'' + r f'`. -/
def regularInverseJet (r : ℕ) (f : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => f n m / radialDivisor r n

/-- The primitive is applied together with the parameter derivative. -/
def parameterPrimitiveJet (f : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => f n (m + 1) / ((n : ℝ) + 1)

/--
@isnad1 id=le.3h5v.s6.548248580024 from=translated src=- shape=6164631c vocab=b347efcd
-/
theorem averageJet_bound {ε F : ℝ} (_hε : 0 < ε) (_hF : 0 ≤ F)
    (f : ℕ → ℕ → ℝ) (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |averageJet f n m| ≤ F * weight ε n m := by
  unfold averageJet
  rw [abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  exact (div_le_self (abs_nonneg _) (by
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith)).trans (hf n m)

/--
@isnad1 id=le.3h5v.s6.16c2a91bf16a from=translated src=- shape=6360c81b vocab=41ca8e3e
-/
theorem primitiveJet_bound {ε F : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    (f : ℕ → ℕ → ℝ) (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |primitiveJet f n m| ≤ 80 * F * weight ε n m := by
  cases n with
  | zero =>
      simpa only [primitiveJet, abs_zero] using
        (mul_nonneg (mul_nonneg (by norm_num) hF) (weight_pos hε 0 m).le)
  | succ n =>
      calc
        |primitiveJet f (n + 1) m| = |averageJet f n m| := rfl
        _ ≤ F * weight ε n m := averageJet_bound hε hF f hf n m
        _ ≤ F * (80 * weight ε (n + 1) m) :=
          mul_le_mul_of_nonneg_left (weight_radial_shift hε n m) hF
        _ = _ := by ring

/--
@isnad1 id=le.1h2v.s4.58516cddd1e2 from=translated src=- shape=c8a788b1 vocab=02140bde
-/
theorem radialDivisor_ge_one {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : 1 ≤ radialDivisor r n := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ha : (1 : ℝ) ≤ n + 1 := by linarith
  have hb : (1 : ℝ) ≤ n + r := by linarith
  simpa only [one_mul, radialDivisor] using
    (mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (n : ℝ) + 1))

/--
@isnad1 id=le.4h6v.s6.94d672cfec29 from=translated src=- shape=65443d21 vocab=e8cae7ae
-/
theorem regularInverseJet_bound {ε F : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    {r : ℕ} (hr : 1 ≤ r) (f : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |regularInverseJet r f n m| ≤ 80 * F * weight ε n m := by
  cases n with
  | zero =>
      simpa only [regularInverseJet, abs_zero] using
        (mul_nonneg (mul_nonneg (by norm_num) hF) (weight_pos hε 0 m).le)
  | succ n =>
      rw [regularInverseJet, abs_div, abs_of_pos (radialDivisor_pos hr n)]
      calc
        |f n m| / radialDivisor r n ≤ |f n m| :=
          div_le_self (abs_nonneg _) (radialDivisor_ge_one hr n)
        _ ≤ F * weight ε n m := hf n m
        _ ≤ F * (80 * weight ε (n + 1) m) :=
          mul_le_mul_of_nonneg_left (weight_radial_shift hε n m) hF
        _ = _ := by ring

/--
@isnad1 id=le.3h5v.s6.b09a85c013e6 from=translated src=- shape=b5a9d79c vocab=2351ff60
-/
theorem parameterPrimitiveJet_bound {ε F : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    (f : ℕ → ℕ → ℝ) (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |parameterPrimitiveJet f n m| ≤ (80 / ε) * F * weight ε n m := by
  cases n with
  | zero =>
      simpa only [parameterPrimitiveJet, abs_zero] using
        (mul_nonneg (mul_nonneg (show 0 ≤ 80 / ε by positivity) hF) (weight_pos hε 0 m).le)
  | succ n =>
      rw [parameterPrimitiveJet, abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
      calc
        |f n (m + 1)| ≤ F * weight ε n (m + 1) := hf n (m + 1)
        _ ≤ F * ((80 / ε) * ((n : ℝ) + 1) * weight ε (n + 1) m) :=
          mul_le_mul_of_nonneg_left (weight_parameter_radial_shift hε n m) hF
        _ = _ := by ring

/-- Put the already estimated mixed coefficient in its output radial degree. -/
def regularInverseMixedJet (r : ℕ) (f g : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => inverseMixedJet r f g n m

/--
@isnad1 id=le.6h8v.s7.37c37a3be14b from=translated src=- shape=c317b611 vocab=4c5c6d9c
-/
theorem regularInverseMixedJet_bound {ε F G : ℝ}
    (hε : 0 < ε) (hF : 0 ≤ F) (hG : 0 ≤ G) {r : ℕ} (hr : 1 ≤ r)
    (f g : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m)
    (hg : ∀ n m, |g n m| ≤ G * weight ε n m) (n m : ℕ) :
    |regularInverseMixedJet r f g n m| ≤ (5120 / ε) * F * G * weight ε n m := by
  cases n with
  | zero =>
      simpa only [regularInverseMixedJet, abs_zero] using
        (mul_nonneg (mul_nonneg (mul_nonneg (show 0 ≤ 5120 / ε by positivity) hF) hG)
          (weight_pos hε 0 m).le)
  | succ n => exact inverseMixedJet_bound hε hF hG hr f g hf hg n m

end

end NavierStokes.AxisWeightEstimates

end

end

@[expose] public section

noncomputable section

namespace NavierStokes.AxisCoefficientSpace

open Set MeasureTheory
open scoped Topology BoundedContinuousFunction ContDiff

/-- A fixed nondegenerate compact real parameter interval. -/
structure Window where
  /-- Left of `Window`, of type `ℝ`. -/
  left : ℝ
  /-- Right of `Window`, of type `ℝ`. -/
  right : ℝ
  nondegenerate : left < right

/-- Interval, given by `Icc I.left I.right`. -/
def Window.interval (I : Window) : Set ℝ := Icc I.left I.right

/-- The continuous clamping map is only an extension device. Smoothness is
proved on the original closed interval, including its one-sided endpoint jets. -/
def Window.project (I : Window) : ℝ → I.interval :=
  projIcc I.left I.right I.nondegenerate.le

/--
@isnad1 id=continuo.0h1v.s5.547495571430 from=translated src=- shape=0a9af14d vocab=305581fc
-/
theorem Window.continuous_project (I : Window) : Continuous I.project :=
  continuous_projIcc

/--
@isnad1 id=eq.1h2v.s5.491d3be6281c from=translated src=- shape=63d368ee vocab=34abc62c
-/
theorem Window.project_of_mem (I : Window) {x : ℝ} (hx : x ∈ I.interval) :
    I.project x = ⟨x, hx⟩ :=
  projIcc_of_mem I.nondegenerate.le hx

/-- Ambient normalized jets with the supremum norm over both indices and
the compact parameter interval. -/
abbrev RawJets (I : Window) := ((ℕ × ℕ) × I.interval) →ᵇ ℝ

/-- Unnormalized, continuously extended `m`-th jet of coefficient `n`. -/
def jet (I : Window) (w : ℕ → ℕ → ℝ) (A : RawJets I) (n m : ℕ) (x : ℝ) : ℝ :=
  w n m * A ((n, m), I.project x)

/--
@isnad1 id=continuo.0h5v.s5.52ffeded2c38 from=translated src=- shape=6ddb174c vocab=ee2f839a
-/
theorem continuous_jet (I : Window) (w : ℕ → ℕ → ℝ) (A : RawJets I) (n m : ℕ) :
    Continuous (jet I w A n m) := by
  exact continuous_const.mul
    (A.continuous.comp (continuous_const.prodMk I.continuous_project))

/--
@isnad1 id=eq.0h5v.s6.c38b51d0bbe8 from=translated src=- shape=f5db6f39 vocab=a543818b
-/
@[simp] theorem jet_zero (I : Window) (w : ℕ → ℕ → ℝ) (n m : ℕ) (x : ℝ) :
    jet I w 0 n m x = 0 := by simp [jet]

/--
@isnad1 id=eq.0h7v.s6.d2f4be918921 from=translated src=- shape=e5fbf133 vocab=670c8243
-/
@[simp] theorem jet_add (I : Window) (w : ℕ → ℕ → ℝ) (A B : RawJets I)
    (n m : ℕ) (x : ℝ) :
    jet I w (A + B) n m x = jet I w A n m x + jet I w B n m x := by
  simp [jet, mul_add]

/--
@isnad1 id=eq.0h7v.s6.1abe26b29c1a from=translated src=- shape=e5fbf133 vocab=92476a9b
-/
@[simp] theorem jet_sub (I : Window) (w : ℕ → ℕ → ℝ) (A B : RawJets I)
    (n m : ℕ) (x : ℝ) :
    jet I w (A - B) n m x = jet I w A n m x - jet I w B n m x := by
  simp [jet, mul_sub]

/--
@isnad1 id=eq.0h7v.s6.d10d2c334c39 from=translated src=- shape=cde70f6f vocab=ffbb2beb
-/
@[simp] theorem jet_smul (I : Window) (w : ℕ → ℕ → ℝ) (c : ℝ) (A : RawJets I)
    (n m : ℕ) (x : ℝ) :
    jet I w (c • A) n m x = c * jet I w A n m x := by
  simp [jet]
  ring

/-- Compatibility is an actual FTC identity for every successive pair of
jets, throughout the full interval. -/
def Compatible (I : Window) (w : ℕ → ℕ → ℝ) (A : RawJets I) : Prop :=
  ∀ n m x, x ∈ I.interval →
    jet I w A n m x = jet I w A n m I.left +
      ∫ t in I.left..x, jet I w A n (m + 1) t

/-- The compatible arrays form a linear subspace of the ambient Banach space. -/
def compatibleSubmodule (I : Window) (w : ℕ → ℕ → ℝ) : Submodule ℝ (RawJets I) where
  carrier := {A | Compatible I w A}
  zero_mem' := by
    intro n m x hx
    simp
  add_mem' := by
    intro A B hA hB n m x hx
    simp only [jet_add]
    rw [intervalIntegral.integral_add
      ((continuous_jet I w A n (m + 1)).intervalIntegrable I.left x)
      ((continuous_jet I w B n (m + 1)).intervalIntegrable I.left x),
      hA n m x hx, hB n m x hx]
    ring
  smul_mem' := by
    intro c A hA n m x hx
    simp only [jet_smul, intervalIntegral.integral_const_mul]
    rw [hA n m x hx]
    ring

/-- The coefficient space, retaining the inherited genuine norm and linear structure. -/
abbrev CoefficientSpace (I : Window) (w : ℕ → ℕ → ℝ) := compatibleSubmodule I w

/-- A coefficient is the zeroth actual jet. -/
def coefficient (I : Window) (w : ℕ → ℕ → ℝ) (A : CoefficientSpace I w) (n : ℕ) : ℝ → ℝ :=
  jet I w A.1 n 0

/-- FTC compatibility identifies the derivative within the closed interval;
this includes the corresponding one-sided endpoint derivatives.
@isnad1 id=hasderiv.1h6v.s10.eeaae8abea38 from=translated src=- shape=f81dd31e vocab=ab0ef655
-/
theorem hasDerivWithinAt_jet (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    HasDerivWithinAt (jet I w A.1 n m) (jet I w A.1 n (m + 1) x) I.interval x := by
  have h := ((continuous_jet I w A.1 n (m + 1)).integral_hasStrictDerivAt I.left
      x).hasDerivAt.const_add
    (jet I w A.1 n m I.left)
  exact h.hasDerivWithinAt.congr_of_mem (fun y hy => A.2 n m y hy) hx

/--
@isnad1 id=eq.1h6v.s10.e852c0f02842 from=translated src=- shape=0e21367a vocab=8ebaa493
-/
theorem derivWithin_jet (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    derivWithin (jet I w A.1 n m) I.interval x = jet I w A.1 n (m + 1) x :=
  (hasDerivWithinAt_jet I w A n m hx).derivWithin
    (uniqueDiffOn_Icc I.nondegenerate x hx)

/-- At every interior point these are the ordinary real derivatives.
@isnad1 id=hasderiv.1h6v.s10.59f1c9be083b from=translated src=- shape=b104ed4b vocab=bb9a7f6e
-/
theorem hasDerivAt_jet_interior (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ}
    (hx : x ∈ Ioo I.left I.right) :
    HasDerivAt (jet I w A.1 n m) (jet I w A.1 n (m + 1) x) x :=
  (hasDerivWithinAt_jet I w A n m ⟨hx.1.le, hx.2.le⟩).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)

/-- Every stored jet is the corresponding iterated derivative of the actual function.
@isnad1 id=eq.1h7v.s10.c31b7f3467fc from=translated src=- shape=675b5e7c vocab=c4f49b3c
-/
theorem iteratedDerivWithin_jet (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n q m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    iteratedDerivWithin m (jet I w A.1 n q) I.interval x = jet I w A.1 n (q + m) x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (fun y hy => ih hy) (ih hx), derivWithin_jet I w A n (q + m) hx]
    simp only [Nat.add_assoc]

/--
@isnad1 id=eq.1h6v.s9.eb459fc638d4 from=translated src=- shape=1d6556a4 vocab=425eccdb
-/
theorem iteratedDerivWithin_coefficient (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    iteratedDerivWithin m (coefficient I w A n) I.interval x = jet I w A.1 n m x := by
  simpa only [coefficient, Nat.zero_add] using iteratedDerivWithin_jet I w A n 0 m hx

/-- The inherited norm controls every actual parameter derivative with its weight.
@isnad1 id=le.0h6v.s10.4e97f04737c9 from=translated src=- shape=e9cb94fe vocab=be7ff9ca
-/
theorem abs_jet_le (I : Window) (w : ℕ → ℕ → ℝ) (A : CoefficientSpace I w)
    (n m : ℕ) (x : ℝ) :
    |jet I w A.1 n m x| ≤ |w n m| * ‖A‖ := by
  rw [jet, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (A.1.norm_coe_le_norm ((n, m), I.project x)) (abs_nonneg _)

/-- Norm convergence controls every derivative uniformly in the parameter.
@isnad1 id=le.0h7v.s11.59041babece0 from=translated src=- shape=b6b0f707 vocab=de601ffa
-/
theorem abs_jet_sub_le (I : Window) (w : ℕ → ℕ → ℝ) (A B : CoefficientSpace I w)
    (n m : ℕ) (x : ℝ) :
    |jet I w A.1 n m x - jet I w B.1 n m x| ≤ |w n m| * ‖A - B‖ := by
  simpa only [Submodule.coe_sub, jet_sub] using abs_jet_le I w (A - B) n m x

/-- For nonzero weights, the normalized actual derivative recovers exactly
the stored bounded-continuous coordinate.
@isnad1 id=eq.1h6v.s9.299314c79348 from=translated src=- shape=a57f2041 vocab=832d8536
-/
theorem normalized_derivative (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, w n m ≠ 0) (A : CoefficientSpace I w)
    (n m : ℕ) (x : I.interval) :
    iteratedDerivWithin m (coefficient I w A n) I.interval x / w n m =
      A.1 ((n, m), x) := by
  rw [iteratedDerivWithin_coefficient I w A n m x.property,
    jet, I.project_of_mem x.property]
  exact mul_div_cancel_left₀ _ (hw n m)

/--
@isnad1 id=eq.1h6v.s9.15e9ea19c49b from=translated src=- shape=e747f576 vocab=6c5eba93
-/
theorem quotient_abs_derivative (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, 0 < w n m) (A : CoefficientSpace I w)
    (n m : ℕ) (x : I.interval) :
    |iteratedDerivWithin m (coefficient I w A n) I.interval x| / w n m =
      |A.1 ((n, m), x)| := by
  calc
    _ = |iteratedDerivWithin m (coefficient I w A n) I.interval x / w n m| := by
      rw [abs_div, abs_of_pos (hw n m)]
    _ = _ := by rw [normalized_derivative I w (fun n m => (hw n m).ne') A n m x]

/-- This is precisely the supremum quotient norm in the manuscript,
expressed by its universal upper-bound characterization.
@isnad1 id=iff.2h4v.s10.032dd3caf075 from=translated src=- shape=ff9d8598 vocab=4ba17570
-/
theorem norm_le_iff_derivative_bound (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, 0 < w n m) (A : CoefficientSpace I w) (C : ℝ) (hC : 0 ≤ C) :
    ‖A‖ ≤ C ↔ ∀ (n m : ℕ) (x : I.interval),
      |iteratedDerivWithin m (coefficient I w A n) I.interval x| / w n m ≤ C := by
  change ‖A.1‖ ≤ C ↔ _
  rw [BoundedContinuousFunction.norm_le hC]
  constructor
  · intro h n m x
    rw [quotient_abs_derivative I w hw A n m x]
    exact h ((n, m), x)
  · intro h p
    rcases p with ⟨⟨n, m⟩, x⟩
    have hx := h n m x
    rw [quotient_abs_derivative I w hw A n m x] at hx
    exact hx

/-- Positive weights leave no independent or invisible jet coordinates:
equality of the actual coefficient functions forces equality in the space.
@isnad1 id=eq.2h4v.s10.11c447f6ffe0 from=translated src=- shape=92158249 vocab=00ed3b7a
-/
theorem coefficient_ext (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, w n m ≠ 0) (A B : CoefficientSpace I w)
    (h : ∀ n x, x ∈ I.interval → coefficient I w A n x = coefficient I w B n x) :
    A = B := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  rintro ⟨⟨n, m⟩, x⟩
  rw [← normalized_derivative I w hw A n m x,
    ← normalized_derivative I w hw B n m x]
  congr 1
  exact iteratedDerivWithin_congr (fun y hy => h n y hy) x.property

/-- Normalize an actual continuous jet family with a uniform weighted bound. -/
def rawOfJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (C : ℝ) (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) : RawJets I :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p : (ℕ × ℕ) × I.interval => J p.1.1 p.1.2 p.2 / w p.1.1 p.1.2)
    (continuous_prod_of_discrete_left.mpr
      (fun p => (hcont p.1 p.2).domRestrict.div_const (w p.1 p.2))) C
    (by
      rintro ⟨⟨n, m⟩, x⟩
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hw n m)]
      exact (div_le_iff₀ (hw n m)).mpr (hbound n m x x.property))

/--
@isnad1 id=eq.4h7v.s7.6ce6c5f685c4 from=translated src=- shape=16c3f116 vocab=cf5de1a0
-/
theorem jet_rawOfJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (C : ℝ) (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    jet I w (rawOfJetFamily I w hw J hcont C hbound) n m x = J n m x := by
  change w n m * (J n m (I.project x) / w n m) = J n m x
  rw [I.project_of_mem hx]
  exact mul_div_cancel₀ _ (hw n m).ne'

/-- Actual derivative compatibility implies the closed FTC compatibility
required by the Banach-space representation.
@isnad1 id=compatib.4h4v.s7.d7c38182c975 from=translated src=- shape=a75592d4 vocab=ff5dedf1
-/
theorem compatible_rawOfJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) :
    Compatible I w (rawOfJetFamily I w hw J hcont C hbound) := by
  intro n m x hx
  have hleft : I.left ∈ I.interval := ⟨le_rfl, I.nondegenerate.le⟩
  have hsub : Icc I.left x ⊆ I.interval := fun y hy => ⟨hy.1, hy.2.trans hx.2⟩
  have hint : IntervalIntegrable (J n (m + 1)) volume I.left x :=
    ContinuousOn.intervalIntegrable_of_Icc hx.1 ((hcont n (m + 1)).mono hsub)
  have hFTC : (∫ t in I.left..x, J n (m + 1) t) = J n m x - J n m I.left := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      ((hcont n m).mono hsub) _ hint
    intro y hy
    exact (hderiv n m y (hsub ⟨hy.1.le, hy.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hy.1 (hy.2.trans_le hx.2))
  have hintEq : (∫ t in I.left..x,
      jet I w (rawOfJetFamily I w hw J hcont C hbound) n (m + 1) t) =
      ∫ t in I.left..x, J n (m + 1) t := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx.1] at hy
    exact jet_rawOfJetFamily I w hw J hcont C hbound n (m + 1) (hsub hy)
  rw [jet_rawOfJetFamily I w hw J hcont C hbound n m hx,
    jet_rawOfJetFamily I w hw J hcont C hbound n m hleft, hintEq, hFTC]
  ring

/-- Reverse constructor used by genuine products and radial operators:
a continuous family with actual adjacent derivatives and the weighted bound
becomes an element of the complete coefficient space. -/
def ofJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) : CoefficientSpace I w :=
  ⟨rawOfJetFamily I w hw J hcont C hbound,
    compatible_rawOfJetFamily I w hw J hcont hderiv C hbound⟩

/--
@isnad1 id=eq.6h7v.s9.b896cb79c08f from=translated src=- shape=2aec7f74 vocab=0af3ed11
-/
theorem jet_ofJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    jet I w (ofJetFamily I w hw J hcont hderiv C hC hbound).1 n m x = J n m x :=
  jet_rawOfJetFamily I w hw J hcont C hbound n m hx

/--
@isnad1 id=eq.6h6v.s7.9774a0f753ca from=translated src=- shape=19e2db5b vocab=ed742217
-/
theorem coefficient_ofJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m)
    (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I w (ofJetFamily I w hw J hcont hderiv C hC hbound) n x = J n 0 x :=
  jet_ofJetFamily I w hw J hcont hderiv C hC hbound n 0 hx

/--
@isnad1 id=le.5h4v.s9.6c0eeb569fb8 from=translated src=- shape=866c849f vocab=d070960c
-/
theorem norm_ofJetFamily_le (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) :
    ‖ofJetFamily I w hw J hcont hderiv C hC hbound‖ ≤ C := by
  apply (norm_le_iff_derivative_bound I w hw _ C hC).mpr
  intro n m x
  rw [iteratedDerivWithin_coefficient I w _ n m x.property,
    jet_ofJetFamily I w hw J hcont hderiv C hC hbound n m x.property]
  exact (div_le_iff₀ (hw n m)).mpr (hbound n m x x.property)

/-- A smooth coefficient family's genuine iterated derivatives form the
adjacent derivative chain required by `ofJetFamily`.
@isnad1 id=hasderiv.2h5v.s7.b547f4c284e0 from=translated src=- shape=e44dac8b vocab=44debd12
-/
theorem hasDerivWithinAt_iterated_smooth (I : Window) (F : ℕ → ℝ → ℝ)
    (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval) (n m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    HasDerivWithinAt (iteratedDerivWithin m (F n) I.interval)
      (iteratedDerivWithin (m + 1) (F n) I.interval x) I.interval x := by
  have hd : DifferentiableWithinAt ℝ (iteratedDerivWithin m (F n) I.interval) I.interval x :=
    (hF n).differentiableOn_iteratedDerivWithin (m := m)
      (by exact_mod_cast (ENat.natCast_lt_top m))
      (uniqueDiffOn_Icc I.nondegenerate) x hx
  simpa only [iteratedDerivWithin_succ] using hd.hasDerivWithinAt

/-- Reverse constructor from actual smooth coefficient functions with
uniform bounds on all their parameter derivatives. -/
def ofSmoothFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (F : ℕ → ℝ → ℝ) (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval →
      |iteratedDerivWithin m (F n) I.interval x| ≤ C * w n m) : CoefficientSpace I w :=
  ofJetFamily I w hw (fun n m => iteratedDerivWithin m (F n) I.interval)
    (fun n m => (hF n).continuousOn_iteratedDerivWithin (m := m)
      (by exact_mod_cast (ENat.natCast_lt_top m).le)
      (uniqueDiffOn_Icc I.nondegenerate))
    (fun n m _ hx => hasDerivWithinAt_iterated_smooth I F hF n m hx) C hC hbound

/-- The specific space in GAX.2, with the manuscript's exact positive weights
when `ε>0`. Completeness and normed vector-space structures are inherited. -/
abbrev AxisSpace (I : Window) (ε : ℝ) :=
  CoefficientSpace I (AxisWeightEstimates.weight ε)

/-- The exact manuscript norm, with actual derivatives in its quotient.
@isnad1 id=iff.2h4v.s10.88e6cfd9bc41 from=translated src=- shape=f154c163 vocab=2bbee4c8
-/
theorem axisSpace_norm_le_iff (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (C : ℝ) (hC : 0 ≤ C) :
    ‖A‖ ≤ C ↔ ∀ (n m : ℕ) (x : I.interval),
      |iteratedDerivWithin m (coefficient I (AxisWeightEstimates.weight ε) A n) I.interval x| /
        AxisWeightEstimates.weight ε n m ≤ C :=
  norm_le_iff_derivative_bound I (AxisWeightEstimates.weight ε)
    (AxisWeightEstimates.weight_pos hε) A C hC

end NavierStokes.AxisCoefficientSpace

end
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
