/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/
module

public import Tengoku.LeanPool.LeanPool.PebblingLean.UpperBoundRecurrence
public import Tengoku

/-!
# Loss bookkeeping for the recursive upper bound

The probabilistic and product arguments produce a recursive construction.  After
normalizing by `(4/3)^n`, the remaining analytic issue is to show that the
multiplicative losses accumulated along the dimension recursion stay bounded.

This file formalizes that bookkeeping abstractly.  It does not choose the final
parameters yet; instead, it proves the deterministic theorem that a bounded
finite loss sum gives a uniform normalized-cost bound.
-/

@[expose] public section

namespace PebblingLean

namespace Hypercube

namespace LossRecurrence

/-- The `k`-fold iterate of a dimension-reduction map, written recursively so
the recurrence proofs can unfold cleanly. -/
def iterate (next : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => iterate next k (next n)

/-- `ActiveFor next n0 k n` means that the first `k` dimensions encountered
from `n` are still in the recursive range `n0 ≤ dimension`. -/
def ActiveFor (next : ℕ → ℕ) (n0 : ℕ) : ℕ → ℕ → Prop
  | 0, _n => True
  | k + 1, n => n0 ≤ n ∧ ActiveFor next n0 k (next n)

/-- Product of the multiplicative losses accumulated over `k` recursive
steps. -/
def lossProduct (next : ℕ → ℕ) (loss : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _n => 1
  | k + 1, n => (1 + loss n) * lossProduct next loss k (next n)

/-- Sum of the additive losses accumulated over `k` recursive steps. -/
def lossSum (next : ℕ → ℕ) (loss : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _n => 0
  | k + 1, n => loss n + lossSum next loss k (next n)

/--
@isnad1 id=le.1h4v.s5.49abe0f11119 from=translated src=- shape=0187c99d vocab=eed689b9
-/
theorem lossProduct_nonneg {next : ℕ → ℕ} {loss : ℕ → ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n) (k n : ℕ) :
    0 ≤ lossProduct next loss k n := by
  induction k generalizing n with
  | zero =>
      simp [lossProduct]
  | succ k ih =>
      exact mul_nonneg (add_nonneg zero_le_one (hloss n)) (ih (next n))

/-- Iterating a normalized recurrence gives a finite product of the losses
times the terminal normalized cost.
@isnad1 id=le.3h6v.s6.4da11136b664 from=translated src=- shape=d9b94ffc vocab=067d216f
-/
theorem cost_le_lossProduct
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (k n : ℕ) (hactive : ActiveFor next n0 k n) :
    R n ≤ lossProduct next loss k n * R (iterate next k n) := by
  revert n
  induction k with
  | zero =>
      intro n _hactive
      simp [lossProduct, iterate]
  | succ k ih =>
      intro n hactive
      rcases hactive with ⟨hn, htail⟩
      have htail_le := ih (next n) htail
      have hfactor_nonneg : 0 ≤ 1 + loss n :=
        add_nonneg zero_le_one (hloss n)
      have htail_mul :
          (1 + loss n) * R (next n) ≤
            (1 + loss n) *
              (lossProduct next loss k (next n) *
                R (iterate next k (next n))) :=
        mul_le_mul_of_nonneg_left htail_le hfactor_nonneg
      calc
        R n ≤ (1 + loss n) * R (next n) := hstep n hn
        _ ≤ (1 + loss n) *
              (lossProduct next loss k (next n) *
                R (iterate next k (next n))) := htail_mul
        _ = lossProduct next loss (k + 1) n *
              R (iterate next (k + 1) n) := by
              simp [lossProduct, iterate, mul_assoc]

/-- Version of `cost_le_lossProduct` with the terminal cost bounded by a
specified base constant.
@isnad1 id=le.4h7v.s6.bafad7b4f9d3 from=translated src=- shape=2a4e9d59 vocab=067d216f
-/
theorem cost_le_lossProduct_mul_base
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 k n : ℕ} {B : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hactive : ActiveFor next n0 k n)
    (hbase : R (iterate next k n) ≤ B) :
    R n ≤ lossProduct next loss k n * B := by
  have hrec := cost_le_lossProduct (next := next) (loss := loss) (R := R)
    (n0 := n0) hloss hstep k n hactive
  have hprod_nonneg := lossProduct_nonneg (next := next) (loss := loss) hloss k n
  exact hrec.trans (mul_le_mul_of_nonneg_left hbase hprod_nonneg)

/-- A finite product of factors `1 + loss` is bounded by the exponential of
the corresponding finite sum.
@isnad1 id=le.1h4v.s5.e476af24b90c from=translated src=- shape=96d5e23d vocab=00deda46
-/
theorem lossProduct_le_exp_lossSum {next : ℕ → ℕ} {loss : ℕ → ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n) (k n : ℕ) :
    lossProduct next loss k n ≤ Real.exp (lossSum next loss k n) := by
  induction k generalizing n with
  | zero =>
      simp [lossProduct, lossSum]
  | succ k ih =>
      have hfactor :
          1 + loss n ≤ Real.exp (loss n) := by
        simpa [add_comm] using Real.add_one_le_exp (loss n)
      have htail := ih (next n)
      calc
        lossProduct next loss (k + 1) n
            = (1 + loss n) * lossProduct next loss k (next n) := by
              simp [lossProduct]
        _ ≤ Real.exp (loss n) *
              Real.exp (lossSum next loss k (next n)) := by
              exact mul_le_mul hfactor htail
                (lossProduct_nonneg (next := next) (loss := loss) hloss k (next n))
                (Real.exp_nonneg _)
        _ = Real.exp (loss n + lossSum next loss k (next n)) := by
              rw [← Real.exp_add]
        _ = Real.exp (lossSum next loss (k + 1) n) := by
              simp [lossSum]

/-- Exponential version of the finite recurrence bound.
@isnad1 id=le.5h7v.s6.366bc70da7da from=translated src=- shape=936e169d vocab=647b0392
-/
theorem cost_le_exp_lossSum_mul_base
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 k n : ℕ} {B : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hactive : ActiveFor next n0 k n)
    (hbase : R (iterate next k n) ≤ B) :
    R n ≤ Real.exp (lossSum next loss k n) * B := by
  have hrec := cost_le_lossProduct_mul_base
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (k := k) (n := n) (B := B) hloss hstep hactive hbase
  have hprod := lossProduct_le_exp_lossSum
    (next := next) (loss := loss) hloss k n
  exact hrec.trans (mul_le_mul_of_nonneg_right hprod hB)

/-- If the accumulated additive loss is at most `L`, the normalized cost is
bounded by `exp L` times the terminal base bound.
@isnad1 id=le.6h8v.s7.b15c81534533 from=translated src=- shape=29affcd5 vocab=647b0392
-/
theorem cost_le_exp_lossBound_mul_base
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 k n : ℕ} {B L : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hactive : ActiveFor next n0 k n)
    (hbase : R (iterate next k n) ≤ B)
    (hsum : lossSum next loss k n ≤ L) :
    R n ≤ Real.exp L * B := by
  have hrec := cost_le_exp_lossSum_mul_base
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (k := k) (n := n) (B := B) hloss hB hstep hactive hbase
  have hexp : Real.exp (lossSum next loss k n) ≤ Real.exp L :=
    Real.exp_le_exp.mpr hsum
  exact hrec.trans (mul_le_mul_of_nonneg_right hexp hB)

/-- A strictly decreasing dimension map always reaches the finite base range
after finitely many recursive steps.
@isnad1 id=ex.1h3v.s5.ecf681aa5367 from=translated src=- shape=e02ee766 vocab=8c86b8db
-/
theorem exists_terminal_iterate_of_decreasing
    {next : ℕ → ℕ} {n0 : ℕ}
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n) (n : ℕ) :
    ∃ k : ℕ, ActiveFor next n0 k n ∧ iterate next k n < n0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < n0
      · exact ⟨0, trivial, hn⟩
      · have hn0 : n0 ≤ n := Nat.le_of_not_gt hn
        rcases ih (next n) (hnext n hn0) with ⟨k, hactive, hterminal⟩
        exact ⟨k + 1, ⟨hn0, hactive⟩, by simpa [iterate] using hterminal⟩

/-- The finite geometric sum `1 + q + ... + q^(k-1)`. -/
def geomSum (q : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, q ^ i

/--
@isnad1 id=le.2h2v.s5.3923d502758c from=translated src=- shape=544aeac4 vocab=187b3da1
-/
theorem geomSum_le_two_of_le_half {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_half : q ≤ (1 : ℝ) / 2) (k : ℕ) :
    geomSum q k ≤ 2 := by
  have hpow :
      ∀ i : ℕ, q ^ i ≤ ((1 : ℝ) / 2) ^ i := by
    intro i
    exact pow_le_pow_left₀ hq_nonneg hq_half i
  have hsum :
      geomSum q k ≤ ∑ i ∈ Finset.range k, ((1 : ℝ) / 2) ^ i := by
    exact Finset.sum_le_sum fun i _hi => hpow i
  exact hsum.trans (sum_geometric_two_le k)

/-- If every active loss is at most `q` times the next active loss, and active
losses are bounded by `M`, then the first loss in a path of length `k+1` is at
most `q^k M`.
@isnad1 id=le.4h7v.s6.30621e1addb0 from=translated src=- shape=b25650fb vocab=fc1e3f0a
-/
theorem first_loss_le_pow_mul_bound
    {next : ℕ → ℕ} {loss : ℕ → ℝ} {n0 : ℕ} {q M : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M)
    (k n : ℕ) (hactive : ActiveFor next n0 (k + 1) n) :
    loss n ≤ q ^ k * M := by
  revert n
  induction k with
  | zero =>
      intro n hactive
      rcases hactive with ⟨hn, _htail⟩
      simpa using hbound n hn
  | succ k ih =>
      intro n hactive
      rcases hactive with ⟨hn, htail⟩
      have hnext0 : n0 ≤ next n := htail.1
      have hfirst := hdecay n hn hnext0
      have htail_bound := ih (next n) htail
      have hmul : q * loss (next n) ≤ q * (q ^ k * M) :=
        mul_le_mul_of_nonneg_left htail_bound hq_nonneg
      calc
        loss n ≤ q * loss (next n) := hfirst
        _ ≤ q * (q ^ k * M) := hmul
        _ = q ^ (k + 1) * M := by
              rw [pow_succ]
              ring

/-- Geometric domination of a finite loss sum along an active recursive path.
@isnad1 id=le.4h7v.s6.38a58dafa948 from=translated src=- shape=9c5eb7b4 vocab=d480d8fe
-/
theorem lossSum_le_geomSum_mul_bound
    {next : ℕ → ℕ} {loss : ℕ → ℝ} {n0 : ℕ} {q M : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M)
    (k n : ℕ) (hactive : ActiveFor next n0 k n) :
    lossSum next loss k n ≤ geomSum q k * M := by
  revert n
  induction k with
  | zero =>
      intro n _hactive
      simp [lossSum, geomSum]
  | succ k ih =>
      intro n hactive
      rcases hactive with ⟨hn, htail⟩
      have hfirst :
          loss n ≤ q ^ k * M :=
        first_loss_le_pow_mul_bound
          (next := next) (loss := loss) (n0 := n0)
          (q := q) (M := M) hq_nonneg hdecay hbound k n
          ⟨hn, htail⟩
      have htail_sum := ih (next n) htail
      calc
        lossSum next loss (k + 1) n
            = loss n + lossSum next loss k (next n) := by
              simp [lossSum]
        _ ≤ q ^ k * M + geomSum q k * M := add_le_add hfirst htail_sum
        _ = geomSum q (k + 1) * M := by
              simp [geomSum, Finset.sum_range_succ]
              ring

/-- Uniform normalized-cost bound when the loss sequence decays geometrically
along recursive paths.
@isnad1 id=le.10h9v.s7.d01b3d1b756c from=translated src=- shape=c18dd6b2 vocab=8a28c935
-/
theorem cost_uniform_bound_of_geometric_loss
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ} {B q M G : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hM : 0 ≤ M)
    (hq_nonneg : 0 ≤ q)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M)
    (hgeom : ∀ k : ℕ, geomSum q k ≤ G) (n : ℕ) :
    R n ≤ Real.exp (G * M) * B := by
  rcases exists_terminal_iterate_of_decreasing
    (next := next) (n0 := n0) hnext n with
    ⟨k, hactive, hterm⟩
  have hsum :
      lossSum next loss k n ≤ geomSum q k * M :=
    lossSum_le_geomSum_mul_bound
      (next := next) (loss := loss) (n0 := n0)
      (q := q) (M := M) hq_nonneg hdecay hbound k n hactive
  have hgeom_mul : geomSum q k * M ≤ G * M :=
    mul_le_mul_of_nonneg_right (hgeom k) hM
  exact cost_le_exp_lossBound_mul_base
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (k := k) (n := n) (B := B) (L := G * M)
    hloss hB hstep hactive (hbase _ hterm) (hsum.trans hgeom_mul)

/-- Convenient geometric-loss bound for ratio at most `1/2`, giving total
loss at most `2M`.  The paper's recursion has a much smaller ratio (`1/16`)
after increasing the base threshold, so this intentionally uses a relaxed
constant.
@isnad1 id=le.10h8v.s8.939324fa24b8 from=translated src=- shape=abc9817e vocab=22a0aaf1
-/
theorem cost_uniform_bound_of_geometric_loss_le_two
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ} {B q M : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hM : 0 ≤ M)
    (hq_nonneg : 0 ≤ q)
    (hq_half : q ≤ (1 : ℝ) / 2)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M) (n : ℕ) :
    R n ≤ Real.exp (2 * M) * B :=
  cost_uniform_bound_of_geometric_loss
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (B := B) (q := q) (M := M) (G := 2)
    hloss hB hM hq_nonneg hnext hstep hbase hdecay hbound
    (geomSum_le_two_of_le_half hq_nonneg hq_half) n

/-- Uniform normalized-cost bound from an explicit terminal path and a bound
on the loss accumulated along that path.
@isnad1 id=le.5h7v.s7.3bd20b931101 from=translated src=- shape=578c0b4c vocab=979ff8a9
-/
theorem cost_uniform_bound_of_terminal_lossBound
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ} {B L : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hterminal :
      ∀ n : ℕ, ∃ k : ℕ,
        ActiveFor next n0 k n ∧
          iterate next k n < n0 ∧
            lossSum next loss k n ≤ L)
    (n : ℕ) :
    R n ≤ Real.exp L * B := by
  rcases hterminal n with ⟨k, hactive, hterm, hsum⟩
  exact cost_le_exp_lossBound_mul_base
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (k := k) (n := n) (B := B) (L := L)
    hloss hB hstep hactive (hbase _ hterm) hsum

/-- Uniform normalized-cost bound for a decreasing dimension map, assuming a
separate estimate on every terminal loss sum.
@isnad1 id=le.6h7v.s7.25dd2dd6ccfd from=translated src=- shape=deca5c3e vocab=979ff8a9
-/
theorem cost_uniform_bound_of_decreasing_lossBound
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ} {B L : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hlossSum :
      ∀ n k : ℕ, ActiveFor next n0 k n →
        iterate next k n < n0 → lossSum next loss k n ≤ L)
    (n : ℕ) :
    R n ≤ Real.exp L * B := by
  rcases exists_terminal_iterate_of_decreasing
    (next := next) (n0 := n0) hnext n with
    ⟨k, hactive, hterm⟩
  exact cost_le_exp_lossBound_mul_base
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (k := k) (n := n) (B := B) (L := L)
    hloss hB hstep hactive (hbase _ hterm)
    (hlossSum n k hactive hterm)

end LossRecurrence

/-- Normalized integer cost bound, divided by `(4/3)^n`. -/
noncomputable def normalizedCost (costBound : ℕ → ℕ) (n : ℕ) : ℝ :=
  (costBound n : ℝ) / (((4 : ℝ) / 3) ^ n)

/--
@isnad1 id=le.0h2v.s4.4f03ca5d6abb from=translated src=- shape=7544a74c vocab=e3f136c1
-/
theorem normalizedCost_nonneg (costBound : ℕ → ℕ) (n : ℕ) :
    0 ≤ normalizedCost costBound n := by
  unfold normalizedCost
  positivity

/-- A concrete finite bound for the normalized costs below a cutoff.  This is
not optimized; it is just a convenient way to discharge finite base cases. -/
noncomputable def finiteBaseNormalizedBound (costBound : ℕ → ℕ) (n0 : ℕ) : ℝ :=
  ∑ n ∈ Finset.range n0, normalizedCost costBound n

/--
@isnad1 id=le.0h2v.s4.09f7ed8e3bcd from=translated src=- shape=7544a74c vocab=446bf372
-/
theorem finiteBaseNormalizedBound_nonneg (costBound : ℕ → ℕ) (n0 : ℕ) :
    0 ≤ finiteBaseNormalizedBound costBound n0 := by
  unfold finiteBaseNormalizedBound
  exact Finset.sum_nonneg fun n _hn => normalizedCost_nonneg costBound n

/--
@isnad1 id=le.1h3v.s4.e7831585d01e from=translated src=- shape=7f3138d5 vocab=32c7db5d
-/
theorem normalizedCost_le_finiteBaseNormalizedBound_of_lt
    (costBound : ℕ → ℕ) {n0 n : ℕ} (hn : n < n0) :
    normalizedCost costBound n ≤ finiteBaseNormalizedBound costBound n0 := by
  unfold finiteBaseNormalizedBound
  exact Finset.single_le_sum
    (fun m _hm => normalizedCost_nonneg costBound m)
    (Finset.mem_range.mpr hn)

/-- Real-valued asymptotic upper-bound statement: for every dimension `n`,
there is an ordinary solvable distribution whose size is at most
`C * (4/3)^n`. -/
def HasRealHypercubePebblingUpperBound (C : ℝ) : Prop :=
  ∀ n : ℕ, ∃ k : ℕ,
    Pebbling.HasSolvableAtMostSize (graph n) 1 k ∧
      (k : ℝ) ≤ C * (((4 : ℝ) / 3) ^ n)

/--
@isnad1 id=le.1h3v.s6.4b2b64b570dc from=translated src=- shape=29232a62 vocab=900978c4
-/
theorem costBound_le_of_normalizedCost_le
    {costBound : ℕ → ℕ} {C : ℝ}
    (hnorm : ∀ n : ℕ, normalizedCost costBound n ≤ C) (n : ℕ) :
    (costBound n : ℝ) ≤ C * (((4 : ℝ) / 3) ^ n) := by
  have hpow_pos : 0 < (((4 : ℝ) / 3) ^ n) := by positivity
  exact (div_le_iff₀ hpow_pos).mp (by simpa [normalizedCost] using hnorm n)

/-- Convert an integer-valued cost-bound construction plus a real normalized
cost estimate into the real asymptotic upper-bound statement.
@isnad1 id=hasrealh.2h2v.s4.af1301d38084 from=translated src=- shape=55f04b30 vocab=6aa91463
-/
theorem hasRealHypercubePebblingUpperBound_of_normalizedCost
    {costBound : ℕ → ℕ} {C : ℝ}
    (hupper : HasHypercubePebblingUpperBound costBound)
    (hnorm : ∀ n : ℕ, normalizedCost costBound n ≤ C) :
    HasRealHypercubePebblingUpperBound C := by
  intro n
  exact ⟨costBound n, hupper n,
    costBound_le_of_normalizedCost_le hnorm n⟩

/-- Final abstract bridge from the geometric normalized-cost recurrence to the
real asymptotic upper-bound statement.  After the numerical parameter choices
prove the hypotheses here, this is the formal end of the upper-bound proof.
@isnad1 id=hasrealh.11h7v.s7.6596020dc0d1 from=translated src=- shape=f22b3d12 vocab=f1e09ab1
-/
theorem hasRealHypercubePebblingUpperBound_of_geometric_normalizedCost_loss
    {costBound next : ℕ → ℕ} {loss : ℕ → ℝ} {n0 : ℕ}
    {B q M : ℝ}
    (hupper : HasHypercubePebblingUpperBound costBound)
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hM : 0 ≤ M)
    (hq_nonneg : 0 ≤ q)
    (hq_half : q ≤ (1 : ℝ) / 2)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n →
        normalizedCost costBound n ≤
          (1 + loss n) * normalizedCost costBound (next n))
    (hbase :
      ∀ n : ℕ, n < n0 → normalizedCost costBound n ≤ B)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M) :
    HasRealHypercubePebblingUpperBound (Real.exp (2 * M) * B) := by
  have hnorm :
      ∀ n : ℕ,
        normalizedCost costBound n ≤ Real.exp (2 * M) * B :=
    LossRecurrence.cost_uniform_bound_of_geometric_loss_le_two
      (next := next) (loss := loss) (R := normalizedCost costBound)
      (n0 := n0) (B := B) (q := q) (M := M)
      hloss hB hM hq_nonneg hq_half hnext hstep hbase hdecay hbound
  exact hasRealHypercubePebblingUpperBound_of_normalizedCost hupper hnorm

end Hypercube

end PebblingLean
