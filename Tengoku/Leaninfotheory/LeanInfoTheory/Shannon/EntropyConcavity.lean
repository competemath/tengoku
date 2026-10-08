/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Probability.FiniteMixture
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.Entropy
import Tengoku

/-!
# Concavity of finite Shannon entropy

This opt-in module proves the finite-selector form of entropy concavity
directly from Jensen's inequality for `Real.negMulLog`. The binary textbook
form is a later specialization through `PMF.binaryMixture`.
-/

namespace LeanInfoTheory
namespace Shannon

open scoped BigOperators

noncomputable section

universe u v

/--
Entropy is concave under a finite PMF-valued selector.

This is the general finite-selector form of the textbook binary entropy
concavity inequality.
-/
theorem sum_mul_entropy_le_entropy_bind
    {iota : Type u} {alpha : Type v}
    [Fintype iota] [Fintype alpha]
    (r : PMF iota) (P : iota -> PMF alpha) :
    (∑ i, (r i).toReal * entropy (P i)) <= entropy (r.bind P) := by
  classical
  calc
    (∑ i, (r i).toReal * entropy (P i)) =
        ∑ a, ∑ i,
          (r i).toReal * Real.negMulLog (P i a).toReal := by
      simp_rw [entropy_eq_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ <= ∑ a, Real.negMulLog ((r.bind P) a).toReal := by
      apply Finset.sum_le_sum
      intro a _
      have hJensen :=
        Real.concaveOn_negMulLog.le_map_sum
          (t := (Finset.univ : Finset iota))
          (w := fun i => (r i).toReal)
          (p := fun i => (P i a).toReal)
          (fun i _ => PMF.toReal_nonneg r i)
          (PMF.sum_toReal r)
          (fun i _ => PMF.toReal_nonneg (P i) a)
      simp only [smul_eq_mul] at hJensen
      rw [PMF.bind_toReal_apply r P a]
      exact hJensen
    _ = entropy (r.bind P) := (entropy_eq_sum (r.bind P)).symm

/--
Entropy is concave under a binary PMF mixture.
-/
theorem binaryMixture_entropy_concave
    {alpha : Type u} [Fintype alpha]
    (t : NNReal) (ht : t <= 1) (p q : PMF alpha) :
    (t : Real) * entropy p +
        ((1 - t : NNReal) : Real) * entropy q <=
      entropy (PMF.binaryMixture t ht p q) := by
  let r : PMF Bool :=
    PMF.ofFintype
      (fun b : Bool => ((cond b t (1 - t) : NNReal) : ENNReal))
      (by simp [ht])
  have hr_true : (r true).toReal = (t : Real) := by
    simp only [r, PMF.ofFintype_apply, Bool.cond_true]
    rw [ENNReal.coe_toReal]
  have hr_false : (r false).toReal = ((1 - t : NNReal) : Real) := by
    simp only [r, PMF.ofFintype_apply, Bool.cond_false]
    rw [ENNReal.coe_toReal]
  change
    (t : Real) * entropy p + ((1 - t : NNReal) : Real) * entropy q <=
      entropy (r.bind fun b => if b then p else q)
  simpa only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Bool.true_eq_false, Bool.false_eq_true, not_false_eq_true,
    Finset.sum_singleton, hr_true, hr_false, ite_true, ite_false] using
    (sum_mul_entropy_le_entropy_bind r (fun b => if b then p else q))

/--
For an interior binary weight, equality in entropy concavity holds exactly
when the two component PMFs are equal.
-/
theorem binaryMixture_entropy_eq_iff
    {alpha : Type u} [Fintype alpha]
    (t : NNReal) (ht : t <= 1) (ht0 : 0 < t) (ht1 : t < 1)
    (p q : PMF alpha) :
    (t : Real) * entropy p +
          ((1 - t : NNReal) : Real) * entropy q =
        entropy (PMF.binaryMixture t ht p q) ↔
      p = q := by
  classical
  let r : PMF Bool :=
    PMF.ofFintype
      (fun b : Bool => ((cond b t (1 - t) : NNReal) : ENNReal))
      (by simp [ht])
  let P : Bool -> PMF alpha := fun b => if b then p else q
  have hr_pos (b : Bool) : 0 < (r b).toReal := by
    cases b
    · have hcompl : 0 < (1 - t : NNReal) := tsub_pos_iff_lt.mpr ht1
      simp only [r, PMF.ofFintype_apply, Bool.cond_false]
      rw [ENNReal.coe_toReal]
      exact_mod_cast hcompl
    · simpa [r, PMF.ofFintype_apply] using
        (show (0 : Real) < (t : Real) by exact_mod_cast ht0)
  have hpoint (a : alpha) :
      (∑ b, (r b).toReal * Real.negMulLog (P b a).toReal) <=
        Real.negMulLog ((r.bind P) a).toReal := by
    have hJensen :=
      Real.concaveOn_negMulLog.le_map_sum
        (t := (Finset.univ : Finset Bool))
        (w := fun b => (r b).toReal)
        (p := fun b => (P b a).toReal)
        (fun b _ => PMF.toReal_nonneg r b)
        (PMF.sum_toReal r)
        (fun b _ => PMF.toReal_nonneg (P b) a)
    simp only [smul_eq_mul] at hJensen
    rw [PMF.bind_toReal_apply r P a]
    exact hJensen
  constructor
  · intro hEntropy
    have hEntropy' :
        (∑ b, (r b).toReal * entropy (P b)) =
          entropy (r.bind P) := by
      simpa [r, P, PMF.binaryMixture, Fintype.univ_bool,
        PMF.ofFintype_apply, ENNReal.coe_sub] using hEntropy
    have hsum :
        (∑ a, ∑ b,
            (r b).toReal * Real.negMulLog (P b a).toReal) =
          ∑ a, Real.negMulLog ((r.bind P) a).toReal := by
      calc
        (∑ a, ∑ b,
            (r b).toReal * Real.negMulLog (P b a).toReal) =
            ∑ b, (r b).toReal * entropy (P b) := by
          simp_rw [entropy_eq_sum, Finset.mul_sum]
          rw [Finset.sum_comm]
        _ = entropy (r.bind P) := hEntropy'
        _ = ∑ a, Real.negMulLog ((r.bind P) a).toReal :=
          entropy_eq_sum (r.bind P)
    have heach (a : alpha) :
        (∑ b, (r b).toReal * Real.negMulLog (P b a).toReal) =
          Real.negMulLog ((r.bind P) a).toReal :=
      (Finset.sum_eq_sum_iff_of_le
        (fun a _ => hpoint a)).1 hsum a (Finset.mem_univ a)
    apply PMF.ext
    intro a
    apply
      (ENNReal.toReal_eq_toReal_iff'
        (p.apply_ne_top a) (q.apply_ne_top a)).1
    have hJensenEq :
        Real.negMulLog
            (∑ b, (r b).toReal • (P b a).toReal) =
          ∑ b, (r b).toReal • Real.negMulLog (P b a).toReal := by
      simp only [smul_eq_mul]
      rw [← PMF.bind_toReal_apply r P a]
      exact (heach a).symm
    have hconst :=
      (Real.strictConcaveOn_negMulLog.map_sum_eq_iff
        (t := (Finset.univ : Finset Bool))
        (w := fun b => (r b).toReal)
        (p := fun b => (P b a).toReal)
        (fun b _ => hr_pos b)
        (PMF.sum_toReal r)
        (fun b _ => PMF.toReal_nonneg (P b) a)).1 hJensenEq
    have htrue := hconst true (Finset.mem_univ true)
    have hfalse := hconst false (Finset.mem_univ false)
    simpa [P] using htrue.trans hfalse.symm
  · rintro rfl
    have hmix : PMF.binaryMixture t ht p p = p := by
      simp [PMF.binaryMixture, PMF.bind_const]
    have hweights :
        (t : Real) + ((1 - t : NNReal) : Real) = 1 := by
      rw [NNReal.coe_sub ht]
      norm_num
    rw [hmix, ← add_mul, hweights, one_mul]

end

end Shannon
end LeanInfoTheory
