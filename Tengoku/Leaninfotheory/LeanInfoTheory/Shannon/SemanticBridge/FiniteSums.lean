/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.InfoMeasures

/-!
# Finite-sum identities for the Shannon semantic bridge

This file contains reusable finite-sum rewrites used by semantic bridge
theorems. The main result is the pointwise finite formula

`I(A; B) = sum_{a,b} p(a,b) log (p(a,b) / (p_A(a) p_B(b)))`.

It is kept separate from the KL bridge so that elementary finite PMF algebra
does not import Radon-Nikodym derivatives or measure-theoretic KL divergence.
-/

namespace LeanInfoTheory
namespace Shannon

open scoped BigOperators

noncomputable section

universe u v

-- Every PMF atom is finite as an `ENNReal`; this is used when moving finite
-- sums from `ENNReal` to `Real`.
private theorem pmf_apply_ne_top {alpha : Type u} (p : PMF alpha) (a : alpha) :
    p a ≠ ⊤ := by
  exact ne_of_lt ((PMF.coe_le_one (p := p) a).trans_lt ENNReal.one_lt_top)

/-! ## Marginal finite-sum identities -/

/--
Real-valued first-marginal mass formula.

Mathematically, for a finite joint PMF `p` on `alpha × beta`,
`p_A(a) = sum_b p(a,b)`, now stated after converting all finite masses to
real numbers.
-/
theorem fstMarginal_toReal_apply {alpha : Type u} {beta : Type v} [Fintype beta]
    (p : PMF (alpha × beta)) (a : alpha) :
    (fstMarginal p a).toReal = ∑ b, (p (a, b)).toReal := by
  classical
  rw [fstMarginal_apply (p := p) (a := a)]
  rw [ENNReal.toReal_sum]
  intro b _hb
  exact pmf_apply_ne_top p (a, b)

/--
Real-valued second-marginal mass formula.

Mathematically, for a finite joint PMF `p` on `alpha × beta`,
`p_B(b) = sum_a p(a,b)`, now stated after converting all finite masses to
real numbers.
-/
theorem sndMarginal_toReal_apply {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) (b : beta) :
    (sndMarginal p b).toReal = ∑ a, (p (a, b)).toReal := by
  classical
  rw [sndMarginal_apply (p := p) (b := b)]
  rw [ENNReal.toReal_sum]
  intro a _ha
  exact pmf_apply_ne_top p (a, b)

/--
Rewrite an expectation of a first-coordinate observable under the joint law as
an expectation under the first marginal:
`sum_{a,b} p(a,b) f(a) = sum_a p_A(a) f(a)`.
-/
theorem sum_toReal_mul_fstMarginal {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) (f : alpha -> Real) :
    (∑ x : alpha × beta, (p x).toReal * f x.1) =
      ∑ a : alpha, (fstMarginal p a).toReal * f a := by
  classical
  calc
    (∑ x : alpha × beta, (p x).toReal * f x.1)
        = ∑ a : alpha, ∑ b : beta, (p (a, b)).toReal * f a := by
          rw [Fintype.sum_prod_type]
    _ = ∑ a : alpha, (∑ b : beta, (p (a, b)).toReal) * f a := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.sum_mul]
    _ = ∑ a : alpha, (fstMarginal p a).toReal * f a := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [fstMarginal_toReal_apply]

/--
Rewrite an expectation of a second-coordinate observable under the joint law as
an expectation under the second marginal:
`sum_{a,b} p(a,b) f(b) = sum_b p_B(b) f(b)`.
-/
theorem sum_toReal_mul_sndMarginal {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) (f : beta -> Real) :
    (∑ x : alpha × beta, (p x).toReal * f x.2) =
      ∑ b : beta, (sndMarginal p b).toReal * f b := by
  classical
  calc
    (∑ x : alpha × beta, (p x).toReal * f x.2)
        = ∑ a : alpha, ∑ b : beta, (p (a, b)).toReal * f b := by
          rw [Fintype.sum_prod_type]
    _ = ∑ b : beta, ∑ a : alpha, (p (a, b)).toReal * f b := by
          rw [Finset.sum_comm]
    _ = ∑ b : beta, (∑ a : alpha, (p (a, b)).toReal) * f b := by
          apply Finset.sum_congr rfl
          intro b _hb
          rw [Finset.sum_mul]
    _ = ∑ b : beta, (sndMarginal p b).toReal * f b := by
          apply Finset.sum_congr rfl
          intro b _hb
          rw [sndMarginal_toReal_apply]

/-! ## Mutual information as a finite log-ratio sum -/

/--
Entropy as the elementary finite sum `sum_a p(a) * (-log p(a))`.

This is definitionally the same as the `Real.negMulLog` formula, but this shape
is better for comparing entropy identities with KL-divergence sums.
-/
theorem entropy_eq_sum_toReal_mul_neg_log {alpha : Type u} [Fintype alpha]
    (p : PMF alpha) :
    entropy p = ∑ a : alpha, (p a).toReal * (-Real.log (p a).toReal) := by
  classical
  rw [entropy_eq_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Real.negMulLog]
  ring

/--
First-marginal entropy as a joint-law expectation:
`H(A) = sum_{a,b} p(a,b) * (-log p_A(a))`.
-/
theorem entropy_fstMarginal_eq_sum_joint {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    entropy (fstMarginal p) =
      ∑ x : alpha × beta, (p x).toReal * (-Real.log (fstMarginal p x.1).toReal) := by
  classical
  calc
    entropy (fstMarginal p)
        = ∑ a : alpha, (fstMarginal p a).toReal *
            (-Real.log (fstMarginal p a).toReal) := by
          exact entropy_eq_sum_toReal_mul_neg_log (fstMarginal p)
    _ = ∑ x : alpha × beta, (p x).toReal *
          (-Real.log (fstMarginal p x.1).toReal) := by
          exact (sum_toReal_mul_fstMarginal p
            (fun a => -Real.log (fstMarginal p a).toReal)).symm

/--
Second-marginal entropy as a joint-law expectation:
`H(B) = sum_{a,b} p(a,b) * (-log p_B(b))`.
-/
theorem entropy_sndMarginal_eq_sum_joint {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    entropy (sndMarginal p) =
      ∑ x : alpha × beta, (p x).toReal * (-Real.log (sndMarginal p x.2).toReal) := by
  classical
  calc
    entropy (sndMarginal p)
        = ∑ b : beta, (sndMarginal p b).toReal *
            (-Real.log (sndMarginal p b).toReal) := by
          exact entropy_eq_sum_toReal_mul_neg_log (sndMarginal p)
    _ = ∑ x : alpha × beta, (p x).toReal *
          (-Real.log (sndMarginal p x.2).toReal) := by
          exact (sum_toReal_mul_sndMarginal p
            (fun b => -Real.log (sndMarginal p b).toReal)).symm

/--
Mutual information written as the joint expectation of the three entropy
summands:

`I(A;B) = sum_{a,b} p(a,b) *
  (-log p_A(a) + -log p_B(b) - -log p(a,b))`.
-/
theorem mutualInfo_eq_sum_neg_log {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    mutualInfo p =
      ∑ x : alpha × beta,
        ((p x).toReal * (-Real.log (fstMarginal p x.1).toReal) +
          (p x).toReal * (-Real.log (sndMarginal p x.2).toReal) -
          (p x).toReal * (-Real.log (p x).toReal)) := by
  classical
  rw [mutualInfo_eq]
  rw [entropy_fstMarginal_eq_sum_joint,
    entropy_sndMarginal_eq_sum_joint,
    entropy_eq_sum_toReal_mul_neg_log]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

/--
Pointwise algebra behind the KL formula for mutual information.

For every atom `(a,b)`, the weighted entropy summand equals
`p(a,b) * log (p(a,b) / (p_A(a) * p_B(b)))`. If `p(a,b)=0`, both sides are
zero; otherwise nonzero joint mass forces both marginal masses to be nonzero.
-/
theorem mutualInfo_summand_eq_log_ratio {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta] (p : PMF (alpha × beta)) (x : alpha × beta) :
    ((p x).toReal * (-Real.log (fstMarginal p x.1).toReal) +
          (p x).toReal * (-Real.log (sndMarginal p x.2).toReal) -
          (p x).toReal * (-Real.log (p x).toReal)) =
        (p x).toReal *
          Real.log ((p x).toReal /
            ((fstMarginal p x.1).toReal * (sndMarginal p x.2).toReal)) := by
  classical
  by_cases hp : (p x).toReal = 0
  · simp [hp]
  · have hp_enn : p x ≠ 0 := (ENNReal.toReal_ne_zero.mp hp).1
    rcases x with ⟨a, b⟩
    have hfst_enn : fstMarginal p a ≠ 0 :=
      fstMarginal_ne_zero_of_apply_ne_zero p hp_enn
    have hsnd_enn : sndMarginal p b ≠ 0 :=
      sndMarginal_ne_zero_of_apply_ne_zero p hp_enn
    have hfst : (fstMarginal p a).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hfst_enn, pmf_apply_ne_top (fstMarginal p) a⟩
    have hsnd : (sndMarginal p b).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hsnd_enn, pmf_apply_ne_top (sndMarginal p) b⟩
    have hprod :
        (fstMarginal p a).toReal * (sndMarginal p b).toReal ≠ 0 :=
      mul_ne_zero hfst hsnd
    rw [Real.log_div hp hprod, Real.log_mul hfst hsnd]
    ring

/--
Finite log-ratio formula for mutual information:

`I(A;B) = sum_{a,b} p(a,b) log (p(a,b) / (p_A(a) p_B(b)))`.
-/
theorem mutualInfo_eq_sum_log_ratio {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    mutualInfo p =
      ∑ x : alpha × beta, (p x).toReal *
        Real.log ((p x).toReal /
          ((fstMarginal p x.1).toReal * (sndMarginal p x.2).toReal)) := by
  classical
  rw [mutualInfo_eq_sum_neg_log]
  apply Finset.sum_congr rfl
  intro x _hx
  exact mutualInfo_summand_eq_log_ratio p x

end

end Shannon
end LeanInfoTheory
