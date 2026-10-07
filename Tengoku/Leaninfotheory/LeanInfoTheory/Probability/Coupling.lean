/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Probability.FiniteChannel
import Tengoku.Leaninfotheory.LeanInfoTheory.Probability.TotalVariation

/-!
# Couplings of probability mass functions

A coupling is an existing joint PMF whose coordinate pushforwards are the
specified laws. The coordinate alphabets may have different types and universes;
the predicate and elementary witnesses need no finiteness or measurable spaces.

Independent existence reuses the constant-channel `PMF.channelJoint`. Diagonal
coupling and coordinate swap use `PMF.map`, preserving the raw joint-law interface
consumed by the separately imported Shannon APIs.

On a common finite alphabet, every coupling bounds total variation by its real
disagreement probability. The proof uses the event attaining total variation
and finite real event sums; no support or positivity premise is required.

`maximalCoupling` constructs the finite common-mass joint law. It chooses the
diagonal law at zero TV and otherwise adds independent residual mass to the
common diagonal. Both coordinate marginals are exactly the supplied laws.
Its disagreement probability is exactly total variation, so the coupling
inequality shows that this witness attains the least possible disagreement.

The law-level convention follows Levin--Peres, Section 4.2, and Sason, Section I:
the first coordinate has law `p`, and the second has law `q`.
-/

namespace PMF

universe u v

open scoped BigOperators ENNReal

/-- A joint law couples `p` and `q` when its first and second pushforwards are
exactly `p` and `q`, respectively. The joint law is the first argument. -/
def IsCoupling {alpha : Type u} {beta : Type v}
    (joint : PMF (alpha × beta)) (p : PMF alpha) (q : PMF beta) : Prop :=
  joint.map Prod.fst = p ∧ joint.map Prod.snd = q

/-- The joint law of a constant channel is a coupling of its input and output laws. -/
theorem isCoupling_channelJoint_const {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (q : PMF beta) :
    IsCoupling (channelJoint p (fun _ => q)) p q := by
  refine ⟨channelJoint_map_fst p _, ?_⟩
  rw [channelJoint_map_snd, bind_const]

/-- Any two supplied PMFs have a coupling, witnessed by the independent joint law. -/
theorem exists_isCoupling {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (q : PMF beta) : ∃ joint, IsCoupling joint p q :=
  ⟨channelJoint p (fun _ => q), isCoupling_channelJoint_const p q⟩

/-- Mapping a law to the diagonal couples that law with itself. -/
theorem isCoupling_map_diag {alpha : Type u} (p : PMF alpha) :
    IsCoupling (p.map (fun a => (a, a))) p p := by
  constructor
  · rw [map_comp]
    exact map_id p
  · rw [map_comp]
    exact map_id p

/-- Swapping a coupling's coordinates reverses its two prescribed marginal laws. -/
theorem IsCoupling.map_swap {alpha : Type u} {beta : Type v}
    {joint : PMF (alpha × beta)} {p : PMF alpha} {q : PMF beta}
    (h : IsCoupling joint p q) : IsCoupling (joint.map Prod.swap) q p := by
  constructor
  · rw [map_comp]
    exact h.2
  · rw [map_comp]
    exact h.1

/-- Total variation is at most the probability that the coupled coordinates differ.
The event uses first-versus-second coordinate order. This is the coupling inequality
from Levin--Peres, Section 4.2, Proposition 4.7, for finite PMFs. -/
theorem IsCoupling.totalVariation_le {alpha : Type u} [Fintype alpha]
    {joint : PMF (alpha × alpha)} {p q : PMF alpha}
    (h : IsCoupling joint p q) :
    totalVariation p q ≤ (joint.toOuterMeasure {xy | xy.1 ≠ xy.2}).toReal := by
  classical
  have event_bound (s : Set alpha) :
      ((joint.map Prod.fst).toOuterMeasure s).toReal -
          ((joint.map Prod.snd).toOuterMeasure s).toReal ≤
        (joint.toOuterMeasure {xy | xy.1 ≠ xy.2}).toReal := by
    rw [toOuterMeasure_map_apply, toOuterMeasure_map_apply,
      toOuterMeasure_toReal_eq_sum, toOuterMeasure_toReal_eq_sum,
      toOuterMeasure_toReal_eq_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro xy _
    by_cases hxy : xy.1 = xy.2
    · simp [Set.indicator, hxy]
    · by_cases hf : xy.1 ∈ s <;> by_cases hs : xy.2 ∈ s <;>
        simp [Set.indicator, hxy, hf, hs]
  rw [totalVariation_eq_toOuterMeasure_sub]
  simpa only [h.1, h.2] using event_bound {a | (q a).toReal ≤ (p a).toReal}

private noncomputable def maximalCouplingMass {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) (xy : alpha × alpha) : ℝ≥0∞ := by
  classical
  exact (if xy.1 = xy.2 then min (p xy.1) (q xy.1) else 0) +
    (p xy.1 - q xy.1) * (q xy.2 - p xy.2) / ENNReal.ofReal (totalVariation p q)

private theorem maximalCouplingMass_row {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) (h : 0 < totalVariation p q) (a : alpha) :
    (∑ b, maximalCouplingMass p q (a, b)) = p a := by
  classical
  simp only [maximalCouplingMass, Finset.sum_add_distrib, div_eq_mul_inv,
    ← Finset.sum_mul, ← Finset.mul_sum]
  rw [← ofReal_totalVariation_eq_sum_sub, totalVariation_comm q p,
    ENNReal.mul_inv_cancel_right (ne_of_gt (ENNReal.ofReal_pos.mpr h))
      ENNReal.ofReal_ne_top]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← tsub_min (a := p a) (b := q a)]
  exact add_tsub_cancel_of_le (min_le_left _ _)

private theorem maximalCouplingMass_col {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) (h : 0 < totalVariation p q) (b : alpha) :
    (∑ a, maximalCouplingMass p q (a, b)) = q b := by
  classical
  simp only [maximalCouplingMass, Finset.sum_add_distrib, div_eq_mul_inv,
    ← Finset.sum_mul]
  rw [← ofReal_totalVariation_eq_sum_sub, mul_comm _ (q b - p b),
    ENNReal.mul_inv_cancel_right (ne_of_gt (ENNReal.ofReal_pos.mpr h))
      ENNReal.ofReal_ne_top]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [min_comm, ← tsub_min (a := q b) (b := p b)]
  exact add_tsub_cancel_of_le (min_le_left _ _)

private noncomputable def maximalCouplingPositive {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) (h : 0 < totalVariation p q) : PMF (alpha × alpha) :=
  PMF.ofFintype (maximalCouplingMass p q) (by
    rw [Fintype.sum_prod_type]
    simp_rw [maximalCouplingMass_row p q h]
    simpa only [tsum_fintype] using p.tsum_coe)

private theorem maximalCouplingPositive_isCoupling {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) (h : 0 < totalVariation p q) :
    IsCoupling (maximalCouplingPositive p q h) p q := by
  classical
  constructor
  · apply PMF.ext
    intro a
    rw [map_apply, tsum_fintype, Fintype.sum_prod_type]
    simp only [maximalCouplingPositive, ofFintype_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact maximalCouplingMass_row p q h a
  · apply PMF.ext
    intro b
    rw [map_apply, tsum_fintype, Fintype.sum_prod_type]
    simp only [maximalCouplingPositive, ofFintype_apply]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact maximalCouplingMass_col p q h b

/-- The finite common-mass coupling of `p` and `q`, with first marginal `p` and
second marginal `q`. At zero TV it is the diagonal law. At positive TV it puts
the common minimum on the diagonal and couples the residual masses independently.
This is the flattened construction of Sason, Section I, equations (5)--(8). -/
noncomputable def maximalCoupling {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) : PMF (alpha × alpha) := by
  classical
  exact if h : totalVariation p q = 0 then p.map (fun a => (a, a))
    else maximalCouplingPositive p q
      (lt_of_le_of_ne (totalVariation_nonneg p q) (Ne.symm h))

/-- The common-mass construction has the two prescribed marginals, including
zero and unit total variation, without any support or cardinality restriction. -/
theorem isCoupling_maximalCoupling {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) : IsCoupling (maximalCoupling p q) p q := by
  classical
  unfold maximalCoupling
  split_ifs with h
  · have hpq := (totalVariation_eq_zero_iff p q).mp h
    subst q
    exact isCoupling_map_diag p
  · exact maximalCouplingPositive_isCoupling p q _

private theorem maximalCoupling_eq_diagonal {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) (h : totalVariation p q = 0) :
    maximalCoupling p q = p.map (fun a => (a, a)) := by
  simp [maximalCoupling, h]

private theorem maximalCoupling_eq_independent {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) (h : totalVariation p q = 1) :
    maximalCoupling p q = channelJoint p (fun _ => q) := by
  classical
  have hm (a : alpha) : min (p a) (q a) = 0 := by
    have hsum : (∑ a, min (p a) (q a)) = 0 := by
      rw [sum_min_eq_ofReal_one_sub_totalVariation, h, sub_self, ENNReal.ofReal_zero]
    exact Finset.sum_eq_zero_iff.mp hsum a (Finset.mem_univ a)
  have hr (a : alpha) : p a - q a = p a := by
    rw [← tsub_min (a := p a) (b := q a), hm a, tsub_zero]
  have hs (a : alpha) : q a - p a = q a := by
    rw [← tsub_min (a := q a) (b := p a), min_comm (q a) (p a), hm a, tsub_zero]
  have h0 : totalVariation p q ≠ 0 := by rw [h]; norm_num
  apply PMF.ext
  intro ⟨a, b⟩
  simp only [maximalCoupling, dite_eq_right h0, maximalCouplingPositive, ofFintype_apply,
    channelJoint_apply]
  simp [maximalCouplingMass, hm, hr, hs, h]

private theorem coupling_agreement_eq_sum_diag {alpha : Type u} [Fintype alpha]
    (joint : PMF (alpha × alpha)) :
    joint.toOuterMeasure {xy | xy.1 = xy.2} = ∑ a, joint (a, a) := by
  classical
  rw [toOuterMeasure_apply_fintype, Fintype.sum_prod_type]
  simp [Set.indicator]

private theorem coupling_disagreement_complement {alpha : Type u} [Finite alpha]
    (joint : PMF (alpha × alpha)) :
    joint.toOuterMeasure {xy | xy.1 ≠ xy.2} =
      1 - joint.toOuterMeasure {xy | xy.1 = xy.2} := by
  classical
  let : Fintype alpha := Fintype.ofFinite alpha
  apply ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
  rw [toOuterMeasure_apply_fintype, toOuterMeasure_apply_fintype,
    ← Finset.sum_add_distrib]
  calc
    _ = ∑ xy, joint xy := by
      apply Finset.sum_congr rfl
      intro xy _
      by_cases hxy : xy.1 = xy.2 <;> simp [Set.indicator, hxy]
    _ = 1 := by simpa only [tsum_fintype] using joint.tsum_coe

private theorem maximalCouplingMass_diag {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) (a : alpha) :
    maximalCouplingMass p q (a, a) = min (p a) (q a) := by
  rcases le_total (p a) (q a) with h | h <;>
    simp [maximalCouplingMass, tsub_eq_zero_of_le h]

private theorem maximalCouplingPositive_agreement {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) (h : 0 < totalVariation p q) :
    (maximalCouplingPositive p q h).toOuterMeasure {xy | xy.1 = xy.2} =
      ENNReal.ofReal (1 - totalVariation p q) := by
  rw [coupling_agreement_eq_sum_diag]
  simp only [maximalCouplingPositive, ofFintype_apply, maximalCouplingMass_diag]
  exact sum_min_eq_ofReal_one_sub_totalVariation p q

private theorem maximalCouplingPositive_disagreement {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) (h : 0 < totalVariation p q) :
    (maximalCouplingPositive p q h).toOuterMeasure {xy | xy.1 ≠ xy.2} =
      ENNReal.ofReal (totalVariation p q) := by
  rw [coupling_disagreement_complement, maximalCouplingPositive_agreement,
    ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr (totalVariation_le_one p q))]
  congr 1
  ring

private theorem independent_disagreement_of_disjoint {alpha : Type u}
    (p q : PMF alpha) (hdis : Disjoint p.support q.support) :
    (channelJoint p (fun _ => q)).toOuterMeasure {xy | xy.1 ≠ xy.2} = 1 := by
  apply (toOuterMeasure_apply_eq_one_iff _ _).2
  rintro ⟨a, b⟩ hab heq
  change a = b at heq
  obtain ⟨ha, hb⟩ := (mem_support_channelJoint_iff p (fun _ => q) a b).1 hab
  exact Set.disjoint_left.mp hdis (heq ▸ ha) hb

/-- The common-mass coupling disagrees with probability exactly total variation
in `ENNReal`, with the event ordered first coordinate versus second coordinate.
This is the attained coupling bound of Sason, Section I, Theorem 2. -/
theorem maximalCoupling_toOuterMeasure_ne {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) :
    (maximalCoupling p q).toOuterMeasure {xy | xy.1 ≠ xy.2} =
      ENNReal.ofReal (totalVariation p q) := by
  classical
  by_cases hzero : totalVariation p q = 0
  · rw [maximalCoupling_eq_diagonal p q hzero, toOuterMeasure_map_apply]
    simp [hzero]
  by_cases hone : totalVariation p q = 1
  · rw [maximalCoupling_eq_independent p q hone,
      independent_disagreement_of_disjoint p q
        ((totalVariation_eq_one_iff_disjoint_support p q).1 hone), hone,
      ENNReal.ofReal_one]
  · simp only [maximalCoupling, dite_eq_right hzero]
    exact maximalCouplingPositive_disagreement p q _

/-- The real disagreement probability of the common-mass coupling is total
variation. Together with `IsCoupling.totalVariation_le`, this proves attainment
of the smallest disagreement among all couplings of the supplied laws. -/
theorem maximalCoupling_toOuterMeasure_ne_toReal {alpha : Type u} [Fintype alpha]
    (p q : PMF alpha) :
    ((maximalCoupling p q).toOuterMeasure {xy | xy.1 ≠ xy.2}).toReal =
      totalVariation p q := by
  rw [maximalCoupling_toOuterMeasure_ne, ENNReal.toReal_ofReal (totalVariation_nonneg p q)]

private theorem coupling_half_add :
    ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

private noncomputable def couplingSparseLeft : PMF (Fin 3) :=
  PMF.ofFintype (fun a => if a = 2 then 0 else ENNReal.ofReal (1 / 2 : ℝ))
    (by simpa [Fin.sum_univ_three] using coupling_half_add)

private noncomputable def couplingSparseRight : PMF (Fin 3) :=
  PMF.ofFintype (fun a => if a = 0 then 0 else ENNReal.ofReal (1 / 2 : ℝ))
    (by simpa [Fin.sum_univ_three] using coupling_half_add)

end PMF
