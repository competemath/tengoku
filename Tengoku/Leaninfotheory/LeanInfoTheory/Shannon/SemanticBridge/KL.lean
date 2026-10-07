/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Conditional
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.FiniteSums
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Product
import Tengoku

/-!
# KL-divergence bridge for finite Shannon information measures

This file connects the finite PMF definitions in `LeanInfoTheory.Shannon` to
mathlib's measure-theoretic `InformationTheory.klDiv`.

The main theorem is

`mutualInfo_eq_toReal_klDiv_joint_indepProd`:

`I(A;B) = D(P_AB || P_A × P_B)`,

where the product of marginals is represented by the project-local PMF
`indepProd (fstMarginal p) (sndMarginal p)`.
-/

namespace LeanInfoTheory
namespace Shannon

open MeasureTheory
open scoped BigOperators

noncomputable section

universe u v

universe w

-- Every PMF atom is finite as an `ENNReal`; this is used when computing the
-- finite Radon-Nikodym derivative pointwise.
private theorem pmf_apply_ne_top {alpha : Type u} (p : PMF alpha) (a : alpha) :
    p a ≠ ⊤ := by
  exact ne_of_lt ((PMF.coe_le_one (p := p) a).trans_lt ENNReal.one_lt_top)

/-! ## Finite PMF support and KL finiteness -/

/--
Absolute continuity between PMF measures is exactly inclusion of their
set-valued supports.

This statement does not require a finite alphabet: measurable singletons let
the forward direction test individual atoms, while the reverse direction uses
the PMF measure's zero-set characterization.
-/
theorem toMeasure_absolutelyContinuous_iff_support_subset
    {alpha : Type u} [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p q : PMF alpha) :
    p.toMeasure ≪ q.toMeasure ↔ p.support ⊆ q.support := by
  constructor
  · intro hpq a ha
    by_contra hqa
    have hq_zero : q.toMeasure ({a} : Set alpha) = 0 := by
      rw [PMF.toMeasure_apply_singleton q a (MeasurableSet.singleton a)]
      exact (q.apply_eq_zero_iff a).2 hqa
    have hp_zero := hpq hq_zero
    rw [PMF.toMeasure_apply_singleton p a (MeasurableSet.singleton a)] at hp_zero
    exact (p.mem_support_iff a).1 ha hp_zero
  · intro hpq
    refine Measure.AbsolutelyContinuous.mk ?_
    intro s hs hq_zero
    rw [PMF.toMeasure_apply_eq_zero_iff q hs] at hq_zero
    rw [PMF.toMeasure_apply_eq_zero_iff p hs]
    rw [Set.disjoint_left] at hq_zero ⊢
    intro a hpa has
    exact hq_zero (hpq hpa) has

/--
On a finite alphabet, PMF KL divergence is finite exactly when the first PMF's
support is contained in the second PMF's support.
-/
theorem klDiv_pmf_ne_top_iff_support_subset
    {alpha : Type u} [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p q : PMF alpha) :
    InformationTheory.klDiv p.toMeasure q.toMeasure ≠ ⊤ ↔
      p.support ⊆ q.support := by
  constructor
  · intro h
    have hac := (InformationTheory.klDiv_ne_top_iff.mp h).1
    exact (toMeasure_absolutelyContinuous_iff_support_subset p q).1 hac
  · intro h
    apply InformationTheory.klDiv_ne_top
    · exact (toMeasure_absolutelyContinuous_iff_support_subset p q).2 h
    · exact Integrable.of_finite

/--
On a finite alphabet, PMF KL divergence is infinite exactly when support
inclusion fails.
-/
theorem klDiv_pmf_eq_top_iff_not_support_subset
    {alpha : Type u} [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p q : PMF alpha) :
    InformationTheory.klDiv p.toMeasure q.toMeasure = ⊤ ↔
      ¬ p.support ⊆ q.support := by
  constructor
  · intro h hsupport
    exact (klDiv_pmf_ne_top_iff_support_subset p q).2 hsupport h
  · intro hsupport
    by_contra h
    exact hsupport ((klDiv_pmf_ne_top_iff_support_subset p q).1 h)

/--
KL divergence between two PMFs is zero exactly when the PMFs are equal.

The alphabet need not be finite: PMF measures are finite measures, and
measurable singletons make `PMF.toMeasure` injective.
-/
theorem klDiv_pmf_eq_zero_iff
    {alpha : Type u} [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p q : PMF alpha) :
    InformationTheory.klDiv p.toMeasure q.toMeasure = 0 ↔ p = q := by
  rw [InformationTheory.klDiv_eq_zero_iff, PMF.toMeasure_inj]

/--
On a finite alphabet and under support inclusion, real-valued PMF KL
divergence is zero exactly when the PMFs are equal.

The support hypothesis is essential: without KL finiteness,
`ENNReal.toReal ⊤ = 0` would make the reverse characterization false.
-/
theorem toReal_klDiv_pmf_eq_zero_iff
    {alpha : Type u} [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p q : PMF alpha) (h : p.support ⊆ q.support) :
    (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal = 0 ↔ p = q := by
  have hne : InformationTheory.klDiv p.toMeasure q.toMeasure ≠ ⊤ :=
    (klDiv_pmf_ne_top_iff_support_subset p q).2 h
  constructor
  · intro hzero
    rcases (ENNReal.toReal_eq_zero_iff _).1 hzero with hkl | htop
    · exact (klDiv_pmf_eq_zero_iff p q).1 hkl
    · exact (hne htop).elim
  · intro hpq
    rw [(klDiv_pmf_eq_zero_iff p q).2 hpq]
    simp

/--
Countable PMF density formula.

If `p.toMeasure ≪ q.toMeasure`, then `p.toMeasure` is obtained from
`q.toMeasure` by the density `a ↦ p(a) / q(a)`. On atoms with `q(a)=0`,
absolute continuity forces `p(a)=0`, so the formula is still valid.
-/
theorem toMeasure_withDensity_pmf_div {alpha : Type u}
    [Countable alpha] [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p q : PMF alpha) (h : p.toMeasure ≪ q.toMeasure) :
    q.toMeasure.withDensity (fun a => p a / q a) = p.toMeasure := by
  classical
  rw [Measure.ext_iff_singleton]
  intro a
  rw [MeasureTheory.withDensity_apply
    (μ := q.toMeasure) (f := fun a => p a / q a)
    (s := ({a} : Set alpha)) (MeasurableSet.singleton a)]
  rw [MeasureTheory.lintegral_singleton]
  rw [PMF.toMeasure_apply_singleton q a (MeasurableSet.singleton a),
    PMF.toMeasure_apply_singleton p a (MeasurableSet.singleton a)]
  by_cases hq : q a = 0
  · have hqmeasure : q.toMeasure ({a} : Set alpha) = 0 := by
      simpa [PMF.toMeasure_apply_singleton q a (MeasurableSet.singleton a)] using hq
    have hpmeasure : p.toMeasure ({a} : Set alpha) = 0 :=
      h hqmeasure
    have hp : p a = 0 := by
      simpa [PMF.toMeasure_apply_singleton p a (MeasurableSet.singleton a)] using hpmeasure
    simp [hq, hp]
  · rw [ENNReal.div_mul_cancel hq (pmf_apply_ne_top q a)]

/--
Finite KL expansion for absolutely continuous PMFs:

`D(P || Q) = sum_a p(a) log (p(a) / q(a))`.

The left-hand side is mathlib's measure-theoretic KL divergence applied to
`PMF.toMeasure`; the right-hand side is the usual finite sum over atoms.
-/
theorem toReal_klDiv_pmf_eq_sum {alpha : Type u}
    [Fintype alpha] [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p q : PMF alpha) (h : p.toMeasure ≪ q.toMeasure) :
    (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal =
      ∑ a : alpha, (p a).toReal * Real.log ((p a / q a).toReal) := by
  classical
  have hdensity_meas : Measurable (fun a : alpha => p a / q a) :=
    measurable_of_finite _
  have hwith :
      q.toMeasure.withDensity (fun a : alpha => p a / q a) = p.toMeasure :=
    toMeasure_withDensity_pmf_div p q h
  have hrn_q :
      p.toMeasure.rnDeriv q.toMeasure =ᵐ[q.toMeasure] fun a : alpha => p a / q a := by
    simpa [hwith] using
      (Measure.rnDeriv_withDensity (ν := q.toMeasure) hdensity_meas)
  have hrn_p :
      p.toMeasure.rnDeriv q.toMeasure =ᵐ[p.toMeasure] fun a : alpha => p a / q a :=
    h.ae_eq hrn_q
  have hllr :
      MeasureTheory.llr p.toMeasure q.toMeasure =ᵐ[p.toMeasure]
        fun a : alpha => Real.log ((p a / q a).toReal) := by
    filter_upwards [hrn_p] with a ha
    simp [MeasureTheory.llr_def, ha]
  rw [InformationTheory.toReal_klDiv_of_measure_eq h (by simp)]
  rw [integral_congr_ae hllr]
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [smul_eq_mul]

/-! ## Uniform reference laws -/

/--
KL divergence from a finite PMF to the uniform law on a nonempty finset is the
uniform log-cardinality minus entropy, provided the PMF is supported on that
finset:

`D(P || U_s) = log |s| - H(P)`.
-/
theorem toReal_klDiv_pmf_uniformOfFinset
    {alpha : Type u} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p : PMF alpha) (s : Finset alpha) (hs : s.Nonempty)
    (h : p.support ⊆ (s : Set alpha)) :
    (InformationTheory.klDiv p.toMeasure
      (PMF.uniformOfFinset s hs).toMeasure).toReal =
        Real.log (s.card : Real) - entropy p := by
  classical
  have hac : p.toMeasure ≪ (PMF.uniformOfFinset s hs).toMeasure := by
    apply (toMeasure_absolutelyContinuous_iff_support_subset p _).2
    simpa using h
  have hn : (s.card : Real) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  rw [toReal_klDiv_pmf_eq_sum p (PMF.uniformOfFinset s hs) hac]
  calc
    (∑ a : alpha,
        (p a).toReal *
          Real.log ((p a / PMF.uniformOfFinset s hs a).toReal)) =
        ∑ a : alpha,
          ((p a).toReal * Real.log (s.card : Real) -
            Real.negMulLog (p a).toReal) := by
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases hpa : p a = 0
      · simp [hpa]
      · have has : a ∈ s := h ((p.mem_support_iff a).2 hpa)
        have hpReal : (p a).toReal ≠ 0 :=
          ENNReal.toReal_ne_zero.2 ⟨hpa, p.apply_ne_top a⟩
        rw [PMF.uniformOfFinset_apply_of_mem hs has]
        simp only [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_natCast]
        rw [div_inv_eq_mul, Real.log_mul hpReal hn, Real.negMulLog]
        ring
    _ = (∑ a : alpha, (p a).toReal) * Real.log (s.card : Real) -
          ∑ a : alpha, Real.negMulLog (p a).toReal := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ = Real.log (s.card : Real) - entropy p := by
      rw [PMF.sum_toReal, entropy_eq_sum, one_mul]

/--
Full-alphabet form of `toReal_klDiv_pmf_uniformOfFinset`:

`D(P || U_alpha) = log |alpha| - H(P)`.
-/
theorem toReal_klDiv_pmf_uniformOfFintype
    {alpha : Type u} [Fintype alpha] [Nonempty alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p : PMF alpha) :
    (InformationTheory.klDiv p.toMeasure
      (PMF.uniformOfFintype alpha).toMeasure).toReal =
        Real.log (Fintype.card alpha : Real) - entropy p := by
  simpa [PMF.uniformOfFintype] using
    (toReal_klDiv_pmf_uniformOfFinset p Finset.univ
      Finset.univ_nonempty (by simp))

/--
Semantic bridge for finite mutual information:

`I(A;B) = D(P_AB || P_A × P_B)`.

Here `P_A × P_B` is represented by the finite independent-product PMF
`indepProd (fstMarginal p) (sndMarginal p)`. This theorem is the finite
textbook identity connecting the entropy definition of mutual information to
mathlib's measure-theoretic KL divergence.
-/
theorem mutualInfo_eq_toReal_klDiv_joint_indepProd
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    [MeasurableSpace (alpha × beta)] [MeasurableSingletonClass (alpha × beta)]
    (p : PMF (alpha × beta)) :
    mutualInfo p =
      (InformationTheory.klDiv p.toMeasure
        (indepProd (fstMarginal p) (sndMarginal p)).toMeasure).toReal := by
  classical
  symm
  rw [toReal_klDiv_pmf_eq_sum
    (p := p) (q := indepProd (fstMarginal p) (sndMarginal p))
    (joint_toMeasure_absolutelyContinuous_indepProd_marginals (p := p))]
  rw [mutualInfo_eq_sum_log_ratio]
  apply Finset.sum_congr rfl
  intro x _hx
  rcases x with ⟨a, b⟩
  simp [ENNReal.toReal_div, ENNReal.toReal_mul]

/--
Product-measure form of the finite mutual-information KL bridge:

`I(A;B) = D(P_AB || P_A.toMeasure.prod P_B.toMeasure)`.
-/
theorem mutualInfo_eq_toReal_klDiv_joint_prod_marginals
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    [MeasurableSpace alpha] [MeasurableSpace beta]
    [MeasurableSingletonClass (alpha × beta)]
    (p : PMF (alpha × beta)) :
    mutualInfo p =
      (InformationTheory.klDiv p.toMeasure
        (Measure.prod (fstMarginal p).toMeasure (sndMarginal p).toMeasure)).toReal := by
  rw [← indepProd_toMeasure (p := fstMarginal p) (q := sndMarginal p)]
  exact mutualInfo_eq_toReal_klDiv_joint_indepProd p

/-! ## Averaged conditional KL bridge -/

/--
Fiberwise KL form of conditional mutual information.

This is zero on zero-marginal third-coordinate atoms. On nonzero atoms it is
`D(P_{A,B|C=c} || P_{A|C=c} × P_{B|C=c})`, using the marginals of the
conditional joint law.
-/
def condMutualInfoFstSndGivenThirdKL
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    [MeasurableSpace (alpha × beta)] [MeasurableSingletonClass (alpha × beta)]
    (p : PMF (alpha × beta × gamma)) (c : gamma) : Real :=
  if hc : thirdMarginal p c = 0 then
    0
  else
    (InformationTheory.klDiv (condFstSndGivenThird p c hc).toMeasure
      (indepProd
        (fstMarginal (condFstSndGivenThird p c hc))
        (sndMarginal (condFstSndGivenThird p c hc))).toMeasure).toReal

/--
The fiber mutual-information helper agrees with the fiberwise KL expression
`D(P_{A,B|C=c} || P_{A|C=c} × P_{B|C=c})`.
-/
theorem condMutualInfoFstSndGivenThird_eq_KL
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta]
    [MeasurableSpace (alpha × beta)] [MeasurableSingletonClass (alpha × beta)]
    (p : PMF (alpha × beta × gamma)) (c : gamma) :
    condMutualInfoFstSndGivenThird p c =
      condMutualInfoFstSndGivenThirdKL p c := by
  by_cases hc : thirdMarginal p c = 0
  · rw [condMutualInfoFstSndGivenThird_of_thirdMarginal_eq_zero p hc]
    rw [condMutualInfoFstSndGivenThirdKL, dite_eq_left hc]
  · rw [condMutualInfoFstSndGivenThird_of_thirdMarginal_ne_zero p hc]
    rw [condMutualInfoFstSndGivenThirdKL, dite_eq_right hc]
    exact mutualInfo_eq_toReal_klDiv_joint_indepProd
      (p := condFstSndGivenThird p c hc)

/--
Averaged conditional-KL bridge for finite conditional mutual information:

`I(A;B | C) =
  sum_c P_C(c) D(P_{A,B|C=c} || P_{A|C=c} × P_{B|C=c})`.

Zero-marginal `c` contribute zero by definition of
`condMutualInfoFstSndGivenThirdKL`.
-/
theorem condMutualInfo_eq_sum_thirdMarginal_mul_condMutualInfoFstSndGivenThirdKL
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    [MeasurableSpace (alpha × beta)] [MeasurableSingletonClass (alpha × beta)]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p =
      ∑ c : gamma,
        (thirdMarginal p c).toReal * condMutualInfoFstSndGivenThirdKL p c := by
  rw [condMutualInfo_eq_sum_thirdMarginal_mul_condMutualInfoFstSndGivenThird]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [condMutualInfoFstSndGivenThird_eq_KL]

end

end Shannon
end LeanInfoTheory
