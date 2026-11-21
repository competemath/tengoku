/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.SubgaussianConcentration
import Tengoku.Seed.Analysis.Convex.Integral
import Tengoku.Seed.Analysis.Convex.SpecificFunctions.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Expected maximum of a finite sub-Gaussian family

This file proves the standard log-sum-exp estimate for the expected absolute
maximum of a finite family with a common sub-Gaussian variance proxy.  No
independence across the family is required.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory NNReal ENNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega T : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The pointwise absolute maximum over a nonempty finite class.-/
def finiteSubgaussianSupAbs
    (X : Omega → T → ℝ) (N : Finset T) (hN : N.Nonempty) : Omega → ℝ :=
  fun omega => N.sup' hN fun t => |X omega t|

omit [MeasurableSpace Omega] in
theorem abs_le_finiteSubgaussianSupAbs
    (X : Omega → T → ℝ) (N : Finset T) (hN : N.Nonempty)
    {t : T} (ht : t ∈ N) (omega : Omega) :
    |X omega t| ≤ finiteSubgaussianSupAbs X N hN omega := by
  exact Finset.le_sup' (fun u => |X omega u|) ht

omit [MeasurableSpace Omega] in
theorem finiteSubgaussianSupAbs_nonneg
    (X : Omega → T → ℝ) (N : Finset T) (hN : N.Nonempty)
    (omega : Omega) :
    0 ≤ finiteSubgaussianSupAbs X N hN omega := by
  exact (abs_nonneg (X omega hN.choose)).trans
    (abs_le_finiteSubgaussianSupAbs X N hN hN.choose_spec omega)

/-- A finite absolute maximum of sub-Gaussian variables is integrable.-/
theorem integrable_finiteSubgaussianSupAbs
    (X : Omega → T → ℝ) (N : Finset T) (hN : N.Nonempty) (v : ℝ≥0)
    (hX : ∀ t ∈ N, HasSubgaussianMGF (fun omega => X omega t) v mu) :
    Integrable (finiteSubgaussianSupAbs X N hN) mu := by
  have hfold : Integrable
      (N.sup' hN (fun t => fun omega => |X omega t|)) mu :=
    Finset.sup'_induction
      (p := fun f : Omega → ℝ => Integrable f mu) hN _
      (fun _ hf _ hg => Integrable.sup hf hg)
      (fun t ht => (hX t ht).integrable.abs)
  have heq : finiteSubgaussianSupAbs X N hN =
      N.sup' hN (fun t => fun omega => |X omega t|) := by
    funext omega
    exact (Finset.sup'_apply hN (fun t => fun omega => |X omega t|) omega).symm
  rw [heq]
  exact hfold

omit [MeasurableSpace Omega] in
/-- The exponential of the finite absolute maximum is bounded pointwise by
the sum of the positive and negative exponential tilts.-/
theorem exp_mul_finiteSubgaussianSupAbs_le_sum
    (X : Omega → T → ℝ) (N : Finset T) (hN : N.Nonempty)
    (lambda : ℝ) (omega : Omega) :
    exp (lambda * finiteSubgaussianSupAbs X N hN omega) ≤
      ∑ t ∈ N, (exp (lambda * X omega t) + exp (-lambda * X omega t)) := by
  obtain ⟨t, ht, hmax⟩ :=
    Finset.exists_mem_eq_sup' hN (fun u => |X omega u|)
  have hterm :
      exp (lambda * finiteSubgaussianSupAbs X N hN omega) ≤
        exp (lambda * X omega t) + exp (-lambda * X omega t) := by
    rw [finiteSubgaussianSupAbs, hmax]
    by_cases hx : 0 ≤ X omega t
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (exp_pos _).le
    · rw [abs_of_nonpos (le_of_not_ge hx)]
      have hmul : lambda * -X omega t = -lambda * X omega t := by ring
      rw [hmul]
      exact le_add_of_nonneg_left (exp_pos _).le
  have hsingle :
      exp (lambda * X omega t) + exp (-lambda * X omega t) ≤
        ∑ u ∈ N, (exp (lambda * X omega u) + exp (-lambda * X omega u)) := by
    exact Finset.single_le_sum
      (s := N)
      (f := fun u => exp (lambda * X omega u) + exp (-lambda * X omega u))
      (fun u _ => add_nonneg (exp_pos _).le (exp_pos _).le) ht
  exact hterm.trans hsingle

/-- Exponential integrability of the finite maximum, obtained from the finite
sum of the two exponential tilts of every variable.-/
theorem integrable_exp_mul_finiteSubgaussianSupAbs
    (X : Omega → T → ℝ) (N : Finset T) (hN : N.Nonempty) (v : ℝ≥0)
    (hX : ∀ t ∈ N, HasSubgaussianMGF (fun omega => X omega t) v mu)
    (lambda : ℝ) :
    Integrable
      (fun omega => exp (lambda * finiteSubgaussianSupAbs X N hN omega)) mu := by
  have hsumInt : Integrable
      (fun omega =>
        ∑ t ∈ N, (exp (lambda * X omega t) + exp (-lambda * X omega t))) mu := by
    apply integrable_finsetSum N
    intro t ht
    have hpos := (hX t ht).integrable_exp_mul lambda
    have hneg := (hX t ht).integrable_exp_mul (-lambda)
    have hneg' : Integrable (fun omega => exp (-lambda * X omega t)) mu := by
      convert hneg using 1
    exact hpos.add hneg'
  apply hsumInt.mono'
  · exact (((integrable_finiteSubgaussianSupAbs X N hN v hX).aemeasurable
      |>.const_mul lambda).exp.aestronglyMeasurable)
  · exact ae_of_all mu fun omega => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_mul_finiteSubgaussianSupAbs_le_sum X N hN lambda omega

/-- Common-proxy MGF bound for the absolute maximum of a finite sub-Gaussian
family.  Dependence between the variables indexed by `N` is unrestricted.-/
theorem integral_exp_mul_finiteSubgaussianSupAbs_le
    [IsProbabilityMeasure mu]
    (X : Omega → T → ℝ) (N : Finset T) (hN : N.Nonempty) (v : ℝ≥0)
    (hX : ∀ t ∈ N, HasSubgaussianMGF (fun omega => X omega t) v mu)
    (lambda : ℝ) :
    (∫ omega, exp (lambda * finiteSubgaussianSupAbs X N hN omega) ∂mu) ≤
      2 * (N.card : ℝ) * exp ((v : ℝ) * lambda ^ 2 / 2) := by
  have hExp := integrable_exp_mul_finiteSubgaussianSupAbs
    X N hN v hX lambda
  have hsumInt : Integrable
      (fun omega =>
        ∑ t ∈ N, (exp (lambda * X omega t) + exp (-lambda * X omega t))) mu := by
    apply integrable_finsetSum N
    intro t ht
    have hpos := (hX t ht).integrable_exp_mul lambda
    have hneg := (hX t ht).integrable_exp_mul (-lambda)
    have hneg' : Integrable (fun omega => exp (-lambda * X omega t)) mu := by
      convert hneg using 1
    exact hpos.add hneg'
  calc
    (∫ omega, exp (lambda * finiteSubgaussianSupAbs X N hN omega) ∂mu) ≤
        ∫ omega,
          ∑ t ∈ N, (exp (lambda * X omega t) + exp (-lambda * X omega t)) ∂mu := by
      exact integral_mono_ae hExp hsumInt
        (ae_of_all mu fun omega =>
          exp_mul_finiteSubgaussianSupAbs_le_sum X N hN lambda omega)
    _ = ∑ t ∈ N,
          ∫ omega, (exp (lambda * X omega t) + exp (-lambda * X omega t)) ∂mu := by
      exact integral_finsetSum N fun t ht => by
        have hpos := (hX t ht).integrable_exp_mul lambda
        have hneg := (hX t ht).integrable_exp_mul (-lambda)
        have hneg' : Integrable (fun omega => exp (-lambda * X omega t)) mu := by
          convert hneg using 1
        exact hpos.add hneg'
    _ ≤ ∑ _t ∈ N, 2 * exp ((v : ℝ) * lambda ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro t ht
      have hpos :
          (∫ omega, exp (lambda * X omega t) ∂mu) ≤
            exp ((v : ℝ) * lambda ^ 2 / 2) := by
        simpa only [mgf] using (hX t ht).mgf_le lambda
      have hneg :
          (∫ omega, exp (-lambda * X omega t) ∂mu) ≤
            exp ((v : ℝ) * lambda ^ 2 / 2) := by
        simpa only [mgf, neg_sq] using (hX t ht).mgf_le (-lambda)
      rw [integral_add
        ((hX t ht).integrable_exp_mul lambda)
        (by
          have h := (hX t ht).integrable_exp_mul (-lambda)
          convert h using 1)]
      linarith
    _ = 2 * (N.card : ℝ) * exp ((v : ℝ) * lambda ^ 2 / 2) := by
      simp
      ring

/-- Parameterized expectation bound for a finite family with common
sub-Gaussian proxy.-/
theorem integral_finiteSubgaussianSupAbs_le
    [IsProbabilityMeasure mu]
    (X : Omega → T → ℝ) (N : Finset T) (hN : N.Nonempty) (v : ℝ≥0)
    (hX : ∀ t ∈ N, HasSubgaussianMGF (fun omega => X omega t) v mu)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    (∫ omega, finiteSubgaussianSupAbs X N hN omega ∂mu) ≤
      log (2 * (N.card : ℝ)) / lambda + (v : ℝ) * lambda / 2 := by
  have hM := integrable_finiteSubgaussianSupAbs X N hN v hX
  have hExp := integrable_exp_mul_finiteSubgaussianSupAbs
    X N hN v hX lambda
  have hjensen :
      exp (∫ omega, lambda * finiteSubgaussianSupAbs X N hN omega ∂mu) ≤
        ∫ omega, exp (lambda * finiteSubgaussianSupAbs X N hN omega) ∂mu := by
    simpa only [Function.comp_apply] using
      ((convexOn_exp).map_integral_le
        Real.continuous_exp.continuousOn isClosed_univ
        (ae_of_all mu fun _ => Set.mem_univ _)
        (hM.const_mul lambda) hExp)
  rw [integral_const_mul] at hjensen
  have hmgf := integral_exp_mul_finiteSubgaussianSupAbs_le
    X N hN v hX lambda
  have hcardPos : 0 < 2 * (N.card : ℝ) := by
    positivity
  have hexpForm :
      2 * (N.card : ℝ) * exp ((v : ℝ) * lambda ^ 2 / 2) =
        exp (log (2 * (N.card : ℝ)) + (v : ℝ) * lambda ^ 2 / 2) := by
    rw [exp_add, exp_log hcardPos]
  have hlinear :
      lambda * (∫ omega, finiteSubgaussianSupAbs X N hN omega ∂mu) ≤
        log (2 * (N.card : ℝ)) + (v : ℝ) * lambda ^ 2 / 2 := by
    apply exp_le_exp.mp
    exact hjensen.trans (hmgf.trans_eq hexpForm)
  calc
    (∫ omega, finiteSubgaussianSupAbs X N hN omega ∂mu) ≤
        (log (2 * (N.card : ℝ)) + (v : ℝ) * lambda ^ 2 / 2) / lambda := by
      apply (le_div_iff₀ hlambda).2
      simpa [mul_comm] using hlinear
    _ = log (2 * (N.card : ℝ)) / lambda + (v : ℝ) * lambda / 2 := by
      field_simp [hlambda.ne']

/-- Optimized finite-class expectation bound.  The common proxy is assumed
strictly positive only to make the optimizing tilt explicit.-/
theorem integral_finiteSubgaussianSupAbs_le_sqrt
    [IsProbabilityMeasure mu]
    (X : Omega → T → ℝ) (N : Finset T) (hN : N.Nonempty) (v : ℝ≥0)
    (hX : ∀ t ∈ N, HasSubgaussianMGF (fun omega => X omega t) v mu)
    (hv : 0 < (v : ℝ)) :
    (∫ omega, finiteSubgaussianSupAbs X N hN omega ∂mu) ≤
      sqrt (2 * (v : ℝ) * log (2 * (N.card : ℝ))) := by
  have hcardOne : 1 ≤ (N.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hN)
  have hcardArg : 1 < 2 * (N.card : ℝ) := by
    nlinarith
  have hlog : 0 < log (2 * (N.card : ℝ)) := log_pos hcardArg
  let L : ℝ := log (2 * (N.card : ℝ))
  let V : ℝ := (v : ℝ)
  let lambda : ℝ := sqrt (2 * L / V)
  have hL : 0 < L := by simpa [L] using hlog
  have hV : 0 < V := by simpa [V] using hv
  have hlambda : 0 < lambda := by
    dsimp only [lambda]
    exact sqrt_pos.2 (div_pos (mul_pos (by norm_num) hL) hV)
  have hbase := integral_finiteSubgaussianSupAbs_le
    X N hN v hX hlambda
  have hlambdaSq : lambda ^ 2 = 2 * L / V := by
    dsimp only [lambda]
    rw [sq_sqrt]
    exact div_nonneg (mul_nonneg (by norm_num) hL.le) hV.le
  have hlambdaSqMul : lambda ^ 2 * V = 2 * L := by
    exact (eq_div_iff hV.ne').mp hlambdaSq
  let R : ℝ := sqrt (2 * V * L)
  have hRnonneg : 0 ≤ R := sqrt_nonneg _
  have hRsq : R ^ 2 = 2 * V * L := by
    dsimp only [R]
    rw [sq_sqrt]
    positivity
  have hVlambdaNonneg : 0 ≤ V * lambda :=
    mul_nonneg hV.le hlambda.le
  have hVlambdaSq : (V * lambda) ^ 2 = 2 * V * L := by
    calc
      (V * lambda) ^ 2 = V * (lambda ^ 2 * V) := by ring
      _ = 2 * V * L := by rw [hlambdaSqMul]; ring
  have hVlambda : V * lambda = R := by
    nlinarith
  have hhalf : L / lambda = V * lambda / 2 := by
    apply (div_eq_iff hlambda.ne').2
    nlinarith [hlambdaSqMul]
  have hopt : L / lambda + V * lambda / 2 = R := by
    rw [hhalf]
    nlinarith
  change (∫ omega, finiteSubgaussianSupAbs X N hN omega ∂mu) ≤
    L / lambda + V * lambda / 2 at hbase
  change (∫ omega, finiteSubgaussianSupAbs X N hN omega ∂mu) ≤ R
  exact hbase.trans_eq hopt

end ProbabilityTheory
