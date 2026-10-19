/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.Definitions
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.BasisLocalization
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.ImportedAnalyticInputs
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.Data.Nat.Factorial.DoubleFactorial
import Tengoku.Seed.MeasureTheory.Integral.Pi
import Tengoku.Seed.Tactic.NormNum.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # ImportedAnalyticInputs -/

@[expose] public section

open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Hermite1DimdLEAN

/-- `oneDimLift`: one Dim Lift. -/
def oneDimLift (f : ℂ → ℂ) : CSpace 1 → ℂ := fun z => f (z 0)

private lemma measurable_ofReal_gaussianDensity (d : ℕ) :
    Measurable (fun z : CSpace d => ENNReal.ofReal (gaussianDensity d z)) := by
  unfold gaussianDensity
  fun_prop

private lemma gaussianDensity_ofReal_lt_top (d : ℕ) :
    ∀ᵐ x : CSpace d, ENNReal.ofReal (gaussianDensity d x) < ⊤ := by
  simp_all

private lemma toReal_gaussianDensity_one (z : CSpace 1) :
    (ENNReal.ofReal (gaussianDensity 1 z)).toReal =
      (1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2) := by
  have hnonneg : 0 ≤ Real.pi⁻¹ * Real.exp (-‖z 0‖ ^ 2) := by positivity
  simp [gaussianDensity, hnonneg]

private lemma integral_funUnique_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℂ → E) :
    ∫ z : CSpace 1, φ (z 0) ∂(volume : Measure (CSpace 1)) =
      ∫ z : ℂ, φ z ∂(volume : Measure ℂ) := by
  have hEq0 :=
    ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
      (f := MeasurableEquiv.funUnique (Fin 1) ℂ) φ)
  exact hEq0

private theorem sum_Icc_eq_sum_Fin {α : Type*} [AddCommMonoid α]
    (N L : ℕ) (hL : 1 ≤ L) (f : ℕ → α) :
    ∑ n ∈ Finset.Icc N (N + L - 1), f n =
      ∑ m : Fin L, f (N + m.1) := by
  symm
  apply Finset.sum_nbij (fun (m : Fin L) => N + m.val)
  · intro m _
    exact Finset.mem_Icc.mpr ⟨Nat.le_add_right N m.val, by omega⟩
  · intro a _ b _ hab
    exact Fin.ext (Nat.add_left_cancel hab)
  · intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    refine ⟨⟨n - N, by omega⟩, Finset.mem_univ _, ?_⟩
    simp_all
  · simp_all

private def bandCoeff (N L : ℕ) (c : Fin L → ℂ) : ℕ → ℂ :=
  fun n => if h : N ≤ n ∧ n < N + L then c ⟨n - N, by omega⟩ else 0

private theorem positiveBandEq (N L : ℕ) (hL : 1 ≤ L) (c : Fin L → ℂ) :
    HermiteLEAN.positiveTrigonometricPolynomial
        (HermiteLEAN.frequencyBand N L) (bandCoeff N L c) =
      bandLimitedPolynomial N L c := by
  ext t
  rw [HermiteLEAN.positiveTrigonometricPolynomial, HermiteLEAN.frequencyBand,
    sum_Icc_eq_sum_Fin N L hL]
  simp [bandLimitedPolynomial, bandCoeff]

private lemma circleL2NormSq_const_mul (a : ℂ) (P : Circle → ℂ) :
    circleL2NormSq (fun t => a * P t) = ‖a‖ ^ 2 * circleL2NormSq P := by
  unfold circleL2NormSq
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [mul_pow]

private lemma circleL2NormSq_real_const_mul (b : ℝ) (f : Circle → ℝ) :
    circleL2NormSq (fun t => b * f t) = b ^ 2 * circleL2NormSq f := by
  unfold circleL2NormSq
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [mul_pow, sq_abs]

private lemma rho_mul_right (a u : ℂ) :
    rho a (a * u) = ‖a‖ * rho 1 u := by
  by_cases ha : a = 0
  · subst ha
    simp [rho]
  · have hnn : 0 ≤ ‖a‖ := norm_nonneg _
    rw [rho, rho]
    have h1 : a + a * u = a * (1 + u) := by ring
    rw [h1, norm_mul]
    calc
      |‖a‖ * ‖1 + u‖ - ‖a‖| = |‖a‖ * (‖1 + u‖ - 1)| := by ring_nf
      _ = ‖a‖ * |‖1 + u‖ - 1| := by rw [abs_mul, abs_of_nonneg hnn]
      _ = ‖a‖ * rho 1 u := by simp [rho]

private lemma measurableSet_complex_annulus
    (j : ℕ) :
    MeasurableSet (HermiteLEAN.annulus j) := by
  have hge : MeasurableSet {z : ℂ | (j : ℝ) ≤ ‖z‖} :=
    measurableSet_le measurable_const measurable_norm
  have hlt : MeasurableSet {z : ℂ | ‖z‖ < (j : ℝ) + 1} :=
    measurableSet_lt measurable_norm measurable_const
  simpa [HermiteLEAN.annulus, Set.ofPred_and] using hge.inter hlt

private theorem gaussianInner_oneDimPhi_eq_weightedInner
    (k m n : ℕ) :
    gaussianInner (d := 1) (oneDimLift (oneDimPhi k m)) (oneDimLift (oneDimPhi k n)) =
      HermitekLEAN.weightedInner (HermitekLEAN.Phi k m) (HermitekLEAN.Phi k n) := by
  change
    gaussianInner (d := 1) (fun z => HermitekLEAN.Phi k m (z 0))
      (fun z => HermitekLEAN.Phi k n (z 0)) =
      HermitekLEAN.weightedInner (HermitekLEAN.Phi k m) (HermitekLEAN.Phi k n)
  unfold gaussianInner HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  rw [gaussianMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_ofReal_gaussianDensity 1) (gaussianDensity_ofReal_lt_top 1)]
  have hcomp :
        ∫ z : CSpace 1,
            HermitekLEAN.Phi k m (z 0) *
              ((Real.exp (-‖z 0‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n (z 0)))
              ∂(volume : Measure (CSpace 1)) =
          ∫ z : ℂ,
            HermitekLEAN.Phi k m z *
              ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))
              ∂(volume : Measure ℂ) :=
    integral_funUnique_one (fun z : ℂ =>
      HermitekLEAN.Phi k m z * ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z)))
  calc
    ∫ z : CSpace 1,
        (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
          ∂(volume : Measure (CSpace 1))
        =
      ∫ z : CSpace 1,
        ((1 / Real.pi : ℂ) *
          ((HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
            (Real.exp (-‖z 0‖ ^ 2) : ℂ))) ∂(volume : Measure (CSpace 1)) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [Algebra.smul_def, toReal_gaussianDensity_one z,
            show (algebraMap ℝ ℂ) ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) =
                ((1 / Real.pi : ℂ) * (Real.exp (-‖z 0‖ ^ 2) : ℂ)) by simp]
          ring
    _ =
      (1 / Real.pi : ℂ) *
        ∫ z : CSpace 1,
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
            (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1)) :=
            MeasureTheory.integral_const_mul _ _
    _ = (1 / Real.pi : ℂ) *
        ∫ z : ℂ,
          (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
            (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) := by
          have hcomp' : ∫ z : CSpace 1,
              (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1)) =
              ∫ z : ℂ,
                (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
                  (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) := by
            rw [show (fun z : CSpace 1 =>
                  (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                    (Real.exp (-‖z 0‖ ^ 2) : ℂ)) =
                fun z : CSpace 1 =>
                  HermitekLEAN.Phi k m (z 0) *
                    ((Real.exp (-‖z 0‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n (z 0))) from
                by funext z; ring,
              hcomp]
            apply integral_congr_ae
            filter_upwards with z
            ring
          rw [hcomp']

private theorem annulusMass_oneDimPhi_eq_annulusIntegralSq
    (k n j : ℕ) :
    annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n)) =
      HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k n) j := by
  classical
  change
    annulusMass (d := 1) (fun _ => j) (fun z => HermitekLEAN.Phi k n (z 0)) =
      HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k n) j
  unfold annulusMass HermitekLEAN.annulusIntegralSq HermiteLEAN.annulusIntegralSq
  rw [gaussianMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_ofReal_gaussianDensity 1) (gaussianDensity_ofReal_lt_top 1)]
  calc
    ∫ z : CSpace 1,
        (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
          (if z ∈ productAnnulus (d := 1) (fun _ => j) then ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 else 0)
          ∂(volume : Measure (CSpace 1))
        =
      ∫ z : CSpace 1,
        ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) *
          (if z ∈ productAnnulus (d := 1) (fun _ => j) then ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 else 0)
          ∂(volume : Measure (CSpace 1)) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [toReal_gaussianDensity_one z]
          simp [smul_eq_mul]
    _ =
      (1 / Real.pi) *
        ∫ z : CSpace 1,
          if z ∈ productAnnulus (d := 1) (fun _ => j) then
            ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 * Real.exp (-‖z 0‖ ^ 2)
          else 0 ∂(volume : Measure (CSpace 1)) := by
          have hrew :
              ∫ z : CSpace 1,
                ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) *
                  (if z ∈ productAnnulus (d := 1) (fun _ => j) then ‖HermitekLEAN.Phi k n (z 0)‖ ^
                      2 else 0)
                  ∂(volume : Measure (CSpace 1)) =
              ∫ z : CSpace 1,
                (1 / Real.pi) *
                  (if z ∈ productAnnulus (d := 1) (fun _ => j) then
                    ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 * Real.exp (-‖z 0‖ ^ 2)
                  else 0) ∂(volume : Measure (CSpace 1)) := by
                apply integral_congr_ae
                filter_upwards with z
                by_cases hz : z ∈ productAnnulus (d := 1) (fun _ => j) <;> simp [hz,
                    mul_left_comm, mul_comm]
          exact hrew.trans (MeasureTheory.integral_const_mul _ _)
    _ =
      (1 / Real.pi) *
        ∫ z : ℂ,
          if z ∈ HermiteLEAN.annulus j then
            ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
          else 0 ∂(volume : Measure ℂ) := by
          let e : CSpace 1 ≃ᵐ ℂ := MeasurableEquiv.funUnique (Fin 1) ℂ
          have hEq0 :=
            ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
              (f := e)
              (fun z : ℂ =>
                if z ∈ HermiteLEAN.annulus j then
                  ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
                else 0))
          have he : ∀ z : CSpace 1, e z = z 0 := fun _ => rfl
          have h := congrArg ((1 / Real.pi) * ·) hEq0
          simp only [productAnnulus, HermiteLEAN.annulus, he, Set.mem_ofPred_eq,
            Fin.forall_fin_one, Nat.cast_add, Nat.cast_one] at h ⊢
          exact h
    _ =
      (1 / Real.pi) *
        ∫ z in HermiteLEAN.annulus j,
          ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ) := by
          congr 1
          rw [← MeasureTheory.integral_indicator (measurableSet_complex_annulus j)]
          simp [Set.indicator]

/-!
# ImportedAnalyticInputs

Statement-only scaffold for the one-variable and abstract analytic inputs.
Scaffolding notes: `ScaffoldingNotes/Imported/analytic_inputs.md`.
-/

/-- Imported one-variable basis orthonormality at fixed true-Hermite level. -/
theorem oneVariableBasisOrthonormal
    (k m n : ℕ) :
    gaussianInner (d := 1) (oneDimLift (oneDimPhi k m)) (oneDimLift (oneDimPhi k n)) =
      if m = n then (1 : ℂ) else 0 := by
  /-
  Scaffolding guidance:
  re-export the frozen one-dimensional basis theorem under a stable name.
  Downstream files only use orthonormality and finite Parseval consequences.
  -/
  rw [gaussianInner_oneDimPhi_eq_weightedInner]
  simpa using (HermitekLEAN.phi_orthonormal (k := k) (m := m) (n := n))

/-- Imported one-variable localization estimate for `n ≥ 1`. -/
theorem oneVariableLocalization
    (k : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ n j : ℕ, 1 ≤ n →
        annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n)) ≤
          C *
            Real.exp
              (-c *
                max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
  /-
  Scaffolding guidance:
  the scaffold keeps the quantifier/hypothesis shape `n ≥ 1`.
  The imported theorem is existential in the localization constants and should
  not be silently strengthened.
  -/
  obtain ⟨C, c, hC, hc, hloc⟩ := HermitekLEAN.single_basis_localization k
  refine ⟨C, c, hC, hc, ?_⟩
  intro n j hn
  rw [annulusMass_oneDimPhi_eq_annulusIntegralSq]
  simpa [oneDimPhi, HermitekLEAN.posPart, HermiteLEAN.posPart] using hloc n j hn

private lemma zero_shift_exp_compare
    (k j : ℕ) (c0 : ℝ) (hc0 : 0 < c0) :
    Real.exp (-c0 * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) ≤
      Real.exp c0 *
        Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
  by_cases hsmall : j ≤ k + 4
  · have hx : posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) = 0 := by
      apply max_eq_right
      exact sub_nonpos.mpr (by exact_mod_cast hsmall)
    have hy : posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ)) = 0 := by
      apply max_eq_right
      exact sub_nonpos.mpr (by exact_mod_cast Nat.le_trans hsmall (Nat.le_succ _))
    rw [hx, hy]
    simpa using (Real.one_le_exp_iff.mpr hc0.le)
  · have hbig : k + 5 ≤ j := by omega
    have hx :
        posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) =
          (j : ℝ) - ((k + 4 : ℕ) : ℝ) := by
      apply max_eq_left
      exact sub_nonneg.mpr (by exact_mod_cast Nat.le_trans (Nat.le_succ _) hbig)
    have hy :
        posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ)) =
          (j : ℝ) - ((k + 5 : ℕ) : ℝ) := by
      apply max_eq_left
      exact sub_nonneg.mpr (by exact_mod_cast hbig)
    have hrel :
        (j : ℝ) - ((k + 4 : ℕ) : ℝ) =
          ((j : ℝ) - ((k + 5 : ℕ) : ℝ)) + 1 := by
      norm_num [Nat.cast_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [hx, hy, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    let y : ℝ := (j : ℝ) - ((k + 5 : ℕ) : ℝ)
    have hybound : 2 * y ≤ y ^ 2 + 1 := by nlinarith [sq_nonneg (y - 1)]
    have hsq : (y + 1) ^ 2 ≤ 4 * (y ^ 2 + 1) := by nlinarith
    have hsq' :
        ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) ^ 2 ≤
          4 * (((j : ℝ) - ((k + 5 : ℕ) : ℝ)) ^ 2 + 1) := by
      rw [hrel]
      simpa [y] using hsq
    nlinarith [hc0, hsq']

/-- Imported positive-frequency circle estimate with frozen constant `144`. -/
theorem positiveFrequencyCircleEstimate
    (E : Finset ℕ) (b : ℕ → ℂ)
    (hpos : ∀ n ∈ E, 0 < n)
    (_hP : HasPositiveFrequencySupport (positiveFrequencyPolynomial E b) E) :
    circleL2NormSq (positiveFrequencyPolynomial E b) ≤
      144 * E.card * circleL2NormSq (fun t => rho 1 (positiveFrequencyPolynomial E b t)) := by
  /-
  Scaffolding guidance:
  this is the circle estimate used on low annuli. Keep the positive-frequency
  hypothesis explicit and keep the exact constant `144`.
  -/
  rw [show circleL2NormSq (positiveFrequencyPolynomial E b) =
      HermiteLEAN.circleL2Sq (HermiteLEAN.positiveTrigonometricPolynomial E b) by
      rfl]
  rw [show circleL2NormSq (fun t => rho 1 (positiveFrequencyPolynomial E b t)) =
      HermiteLEAN.circleRhoNormSq (HermiteLEAN.positiveTrigonometricPolynomial E b) by
      simp [circleL2NormSq, rho, positiveFrequencyPolynomial, HermiteLEAN.circleRhoNormSq,
        HermiteLEAN.positiveTrigonometricPolynomial, HermiteLEAN.rho, sq_abs]]
  simpa using
    HermitekLEAN.local_circle_estimate E
      (by
        intro n hn
        exact Nat.succ_le_of_lt (hpos n hn))
      b

/-- Imported high-frequency band estimate with frozen constants `32` and `1343`. -/
theorem highFrequencyBandEstimate
    (N L : ℕ) (c : Fin L → ℂ)
    (hgap : 1343 * L ^ 2 ≤ N ^ 2)
    (hP : HasBandlimitedSupport (bandLimitedPolynomial N L c) N L) :
    circleL2NormSq (bandLimitedPolynomial N L c) ≤
      32 * circleL2NormSq (fun t => rho 1 (bandLimitedPolynomial N L c t)) := by
  /-
  Scaffolding guidance:
  this is the band-limited estimate used after the degree-threshold argument.
  Preserve the exact constants and the separate support hypothesis.
  -/
  by_cases hL0 : L = 0
  · subst hL0
    simp only [circleL2NormSq, bandLimitedPolynomial, univ_eq_empty, Nat.cast_add, fourier_apply,
      fourier_add', natCast_zsmul, sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero, norm_eq_abs, sq_abs, integral_const,
      probReal_univ, smul_eq_mul, one_mul, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    positivity
  · have hL : 1 ≤ L := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hL0)
    have hNsqpos : 0 < N ^ 2 := lt_of_lt_of_le (by positivity) hgap
    have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at hNsqpos
    have hBandEq := positiveBandEq N L hL c
    calc
      circleL2NormSq (bandLimitedPolynomial N L c)
          = HermiteLEAN.circleL2Sq
              (HermiteLEAN.positiveTrigonometricPolynomial
                (HermiteLEAN.frequencyBand N L) (bandCoeff N L c)) := by
            rw [hBandEq]
            rfl
      _ ≤ 32 * HermiteLEAN.circleRhoNormSq
            (HermiteLEAN.positiveTrigonometricPolynomial
              (HermiteLEAN.frequencyBand N L) (bandCoeff N L c)) := by
            have hgap_real : 1343 * (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgap
            simpa using
              HermitekLEAN.high_frequency_circle_estimate N L hN hL (bandCoeff N L c)
                hgap_real
      _ = 32 * circleL2NormSq (fun t => rho 1 (bandLimitedPolynomial N L c t)) := by
            rw [hBandEq]
            simp [circleL2NormSq, rho, HermiteLEAN.circleRhoNormSq, HermiteLEAN.rho,
              sq_abs]

/-- Project-owned upgrade of localization that now includes the zero mode. -/
theorem localizationIncludingZero
    (k : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ n j : ℕ,
        annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n)) ≤
          C *
            Real.exp
              (-c *
                max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
  /-
  Scaffolding guidance:
  derive the `n = 0` case directly from the explicit formula, then package
  the all-`n` statement for downstream reuse.
  -/
  obtain ⟨C1, c1, hC1, hc1, hloc1⟩ := oneVariableLocalization k
  obtain ⟨C0, c0, hC0, hc0, hloc0⟩ := HermitekLEAN.phi0_localization k
  let C : ℝ := max C1 (C0 * Real.exp c0)
  let c : ℝ := min c1 (c0 / 4)
  refine ⟨C, c, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hC1 (le_max_left _ _)
  · exact lt_min hc1 (by positivity)
  · intro n j
    by_cases hn : n = 0
    · subst hn
      have hexact :
          max (|((j : ℕ) : ℝ) - Real.sqrt ((0 : ℕ) : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 =
            posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) := by simp [Real.sqrt_zero, posPart]
      rw [annulusMass_oneDimPhi_eq_annulusIntegralSq]
      have hphi0 :
          HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k 0) j ≤
            C0 * Real.exp (-c0 * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) := by
        simpa [oneDimPhi, HermitekLEAN.phi0, HermitekLEAN.posPart, HermiteLEAN.posPart,
          _root_.posPart_def] using hloc0 j
      have hcompare := zero_shift_exp_compare k j c0 hc0
      have hCle : C0 * Real.exp c0 ≤ C := le_max_right _ _
      have hcle : c ≤ c0 / 4 := min_le_right _ _
      calc
        HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k 0) j
            ≤ C0 * Real.exp (-c0 * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) := hphi0
        _ ≤ (C0 * Real.exp c0) *
              Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
              have := mul_le_mul_of_nonneg_left hcompare (le_of_lt hC0)
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
        _ ≤ C * Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
              have hexp_nonneg :
                  0 ≤ Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
                positivity
              exact mul_le_mul_of_nonneg_right hCle hexp_nonneg
        _ ≤ C * Real.exp (-(c * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              apply Real.exp_le_exp.mpr
              nlinarith [hcle, sq_nonneg (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ)))]
        _ = C * Real.exp (-c *
              max (|((j : ℕ) : ℝ) - Real.sqrt ((0 : ℕ) : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
              simp_all
    · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hbase := hloc1 n j hn1
      have hCle : C1 ≤ C := le_max_left _ _
      have hcle : c ≤ c1 := min_le_left _ _
      calc
        annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n))
            ≤ C1 *
              Real.exp
                (-c1 *
                  max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := hbase
        _ ≤ C *
              Real.exp
                (-c1 *
                  max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
              have hexp_nonneg :
                  0 ≤ Real.exp
                    (-c1 *
                      max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
                positivity
              exact mul_le_mul_of_nonneg_right hCle hexp_nonneg
        _ ≤ C *
              Real.exp
                (-c *
                  max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              apply Real.exp_le_exp.mpr
              nlinarith [hcle,
                sq_nonneg (max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0)]

/-- Scalar-rescaled positive-frequency estimate for an arbitrary background `a`. -/
theorem scaledPositiveFrequencyCircleEstimate
    (a : ℂ) (E : Finset ℕ) (P : Circle → ℂ)
    (hpos : ∀ n ∈ E, 0 < n)
    (hP : HasPositiveFrequencySupport P E) :
    circleL2NormSq P ≤ 144 * E.card * circleL2NormSq (fun t => rho a (P t)) := by
  /-
  Scaffolding guidance:
  normalize by `a` when `a ≠ 0`, and keep the `a = 0` branch separate.
  Export the final statement so later files do not redo the rescaling.
  -/
  by_cases ha : a = 0
  · subst ha
    rcases hP with ⟨b, rfl⟩
    by_cases hE : E = ∅
    · subst hE
      simp [positiveFrequencyPolynomial, circleL2NormSq, rho]
    · have hnonneg : 0 ≤ circleL2NormSq (positiveFrequencyPolynomial E b) := by
        unfold circleL2NormSq
        positivity
      have hcard : 0 < E.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hE)
      have honeR : (1 : ℝ) ≤ E.card := by exact_mod_cast (Nat.succ_le_of_lt hcard)
      have hfac : (1 : ℝ) ≤ 144 * (E.card : ℝ) := by nlinarith
      calc
        circleL2NormSq (positiveFrequencyPolynomial E b)
            ≤ 144 * E.card * circleL2NormSq (positiveFrequencyPolynomial E b) :=
              le_mul_of_one_le_left hnonneg hfac
        _ =
          144 * E.card *
            circleL2NormSq (fun t => rho 0 (positiveFrequencyPolynomial E b t)) := by
              simp [circleL2NormSq, rho]
  · rcases hP with ⟨b, rfl⟩
    let Q : Circle → ℂ := positiveFrequencyPolynomial E (fun n => a⁻¹ * b n)
    have hQ : HasPositiveFrequencySupport Q E := ⟨fun n => a⁻¹ * b n, rfl⟩
    have hbase :=
      positiveFrequencyCircleEstimate E (fun n => a⁻¹ * b n) hpos hQ
    have hbaseQ :
        circleL2NormSq Q ≤
          144 * E.card * circleL2NormSq (fun t => rho 1 (Q t)) := by simpa [Q] using hbase
    have hmulP : (fun t => a * Q t) = positiveFrequencyPolynomial E b := by
      funext t
      simp only [Q, positiveFrequencyPolynomial, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro n hn
      field_simp [ha]
    have hmulR : (fun t => rho a (a * Q t)) = fun t => ‖a‖ * rho 1 (Q t) := by
      funext t
      simp [rho_mul_right]
    rw [← hmulP, circleL2NormSq_const_mul]
    have hconstR :
        circleL2NormSq (fun t => ‖a‖ * rho 1 (Q t)) =
          ‖a‖ ^ 2 * circleL2NormSq (fun t => rho 1 (Q t)) :=
      circleL2NormSq_real_const_mul ‖a‖ (fun t => rho 1 (Q t))
    calc
      ‖a‖ ^ 2 * circleL2NormSq Q ≤
          144 * E.card * (‖a‖ ^ 2 * circleL2NormSq (fun t => rho 1 (Q t))) := by
            have hscaled := mul_le_mul_of_nonneg_left hbaseQ (sq_nonneg ‖a‖)
            simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
      _ = 144 * E.card * circleL2NormSq (fun t => ‖a‖ * rho 1 (Q t)) := by rw [hconstR]
      _ = 144 * E.card * circleL2NormSq (fun t => rho a (a * Q t)) := by rw [hmulR]

/-- Scalar-rescaled high-frequency estimate for an arbitrary background `a`. -/
theorem scaledHighFrequencyBandEstimate
    (a : ℂ) (N L : ℕ) (P : Circle → ℂ)
    (hgap : 1343 * L ^ 2 ≤ N ^ 2)
    (hP : HasBandlimitedSupport P N L) :
    circleL2NormSq P ≤ 32 * circleL2NormSq (fun t => rho a (P t)) := by
  by_cases ha : a = 0
  · subst ha
    have hnonneg : 0 ≤ circleL2NormSq P := by
      unfold circleL2NormSq
      positivity
    calc
      circleL2NormSq P ≤ 32 * circleL2NormSq P := by nlinarith
      _ = 32 * circleL2NormSq (fun t => rho 0 (P t)) := by simp [circleL2NormSq, rho]
  · rcases hP with ⟨c, rfl⟩
    let Q : Circle → ℂ := bandLimitedPolynomial N L (fun m => a⁻¹ * c m)
    have hQ : HasBandlimitedSupport Q N L := ⟨fun m => a⁻¹ * c m, rfl⟩
    have hbase := highFrequencyBandEstimate N L (fun m => a⁻¹ * c m) hgap hQ
    have hbaseQ : circleL2NormSq Q ≤ 32 * circleL2NormSq (fun t => rho 1 (Q t)) := by
      simpa [Q] using hbase
    have hmulP : (fun t => a * Q t) = bandLimitedPolynomial N L c := by
      funext t
      simp only [Q, bandLimitedPolynomial, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m hm
      field_simp [ha]
    have hmulR : (fun t => rho a (a * Q t)) = fun t => ‖a‖ * rho 1 (Q t) := by
      funext t
      simp [rho_mul_right]
    rw [← hmulP, circleL2NormSq_const_mul]
    have hconstR :
        circleL2NormSq (fun t => ‖a‖ * rho 1 (Q t)) =
          ‖a‖ ^ 2 * circleL2NormSq (fun t => rho 1 (Q t)) :=
      circleL2NormSq_real_const_mul ‖a‖ (fun t => rho 1 (Q t))
    calc
      ‖a‖ ^ 2 * circleL2NormSq Q ≤
          32 * (‖a‖ ^ 2 * circleL2NormSq (fun t => rho 1 (Q t))) :=
            mul_le_mul_of_nonneg_left hbaseQ (sq_nonneg ‖a‖) |>.trans_eq (by ring)
      _ = 32 * circleL2NormSq (fun t => ‖a‖ * rho 1 (Q t)) := by rw [hconstR]
      _ = 32 * circleL2NormSq (fun t => rho a (a * Q t)) := by rw [hmulR]

/-- One-variable angular factorization used in the annulus orthogonality argument. -/
private lemma oneVariableAngularFactorization_termwise
    (r t : ℝ) (k n j : ℕ) (hjk : j ≤ k) (hjn : j ≤ n) :
    (r : ℂ) ^ (k - j) *
      ((r : ℂ) ^ (n - j) *
        (Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
          ((Nat.choose k j : ℂ) *
            ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
              (Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j) *
                ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))))) =
    Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
      ((Nat.choose k j : ℂ) *
        ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
          ((-1 : ℂ) ^ j * ((↑r : ℂ) ^ (n + k - j * 2) * ((↑√↑k.factorial)⁻¹ *
              (↑√↑n.factorial)⁻¹))))) := by
  have hrpow :
      (r : ℂ) ^ (k - j) * (r : ℂ) ^ (n - j) =
        (r : ℂ) ^ (n + k - j * 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hphase :
      Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
          Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j) =
        Complex.exp (Complex.I * (↑t * (↑n - ↑k))) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [Nat.cast_sub hjn, Nat.cast_sub hjk]
    ring
  calc
    (r : ℂ) ^ (k - j) *
        ((r : ℂ) ^ (n - j) *
          (Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
            ((Nat.choose k j : ℂ) *
              ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
                (Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j) *
                  ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))))) =
      ((r : ℂ) ^ (k - j) * (r : ℂ) ^ (n - j)) *
        ((Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
            Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j)) *
          ((Nat.choose k j : ℂ) *
            ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
              ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))) := by ring
    _ =
      (↑r : ℂ) ^ (n + k - j * 2) *
        (Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
          ((Nat.choose k j : ℂ) *
            ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
              ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))) := by rw [hrpow, hphase]
    _ =
      Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
        ((Nat.choose k j : ℂ) *
          ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
            ((-1 : ℂ) ^ j * ((↑r : ℂ) ^ (n + k - j * 2) * ((↑√↑k.factorial)⁻¹ *
                (↑√↑n.factorial)⁻¹))))) := by ring

theorem oneVariableAngularFactorization
    (k n : ℕ) :
    ∃ radial : Polynomial ℝ,
      ∀ r t : ℝ,
        oneDimPhi k n ((r : ℂ) * Complex.exp (Complex.I * t)) =
          Complex.exp (Complex.I * ((((n : ℤ) - (k : ℤ)) : ℂ) * t)) *
            radial.eval₂ (algebraMap ℝ ℂ) r := by
  let radial : Polynomial ℝ :=
    Finset.sum (Finset.range (min k n + 1)) fun j =>
      Polynomial.monomial (n + k - j * 2)
        (((Nat.choose k j : ℝ) *
            ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ))) *
          (((-1 : ℝ) ^ j) *
            (((Real.sqrt (Nat.factorial k : ℝ))⁻¹) *
              ((Real.sqrt (Nat.factorial n : ℝ))⁻¹))))
  refine ⟨radial, ?_⟩
  intro r t
  have hnorm :
      (1 / (↑(Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)) =
        ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
          (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹ : ℂ) := by
    have hnormR :
        (1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) =
          (Real.sqrt (Nat.factorial k : ℝ))⁻¹ *
            (Real.sqrt (Nat.factorial n : ℝ))⁻¹ := by
      rw [Real.sqrt_mul (show (0 : ℝ) ≤ Nat.factorial k by positivity)]
      field_simp
        [Real.sqrt_ne_zero'.2
          (by exact_mod_cast Nat.factorial_pos k : (0 : ℝ) < Nat.factorial k),
         Real.sqrt_ne_zero'.2
          (by exact_mod_cast Nat.factorial_pos n : (0 : ℝ) < Nat.factorial n)]
    exact_mod_cast hnormR
  have hstar_z :
      star ((r : ℂ) * Complex.exp (Complex.I * t)) =
        (r : ℂ) * Complex.exp (-(Complex.I * t)) := by
    rw [Complex.star_def, map_mul, ← Complex.exp_conj]
    simp
  have hphaseCast :
      Complex.exp (Complex.I * ((((n : ℤ) - (k : ℤ)) : ℂ) * t)) =
        Complex.exp (Complex.I * (↑t * (↑n - ↑k))) := by
    congr 1
    push_cast
    ring
  unfold oneDimPhi
  rw [hphaseCast, hnorm, Finset.mul_sum]
  have hsum :
      Finset.sum (Finset.range (min k n + 1))
        (fun j =>
          ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
              (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹) *
            (((-1 : ℂ) ^ j * ↑(Nat.choose k j) *
                  (↑(Nat.factorial n) / ↑(Nat.factorial (n - j)))) *
              (((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (n - j) *
                star ((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (k - j)))) =
      Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
        Finset.sum (Finset.range (min k n + 1))
          (fun j =>
            ↑(Nat.choose k j) *
              (↑(Nat.factorial n) / ↑(Nat.factorial (n - j)) *
                ((-1 : ℂ) ^ j *
                  ((r : ℂ) ^ (n + k - j * 2) *
                    ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
                      (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹))))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range, Nat.lt_add_one_iff, le_min_iff] at hj
    obtain ⟨hjk, hjn⟩ := hj
    rw [hstar_z, mul_pow, mul_pow]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      oneVariableAngularFactorization_termwise r t k n j hjk hjn
  have hsum' :
      Finset.sum (Finset.range (min k n + 1))
        (fun i =>
          ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
                (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹) *
              ((-1 : ℂ) ^ i * ↑(Nat.choose k i) *
                    (↑(Nat.factorial n) / ↑(Nat.factorial (n - i))) *
                  ((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (n - i) *
                star ((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (k - i))) =
      Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
        Finset.sum (Finset.range (min k n + 1))
          (fun j =>
            ↑(Nat.choose k j) *
              (↑(Nat.factorial n) / ↑(Nat.factorial (n - j)) *
                ((-1 : ℂ) ^ j *
                  ((r : ℂ) ^ (n + k - j * 2) *
                    ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
                      (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹))))) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  rw [hsum']
  congr 1
  simp [radial, Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial,
    mul_assoc, mul_left_comm, mul_comm]

end Hermite1DimdLEAN
