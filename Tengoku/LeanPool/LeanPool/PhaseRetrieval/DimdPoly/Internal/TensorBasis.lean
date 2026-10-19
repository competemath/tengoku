/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.ImportedAnalyticInputs
public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.Definitions
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ImportedAnalyticInputs
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ProductBasisAndAnnuli
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.TrueLevelBasis
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.Data.Nat.Factorial.DoubleFactorial
import Tengoku.Seed.Tactic.NormNum.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # TensorBasis -/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace DimdPolyLEAN

/-!
# TensorBasis

Statement-first scaffold for the frozen coefficient model and realization maps
for the fixed-dimension polyanalytic Fock basis.
-/

theorem coeff_ofPkappa
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) (alpha : Idx d) :
    coeffSkappa (ofPkappa kappa F) alpha = coeffPkappa F alpha := by
  let _ := hd
  simp [coeffSkappa, coeffPkappa, ofPkappa]

theorem evalPkappa_zero
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    evalPkappa kappa (0 : Pkappa d kappa) = 0 := by
  let _ := hd
  ext z
  simp [evalPkappa]

theorem evalPkappa_add
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    evalPkappa kappa (F + G) = fun z => evalPkappa kappa F z + evalPkappa kappa G z := by
  let _ := hd
  ext z
  simp [evalPkappa, Finsupp.sum_add_index, add_mul]

theorem evalPkappa_smul
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (c : ℂ) (F : Pkappa d kappa) :
    evalPkappa kappa (c • F) = fun z => c * evalPkappa kappa F z := by
  let _ := hd
  ext z
  by_cases hc : c = 0
  · subst c
    simp [evalPkappa]
  · unfold evalPkappa
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_smul_eq hc, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    rw [Finsupp.smul_apply]
    simp [mul_left_comm, mul_comm]

theorem evalPkappa_sub
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    evalPkappa kappa (F - G) = fun z => evalPkappa kappa F z - evalPkappa kappa G z := by
  let _ := hd
  have hneg : -G = (-1 : ℂ) • G := by
    simp_all
  rw [sub_eq_add_neg, hneg, evalPkappa_add hd kappa F ((-1 : ℂ) • G),
    evalPkappa_smul hd kappa (-1 : ℂ) G]
  ext z
  simp [sub_eq_add_neg]

theorem projFinset_idempotent
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (E : Finset (Idx d)) (F : Pkappa d kappa) :
    projFinset E (projFinset E F) = projFinset E F := by
  let _ := hd
  ext alpha
  by_cases h : alpha ∈ E
  · simp [projFinset, h]
  · simp [projFinset, h]

theorem exact_truncate_coeff_energy
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (E : Finset (Idx d)) (F : Skappa d kappa) :
    ‖truncateFinset E F‖ ^ 2 = Finset.sum E (fun alpha => ‖coeffSkappa F alpha‖ ^ 2) := by
  let _ := hd
  classical
  have hcoeff :
      ∀ alpha : Idx d, truncateFinset E F alpha = if alpha ∈ E then coeffSkappa F alpha else 0 := by
    intro alpha
    have hsum :
        truncateFinset E F alpha =
          (∑ beta ∈ E, Finsupp.single beta (coeffSkappa F beta)) alpha := by rfl
    rw [hsum]
    by_cases h : alpha ∈ E
    · simp [h, Finsupp.single_apply]
    · simp [h, Finsupp.single_apply]
  have hsupp : (truncateFinset E F).support ⊆ E := by
    intro alpha halpha
    simp_all
  change
    (Real.sqrt (Finset.sum (truncateFinset E F).support
      (fun alpha => ‖truncateFinset E F alpha‖ ^ 2))) ^ 2 =
      Finset.sum E (fun alpha => ‖coeffSkappa F alpha‖ ^ 2)
  rw [Real.sq_sqrt]
  · calc
      Finset.sum (truncateFinset E F).support
          (fun alpha => ‖truncateFinset E F alpha‖ ^ 2)
          = Finset.sum E (fun alpha => ‖truncateFinset E F alpha‖ ^ 2) := by
            exact Finset.sum_subset hsupp fun alpha _E hsupport => by
              simp_all
      _ = Finset.sum E (fun alpha => ‖coeffSkappa F alpha‖ ^ 2) := by
            simp_all
  · positivity

private theorem phi1D_eq_oneDimPhi
    (k n : Nat) (z : ℂ) :
    phi1D k n z = Hermite1DimdLEAN.oneDimPhi k n z := by
  unfold phi1D complexHermite Hermite1DimdLEAN.oneDimPhi
  congr 1
  · simp [one_div, mul_comm]
  · rw [Nat.min_comm k n]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj' : j ≤ min n k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjn : j ≤ n := le_trans hj' (Nat.min_le_left _ _)
    have hfac_ne : (Nat.factorial (n - j) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - j)
    have hfactor : (Nat.factorial j : ℂ) * (Nat.choose n j : ℂ) =
        (Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) := by
      apply mul_right_cancel₀ hfac_ne
      calc
        ((Nat.factorial j : ℂ) * (Nat.choose n j : ℂ)) * (Nat.factorial (n - j) : ℂ)
            = (Nat.choose n j : ℂ) * (Nat.factorial j : ℂ) * (Nat.factorial (n - j) : ℂ) := by ring
        _ = (Nat.factorial n : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
        _ = ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
              (Nat.factorial (n - j) : ℂ) := by field_simp [hfac_ne]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      congrArg
        (fun x : ℂ => ((-1 : ℂ) ^ j) * x * (Nat.choose k j : ℂ) * z ^ (n - j) * (star z) ^ (k - j))
        hfactor

private theorem Phi_eq_PhiKappaAlpha
    {d : Nat} (kappa alpha : MultiIndex d) (z : Cd d) :
    Phi kappa alpha z = Hermite1DimdLEAN.PhiKappaAlpha kappa alpha z := by
  unfold Phi Hermite1DimdLEAN.PhiKappaAlpha
  refine Finset.prod_congr rfl ?_
  intro q hq
  exact phi1D_eq_oneDimPhi (kappa q) (alpha q) (z q)

private lemma oneDimPhi_phaseLaw
    (k n : Nat) (t : ℝ) (z : ℂ) :
    Hermite1DimdLEAN.oneDimPhi k n (Complex.exp (Complex.I * t) * z) =
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
        Hermite1DimdLEAN.oneDimPhi k n z := by
  obtain ⟨radial, hradial⟩ := Hermite1DimdLEAN.oneVariableAngularFactorization k n
  have hz : ((‖z‖ : ℂ) * Complex.exp (Complex.I * z.arg)) = z := by
    simp [mul_comm Complex.I (z.arg : ℂ), Complex.norm_mul_exp_arg_mul_I z]
  have hrot :
      Complex.exp (Complex.I * t) * z =
        ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
    calc
      Complex.exp (Complex.I * t) * z =
          Complex.exp (Complex.I * t) * ((‖z‖ : ℂ) * Complex.exp (Complex.I * z.arg)) := by rw [hz]
      _ = ((‖z‖ : ℂ) * Complex.exp (Complex.I * t)) * Complex.exp (Complex.I * z.arg) := by ring_nf
      _ = (‖z‖ : ℂ) * (Complex.exp (Complex.I * t) * Complex.exp (Complex.I * z.arg)) := by
            rw [mul_assoc]
      _ = ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
            rw [← Complex.exp_add]
            congr 1
            ring_nf
  have hleft :
      Hermite1DimdLEAN.oneDimPhi k n ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa using hradial ‖z‖ (t + z.arg)
  have hright :
      Hermite1DimdLEAN.oneDimPhi k n z =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa [hz] using hradial ‖z‖ z.arg
  have hexp :
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
          Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) := by
    rw [show Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) =
        Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * t)) +
          Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) by ring_nf]
    rw [Complex.exp_add]
  calc
    Hermite1DimdLEAN.oneDimPhi k n (Complex.exp (Complex.I * t) * z) =
        Hermite1DimdLEAN.oneDimPhi k n
          ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by rw [hrot]
    _ = Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := hleft
    _ = Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
          Hermite1DimdLEAN.oneDimPhi k n z := by
          rw [hexp, hright]
          ring_nf

theorem Phi_rotate_one_exp
    {d : Nat} (kappa alpha : MultiIndex d) (q0 : Fin d) (t : ℝ) (z : Cd d) :
    Phi kappa alpha (Function.update z q0 (Complex.exp (Complex.I * t) * z q0)) =
      Complex.exp (Complex.I * (((alpha q0 : ℤ) - (kappa q0 : ℤ) : ℂ) * t)) *
        Phi kappa alpha z := by
  classical
  rw [Phi_eq_PhiKappaAlpha, Phi_eq_PhiKappaAlpha]
  unfold Hermite1DimdLEAN.PhiKappaAlpha
  have hupdate :
      (fun q : Fin d =>
        Hermite1DimdLEAN.oneDimPhi (kappa q) (alpha q)
          (Function.update z q0 (Complex.exp (Complex.I * t) * z q0) q)) =
        Function.update
          (fun q : Fin d => Hermite1DimdLEAN.oneDimPhi (kappa q) (alpha q) (z q))
          q0
          (Hermite1DimdLEAN.oneDimPhi (kappa q0) (alpha q0)
            (Complex.exp (Complex.I * t) * z q0)) := by
    funext q
    by_cases hq : q = q0
    · simp_all
    · simp [Function.update, hq]
  rw [hupdate, Finset.prod_update_of_mem (s := Finset.univ) (i := q0) (by simp), oneDimPhi_phaseLaw]
  conv_rhs =>
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (s := Finset.univ) (i := q0) (by simp)]
  ring_nf

private lemma fourier_mk_eq_exp
    (n : ℤ) (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : Circle) : ℂ) =
      Complex.exp (Complex.I * (n : ℂ) * θ) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem Phi_rotateCoord_circle_phase
    {d : Nat} (kappa alpha : MultiIndex d) (q0 : Fin d)
    (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      Phi kappa alpha
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
    (fourier ((alpha q0 : Nat) : Int) x : ℂ) *
      Phi kappa alpha z := by
  induction x using Quotient.inductionOn with
  | h θ =>
      rw [fourier_mk_eq_exp ((kappa q0 : Nat) : Int) θ,
        fourier_mk_eq_exp ((alpha q0 : Nat) : Int) θ,
        fourier_mk_eq_exp (1 : Int) θ]
      have hone :
        Complex.exp (Complex.I * ((1 : ℤ) : ℂ) * θ) =
            Complex.exp (Complex.I * θ) := by
        simp_all
      rw [hone, Phi_rotate_one_exp]
      have hphase :
          Complex.exp (Complex.I * (((kappa q0 : Nat) : Int) : ℂ) * θ) *
              (Complex.exp
                (Complex.I * (((alpha q0 : ℤ) - (kappa q0 : ℤ) : ℂ) * θ)) *
                Phi kappa alpha z) =
            Complex.exp (Complex.I * (((alpha q0 : Nat) : Int) : ℂ) * θ) *
              Phi kappa alpha z := by
        rw [← mul_assoc, ← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
      exact hphase

theorem evalPkappa_rotateCoord_circle_phase_sum
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (F : Pkappa d kappa) (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      evalPkappa kappa F
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
      ∑ alpha ∈ F.support,
        F alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
  classical
  unfold evalPkappa
  rw [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  have hphase :=
    Phi_rotateCoord_circle_phase
      (kappa := kappa) (alpha := alpha) (q0 := q0) x z
  have hchar : circleChar (alpha q0) x = (fourier ((alpha q0 : Nat) : Int) x : ℂ) :=
    circleChar_eq_fourier_nat (alpha q0) x
  calc
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
        (F alpha *
          Phi kappa alpha
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)))
      = F alpha *
          ((fourier ((kappa q0 : Nat) : Int) x : ℂ) *
            Phi kappa alpha
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) := by ring_nf
    _ = F alpha * ((fourier ((alpha q0 : Nat) : Int) x : ℂ) * Phi kappa alpha z) := by rw [hphase]
    _ = F alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
          rw [hchar]
          ring_nf

theorem toFun_ofPkappa
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    toFun kappa (ofPkappa kappa F) = evalPkappa kappa F := by
  ext z
  rw [toFun, evalPkappa, Finsupp.sum]
  have hzero :
      ∀ alpha ∉ F.support,
        coeffSkappa (ofPkappa kappa F) alpha * Phi kappa alpha z = 0 := by
    intro alpha halpha
    simp [coeffSkappa, ofPkappa, Finsupp.notMem_support_iff.mp halpha]
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [coeffSkappa, ofPkappa]

theorem summable_skappa_eval_mul_of_phi_sq
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (z : Cd d)
    (hPhi : Summable (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2)) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha * Phi kappa alpha z) := by
  have hU : Summable (fun alpha : Idx d => ‖coeffSkappa U alpha‖ ^ 2) := by
    simpa [coeffSkappa] using U.summable_norm_sq
  refine Summable.of_norm_bounded
    (g := fun alpha : Idx d =>
      (‖coeffSkappa U alpha‖ ^ 2 + ‖Phi kappa alpha z‖ ^ 2) / 2)
    ((hU.add hPhi).div_const 2) ?_
  intro alpha
  have hmul :
      ‖coeffSkappa U alpha * Phi kappa alpha z‖ <=
        ‖coeffSkappa U alpha‖ * ‖Phi kappa alpha z‖ :=
    norm_mul_le _ _
  have hsq :
      ‖coeffSkappa U alpha‖ * ‖Phi kappa alpha z‖ <=
        (‖coeffSkappa U alpha‖ ^ 2 + ‖Phi kappa alpha z‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖coeffSkappa U alpha‖ - ‖Phi kappa alpha z‖)]
  exact le_trans hmul hsq

theorem box_subset_box
    {d : Nat} {J K : MultiIndex d} (hJK : J ≤ K) :
    box J ⊆ box K := by
  intro alpha halpha
  rw [box, Fintype.mem_piFinset] at halpha ⊢
  intro q
  have hq := halpha q
  rw [Finset.mem_range] at hq ⊢
  exact Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp hq) (hJK q))

theorem finite_subset_box
    {d : Nat} (E : Finset (Idx d)) :
    ∃ J : MultiIndex d, E ⊆ box J := by
  refine ⟨fun q => Finset.sup E (fun alpha : Idx d => alpha q), ?_⟩
  intro alpha halpha
  rw [box, Fintype.mem_piFinset]
  intro q
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact Finset.le_sup (s := E) (f := fun beta : Idx d => beta q) halpha

theorem tendsto_box_atTop
    {d : Nat} :
    Filter.Tendsto (fun J : MultiIndex d => box J) Filter.atTop Filter.atTop := by
  refine (show Monotone (fun J : MultiIndex d => box J) from ?_).tendsto_atTop_finset ?_
  · intro J K hJK
    exact box_subset_box hJK
  · intro alpha
    refine ⟨alpha, ?_⟩
    rw [box, Fintype.mem_piFinset]
    simp_all

/-!
## Representative bridge stubs

These are the `Skappa` realization facts needed by the phase-space exact
modulus recovery file.  They are declaration-shaped stubs for the
locally-uniform/L2 representative package described in the tensor-basis

-/

/-- `partialSum`: partial Sum. -/
def partialSum
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (J : MultiIndex d) :
    Cd d -> ℂ :=
  fun z => Finset.sum (box J) fun alpha => coeffSkappa U alpha * Phi kappa alpha z

/-- `evalPkappaL2`: eval Pkappa L2. -/
def evalPkappaL2 {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    L2Tensor d :=
  toL2 kappa (ofPkappa kappa F)

/-- `PhiL2`: Phi L2. -/
def PhiL2 {d : Nat} (kappa : MultiIndex d) (alpha : Idx d) : L2Tensor d :=
  evalPkappaL2 kappa (Finsupp.single alpha 1)

/-- `BoxPartialSumsLocallyUniformTo`: Box Partial Sums Locally Uniform To. -/
def BoxPartialSumsLocallyUniformTo
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (f : Cd d -> ℂ) : Prop :=
  TendstoLocallyUniformly (fun J : MultiIndex d => partialSum kappa U J) f Filter.atTop

/-- `BoxPartialSumsLocallyUniformCauchy`: Box Partial Sums Locally Uniform Cauchy. -/
def BoxPartialSumsLocallyUniformCauchy
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) : Prop :=
  (∀ K : Set (Cd d), IsCompact K ->
    UniformCauchySeqOn (fun J : MultiIndex d => partialSum kappa U J) Filter.atTop K) ∧
  BoxPartialSumsLocallyUniformTo kappa U (toFun kappa U)

/-- `IsTensorL2Rep`: Is Tensor L2 Rep. -/
def IsTensorL2Rep {d : Nat} (F : L2Tensor d) (f : Cd d -> ℂ) : Prop :=
  ∃ hf_mem : MeasureTheory.MemLp f 2 (gammaD d), hf_mem.toLp f = F

/-- `L2BoxPartialSumsTendTo`: L2 Box Partial Sums Tend To. -/
def L2BoxPartialSumsTendTo
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (F : L2Tensor d) : Prop :=
  Filter.Tendsto (fun J : MultiIndex d => evalPkappaL2 kappa (truncateFinset (box J) U))
    Filter.atTop (nhds F) ∧
  IsTensorL2Rep F (toFun kappa U)

theorem continuous_Phi
    {d : Nat} (kappa alpha : MultiIndex d) :
    Continuous (Phi kappa alpha) := by
  unfold Phi phi1D complexHermite
  continuity

theorem continuous_evalPkappa
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Continuous (evalPkappa kappa F) := by
  unfold evalPkappa
  refine continuous_finsetSum _ ?_
  intro alpha halpha
  exact continuous_const.mul (continuous_Phi kappa alpha)

theorem evalPkappa_truncateFinset
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (E : Finset (Idx d)) :
    evalPkappa kappa (truncateFinset E U) =
      fun z : Cd d => ∑ alpha ∈ E, coeffSkappa U alpha * Phi kappa alpha z := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      ext z
      simp [truncateFinset, evalPkappa]
  | insert alpha E hnot hE =>
      ext z
      have hE' :
          Finsupp.sum (∑ beta ∈ E, Finsupp.single beta (coeffSkappa U beta))
              (fun beta c => c * Phi kappa beta z) =
            ∑ beta ∈ E, coeffSkappa U beta * Phi kappa beta z := by
        simpa [truncateFinset, evalPkappa] using congrFun hE z
      rw [show truncateFinset (insert alpha E) U =
          Finsupp.single alpha (coeffSkappa U alpha) +
            (∑ beta ∈ E, Finsupp.single beta (coeffSkappa U beta)) by
        simp [truncateFinset, Finset.sum_insert hnot]]
      rw [congrFun
        (evalPkappa_add hd kappa (Finsupp.single alpha (coeffSkappa U alpha))
          (∑ beta ∈ E, Finsupp.single beta (coeffSkappa U beta))) z]
      rw [Finset.sum_insert hnot]
      simp [evalPkappa, hE']

private def phiMajorant (k n : Nat) (R : ℝ) : ℝ :=
  ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
    Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))

theorem partialSum_continuous
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (J : MultiIndex d) :
    Continuous (partialSum kappa U J) := by
  let _ := hd
  unfold partialSum
  refine continuous_finsetSum _ ?_
  intro alpha halpha
  exact continuous_const.mul (continuous_Phi kappa alpha)

theorem continuous_limit_of_locallyUniform_boxPartialSums
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    {f : Cd d -> ℂ}
    (hlim : BoxPartialSumsLocallyUniformTo kappa U f) :
    Continuous f := by
  let _ := hd
  exact hlim.continuous <| Filter.Frequently.of_forall fun J =>
    partialSum_continuous hd kappa U J

theorem toL2_eq_of_toFun_eq
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d} {U V : Skappa d kappa}
    (h : ∀ z, toFun kappa U z = toFun kappa V z) :
    toL2 kappa U = toL2 kappa V := by
  let _ := hd
  have hfun : toFun kappa U = toFun kappa V := funext h
  unfold toL2
  rw [hfun]

theorem skappa_ext_of_coeff_eq
    {d : Nat} {kappa : MultiIndex d} {U V : Skappa d kappa}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = coeffSkappa V alpha) :
    U = V := by
  cases U
  cases V
  simp only [coeffSkappa] at hcoeff
  congr
  funext alpha
  exact hcoeff alpha

theorem toFun_smul_complex
    {d : Nat} (kappa : MultiIndex d) (w : ℂ) (U : Skappa d kappa) :
    toFun kappa (w • U) = fun z => w * toFun kappa U z := by
  funext z
  calc
    (∑' alpha : Idx d, (w • U).coeff alpha * Phi kappa alpha z) =
        ∑' alpha : Idx d, w * (U.coeff alpha * Phi kappa alpha z) :=
          tsum_congr fun alpha => mul_assoc w (U.coeff alpha) (Phi kappa alpha z)
    _ = w * ∑' alpha : Idx d, U.coeff alpha * Phi kappa alpha z := by rw [tsum_mul_left]

end DimdPolyLEAN
