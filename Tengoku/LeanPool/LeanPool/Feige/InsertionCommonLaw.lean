/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.TwoPoint
public import Tengoku.LeanPool.LeanPool.Feige.SignedExpLaw
public import Tengoku.LeanPool.LeanPool.Feige.TransferProbability23
public import Tengoku.LeanPool.LeanPool.Feige.InsertionCommonDensity
public import Tengoku
import Tengoku.LeanPool.LeanPool.Feige.NNRealExponentialLaw

/-!
# Signed-sum laws along a Boolean insertion edge

The event defining `twoPointKFinset` is rewritten as nonnegativity of the
corresponding signed exponential sum.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Feige

noncomputable section

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The signed exponential statistic at Boolean state `S`. -/
def stateSignedSum (γ β : ι → ℝ) (S : Finset ι)
    (e : Option ι → NNReal) : ℝ :=
  (e none : ℝ) +
    ∑ i, if i ∈ S then -(β i * (e (some i) : ℝ))
      else γ i * (e (some i) : ℝ)

theorem measurable_stateSignedSum (γ β : ι → ℝ) (S : Finset ι) :
    Measurable (stateSignedSum γ β S) := by
  unfold stateSignedSum
  apply Measurable.add
  · exact (measurable_pi_apply none).coe_nnreal_real
  · apply Finset.measurable_fun_sum
    intro i hi
    by_cases hiS : i ∈ S
    · simp only [ite_eq_left hiS]
      fun_prop
    · simp only [ite_eq_right hiS]
      fun_prop

/-- Pushforward law of the signed sum at state `S`. -/
noncomputable def stateLaw (γ β : ι → ℝ) (S : Finset ι) : Measure ℝ :=
  Measure.map (stateSignedSum γ β S) (expProductMeasure ι)

/-- The original event in the definition of `K` is exactly nonnegativity
of the signed sum. -/
theorem kEvent_twoPointVector_eq_stateSignedSum
    (γ β : ι → ℝ) (S : Finset ι) :
    kEvent (twoPointVector γ β (S : Set ι)) =
      stateSignedSum γ β S ⁻¹' Ici 0 := by
  ext e
  simp only [kEvent, mem_ofPred_eq, mem_preimage, mem_Ici]
  have hsum :
      (∑ i, (twoPointVector γ β (S : Set ι) i - 1) *
          (e (some i) : ℝ)) =
        -(∑ i, if i ∈ S then -(β i * (e (some i) : ℝ))
          else γ i * (e (some i) : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiS : i ∈ S
    · simp [twoPointVector, hiS, highValue]
    · simp [twoPointVector, hiS, lowValue]
  rw [hsum]
  unfold stateSignedSum
  change
    -(∑ i, if i ∈ S then -(β i * (e (some i) : ℝ))
      else γ i * (e (some i) : ℝ)) ≤ (e none : ℝ) ↔
    0 ≤ (e none : ℝ) +
      ∑ i, if i ∈ S then -(β i * (e (some i) : ℝ))
        else γ i * (e (some i) : ℝ)
  constructor <;> intro h <;> linarith

/-- `twoPointKFinset` is the nonnegative-tail probability of the actual
signed exponential state law. -/
theorem twoPointKFinset_eq_stateLaw
    (γ β : ι → ℝ) (S : Finset ι) :
    twoPointKFinset γ β S =
      ENNReal.toReal (stateLaw γ β S (Ici 0)) := by
  rw [twoPointKFinset, twoPointK, dirichletK, stateLaw,
    Measure.map_apply (measurable_stateSignedSum γ β S) measurableSet_Ici,
    ← kEvent_twoPointVector_eq_stateSignedSum]
  rfl

/-- The common signed sum obtained by deleting the changed coordinate, on
the original product sample space. -/
def stateCommonSignedSum (γ β : ι → ℝ) (S : Finset ι) (changed : ι)
    (e : Option ι → NNReal) : ℝ :=
  (e none : ℝ) +
    ∑ i ∈ Finset.univ.erase changed,
      if i ∈ S then -(β i * (e (some i) : ℝ))
      else γ i * (e (some i) : ℝ)

theorem measurable_stateCommonSignedSum
    (γ β : ι → ℝ) (S : Finset ι) (changed : ι) :
    Measurable (stateCommonSignedSum γ β S changed) := by
  unfold stateCommonSignedSum
  apply Measurable.add
  · exact (measurable_pi_apply none).coe_nnreal_real
  · apply Finset.measurable_fun_sum
    intro i hi
    by_cases hiS : i ∈ S
    · simp only [ite_eq_left hiS]
      fun_prop
    · simp only [ite_eq_right hiS]
      fun_prop

/-- At the low endpoint, the state sum is the common sum plus the changed
positive exponential. -/
theorem stateSignedSum_eq_common_add
    (γ β : ι → ℝ) (S : Finset ι) (changed : ι)
    (hj : changed ∉ S) (e : Option ι → NNReal) :
    stateSignedSum γ β S e =
      stateCommonSignedSum γ β S changed e +
        γ changed * (e (some changed) : ℝ) := by
  unfold stateSignedSum stateCommonSignedSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ changed)]
  simp only [hj, ite_false]
  ring

/-- At the high endpoint, the changed coordinate contributes the
corresponding negative exponential to the same common sum. -/
theorem stateSignedSum_insert_eq_common_sub
    (γ β : ι → ℝ) (S : Finset ι) (changed : ι)
    (hj : changed ∉ S) (e : Option ι → NNReal) :
    stateSignedSum γ β (insert changed S) e =
      stateCommonSignedSum γ β S changed e -
        β changed * (e (some changed) : ℝ) := by
  unfold stateSignedSum stateCommonSignedSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ changed)]
  have herase :
      ∀ i ∈ Finset.univ.erase changed,
        (if i ∈ insert changed S
          then -(β i * (e (some i) : ℝ))
          else γ i * (e (some i) : ℝ)) =
        (if i ∈ S then -(β i * (e (some i) : ℝ))
          else γ i * (e (some i) : ℝ)) := by
    intro i hi
    have hine : i ≠ changed := (Finset.mem_erase.mp hi).1
    simp [hine]
  rw [Finset.sum_congr rfl herase]
  simp [hj]
  ring

/-- The common law on an insertion edge, constructed as the convolution of
the unchanged signed exponential factors together with the distinguished
rate-one exponential `E₀`. -/
noncomputable def insertionCommonLaw
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) : Measure ℝ :=
  LikelihoodRatio.finiteSignedExpSumMeasure
    (LikelihoodRatio.commonFactors γ β hγ hβ S changed)

/-- The common law has exactly the explicit finite signed-exponential
density used by the TP2 argument. -/
theorem insertionCommonLaw_eq_withDensity
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) :
    insertionCommonLaw γ β hγ hβ S changed =
      volume.withDensity
        (LikelihoodRatio.finiteSignedExpSumDensity
          (LikelihoodRatio.commonFactors γ β hγ hβ S changed)) := by
  exact LikelihoodRatio.finiteSignedExpSumMeasure_eq_withDensity _

/-- Law of the low endpoint obtained by adding the changed coordinate's
positive scaled exponential to the common part. -/
noncomputable def insertionLowEndpointLaw
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) : Measure ℝ :=
  TransferStein.zPlusLaw
    (insertionCommonLaw γ β hγ hβ S changed) (γ changed)

/-- Law of the high endpoint obtained by subtracting the changed
coordinate's scaled exponential from the common part. -/
noncomputable def insertionHighEndpointLaw
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) : Measure ℝ :=
  TransferStein.zMinusLaw
    (insertionCommonLaw γ β hγ hβ S changed) (β changed)

theorem insertionLowEndpointLaw_eq_zPlus
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) :
    insertionLowEndpointLaw γ β hγ hβ S changed =
      TransferStein.zPlusLaw
        (insertionCommonLaw γ β hγ hβ S changed) (γ changed) :=
  rfl

theorem insertionHighEndpointLaw_eq_zMinus
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) :
    insertionHighEndpointLaw γ β hγ hβ S changed =
      TransferStein.zMinusLaw
        (insertionCommonLaw γ β hγ hβ S changed) (β changed) :=
  rfl

/-- The real-valued signed contribution of one coordinate. -/
def signedCoordinate
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (i : ι) (x : NNReal) : ℝ :=
  match (LikelihoodRatio.stateFactor γ β hγ hβ S i).direction with
  | .positive =>
      (LikelihoodRatio.stateFactor γ β hγ hβ S i).scale * (x : ℝ)
  | .negative =>
      -((LikelihoodRatio.stateFactor γ β hγ hβ S i).scale * (x : ℝ))

omit [Fintype ι] in
theorem measurable_signedCoordinate
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (i : ι) :
    Measurable (signedCoordinate γ β hγ hβ S i) := by
  unfold signedCoordinate
  split <;> fun_prop

omit [Fintype ι] in
theorem map_signedCoordinate_nnexpMeasure
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (i : ι) :
    Measure.map (signedCoordinate γ β hγ hβ S i) nnexpMeasure =
      (LikelihoodRatio.stateFactor γ β hγ hβ S i).sourceLaw := by
  rw [LikelihoodRatio.SignedExpFactor.sourceLaw, ← map_nnexpMeasure_coe]
  rw [Measure.map_map]
  · rfl
  · cases h :
      (LikelihoodRatio.stateFactor γ β hγ hβ S i).direction <;> fun_prop
  · exact NNReal.continuous_coe.measurable

/-- The distinguished exponential or a signed coordinate on the product space. -/
def transformedCoordinate
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (o : Option ι) (e : Option ι → NNReal) : ℝ :=
  match o with
  | none => (e none : ℝ)
  | some i => signedCoordinate γ β hγ hβ S i (e (some i))

omit [Fintype ι] in
theorem measurable_transformedCoordinate
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (o : Option ι) :
    Measurable (transformedCoordinate γ β hγ hβ S o) := by
  cases o with
  | none => exact (measurable_pi_apply none).coe_nnreal_real
  | some i =>
      exact (measurable_signedCoordinate γ β hγ hβ S i).comp
        (measurable_pi_apply (some i))

/-- The distinguished index together with the coordinate indices in `T`. -/
def commonIndexSet (T : Finset ι) : Finset (Option ι) :=
  insert none (T.image some)

omit [Fintype ι] in
theorem sum_commonIndexSet
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S T : Finset ι) (e : Option ι → NNReal) :
    (∑ o ∈ commonIndexSet T,
        transformedCoordinate γ β hγ hβ S o e) =
      (e none : ℝ) +
        ∑ i ∈ T, signedCoordinate γ β hγ hβ S i (e (some i)) := by
  unfold commonIndexSet
  rw [Finset.sum_insert (by simp)]
  simp only [transformedCoordinate]
  rw [Finset.sum_image (by
    intro i hi j hj hij
    exact Option.some.inj hij)]

theorem finiteSignedExpSumSourceMeasure_perm
    {Fs Gs : List LikelihoodRatio.SignedExpFactor}
    (h : Fs.Perm Gs) :
    LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs =
      LikelihoodRatio.finiteSignedExpSumSourceMeasure Gs := by
  induction h with
  | nil => rfl
  | cons F h ih =>
      simp only [LikelihoodRatio.finiteSignedExpSumSourceMeasure]
      rw [ih]
  | swap F G Fs =>
      let : SFinite F.sourceLaw := by
        rw [F.sourceLaw_eq_withDensity]
        infer_instance
      let : SFinite G.sourceLaw := by
        rw [G.sourceLaw_eq_withDensity]
        infer_instance
      let : SFinite
          (LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs) := by
        rw [LikelihoodRatio.finiteSignedExpSumSourceMeasure_eq]
        infer_instance
      simp only [LikelihoodRatio.finiteSignedExpSumSourceMeasure]
      calc
        G.sourceLaw ∗
            (F.sourceLaw ∗
              LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs) =
          (G.sourceLaw ∗ F.sourceLaw) ∗
            LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs := by
              rw [Measure.conv_assoc]
        _ = (F.sourceLaw ∗ G.sourceLaw) ∗
            LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs := by
              rw [Measure.conv_comm G.sourceLaw F.sourceLaw]
        _ = F.sourceLaw ∗
            (G.sourceLaw ∗
              LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs) := by
              rw [Measure.conv_assoc]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem zPlusLaw_eq_conv_map_mul
    (ν : Measure ℝ) [SFinite ν] (t : ℝ) :
    TransferStein.zPlusLaw ν t =
      ν ∗ Measure.map (fun x : ℝ ↦ t * x) (expMeasure 1) := by
  unfold TransferStein.zPlusLaw Measure.conv
  calc
    Measure.map (fun p : ℝ × ℝ ↦ p.1 + t * p.2)
        (ν.prod (expMeasure 1)) =
      Measure.map (fun p : ℝ × ℝ ↦ p.1 + p.2)
        (Measure.map (Prod.map id (fun x : ℝ ↦ t * x))
          (ν.prod (expMeasure 1))) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · fun_prop
    _ = Measure.map (fun p : ℝ × ℝ ↦ p.1 + p.2)
        ((Measure.map id ν).prod
          (Measure.map (fun x : ℝ ↦ t * x) (expMeasure 1))) := by
            rw [Measure.map_prod_map ν (expMeasure 1)
              measurable_id (by fun_prop)]
    _ = _ := by rw [Measure.map_id]

theorem zMinusLaw_eq_conv_map_neg_mul
    (ν : Measure ℝ) [SFinite ν] (t : ℝ) :
    TransferStein.zMinusLaw ν t =
      ν ∗ Measure.map (fun x : ℝ ↦ -(t * x)) (expMeasure 1) := by
  unfold TransferStein.zMinusLaw Measure.conv
  calc
    Measure.map (fun p : ℝ × ℝ ↦ p.1 - t * p.2)
        (ν.prod (expMeasure 1)) =
      Measure.map (fun p : ℝ × ℝ ↦ p.1 + p.2)
        (Measure.map (Prod.map id (fun x : ℝ ↦ -(t * x)))
          (ν.prod (expMeasure 1))) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · fun_prop
    _ = Measure.map (fun p : ℝ × ℝ ↦ p.1 + p.2)
        ((Measure.map id ν).prod
          (Measure.map (fun x : ℝ ↦ -(t * x)) (expMeasure 1))) := by
            rw [Measure.map_prod_map ν (expMeasure 1)
              measurable_id (by fun_prop)]
    _ = _ := by rw [Measure.map_id]

end

end Feige
