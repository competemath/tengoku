/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Tengoku.Formalslt.FormalSLT.StochasticDynamics.TrajectoryRisk

/-!
# Prequential risk on arbitrary measurable state spaces

This file removes the finite-state restriction from the semantic trajectory
layer.  The state space is an arbitrary measurable space, the continuation at
time `n` is an arbitrary Markov kernel selected by the complete prefix, and a
score is required to be jointly strongly measurable in that prefix and the
next state.

For a jointly measurable `[0,1]` score, the observed score is integrable, its
kernel integral is its exact conditional expectation, and the resulting
innovation (or oppositely signed shortfall) is increment-adapted,
conditionally centered, bounded by one, and has conditional second moment at
most `1/4`.  No topology, stationarity, finite-memory assumption, or
PAC--Bayes mixture is used here.

The finite-state declarations in `TrajectoryRisk` remain unchanged.  The
theorems below reuse their definitions and expose the additional measurability
hypothesis needed outside countable spaces.
-/

open Filter Finset Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z : Type*} [MeasurableSpace Z]

/-- The measurability contract needed for a trajectory score on a general
measurable state space.  It is joint in the complete prefix and next state. -/
def JointlyStronglyMeasurableTrajectoryScore
    (score : TrajectoryScore Z) : Prop :=
  ∀ n, StronglyMeasurable
    (fun p : (((i : Finset.Iic n) → Z) × Z) ↦ score n p.1 p.2)

private lemma stronglyMeasurable_piLE_of_prefix_general
    (n : ℕ) (g : ((i : Finset.Iic n) → Z) → ℝ)
    (hg : StronglyMeasurable g) :
    StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ ↦ Z) n]
      (fun x ↦ g (Preorder.frestrictLe n x)) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact hg.comp_measurable (comap_measurable _)

/-- A jointly measurable score observed at step `n` is measurable with
respect to the path through coordinate `n+1`.
@isnad1 id=strongly.1h3v.s6.5710a728c0bb from=translated src=- shape=876580dc vocab=64e9dcba
-/
lemma stronglyMeasurable_observedTrajectoryScore_succ_of_joint
    {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (n : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ ↦ Z) (n + 1)]
      (observedTrajectoryScore score n) := by
  let g : ((i : Finset.Iic (n + 1)) → Z) → ℝ := fun u ↦
    score n
      (Preorder.frestrictLe₂ (π := fun _ : ℕ ↦ Z) (Nat.le_succ n) u)
      (u ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
  have hg0 := (hscore_meas n).comp_measurable
    ((Preorder.measurable_frestrictLe₂
      (X := fun _ : ℕ ↦ Z) (Nat.le_succ n)).prodMk
        (measurable_pi_apply
          ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩))
  have hg : StronglyMeasurable g := by
    convert hg0 using 1
    funext u
    rfl
  have hmeas := stronglyMeasurable_piLE_of_prefix_general (n + 1) g hg
  change StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ ↦ Z) (n + 1)]
    (fun x ↦ score n (Preorder.frestrictLe n x) (x (n + 1)))
  convert hmeas using 1
  funext x
  simp only [g, Preorder.frestrictLe_apply]
  congr 1

/--
@isnad1 id=measurab.1h3v.s5.33e47d954afe from=translated src=- shape=876580dc vocab=65e807a7
-/
lemma measurable_observedTrajectoryScore_of_joint
    {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (n : ℕ) :
    Measurable (observedTrajectoryScore score n) :=
  ((stronglyMeasurable_observedTrajectoryScore_succ_of_joint hscore_meas n).mono
    ((Filtration.piLE (X := fun _ : ℕ ↦ Z)).le (n + 1))).measurable

/--
@isnad1 id=integrab.2h5v.s8.6f60e06dae68 from=translated src=- shape=b6e44eb6 vocab=92716f4e
-/
lemma integrable_observedTrajectoryScore_of_joint
    {kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z}
    [∀ n, IsMarkovKernel (kappa n)] {x0 : Z} {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (hscore : ∀ n u y, score n u y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    Integrable (observedTrajectoryScore score n) (trajectoryMeasure kappa x0) := by
  refine Integrable.of_bound
    (measurable_observedTrajectoryScore_of_joint hscore_meas n).aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (observedTrajectoryScore_mem_Icc hscore n x).1]
    exact (observedTrajectoryScore_mem_Icc hscore n x).2

/-- The continuation integral of a measurable observed score reduces to the
one-step kernel integral selected by the supplied prefix.
@isnad1 id=eq.1h5v.s9.375b646ff427 from=translated src=- shape=6affe1e0 vocab=c9b901fd
-/
lemma integral_observedTrajectoryScore_traj_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)]
    (score : TrajectoryScore Z)
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (n : ℕ) (u : (i : Finset.Iic n) → Z) :
    ∫ x, observedTrajectoryScore score n x
        ∂Kernel.traj (X := fun _ : ℕ ↦ Z) kappa n u =
      ∫ y, score n u y ∂kappa n u := by
  let mu_n : Measure (ℕ → Z) :=
    Kernel.traj (X := fun _ : ℕ ↦ Z) kappa n u
  have hrow : StronglyMeasurable (fun y ↦ score n u y) := by
    simpa only [Function.comp_def] using
      (hscore_meas n).comp_measurable
        (measurable_prodMk_left (x := u))
  calc
    ∫ x, observedTrajectoryScore score n x ∂mu_n =
        ∫ x, observedTrajectoryScore score n
          (Function.updateFinset x (Finset.Iic n) u) ∂mu_n := by
      exact Kernel.integral_traj (X := fun _ : ℕ ↦ Z) u
        (measurable_observedTrajectoryScore_of_joint hscore_meas n).aestronglyMeasurable
    _ = ∫ x, score n u (x (n + 1)) ∂mu_n := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        unfold observedTrajectoryScore
        change score n (Preorder.frestrictLe n
            (Function.updateFinset x (Finset.Iic n) u))
          (Function.updateFinset x (Finset.Iic n) u (n + 1)) =
            score n u (x (n + 1))
        rw [show Preorder.frestrictLe n
            (Function.updateFinset x (Finset.Iic n) u) = u by
          funext i
          simp [Preorder.frestrictLe_apply, Function.updateFinset]]
        simp [Function.updateFinset, Finset.mem_Iic]
    _ = ∫ y, score n u y
          ∂Measure.map (fun x : ℕ → Z ↦ x (n + 1)) mu_n := by
      symm
      exact integral_map
        (measurable_pi_apply (n + 1)).aemeasurable
        hrow.aestronglyMeasurable
    _ = ∫ y, score n u y ∂kappa n u := by
      rw [show Measure.map (fun x : ℕ → Z ↦ x (n + 1)) mu_n = kappa n u by
        exact map_trajectory_next kappa n u]

/-- The kernel-conditional risk is prefix-measurable on an arbitrary
measurable state space.
@isnad1 id=strongly.1h4v.s8.2947bdbb59f9 from=translated src=- shape=76e6ac85 vocab=6c21268a
-/
lemma stronglyMeasurable_conditionalTrajectoryRisk_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)]
    {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (n : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ ↦ Z) n]
      (conditionalTrajectoryRisk kappa score n) := by
  let g : ((i : Finset.Iic n) → Z) → ℝ := fun u ↦
    ∫ y, score n u y ∂kappa n u
  have hg : StronglyMeasurable g := by
    simpa only [g] using
      MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'
        (κ := kappa n) (hscore_meas n)
  change StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ ↦ Z) n]
    (fun x ↦ ∫ y, score n (Preorder.frestrictLe n x) y
      ∂kappa n (Preorder.frestrictLe n x))
  simpa only [g] using
    stronglyMeasurable_piLE_of_prefix_general n g hg

/--
@isnad1 id=mem.2h5v.s8.dfcc9c50e3be from=translated src=- shape=8b77705f vocab=36db270b
-/
lemma conditionalTrajectoryRisk_mem_Icc_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)] {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (hscore : ∀ n u y, score n u y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (x : ℕ → Z) :
    conditionalTrajectoryRisk kappa score n x ∈ Set.Icc (0 : ℝ) 1 := by
  let u := Preorder.frestrictLe n x
  let rowScore : Z → ℝ := fun y ↦ score n u y
  have hrow_meas : StronglyMeasurable rowScore := by
    simpa only [rowScore, Function.comp_def] using
      (hscore_meas n).comp_measurable
        (measurable_prodMk_left (x := u))
  have hrow_int : Integrable rowScore (kappa n u) := by
    refine Integrable.of_bound hrow_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hscore n u y).1]
      exact (hscore n u y).2
  constructor
  · exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun y ↦ (hscore n u y).1)
  · have hle := integral_mono_ae hrow_int (integrable_const (1 : ℝ))
        (Filter.Eventually.of_forall fun y ↦ (hscore n u y).2)
    change (∫ y, rowScore y ∂kappa n u) ≤ 1
    calc
      ∫ y, rowScore y ∂kappa n u ≤ ∫ _ : Z, (1 : ℝ) ∂kappa n u := hle
      _ = 1 := by simp

/--
@isnad1 id=integrab.2h5v.s8.74d6058ee3b5 from=translated src=- shape=ab0b1d18 vocab=0cf4576e
-/
lemma integrable_conditionalTrajectoryRisk_of_joint
    {kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z}
    [∀ n, IsMarkovKernel (kappa n)] {x0 : Z} {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (hscore : ∀ n u y, score n u y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    Integrable (conditionalTrajectoryRisk kappa score n)
      (trajectoryMeasure kappa x0) := by
  have hrisk_meas : StronglyMeasurable
      (conditionalTrajectoryRisk kappa score n) :=
    (stronglyMeasurable_conditionalTrajectoryRisk_of_joint kappa hscore_meas n).mono
      ((Filtration.piLE (X := fun _ : ℕ ↦ Z)).le n)
  refine Integrable.of_bound hrisk_meas.aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (conditionalTrajectoryRisk_mem_Icc_of_joint kappa hscore_meas hscore n x).1]
    exact (conditionalTrajectoryRisk_mem_Icc_of_joint kappa hscore_meas hscore n x).2

/-- Exact conditional expectation for a bounded jointly measurable score on
an arbitrary measurable state space.
@isnad1 id=eventual.2h5v.s8.9fb356229e8d from=translated src=- shape=18c250af vocab=341e2d11
-/
theorem observedTrajectoryScore_condExp_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)] (x0 : Z)
    (score : TrajectoryScore Z)
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (hscore : ∀ n u y, score n u y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    (trajectoryMeasure kappa x0)[observedTrajectoryScore score n |
        Filtration.piLE (X := fun _ : ℕ ↦ Z) n] =ᵐ[trajectoryMeasure kappa x0]
      conditionalTrajectoryRisk kappa score n := by
  have hcond := Kernel.condExp_traj
    (X := fun _ : ℕ ↦ Z) (κ := kappa)
    (a := 0) (b := n) (Nat.zero_le n)
    (integrable_observedTrajectoryScore_of_joint
      (kappa := kappa) (x0 := x0) hscore_meas hscore n)
  unfold trajectoryMeasure
  filter_upwards [hcond] with x hx
  rw [hx, integral_observedTrajectoryScore_traj_of_joint
    kappa score hscore_meas n]
  rfl

/--
@isnad1 id=incremen.1h3v.s8.3e6071cca2cb from=translated src=- shape=31fbfab4 vocab=b7ba4c40
-/
lemma trajectoryRiskInnovation_incrementAdapted_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)]
    {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score) :
    AnytimeValid.IncrementAdapted
      (Filtration.piLE (X := fun _ : ℕ ↦ Z))
      (trajectoryRiskInnovation kappa score) := by
  intro n
  exact (stronglyMeasurable_observedTrajectoryScore_succ_of_joint hscore_meas n).sub
    ((stronglyMeasurable_conditionalTrajectoryRisk_of_joint kappa hscore_meas n).mono
      ((Filtration.piLE (X := fun _ : ℕ ↦ Z)).mono (Nat.le_succ n)))

/--
@isnad1 id=integrab.2h5v.s8.06d4a57feef4 from=translated src=- shape=ab0b1d18 vocab=bbc7f2e1
-/
lemma integrable_trajectoryRiskInnovation_of_joint
    {kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z}
    [∀ n, IsMarkovKernel (kappa n)] {x0 : Z} {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (hscore : ∀ n u y, score n u y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    Integrable (trajectoryRiskInnovation kappa score n)
      (trajectoryMeasure kappa x0) := by
  exact (integrable_observedTrajectoryScore_of_joint
      (kappa := kappa) (x0 := x0) hscore_meas hscore n).sub
    (integrable_conditionalTrajectoryRisk_of_joint
      (kappa := kappa) (x0 := x0) hscore_meas hscore n)

/--
@isnad1 id=le.2h5v.s8.0671fb8b8cc2 from=translated src=- shape=58f0b12d vocab=e6575006
-/
lemma abs_trajectoryRiskInnovation_le_one_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)] {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (hscore : ∀ n u y, score n u y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (x : ℕ → Z) :
    |trajectoryRiskInnovation kappa score n x| ≤ 1 := by
  have hobserved := observedTrajectoryScore_mem_Icc hscore n x
  have hrisk := conditionalTrajectoryRisk_mem_Icc_of_joint
    kappa hscore_meas hscore n x
  rcases hobserved with ⟨hobserved0, hobserved1⟩
  rcases hrisk with ⟨hrisk0, hrisk1⟩
  rw [abs_le]
  unfold trajectoryRiskInnovation
  constructor <;> linarith

/-- The general-state trajectory innovation is conditionally centered.
@isnad1 id=eventual.2h5v.s8.cd57a5020440 from=translated src=- shape=f265b8bb vocab=bc486e9f
-/
theorem trajectoryRiskInnovation_condExp_eq_zero_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)] (x0 : Z)
    {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (hscore : ∀ n u y, score n u y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    (trajectoryMeasure kappa x0)[trajectoryRiskInnovation kappa score n |
        Filtration.piLE (X := fun _ : ℕ ↦ Z) n] =ᵐ[trajectoryMeasure kappa x0] 0 := by
  have hobserved_int := integrable_observedTrajectoryScore_of_joint
    (kappa := kappa) (x0 := x0) hscore_meas hscore n
  have hrisk_int := integrable_conditionalTrajectoryRisk_of_joint
    (kappa := kappa) (x0 := x0) hscore_meas hscore n
  have hsub := condExp_sub hobserved_int hrisk_int
    (Filtration.piLE (X := fun _ : ℕ ↦ Z) n)
  have hsub' :
      (trajectoryMeasure kappa x0)[trajectoryRiskInnovation kappa score n |
          Filtration.piLE (X := fun _ : ℕ ↦ Z) n] =ᵐ[trajectoryMeasure kappa x0]
        (trajectoryMeasure kappa x0)[observedTrajectoryScore score n |
            Filtration.piLE (X := fun _ : ℕ ↦ Z) n] -
          (trajectoryMeasure kappa x0)[conditionalTrajectoryRisk kappa score n |
            Filtration.piLE (X := fun _ : ℕ ↦ Z) n] := by
    rw [show trajectoryRiskInnovation kappa score n =
        observedTrajectoryScore score n - conditionalTrajectoryRisk kappa score n by rfl]
    exact hsub
  have hobserved := observedTrajectoryScore_condExp_of_joint
    kappa x0 score hscore_meas hscore n
  have hrisk :
      (trajectoryMeasure kappa x0)[conditionalTrajectoryRisk kappa score n |
          Filtration.piLE (X := fun _ : ℕ ↦ Z) n] =
      conditionalTrajectoryRisk kappa score n :=
    condExp_of_stronglyMeasurable
      ((Filtration.piLE (X := fun _ : ℕ ↦ Z)).le n)
      (stronglyMeasurable_conditionalTrajectoryRisk_of_joint
        kappa hscore_meas n) hrisk_int
  filter_upwards [hsub', hobserved] with x hsubx hobservedx
  rw [hsubx]
  change (trajectoryMeasure kappa x0)[observedTrajectoryScore score n |
      Filtration.piLE (X := fun _ : ℕ ↦ Z) n] x -
    (trajectoryMeasure kappa x0)[conditionalTrajectoryRisk kappa score n |
      Filtration.piLE (X := fun _ : ℕ ↦ Z) n] x = 0
  rw [hobservedx, hrisk]
  simp

/-- A bounded jointly measurable score retains the sharp `1/4` conditional
second-moment bound on arbitrary measurable state spaces.
@isnad1 id=eventual.2h5v.s8.a50860c424fc from=translated src=- shape=48cb5c4d vocab=45ed5801
-/
theorem trajectoryRiskInnovation_condSecondMoment_le_one_fourth_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)] (x0 : Z)
    {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (hscore : ∀ n u y, score n u y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    (trajectoryMeasure kappa x0)[
        fun x ↦ (trajectoryRiskInnovation kappa score n x) ^ 2 |
        Filtration.piLE (X := fun _ : ℕ ↦ Z) n] ≤ᵐ[trajectoryMeasure kappa x0]
      fun _ ↦ (1 / 4 : ℝ) := by
  let mu := trajectoryMeasure kappa x0
  let filt := Filtration.piLE (X := fun _ : ℕ ↦ Z)
  let loss := observedTrajectoryScore score n
  have hloss_Icc : ∀ᵐ x ∂mu, loss x ∈ Set.Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall fun x ↦ observedTrajectoryScore_mem_Icc hscore n x
  have hloss_memLp : MemLp loss 2 mu :=
    memLp_of_bounded hloss_Icc
      (measurable_observedTrajectoryScore_of_joint hscore_meas n).aestronglyMeasurable 2
  have hloss_cond :
      mu[loss | filt n] =ᵐ[mu] conditionalTrajectoryRisk kappa score n := by
    simpa only [mu, filt, loss] using
      observedTrajectoryScore_condExp_of_joint
        kappa x0 score hscore_meas hscore n
  have hinnovation_eq_condVar :
      mu[fun x ↦ (trajectoryRiskInnovation kappa score n x) ^ 2 | filt n] =ᵐ[mu]
        Var[loss; mu | filt n] := by
    unfold ProbabilityTheory.condVar
    refine condExp_congr_ae ?_
    filter_upwards [hloss_cond] with x hx
    change (loss x - conditionalTrajectoryRisk kappa score n x) ^ 2 =
      (loss x - mu[loss | filt n] x) ^ 2
    rw [hx]
  have hcondVar_formula :=
    condVar_ae_eq_condExp_sq_sub_sq_condExp (filt.le n) hloss_memLp
  have hloss_sq_le : ∀ᵐ x ∂mu, loss x ^ 2 ≤ loss x :=
    hloss_Icc.mono fun x hx ↦ by
      rcases hx with ⟨hx0, hx1⟩
      nlinarith [sq_nonneg (loss x)]
  have hcond_sq_le := condExp_mono (m := filt n) (μ := mu)
    hloss_memLp.integrable_sq
    (integrable_observedTrajectoryScore_of_joint
      (kappa := kappa) (x0 := x0) hscore_meas hscore n)
    hloss_sq_le
  filter_upwards [hinnovation_eq_condVar, hcondVar_formula,
    hcond_sq_le, hloss_cond] with x hinnovation hformula hsq hmean
  rw [hinnovation, hformula]
  change mu[fun x ↦ loss x ^ 2 | filt n] x - (mu[loss | filt n] x) ^ 2 ≤ 1 / 4
  have hrisk := conditionalTrajectoryRisk_mem_Icc_of_joint
    kappa hscore_meas hscore n x
  rw [hmean] at hsq ⊢
  nlinarith [sq_nonneg (conditionalTrajectoryRisk kappa score n x - 1 / 2)]

/-- Conditional risk minus observation.  This is the sign convention used by
upper-confidence risk bounds; its square equals the innovation square. -/
def measurableTrajectoryRiskShortfall
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    (score : TrajectoryScore Z) (n : ℕ) (x : ℕ → Z) : ℝ :=
  conditionalTrajectoryRisk kappa score n x - observedTrajectoryScore score n x

/--
@isnad1 id=eq.0h4v.s7.1274a468c387 from=translated src=- shape=852d9a29 vocab=b2354476
-/
lemma measurableTrajectoryRiskShortfall_eq_neg_innovation
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    (score : TrajectoryScore Z) (n : ℕ) :
    measurableTrajectoryRiskShortfall kappa score n =
      -(trajectoryRiskInnovation kappa score n) := by
  funext x
  change conditionalTrajectoryRisk kappa score n x -
      observedTrajectoryScore score n x =
    -(observedTrajectoryScore score n x -
      conditionalTrajectoryRisk kappa score n x)
  ring

/--
@isnad1 id=incremen.1h3v.s8.38e03f1605fe from=translated src=- shape=31fbfab4 vocab=27bff5cf
-/
lemma measurableTrajectoryRiskShortfall_incrementAdapted_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)]
    {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score) :
    AnytimeValid.IncrementAdapted
      (Filtration.piLE (X := fun _ : ℕ ↦ Z))
      (measurableTrajectoryRiskShortfall kappa score) := by
  intro n
  rw [measurableTrajectoryRiskShortfall_eq_neg_innovation]
  exact (trajectoryRiskInnovation_incrementAdapted_of_joint
    kappa hscore_meas n).neg

/--
@isnad1 id=le.2h5v.s8.1be9090fac39 from=translated src=- shape=58f0b12d vocab=50347b04
-/
lemma abs_measurableTrajectoryRiskShortfall_le_one_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)] {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (hscore : ∀ n u y, score n u y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (x : ℕ → Z) :
    |measurableTrajectoryRiskShortfall kappa score n x| ≤ 1 := by
  rw [measurableTrajectoryRiskShortfall_eq_neg_innovation]
  simp only [Pi.neg_apply, abs_neg]
  exact abs_trajectoryRiskInnovation_le_one_of_joint
    kappa hscore_meas hscore n x

/--
@isnad1 id=eventual.2h5v.s8.4208820afc3b from=translated src=- shape=f265b8bb vocab=5db93d18
-/
theorem measurableTrajectoryRiskShortfall_condExp_eq_zero_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)] (x0 : Z)
    {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (hscore : ∀ n u y, score n u y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    (trajectoryMeasure kappa x0)[measurableTrajectoryRiskShortfall kappa score n |
        Filtration.piLE (X := fun _ : ℕ ↦ Z) n] =ᵐ[trajectoryMeasure kappa x0] 0 := by
  rw [measurableTrajectoryRiskShortfall_eq_neg_innovation]
  filter_upwards [condExp_neg (μ := trajectoryMeasure kappa x0)
      (trajectoryRiskInnovation kappa score n)
      (Filtration.piLE (X := fun _ : ℕ ↦ Z) n),
    trajectoryRiskInnovation_condExp_eq_zero_of_joint
      kappa x0 hscore_meas hscore n] with x hneg hzero
  rw [hneg]
  simp only [Pi.neg_apply, hzero, Pi.zero_apply, neg_zero]

/--
@isnad1 id=eventual.2h5v.s8.09ef1177d4f6 from=translated src=- shape=48cb5c4d vocab=37b80fab
-/
theorem measurableTrajectoryRiskShortfall_condSecondMoment_le_one_fourth_of_joint
    (kappa : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (kappa n)] (x0 : Z)
    {score : TrajectoryScore Z}
    (hscore_meas : JointlyStronglyMeasurableTrajectoryScore score)
    (hscore : ∀ n u y, score n u y ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) :
    (trajectoryMeasure kappa x0)[
        fun x ↦ (measurableTrajectoryRiskShortfall kappa score n x) ^ 2 |
        Filtration.piLE (X := fun _ : ℕ ↦ Z) n] ≤ᵐ[trajectoryMeasure kappa x0]
      fun _ ↦ (1 / 4 : ℝ) := by
  have hsq : (fun x ↦ (measurableTrajectoryRiskShortfall kappa score n x) ^ 2) =
      fun x ↦ (trajectoryRiskInnovation kappa score n x) ^ 2 := by
    funext x
    rw [measurableTrajectoryRiskShortfall_eq_neg_innovation]
    simp
  rw [hsq]
  exact trajectoryRiskInnovation_condSecondMoment_le_one_fourth_of_joint
    kappa x0 hscore_meas hscore n

/-! ## A genuinely nonfinite-state receipt -/

/-- A deterministic real-valued continuation: the next state is the affine
image `(current + 1) / 2` of the latest state in the prefix. -/
def affineRealPrefixKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → ℝ) ℝ :=
  Kernel.deterministic
    (fun u ↦ (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩ + 1) / 2)
    (by fun_prop)

/--
@isnad1 id=ismarkov.0h1v.s6.48f47efb74f5 from=translated src=- shape=a6d8d94c vocab=4fed83a5
-/
instance affineRealPrefixKernel.instIsMarkovKernel (n : ℕ) :
    IsMarkovKernel (affineRealPrefixKernel n) := by
  unfold affineRealPrefixKernel
  infer_instance

/-- Clip a real next-state observation into `[0,1]`. -/
def clippedRealTrajectoryScore : TrajectoryScore ℝ :=
  fun _ _ y ↦ max 0 (min 1 y)

/--
@isnad1 id=jointlys.0h0v.s2.1daa1b1861d3 from=translated src=- shape=25b03439 vocab=1d9284e6
-/
lemma clippedRealTrajectoryScore_jointlyStronglyMeasurable :
    JointlyStronglyMeasurableTrajectoryScore clippedRealTrajectoryScore := by
  intro n
  change StronglyMeasurable
    (fun p : (((i : Finset.Iic n) → ℝ) × ℝ) ↦ max 0 (min 1 p.2))
  exact (continuous_const.max (continuous_const.min continuous_snd)).stronglyMeasurable

/--
@isnad1 id=mem.0h3v.s5.00a97c1bc2c3 from=translated src=- shape=d5f343ff vocab=2ef6e79c
-/
lemma clippedRealTrajectoryScore_mem_Icc
    (n : ℕ) (u : (i : Finset.Iic n) → ℝ) (y : ℝ) :
    clippedRealTrajectoryScore n u y ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left 0 (min 1 y)
  · exact max_le (by norm_num) (min_le_left 1 y)

/-- The general conditional-expectation theorem instantiated on a genuinely
infinite state space.
@isnad1 id=eventual.0h2v.s6.b7d6c5a7b205 from=translated src=- shape=8de7967c vocab=5053e603
-/
theorem clippedRealTrajectoryScore_condExp (x0 : ℝ) (n : ℕ) :
    (trajectoryMeasure affineRealPrefixKernel x0)[
        observedTrajectoryScore clippedRealTrajectoryScore n |
        Filtration.piLE (X := fun _ : ℕ ↦ ℝ) n] =ᵐ[
      trajectoryMeasure affineRealPrefixKernel x0]
      conditionalTrajectoryRisk affineRealPrefixKernel
        clippedRealTrajectoryScore n :=
  observedTrajectoryScore_condExp_of_joint affineRealPrefixKernel x0
    clippedRealTrajectoryScore
    clippedRealTrajectoryScore_jointlyStronglyMeasurable
    clippedRealTrajectoryScore_mem_Icc n

/-- On the zero prefix, the first affine continuation and its clipped risk are
exactly `1/2`.
@isnad1 id=eq.0h0v.s5.51e161483ac9 from=translated src=- shape=a595b9b5 vocab=8309a091
-/
lemma clippedRealTrajectoryRisk_zero_prefix :
    conditionalTrajectoryRisk affineRealPrefixKernel
      clippedRealTrajectoryScore 0 (fun _ ↦ 0) = (1 / 2 : ℝ) := by
  unfold conditionalTrajectoryRisk affineRealPrefixKernel
    clippedRealTrajectoryScore
  rw [Kernel.integral_deterministic (by fun_prop)]
  norm_num

end

end FormalSLT.StochasticDynamics
