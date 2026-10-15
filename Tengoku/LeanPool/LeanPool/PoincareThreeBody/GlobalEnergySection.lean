/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.NormalizationClosure
import Tengoku.LeanPool.LeanPool.PoincareThreeBody.Analytic
import Tengoku.LeanPool.LeanPool.PoincareThreeBody.ParameterizedAnalyticDivision
public import Tengoku

/-!
# A global analytic section of the mass-zero energy map

The rotating Kepler Hamiltonian admits a collision-free analytic phase-space section over every
real energy.  This supplies a canonical globally analytic one-variable representative for the
mass-zero coefficient of any jointly analytic family.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

/-- A small positive radius chosen so that the remaining kinetic radicand is positive for every
real energy. -/
noncomputable def globalEnergyRadius (energy : ℝ) : ℝ :=
  1 / (energy ^ 2 + 2)

/--
@isnad1 id=lt.0h1v.s3.9eb5dcc84aba from=translated src=- shape=8a62b088 vocab=ed6b4f6f
-/
theorem globalEnergyRadius_pos (energy : ℝ) : 0 < globalEnergyRadius energy := by
  unfold globalEnergyRadius
  positivity

/--
@isnad1 id=eq.0h1v.s5.411a545193e3 from=translated src=- shape=cd6ec0a4 vocab=17b405e8
-/
theorem one_div_globalEnergyRadius (energy : ℝ) :
    1 / globalEnergyRadius energy = energy ^ 2 + 2 := by
  unfold globalEnergyRadius
  field_simp

/-- The squared shifted momentum needed to realize the prescribed energy. -/
noncomputable def globalEnergyRadicand (energy : ℝ) : ℝ :=
  2 * (energy + globalEnergyRadius energy ^ 2 / 2 +
    1 / globalEnergyRadius energy)

/--
@isnad1 id=lt.0h1v.s3.8ea93f5895b7 from=translated src=- shape=8a62b088 vocab=c299a4f5
-/
theorem globalEnergyRadicand_pos (energy : ℝ) :
    0 < globalEnergyRadicand energy := by
  rw [globalEnergyRadicand, one_div_globalEnergyRadius]
  have hsquare : 0 ≤ (energy + 1 / 2 : ℝ) ^ 2 := sq_nonneg _
  have hradius : 0 ≤ globalEnergyRadius energy ^ 2 := sq_nonneg _
  nlinarith

/-- Positive shifted momentum along the global section. -/
noncomputable def globalEnergySpeed (energy : ℝ) : ℝ :=
  Real.sqrt (globalEnergyRadicand energy)

/--
@isnad1 id=eq.0h1v.s4.2d2f55249bfe from=translated src=- shape=43966446 vocab=79fe6b65
-/
theorem globalEnergySpeed_sq (energy : ℝ) :
    globalEnergySpeed energy ^ 2 = globalEnergyRadicand energy := by
  exact Real.sq_sqrt (globalEnergyRadicand_pos energy).le

/-- An explicit collision-free phase point with mass-zero Hamiltonian equal to `energy`. -/
noncomputable def globalEnergySection (energy : ℝ) : PhaseSpace :=
  ![0, globalEnergyRadius energy,
    -globalEnergySpeed energy - globalEnergyRadius energy, 0]

/--
@isnad1 id=mem.0h1v.s4.baf9e23e558d from=translated src=- shape=a3eb77dd vocab=61e4c3c6
-/
theorem globalEnergySection_collisionFree (energy : ℝ) :
    (0, globalEnergySection energy) ∈ collisionFree := by
  constructor
  · simp only [firstPrimaryDistanceSq, globalEnergySection,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    positivity
  · simp only [secondPrimaryDistanceSq, globalEnergySection,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    intro hzero
    norm_num at hzero
    exact (globalEnergyRadius_pos energy).ne' hzero

/-- The explicit section is a right inverse of the mass-zero Hamiltonian.
@isnad1 id=eq.0h1v.s3.bc05a88d8c79 from=translated src=- shape=608b0a34 vocab=38e91f2e
-/
theorem hamiltonian_zero_globalEnergySection (energy : ℝ) :
    hamiltonian 0 (globalEnergySection energy) = energy := by
  let radius := globalEnergyRadius energy
  let speed := globalEnergySpeed energy
  have hradius : 0 < radius := globalEnergyRadius_pos energy
  have hinverse : 1 / radius = energy ^ 2 + 2 :=
    one_div_globalEnergyRadius energy
  have hspeed : speed ^ 2 =
      2 * (energy + radius ^ 2 / 2 + 1 / radius) := by
    exact globalEnergySpeed_sq energy
  have hsqrtRadius : Real.sqrt (radius ^ 2) = radius := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hradius]
  unfold hamiltonian potential globalEnergySection
  change ((-speed - radius) ^ 2 + 0 ^ 2) / 2 +
      (-speed - radius) * radius - 0 * 0 -
        (0 / Real.sqrt ((0 - 1 + 0) ^ 2 + radius ^ 2) +
          (1 - 0) / Real.sqrt ((0 + 0) ^ 2 + radius ^ 2)) = energy
  norm_num only [zero_pow, zero_add, zero_mul, one_mul, sub_zero, zero_div]
  rw [hsqrtRadius]
  rw [hinverse] at hspeed ⊢
  nlinarith

/--
@isnad1 id=eq.0h0v.s5.c70f4d2b56f0 from=translated src=- shape=a644ce02 vocab=a3dc4913
-/
@[simp] theorem globalEnergyRadius_neg_two :
    globalEnergyRadius (-2) = (1 / 6 : ℝ) := by
  norm_num [globalEnergyRadius]

/--
@isnad1 id=eq.0h0v.s5.3f77a36d638a from=translated src=- shape=a644ce02 vocab=da7c7fc9
-/
@[simp] theorem globalEnergyRadicand_neg_two :
    globalEnergyRadicand (-2) = (289 / 36 : ℝ) := by
  norm_num [globalEnergyRadicand, globalEnergyRadius]

/--
@isnad1 id=eq.0h0v.s5.6c14b257c9c5 from=translated src=- shape=a644ce02 vocab=f92931e4
-/
@[simp] theorem globalEnergySpeed_neg_two :
    globalEnergySpeed (-2) = (17 / 6 : ℝ) := by
  rw [globalEnergySpeed, globalEnergyRadicand_neg_two]
  have hnonneg : (0 : ℝ) ≤ 17 / 6 := by norm_num
  rw [show (289 / 36 : ℝ) = (17 / 6) ^ 2 by norm_num,
    Real.sqrt_sq hnonneg]

/-- A rational phase-space anchor for the global section.
@isnad1 id=eq.0h0v.s6.5cb94784a500 from=translated src=- shape=4e581feb vocab=3979a700
-/
theorem globalEnergySection_neg_two :
    globalEnergySection (-2) = ![(0 : ℝ), 1 / 6, -3, 0] := by
  funext coordinate
  fin_cases coordinate <;>
    norm_num [globalEnergySection]

/--
@isnad1 id=eq.0h0v.s5.99c67687423e from=translated src=- shape=1aa535ae vocab=7ce08325
-/
theorem cartesianAngularAction_globalEnergySection_neg_two :
    cartesianAngularAction (globalEnergySection (-2)) = (1 / 2 : ℝ) := by
  rw [globalEnergySection_neg_two]
  simp only [cartesianAngularAction, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num

/--
@isnad1 id=analytic.0h1v.s5.21c361533cc5 from=translated src=- shape=1111aaa7 vocab=687b5be9
-/
theorem analyticAt_globalEnergyRadius (energy : ℝ) :
    AnalyticAt ℝ globalEnergyRadius energy := by
  unfold globalEnergyRadius
  exact analyticAt_const.div ((analyticAt_id.pow 2).add analyticAt_const)
    (by positivity)

/--
@isnad1 id=analytic.0h1v.s5.eef1adda0f23 from=translated src=- shape=1111aaa7 vocab=f7bed4bf
-/
theorem analyticAt_globalEnergyRadicand (energy : ℝ) :
    AnalyticAt ℝ globalEnergyRadicand energy := by
  unfold globalEnergyRadicand
  have hradius := analyticAt_globalEnergyRadius energy
  have hone : AnalyticAt ℝ (fun _ : ℝ ↦ (1 : ℝ)) energy := analyticAt_const
  have htwo : AnalyticAt ℝ (fun _ : ℝ ↦ (2 : ℝ)) energy := analyticAt_const
  apply (htwo.mul
    (analyticAt_id.add (((hradius.pow 2).div_const (c := (2 : ℝ))).add
      (hone.div hradius (globalEnergyRadius_pos energy).ne')))).congr
  filter_upwards [] with candidate
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Pi.div_apply, id_eq]
  ring

/--
@isnad1 id=analytic.0h1v.s5.c5d08dceed81 from=translated src=- shape=1111aaa7 vocab=e4866ae3
-/
theorem analyticAt_globalEnergySpeed (energy : ℝ) :
    AnalyticAt ℝ globalEnergySpeed energy := by
  unfold globalEnergySpeed
  exact (analyticAt_sqrt_of_pos (globalEnergyRadicand_pos energy)).comp
    (analyticAt_globalEnergyRadicand energy)

/--
@isnad1 id=analytic.0h1v.s6.5fa44822ae06 from=translated src=- shape=33904196 vocab=9c425d9b
-/
theorem analyticAt_globalEnergySection (energy : ℝ) :
    AnalyticAt ℝ globalEnergySection energy := by
  apply AnalyticAt.pi
  intro coordinate
  fin_cases coordinate
  · exact analyticAt_const
  · exact analyticAt_globalEnergyRadius energy
  · exact (analyticAt_globalEnergySpeed energy).neg.sub
      (analyticAt_globalEnergyRadius energy)
  · exact analyticAt_const

/-- Evaluate the mass-zero coefficient along the global energy section. -/
noncomputable def globalEnergyCoefficient
    (F : ℝ → PhaseSpace → ℝ) (energy : ℝ) : ℝ :=
  F 0 (globalEnergySection energy)

/-- Joint analyticity makes the global energy representative analytic at every real energy.
@isnad1 id=analytic.2h3v.s5.230df86ec4a5 from=translated src=- shape=e3525b5d vocab=363aa291
-/
theorem IsJointlyAnalytic.analyticAt_globalEnergyCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F) (energy : ℝ) :
    AnalyticAt ℝ (globalEnergyCoefficient F) energy := by
  have hdomain : (0, globalEnergySection energy) ∈ parameterDomain δ :=
    ⟨by simpa using hδ, globalEnergySection_collisionFree energy⟩
  have hcurve : AnalyticAt ℝ
      (fun candidateEnergy ↦ ((0 : ℝ), globalEnergySection candidateEnergy)) energy :=
    analyticAt_const.prod (analyticAt_globalEnergySection energy)
  exact (hanalytic (0, globalEnergySection energy) hdomain).comp
    (f := fun candidateEnergy ↦ ((0 : ℝ), globalEnergySection candidateEnergy)) hcurve

/-- Intrinsic form of the classical zeroth-coefficient conclusion: the coefficient at a phase
point equals its value on the canonical section at the same Kepler energy. -/
def GlobalZerothCoefficientFactorization : Prop :=
  ∀ {δ : ℝ} {F : ℝ → PhaseSpace → ℝ},
    0 < δ → IsJointlyAnalytic δ F → IsFirstIntegralFamily δ F →
      ∀ state, (0, state) ∈ collisionFree →
        F 0 state = globalEnergyCoefficient F (hamiltonian 0 state)

/-- Difference between the mass-zero coefficient and its value on the canonical section at the
same Kepler energy. -/
noncomputable def globalEnergyDefect
    (F : ℝ → PhaseSpace → ℝ) (state : PhaseSpace) : ℝ :=
  F 0 state - globalEnergyCoefficient F (hamiltonian 0 state)

/-- The global energy defect is analytic throughout the mass-zero collision-free phase domain.
@isnad1 id=analytic.2h2v.s7.2110a879ef03 from=translated src=- shape=fd9ce210 vocab=73df839b
-/
theorem IsJointlyAnalytic.analyticOnNhd_globalEnergyDefect
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F) :
    AnalyticOnNhd ℝ (globalEnergyDefect F) massZeroCollisionFree := by
  intro state hcollision
  have hdomain : (0, state) ∈ parameterDomain δ :=
    ⟨by simpa using hδ, hcollision⟩
  have hembedding : AnalyticAt ℝ
      (fun candidate : PhaseSpace ↦ ((0 : ℝ), candidate)) state :=
    analyticAt_const.prod analyticAt_id
  have hcandidate : AnalyticAt ℝ (F 0) state :=
    (hanalytic (0, state) hdomain).comp
      (f := fun candidate : PhaseSpace ↦ ((0 : ℝ), candidate)) hembedding
  have hhamiltonian : AnalyticAt ℝ (hamiltonian 0) state :=
    (hamiltonian_analyticAt hcollision).comp
      (f := fun candidate : PhaseSpace ↦ ((0 : ℝ), candidate)) hembedding
  have hcoefficient : AnalyticAt ℝ
      (globalEnergyCoefficient F) (hamiltonian 0 state) :=
    IsJointlyAnalytic.analyticAt_globalEnergyCoefficient hδ hanalytic _
  exact hcandidate.sub (hcoefficient.comp (f := hamiltonian 0) hhamiltonian)

/-- Local version of the classical factorization obligation at the rational elliptic anchor. -/
def LocalZerothCoefficientFactorizationAtAnchor : Prop :=
  ∀ {δ : ℝ} {F : ℝ → PhaseSpace → ℝ},
    0 < δ → IsJointlyAnalytic δ F → IsFirstIntegralFamily δ F →
      ∀ᶠ state in nhds (globalEnergySection (-2)),
        F 0 state = globalEnergyCoefficient F (hamiltonian 0 state)

/-- Analytic continuation turns factorization on the anchor patch into factorization on the full
connected mass-zero collision-free phase domain.
@isnad1 id=iff.0h0v.s1.3ea28e513236 from=translated src=- shape=25b03439 vocab=a82328f2
-/
theorem localZerothCoefficientFactorizationAtAnchor_iff_global :
    LocalZerothCoefficientFactorizationAtAnchor ↔
      GlobalZerothCoefficientFactorization := by
  constructor
  · intro hlocal δ F hδ hanalytic hfirstIntegral state hcollision
    have hdefectAnalytic :=
      IsJointlyAnalytic.analyticOnNhd_globalEnergyDefect hδ hanalytic
    have hbase : globalEnergySection (-2) ∈ massZeroCollisionFree :=
      globalEnergySection_collisionFree (-2)
    have hdefectZero : ∀ᶠ candidate in nhds (globalEnergySection (-2)),
        globalEnergyDefect F candidate = 0 := by
      filter_upwards [hlocal hδ hanalytic hfirstIntegral] with candidate heq
      exact sub_eq_zero.mpr heq
    have hglobal : Set.EqOn (globalEnergyDefect F) 0 massZeroCollisionFree :=
      hdefectAnalytic.eqOn_of_preconnected_of_eventuallyEq
        analyticOnNhd_const isPreconnected_massZeroCollisionFree hbase hdefectZero
    exact sub_eq_zero.mp (hglobal hcollision)
  · intro hglobal δ F hδ hanalytic hfirstIntegral
    have hfirst : ∀ᶠ candidate in nhds (globalEnergySection (-2)),
        firstPrimaryDistanceSq 0 candidate ≠ 0 := by
      have hcontinuous : Continuous (firstPrimaryDistanceSq 0) := by
        unfold firstPrimaryDistanceSq
        fun_prop
      exact hcontinuous.continuousAt.eventually_ne
        (globalEnergySection_collisionFree (-2)).1
    have hsecond : ∀ᶠ candidate in nhds (globalEnergySection (-2)),
        secondPrimaryDistanceSq 0 candidate ≠ 0 := by
      have hcontinuous : Continuous (secondPrimaryDistanceSq 0) := by
        unfold secondPrimaryDistanceSq
        fun_prop
      exact hcontinuous.continuousAt.eventually_ne
        (globalEnergySection_collisionFree (-2)).2
    filter_upwards [hfirst, hsecond] with state hstateFirst hstateSecond
    exact hglobal hδ hanalytic hfirstIntegral state
      ⟨hstateFirst, hstateSecond⟩

/-- The canonical-section formulation is exactly equivalent to the energy-function formulation
used by the normalization induction.
@isnad1 id=iff.0h0v.s1.1cbbb157da22 from=translated src=- shape=25b03439 vocab=57c7be07
-/
theorem globalZerothCoefficientFactorization_iff_classicalPrinciple :
    GlobalZerothCoefficientFactorization ↔ ClassicalZerothCoefficientPrinciple := by
  constructor
  · intro hfactor δ F hδ hanalytic hfirstIntegral
    refine ⟨globalEnergyCoefficient F,
      IsJointlyAnalytic.analyticAt_globalEnergyCoefficient hδ hanalytic,
      hfactor hδ hanalytic hfirstIntegral⟩
  · intro hprinciple δ F hδ hanalytic hfirstIntegral state hcollision
    obtain ⟨energyFunction, _henergy, hcancel⟩ :=
      hprinciple hδ hanalytic hfirstIntegral
    have hsection (energy : ℝ) :
        globalEnergyCoefficient F energy = energyFunction energy := by
      unfold globalEnergyCoefficient
      rw [hcancel (globalEnergySection energy)
        (globalEnergySection_collisionFree energy),
        hamiltonian_zero_globalEnergySection]
    rw [hcancel state hcollision, hsection]

/-- With analytic mass division now proved, the exact challenge is reduced to the intrinsic
classical factorization statement alone.
@isnad1 id=not.1h0v.s5.f66deecf8951 from=translated src=- shape=bdf693e7 vocab=25b3a5b7
-/
theorem nonintegrability_of_globalZerothCoefficientFactorization
    (hfactor : GlobalZerothCoefficientFactorization) :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧
        IsIndependentSomewhere δ F := by
  apply nonintegrability_of_zerothCoefficient_of_massDivision
  · exact globalZerothCoefficientFactorization_iff_classicalPrinciple.mp hfactor
  · exact jointAnalyticMassDivisionPrinciple

end LeanPool.PoincareThreeBody
