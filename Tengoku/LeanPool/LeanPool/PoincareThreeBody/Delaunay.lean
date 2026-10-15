/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.Resonance
public import Tengoku

/-!
# Delaunay frequencies and resonant actions

At zero mass the planar rotating Kepler Hamiltonian in Delaunay actions is
`-1 / (2 * I₁²) - I₂`, with frequency `(I₁⁻³, -1)`. Positive rational frequency ratios give an
explicit family of resonant actions.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

/-- The rotating Kepler Hamiltonian in planar Delaunay actions. -/
noncomputable def delaunayHamiltonian (action : ActionSpace) : ℝ :=
  -1 / (2 * (action 0) ^ 2) - action 1

/-- The frequency of the rotating Kepler Hamiltonian. -/
noncomputable def delaunayFrequency (firstAction : ℝ) : ActionSpace :=
  ![1 / firstAction ^ 3, -1]

/-- A positive Delaunay action whose Kepler frequency ratio is the positive rational `q / p`. -/
noncomputable def resonantFirstAction (p q : ℕ) : ℝ :=
  ((p : ℝ) / (q : ℝ)) ^ ((3 : ℝ)⁻¹)

/-- The integer resonance vector, regarded as a real vector. -/
def resonanceVector (p q : ℕ) : ActionSpace :=
  ![(p : ℝ), (q : ℝ)]

/--
@isnad1 id=hasderiv.1h2v.s7.c46659394c2f from=translated src=- shape=085a3292 vocab=9895cf3c
-/
theorem hasDerivAt_delaunayHamiltonian_firstAction {firstAction : ℝ}
    (hfirstAction : firstAction ≠ 0) (secondAction : ℝ) :
    HasDerivAt (fun action ↦ -1 / (2 * action ^ 2) - secondAction)
      (1 / firstAction ^ 3) firstAction := by
  have hsquare := hasDerivAt_pow 2 firstAction
  have hdenominator := hsquare.const_mul 2
  have hinverse := hdenominator.inv
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hfirstAction))
  have hraw := (HasDerivAt.neg hinverse).sub_const secondAction
  apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards [] with action
    simp [div_eq_mul_inv]
  · field_simp [hfirstAction]
    ring

/--
@isnad1 id=hasderiv.0h2v.s6.881d1356aec0 from=translated src=- shape=3a6e9c7b vocab=9895cf3c
-/
theorem hasDerivAt_delaunayHamiltonian_secondAction (firstAction secondAction : ℝ) :
    HasDerivAt (fun action ↦ -1 / (2 * firstAction ^ 2) - action) (-1) secondAction := by
  have hraw := (hasDerivAt_const secondAction (-1 / (2 * firstAction ^ 2))).sub
    (hasDerivAt_id secondAction)
  apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards [] with action
  rfl

/--
@isnad1 id=eq.1h2v.s7.1daad8807685 from=translated src=- shape=f751d683 vocab=f75f9491
-/
theorem deriv_delaunayHamiltonian_firstAction {firstAction : ℝ}
    (hfirstAction : firstAction ≠ 0) (secondAction : ℝ) :
    deriv (fun action ↦ -1 / (2 * action ^ 2) - secondAction) firstAction =
      1 / firstAction ^ 3 :=
  (hasDerivAt_delaunayHamiltonian_firstAction hfirstAction secondAction).deriv

/--
@isnad1 id=eq.0h2v.s6.9d91453233a3 from=translated src=- shape=d2d9fe27 vocab=f75f9491
-/
theorem deriv_delaunayHamiltonian_secondAction (firstAction secondAction : ℝ) :
    deriv (fun action ↦ -1 / (2 * firstAction ^ 2) - action) secondAction = -1 :=
  (hasDerivAt_delaunayHamiltonian_secondAction firstAction secondAction).deriv

/-- The displayed Kepler frequency is the coordinate gradient of the Delaunay Hamiltonian.
@isnad1 id=eq.1h2v.s7.54e165f89875 from=translated src=- shape=faaf7ed5 vocab=3672dbd4
-/
theorem delaunayFrequency_eq_coordinateDerivatives {firstAction : ℝ}
    (hfirstAction : firstAction ≠ 0) (secondAction : ℝ) :
    delaunayFrequency firstAction =
      ![deriv (fun action ↦ delaunayHamiltonian ![action, secondAction]) firstAction,
        deriv (fun action ↦ delaunayHamiltonian ![firstAction, action]) secondAction] := by
  funext i
  fin_cases i
  · change 1 / firstAction ^ 3 =
      deriv (fun action ↦ -1 / (2 * action ^ 2) - secondAction) firstAction
    exact (deriv_delaunayHamiltonian_firstAction hfirstAction secondAction).symm
  · change (-1 : ℝ) =
      deriv (fun action ↦ -1 / (2 * firstAction ^ 2) - action) secondAction
    exact (deriv_delaunayHamiltonian_secondAction firstAction secondAction).symm

/--
@isnad1 id=lt.2h2v.s5.dac4eb829611 from=translated src=- shape=e8b7e832 vocab=14beccc6
-/
lemma resonantFirstAction_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    0 < resonantFirstAction p q := by
  exact Real.rpow_pos_of_pos (div_pos (by positivity) (by positivity)) _

/--
@isnad1 id=eq.2h2v.s5.f88f3797a5d9 from=translated src=- shape=d8375aa5 vocab=ee646126
-/
lemma resonantFirstAction_cube {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    resonantFirstAction p q ^ 3 = (p : ℝ) / (q : ℝ) := by
  apply Real.rpow_inv_natCast_pow
  · exact (div_pos (by positivity) (by positivity)).le
  · norm_num

/--
@isnad1 id=ne.1h2v.s5.b3909197aa78 from=translated src=- shape=8106d9e7 vocab=99d24e1f
-/
lemma resonanceVector_ne_zero {p q : ℕ} (hp : 0 < p) : resonanceVector p q ≠ 0 := by
  intro hzero
  have hcoordinate : (p : ℝ) = 0 := by
    simpa only [resonanceVector, Matrix.cons_val_zero, Pi.zero_apply] using congrFun hzero 0
  exact (Nat.cast_ne_zero.mpr hp.ne') hcoordinate

/-- Every pair of positive natural numbers determines an exact Kepler resonance.
@isnad1 id=eq.2h2v.s5.768849b25214 from=translated src=- shape=70d13e69 vocab=4157cf9e
-/
theorem resonantFirstAction_is_resonant {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    dot (resonanceVector p q) (delaunayFrequency (resonantFirstAction p q)) = 0 := by
  have hpReal : (p : ℝ) ≠ 0 := by positivity
  have hqReal : (q : ℝ) ≠ 0 := by positivity
  rw [dot_eq]
  simp only [resonanceVector, delaunayFrequency, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_neg, mul_one]
  rw [resonantFirstAction_cube hp hq]
  field_simp
  ring

/-- Positive rational Kepler resonances occur in every positive open interval.
@isnad1 id=ex.2h2v.s6.fb1039419899 from=translated src=- shape=5f266964 vocab=14beccc6
-/
theorem exists_resonantFirstAction_between {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      a < resonantFirstAction p q ∧ resonantFirstAction p q < b := by
  have hcubes : a ^ 3 < b ^ 3 := (show Odd 3 by decide).pow_lt_pow.mpr hab
  obtain ⟨r, har, hrb⟩ := exists_rat_btwn hcubes
  have hrposReal : (0 : ℝ) < (r : ℝ) := lt_trans (by positivity) har
  have hrpos : (0 : ℚ) < r := by exact_mod_cast hrposReal
  let p := r.num.natAbs
  let q := r.den
  have hnumPos : 0 < r.num := Rat.num_pos.mpr hrpos
  have hp : 0 < p := Int.natAbs_pos.mpr hnumPos.ne'
  have hq : 0 < q := r.pos
  have hnumCast : (p : ℝ) = (r.num : ℝ) := by
    norm_cast
    exact Int.natAbs_of_nonneg hnumPos.le
  have hratio : (p : ℝ) / (q : ℝ) = (r : ℝ) := by
    rw [hnumCast, Rat.cast_def]
  have hcube : resonantFirstAction p q ^ 3 = (r : ℝ) :=
    (resonantFirstAction_cube hp hq).trans hratio
  refine ⟨p, q, hp, hq, ?_, ?_⟩
  · apply (show Odd 3 by decide).pow_lt_pow.mp
    rwa [hcube]
  · apply (show Odd 3 by decide).pow_lt_pow.mp
    rwa [hcube]

/-- The positive first Delaunay action axis. -/
abbrev PositiveAction := Set.Ioi (0 : ℝ)

/-- The positive actions whose Kepler frequency is irrational. -/
def irrationalFrequencyPositiveActions : Set PositiveAction :=
  {action | Irrational (1 / action.1 ^ 3)}

/-- Actions with irrational Kepler frequency occur in every positive open interval.
@isnad1 id=ex.2h2v.s6.bf06ca2da25e from=translated src=- shape=9de5d363 vocab=d9992d9b
-/
theorem exists_irrationalFrequencyAction_between {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ∃ action : ℝ, a < action ∧ action < b ∧
      Irrational (1 / action ^ 3) := by
  have hb : 0 < b := ha.trans hab
  have hacube : 0 < a ^ 3 := pow_pos ha 3
  have hbcube : 0 < b ^ 3 := pow_pos hb 3
  have hfrequencyInterval : 1 / b ^ 3 < 1 / a ^ 3 := by
    exact one_div_lt_one_div_of_lt hacube (by
      exact (show Odd 3 by decide).pow_lt_pow.mpr hab)
  obtain ⟨frequency, hirrational, hfrequencyLower, hfrequencyUpper⟩ :=
    exists_irrational_btwn hfrequencyInterval
  have hfrequency : 0 < frequency :=
    (by positivity : 0 < 1 / b ^ 3).trans hfrequencyLower
  let action : ℝ := (1 / frequency) ^ ((3 : ℝ)⁻¹)
  have hactionCube : action ^ 3 = 1 / frequency := by
    dsimp only [action]
    exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num)
  have haCubeLt : a ^ 3 < action ^ 3 := by
    rw [hactionCube]
    apply (lt_div_iff₀ hfrequency).2
    have := (lt_div_iff₀ hacube).1 hfrequencyUpper
    simpa [mul_comm] using this
  have hcubeLtB : action ^ 3 < b ^ 3 := by
    rw [hactionCube]
    apply (div_lt_iff₀ hfrequency).2
    have := (div_lt_iff₀ hbcube).1 hfrequencyLower
    simpa [mul_comm] using this
  have haAction : a < action := (show Odd 3 by decide).pow_lt_pow.mp haCubeLt
  have hactionB : action < b := (show Odd 3 by decide).pow_lt_pow.mp hcubeLtB
  refine ⟨action, haAction, hactionB, ?_⟩
  have hfrequencyIdentity : 1 / action ^ 3 = frequency := by
    rw [hactionCube]
    field_simp
  rwa [hfrequencyIdentity]

/-- Positive actions with irrational Kepler frequency form a dense set.
@isnad1 id=dense.0h0v.s4.a5bab8d04458 from=translated src=- shape=a05c23ef vocab=f80bf86a
-/
theorem irrationalFrequencyPositiveActions_dense :
    Dense irrationalFrequencyPositiveActions := by
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨action, ha, hb, hirrational⟩ :=
    exists_irrationalFrequencyAction_between a.2 (show a.1 < b.1 from hab)
  let positiveAction : PositiveAction := ⟨action, a.2.trans ha⟩
  exact ⟨positiveAction, hirrational, ha, hb⟩

/-- The positive actions with a rational Kepler frequency ratio. -/
def resonantPositiveActions : Set PositiveAction :=
  {x | ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ x.1 = resonantFirstAction p q}

/--
@isnad1 id=dense.0h0v.s4.24b2c813de81 from=translated src=- shape=a05c23ef vocab=84d786ea
-/
theorem resonantPositiveActions_dense : Dense resonantPositiveActions := by
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨p, q, hp, hq, ha, hb⟩ :=
    exists_resonantFirstAction_between a.2 (show a.1 < b.1 from hab)
  let c : PositiveAction := ⟨resonantFirstAction p q, resonantFirstAction_pos hp hq⟩
  refine ⟨c, ?_, ha, hb⟩
  exact ⟨p, q, hp, hq, rfl⟩

/--
@isnad1 id=continuo.0h0v.s6.dc57a88425f6 from=translated src=- shape=18cf3eb5 vocab=5d526e2a
-/
theorem continuous_delaunayFrequencyOnPositive :
    Continuous (fun action : PositiveAction ↦ delaunayFrequency action.1) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun action : PositiveAction ↦ 1 / action.1 ^ 3)
    apply ((continuous_subtype_val.pow 3).inv₀ fun action ↦
      pow_ne_zero 3 (ne_of_gt action.2)).congr
    intro action
    simp [one_div]
  · change Continuous (fun _ : PositiveAction ↦ (-1 : ℝ))
    exact continuous_const

/-- Orthogonality at every rational Kepler resonance forces dependence at every positive action.
@isnad1 id=not.2h2v.s7.4e586ee8e863 from=translated src=- shape=0342e020 vocab=c675e899
-/
theorem delaunayDenseResonance_obstruction {differential : PositiveAction → ActionSpace}
    (hdifferential : Continuous differential)
    (hresonant : ∀ {p q : ℕ} (hp : 0 < p) (hq : 0 < q),
      dot (resonanceVector p q)
        (differential ⟨resonantFirstAction p q, resonantFirstAction_pos hp hq⟩) = 0)
    (action : PositiveAction) :
    ¬LinearIndependent ℝ ![delaunayFrequency action.1, differential action] := by
  apply denseResonance_obstruction resonantPositiveActions_dense
    continuous_delaunayFrequencyOnPositive hdifferential
  intro resonant hresonantAction
  rcases hresonantAction with ⟨p, q, hp, hq, heq⟩
  have hsubtype : resonant =
      ⟨resonantFirstAction p q, resonantFirstAction_pos hp hq⟩ := Subtype.ext heq
  subst resonant
  exact wedge_eq_zero_of_resonance (resonanceVector_ne_zero hp)
    (resonantFirstAction_is_resonant hp hq) (hresonant hp hq)

/-- The first homological equation and nonvanishing perturbing modes at all rational resonances
exclude an independent leading integral throughout the positive Delaunay action axis.
@isnad1 id=not.3h4v.s8.d23eb72be230 from=translated src=- shape=ac7e7d2b vocab=4d3a9c3c
-/
theorem delaunayHomological_obstruction {differential : PositiveAction → ActionSpace}
    (hdifferential : Continuous differential) (correction perturbation : ℕ → ℕ → ℝ)
    (hperturbation : ∀ p q, 0 < p → 0 < q → perturbation p q ≠ 0)
    (hequation : ∀ p q (hp : 0 < p) (hq : 0 < q),
      dot (resonanceVector p q) (delaunayFrequency (resonantFirstAction p q)) *
          correction p q +
        dot (resonanceVector p q)
            (differential
              ⟨resonantFirstAction p q, resonantFirstAction_pos hp hq⟩) *
          perturbation p q = 0)
    (action : PositiveAction) :
    ¬LinearIndependent ℝ ![delaunayFrequency action.1, differential action] := by
  apply delaunayDenseResonance_obstruction hdifferential
  intro p q hp hq
  have h := hequation p q hp hq
  rw [resonantFirstAction_is_resonant hp hq, zero_mul, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_right (hperturbation p q hp hq)

/-- The abstract linear-algebra obstruction at every positive rational Kepler resonance.
@isnad1 id=not.3h3v.s6.7934b9e6b898 from=translated src=- shape=7174f4fe vocab=f0bdf40b
-/
theorem rationalKeplerResonance_obstruction {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {differential : ActionSpace} (hdifferential :
      dot (resonanceVector p q) differential = 0) :
    ¬LinearIndependent ℝ
      ![delaunayFrequency (resonantFirstAction p q), differential] :=
  not_linearIndependent_of_common_resonance (resonanceVector_ne_zero hp)
    (resonantFirstAction_is_resonant hp hq) hdifferential

end LeanPool.PoincareThreeBody
