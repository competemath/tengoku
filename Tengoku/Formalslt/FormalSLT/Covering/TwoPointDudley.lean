import Tengoku.Formalslt.FormalSLT.Covering.FiniteSubGaussianChaining
import Tengoku.Formalslt.FormalSLT.Rademacher.Massart

/-!
# Two-point finite dyadic-net Dudley example

This module instantiates `FiniteDyadicNetSequence` on a second metric index
family, the two-point discrete space. Its purpose is API pressure: the
dyadic-net sequence abstraction is used outside the unit interval.

The result remains finite-scale. It does not assert a continuous Dudley
integral, total boundedness, separability, or a measurable supremum over an
arbitrary class.
-/

namespace FormalSLT.Covering.TwoPointDudley

open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.FiniteSubGaussianChaining.FiniteSubGaussianProcess
open FormalSLT.Rademacher.FiniteSample
open scoped BigOperators

noncomputable section

/-- The second metric index family used to exercise the generic dyadic-net
sequence API. -/
abbrev TwoPoint : Type := Bool

/-- Discrete metric on the two-point index family. -/
def twoPointDist (s t : TwoPoint) : ℝ :=
  if s = t then 0 else 1

/--
@isnad1 id=le.0h2v.s4.dbfd1fda809d from=translated src=- shape=5ffe46ab vocab=f208a5e3
-/
theorem twoPointDist_nonneg (s t : TwoPoint) : 0 ≤ twoPointDist s t := by
  by_cases h : s = t <;> simp [twoPointDist, h]

/--
@isnad1 id=eq.0h2v.s3.58ac6a01be22 from=translated src=- shape=ab795eaa vocab=7667280b
-/
theorem twoPointDist_symm (s t : TwoPoint) :
    twoPointDist s t = twoPointDist t s := by
  cases s <;> cases t <;> norm_num [twoPointDist]

/--
@isnad1 id=le.0h3v.s4.1d9dd4cd8afa from=translated src=- shape=5968a5f3 vocab=57910c6e
-/
theorem twoPointDist_triangle (x y z : TwoPoint) :
    twoPointDist x z ≤ twoPointDist x y + twoPointDist y z := by
  cases x <;> cases y <;> cases z <;> norm_num [twoPointDist]

/-- A one-coordinate Rademacher process on the two-point index family. -/
def twoPointRademacherValue (ω : Bool) (t : TwoPoint) : ℝ :=
  if t then signOfBool ω else 0

private theorem twoPointRademacherValue_le_one (ω : Bool) (t : TwoPoint) :
    twoPointRademacherValue ω t ≤ 1 := by
  cases ω <;> cases t <;> norm_num [twoPointRademacherValue, signOfBool]

/--
@isnad1 id=le.0h3v.s7.9fc9bc0cf6c6 from=translated src=- shape=602b67c9 vocab=5eab1d35
-/
theorem twoPoint_rademacher_mgf_bound (s t : TwoPoint) (lam : ℝ) :
    finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
        (fun ω => Real.exp
          (lam * (twoPointRademacherValue ω t - twoPointRademacherValue ω s))) ≤
      Real.exp (lam ^ 2 * (1 : ℝ) * twoPointDist s t ^ 2 / 2) := by
  cases s <;> cases t
  · norm_num [finiteExpectation, twoPointRademacherValue, twoPointDist]
  · calc
      finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
          (fun ω => Real.exp
            (lam * (twoPointRademacherValue ω true -
              twoPointRademacherValue ω false)))
          = (∑ b : Bool, Real.exp (lam * signOfBool b * (1 : ℝ))) / 2 := by
              simp [finiteExpectation, twoPointRademacherValue]
              ring
      _ ≤ Real.exp (lam ^ 2 * (1 : ℝ) ^ 2 / 2) := by
              rw [FormalSLT.Rademacher.Massart.avg_exp_sign]
              exact FormalSLT.Rademacher.Massart.cosh_le_exp_sq_half lam 1
      _ = Real.exp (lam ^ 2 * (1 : ℝ) * twoPointDist false true ^ 2 / 2) := by
              norm_num [twoPointDist]
  · calc
      finiteExpectation (fun _ : Bool => (1 : ℝ) / 2)
          (fun ω => Real.exp
            (lam * (twoPointRademacherValue ω false -
              twoPointRademacherValue ω true)))
          = (∑ b : Bool, Real.exp (lam * signOfBool b * (-1 : ℝ))) / 2 := by
              simp [finiteExpectation, twoPointRademacherValue]
              ring
      _ ≤ Real.exp (lam ^ 2 * (-1 : ℝ) ^ 2 / 2) := by
              rw [FormalSLT.Rademacher.Massart.avg_exp_sign]
              exact FormalSLT.Rademacher.Massart.cosh_le_exp_sq_half lam (-1)
      _ = Real.exp (lam ^ 2 * (1 : ℝ) * twoPointDist true false ^ 2 / 2) := by
              norm_num [twoPointDist]
  · norm_num [finiteExpectation, twoPointRademacherValue, twoPointDist]

/-- The two-point Rademacher process packaged as a finite sub-Gaussian
process. -/
def twoPointRademacherProcess : FiniteSubGaussianProcess Bool TwoPoint where
  weight := fun _ => (1 : ℝ) / 2
  weight_nonneg := by intro ω; norm_num
  weight_sum_one := by norm_num [Fintype.sum_bool]
  X := twoPointRademacherValue
  dist := twoPointDist
  dist_nonneg := twoPointDist_nonneg
  varianceProxy := 1
  varianceProxy_nonneg := by norm_num
  mgf_increment := twoPoint_rademacher_mgf_bound

/-- Full two-point net at dyadic level `j`. The centers are both points; the
positive radius is chosen to fit the generic dyadic radius interface. -/
def twoPointDyadicNet (j : ℕ) : FiniteNet TwoPoint Bool where
  dist := twoPointDist
  dist_nonneg := twoPointDist_nonneg
  center := id
  project := id
  radius := (1 : ℝ) / (2 : ℝ) ^ (j + 2)
  radius_nonneg := by positivity
  covers := by
    intro t
    cases t <;> simp [twoPointDist]

def twoPointDyadicCoverCount (_j : ℕ) : ℕ := 4

/--
@isnad1 id=eq.0h1v.s4.47f7fc636e27 from=translated src=- shape=3d1b0112 vocab=1b9589c5
-/
theorem twoPointDyadicNet_dist (j : ℕ) :
    (twoPointDyadicNet j).dist = twoPointRademacherProcess.dist := by
  rfl

/--
@isnad1 id=lt.0h1v.s5.0d33a3802146 from=translated src=- shape=25b052d0 vocab=74571843
-/
theorem twoPointDyadicNet_radius_pos (j : ℕ) :
    0 < (twoPointDyadicNet j).radius + (twoPointDyadicNet (j + 1)).radius := by
  simp [twoPointDyadicNet]
  positivity

/--
@isnad1 id=le.0h1v.s6.6644f2e60c78 from=translated src=- shape=c18e13a8 vocab=7375e91a
-/
theorem twoPointDyadicNet_radius_geometric (j : ℕ) :
    (twoPointDyadicNet j).radius + (twoPointDyadicNet (j + 1)).radius ≤
      (1 : ℝ) / (2 : ℝ) ^ j := by
  have hpow_pos : 0 < (2 : ℝ) ^ j := by positivity
  change
    (1 : ℝ) / (2 : ℝ) ^ (j + 2) +
        (1 : ℝ) / (2 : ℝ) ^ ((j + 1) + 2) ≤
      (1 : ℝ) / (2 : ℝ) ^ j
  rw [show (j + 1) + 2 = j + 3 by
    rw [Nat.add_assoc]]
  have hscaled :
      (1 : ℝ) / (2 : ℝ) ^ (j + 2) +
          (1 : ℝ) / (2 : ℝ) ^ (j + 3) =
        (3 : ℝ) / (8 * (2 : ℝ) ^ j) := by
    field_simp [hpow_pos.ne']
    ring
  rw [hscaled]
  have hmul : (3 : ℝ) ≤ 8 := by norm_num
  have hden_pos : 0 < (8 : ℝ) * (2 : ℝ) ^ j := by positivity
  calc
    (3 : ℝ) / (8 * (2 : ℝ) ^ j)
        ≤ 8 / (8 * (2 : ℝ) ^ j) :=
          div_le_div_of_nonneg_right hmul hden_pos.le
    _ = (1 : ℝ) / (2 : ℝ) ^ j := by
          field_simp [hpow_pos.ne']

/--
@isnad1 id=lt.0h1v.s5.c50e28f4b576 from=translated src=- shape=238233b4 vocab=c1ffb9ba
-/
theorem twoPointDyadicNet_pair_card_gt_one (j : ℕ) :
    1 < Fintype.card
      (FiniteNet.ProjectionPair (twoPointDyadicNet j) (twoPointDyadicNet (j + 1))) := by
  let p0 : FiniteNet.ProjectionPair (twoPointDyadicNet j) (twoPointDyadicNet (j + 1)) :=
    FiniteNet.projectionPairOf (twoPointDyadicNet j) (twoPointDyadicNet (j + 1)) false
  let p1 : FiniteNet.ProjectionPair (twoPointDyadicNet j) (twoPointDyadicNet (j + 1)) :=
    FiniteNet.projectionPairOf (twoPointDyadicNet j) (twoPointDyadicNet (j + 1)) true
  refine Fintype.one_lt_card_iff.mpr ⟨p0, p1, ?_⟩
  intro hp
  have hfst : p0.1.1 = p1.1.1 := congrArg (fun p => p.1.1) hp
  norm_num [p0, p1, FiniteNet.projectionPairOf, twoPointDyadicNet] at hfst

/--
@isnad1 id=eq.0h1v.s3.8f65ab04693c from=translated src=- shape=b2519bca vocab=2661c669
-/
theorem twoPointDyadicNet_coveringNumber (j : ℕ) :
    (twoPointDyadicNet j).coveringNumber = 2 := by
  simp [FiniteNet.coveringNumber]

/--
@isnad1 id=le.0h1v.s5.2de97fa84d8e from=translated src=- shape=31807e71 vocab=a5014a50
-/
theorem twoPointDyadicNet_coverCount_le (j : ℕ) :
    (twoPointDyadicNet j).coveringNumber *
        (twoPointDyadicNet (j + 1)).coveringNumber ≤
      twoPointDyadicCoverCount j := by
  simp [twoPointDyadicNet_coveringNumber, twoPointDyadicCoverCount]

/-- The second concrete `FiniteDyadicNetSequence` instantiation, independent of
the unit-interval rounded grid. -/
def twoPointDyadicNetSequence :
    FiniteSubGaussianProcess.FiniteDyadicNetSequence
      twoPointRademacherProcess (fun _j : ℕ => Bool) where
  N := twoPointDyadicNet
  coverCount := twoPointDyadicCoverCount
  radiusScale := 1
  dist_eq := twoPointDyadicNet_dist
  dist_symm := twoPointDist_symm
  dist_triangle := twoPointDist_triangle
  radiusScale_nonneg := by norm_num
  radius_pos := twoPointDyadicNet_radius_pos
  radius_geometric := twoPointDyadicNet_radius_geometric
  pair_card_gt_one := twoPointDyadicNet_pair_card_gt_one
  coverCount_le := twoPointDyadicNet_coverCount_le

private theorem twoPointRademacher_coarse (m : ℕ) :
    finiteExpectation twoPointRademacherProcess.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex (twoPointDyadicNet m) =>
          twoPointRademacherProcess.X ω
            ((twoPointDyadicNet 0).projection
              (FiniteNet.ProjectedIndex.source (twoPointDyadicNet m) u)))) ≤
      (1 : ℝ) := by
  calc
    finiteExpectation twoPointRademacherProcess.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex (twoPointDyadicNet m) =>
          twoPointRademacherProcess.X ω
            ((twoPointDyadicNet 0).projection
              (FiniteNet.ProjectedIndex.source (twoPointDyadicNet m) u))))
        ≤ finiteExpectation twoPointRademacherProcess.weight
            (fun _ω : Bool => (1 : ℝ)) := by
          refine finiteExpectation_mono twoPointRademacherProcess.weight_nonneg ?_
          intro ω
          unfold finiteSup
          exact Finset.sup'_le Finset.univ_nonempty _ fun u _hu =>
            twoPointRademacherValue_le_one ω
              ((twoPointDyadicNet 0).projection
                (FiniteNet.ProjectedIndex.source (twoPointDyadicNet m) u))
    _ = (1 : ℝ) := by
          exact finiteExpectation_const_of_sum_one
            twoPointRademacherProcess.weight 1
            twoPointRademacherProcess.weight_sum_one

/-- Packaged finite-dyadic Dudley instance for the two-point Rademacher
process. -/
def twoPointDudleyInstance :
    FiniteDyadicDudleyInstance twoPointRademacherProcess (fun _j : ℕ => Bool) where
  netSequence := twoPointDyadicNetSequence
  coarseBudget := 1
  variance_pos := by norm_num [twoPointRademacherProcess]
  coarse_bound := twoPointRademacher_coarse

/-- Supremum functional for the two-point Rademacher process. -/
def twoPointRademacherSup (ω : Bool) : ℝ :=
  finiteSup (fun t : TwoPoint => twoPointRademacherProcess.X ω t)

/--
@isnad1 id=le.0h2v.s5.1124fdb5ff36 from=translated src=- shape=7c24464d vocab=2e5aa702
-/
theorem twoPointRademacherSup_le_projectedSup (m : ℕ) (ω : Bool) :
    twoPointRademacherSup ω ≤
      finiteSup
        (fun u : FiniteNet.ProjectedIndex (twoPointDyadicNet m) =>
          twoPointRademacherProcess.X ω ((twoPointDyadicNet m).center u.1)) := by
  unfold twoPointRademacherSup finiteSup
  apply Finset.sup'_le
  intro t _ht
  let u : FiniteNet.ProjectedIndex (twoPointDyadicNet m) := ⟨t, ⟨t, rfl⟩⟩
  have hle :=
    Finset.le_sup'
      (fun u : FiniteNet.ProjectedIndex (twoPointDyadicNet m) =>
        twoPointRademacherProcess.X ω ((twoPointDyadicNet m).center u.1))
      (Finset.mem_univ u)
  simpa [u, twoPointDyadicNet] using hle

/-- Supplied-supremum adapter for the two-point Rademacher process. -/
def twoPointRademacherSupAdapter :
    FiniteDyadicDudleyInstance.SupremumAdapter twoPointDudleyInstance where
  supFunctional := twoPointRademacherSup
  terminalError := 0
  terminal_bound := by
    intro m ω
    convert twoPointRademacherSup_le_projectedSup m ω using 1;
      simp [twoPointDudleyInstance, twoPointDyadicNetSequence]

end

end FormalSLT.Covering.TwoPointDudley
