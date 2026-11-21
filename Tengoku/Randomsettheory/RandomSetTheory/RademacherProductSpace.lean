/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.MeasureTheory.Integral.Pi
import Tengoku.Seed.Probability.Distributions.Uniform
import Tengoku.Seed.Probability.ProbabilityMassFunction.Integrals
import Tengoku.Randomsettheory.RandomSetTheory.FiniteSymmetrization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A canonical finite product of Rademacher signs

This file supplies an actual probability space carrying any prescribed
finite family of independent Rademacher variables.  The base space is the
uniform law on `Bool`; the product space is `Fin n -> Bool`, and booleans are
mapped to the real signs `+1` and `-1`.

The construction removes the need for empirical-process applications to
postulate the existence of an auxiliary sign space.
-/

open MeasureTheory

noncomputable section

namespace ProbabilityTheory

/-- The uniform probability measure on the two booleans.-/
def rademacherBoolMeasure : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure rademacherBoolMeasure := by
  unfold rademacherBoolMeasure
  infer_instance

/-- The real sign associated with a boolean.-/
def canonicalRademacherSign (b : Bool) : Real :=
  if b then 1 else -1

theorem measurable_canonicalRademacherSign :
    Measurable canonicalRademacherSign := by
  fun_prop

@[simp]
theorem canonicalRademacherSign_true :
    canonicalRademacherSign true = 1 := rfl

@[simp]
theorem canonicalRademacherSign_false :
    canonicalRademacherSign false = -1 := rfl

theorem canonicalRademacherSign_eq_one_or_neg_one (b : Bool) :
    canonicalRademacherSign b = 1 ∨ canonicalRademacherSign b = -1 := by
  cases b <;> simp

theorem integral_canonicalRademacherSign_eq_zero :
    (∫ b, canonicalRademacherSign b ∂rademacherBoolMeasure) = 0 := by
  unfold rademacherBoolMeasure
  rw [PMF.integral_eq_sum]
  simp [canonicalRademacherSign, PMF.uniformOfFintype_apply]

/-- The canonical space carrying `n` independent signs.-/
abbrev CanonicalRademacherSpace (n : Nat) := Fin n -> Bool

/-- Product of the uniform boolean laws.-/
def canonicalRademacherMeasure (n : Nat) :
    Measure (CanonicalRademacherSpace n) :=
  Measure.pi (fun _ : Fin n => rademacherBoolMeasure)

/-- The `i`-th coordinate sign on the canonical product space.-/
def canonicalRademacherCoordinate {n : Nat} (i : Fin n)
    (eta : CanonicalRademacherSpace n) : Real :=
  canonicalRademacherSign (eta i)

theorem measurable_canonicalRademacherCoordinate
    {n : Nat} (i : Fin n) :
    Measurable (canonicalRademacherCoordinate i) := by
  exact measurable_canonicalRademacherSign.comp (measurable_pi_apply i)

theorem canonicalRademacherCoordinate_eq_one_or_neg_one
    {n : Nat} (i : Fin n) (eta : CanonicalRademacherSpace n) :
    canonicalRademacherCoordinate i eta = 1 ∨
      canonicalRademacherCoordinate i eta = -1 :=
  canonicalRademacherSign_eq_one_or_neg_one (eta i)

/-- The canonical coordinate signs are mutually independent.-/
theorem iIndepFun_canonicalRademacherCoordinate (n : Nat) :
    iIndepFun (fun i : Fin n => canonicalRademacherCoordinate i)
      (canonicalRademacherMeasure n) := by
  exact iIndepFun_pi
    (μ := fun _ : Fin n => rademacherBoolMeasure)
    (X := fun _ : Fin n => canonicalRademacherSign)
    (fun _ => measurable_canonicalRademacherSign.aemeasurable)

/-- Every canonical coordinate has expectation zero.-/
theorem integral_canonicalRademacherCoordinate_eq_zero
    {n : Nat} (i : Fin n) :
    (∫ eta, canonicalRademacherCoordinate i eta
      ∂canonicalRademacherMeasure n) = 0 := by
  unfold canonicalRademacherCoordinate canonicalRademacherMeasure
  rw [integral_comp_eval
    measurable_canonicalRademacherSign.aestronglyMeasurable]
  exact integral_canonicalRademacherSign_eq_zero

/-- Each coordinate is a Rademacher variable in the reusable abstract sense
of `FiniteSymmetrization`.-/
theorem isRademacher_canonicalRademacherCoordinate
    {n : Nat} (i : Fin n) :
    IsRademacher (canonicalRademacherCoordinate i)
      (canonicalRademacherMeasure n) := by
  refine {
    aemeasurable :=
      (measurable_canonicalRademacherCoordinate i).aemeasurable
    ae_eq_one_or_neg_one := ae_of_all _ fun eta =>
      canonicalRademacherCoordinate_eq_one_or_neg_one i eta
    integral_eq_zero := integral_canonicalRademacherCoordinate_eq_zero i }

end ProbabilityTheory
