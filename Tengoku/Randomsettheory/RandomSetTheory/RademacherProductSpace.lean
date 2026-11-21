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

/--
@isnad1 id=measurab.0h0v.s2.91d0ada78847 from=translated src=- shape=54c8eceb vocab=5c412f04
-/
theorem measurable_canonicalRademacherSign :
    Measurable canonicalRademacherSign := by
  fun_prop

/--
@isnad1 id=eq.0h0v.s3.acfe965ed0d4 from=translated src=- shape=b0ae1d2b vocab=1b524e5e
-/
@[simp]
theorem canonicalRademacherSign_true :
    canonicalRademacherSign true = 1 := rfl

/--
@isnad1 id=eq.0h0v.s3.4aa6dfdedb85 from=translated src=- shape=f7285ee8 vocab=2124372d
-/
@[simp]
theorem canonicalRademacherSign_false :
    canonicalRademacherSign false = -1 := rfl

/--
@isnad1 id=or.0h1v.s4.8cf4728b0f0c from=translated src=- shape=af53c325 vocab=e8b10711
-/
theorem canonicalRademacherSign_eq_one_or_neg_one (b : Bool) :
    canonicalRademacherSign b = 1 ∨ canonicalRademacherSign b = -1 := by
  cases b <;> simp

/--
@isnad1 id=eq.0h0v.s4.98798e0ec857 from=translated src=- shape=a2f93b9d vocab=5c827314
-/
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

/--
@isnad1 id=measurab.0h2v.s4.9e0494dbebb4 from=translated src=- shape=cc4c7d09 vocab=1fb0230a
-/
theorem measurable_canonicalRademacherCoordinate
    {n : Nat} (i : Fin n) :
    Measurable (canonicalRademacherCoordinate i) := by
  exact measurable_canonicalRademacherSign.comp (measurable_pi_apply i)

/--
@isnad1 id=or.0h3v.s5.e7ee3513eb7b from=translated src=- shape=41d422f1 vocab=f3590c70
-/
theorem canonicalRademacherCoordinate_eq_one_or_neg_one
    {n : Nat} (i : Fin n) (eta : CanonicalRademacherSpace n) :
    canonicalRademacherCoordinate i eta = 1 ∨
      canonicalRademacherCoordinate i eta = -1 :=
  canonicalRademacherSign_eq_one_or_neg_one (eta i)

/-- The canonical coordinate signs are mutually independent.
@isnad1 id=iindepfu.0h1v.s5.416fff1f506e from=translated src=- shape=2d0afe5b vocab=45f18752
-/
theorem iIndepFun_canonicalRademacherCoordinate (n : Nat) :
    iIndepFun (fun i : Fin n => canonicalRademacherCoordinate i)
      (canonicalRademacherMeasure n) := by
  exact iIndepFun_pi
    (μ := fun _ : Fin n => rademacherBoolMeasure)
    (X := fun _ : Fin n => canonicalRademacherSign)
    (fun _ => measurable_canonicalRademacherSign.aemeasurable)

/-- Every canonical coordinate has expectation zero.
@isnad1 id=eq.0h2v.s5.d3d6f7883477 from=translated src=- shape=5d297a0e vocab=3464b886
-/
theorem integral_canonicalRademacherCoordinate_eq_zero
    {n : Nat} (i : Fin n) :
    (∫ eta, canonicalRademacherCoordinate i eta
      ∂canonicalRademacherMeasure n) = 0 := by
  unfold canonicalRademacherCoordinate canonicalRademacherMeasure
  rw [integral_comp_eval
    measurable_canonicalRademacherSign.aestronglyMeasurable]
  exact integral_canonicalRademacherSign_eq_zero

/-- Each coordinate is a Rademacher variable in the reusable abstract sense
of `FiniteSymmetrization`.
@isnad1 id=isradema.0h2v.s4.3a149e3e069b from=translated src=- shape=e2baf582 vocab=17316a11
-/
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
