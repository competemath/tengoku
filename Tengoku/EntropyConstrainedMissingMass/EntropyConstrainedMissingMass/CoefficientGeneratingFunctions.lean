import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.CoefficientPartialFractions
import Tengoku.Seed.RingTheory.PowerSeries.Inverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Formal power series connecting the finite coefficient representation to the manuscript. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open PowerSeries

def linearFactor (a : ℝ) : PowerSeries ℝ := 1 - C a * X

def homogeneousSeries (x y z : ℝ) : PowerSeries ℝ := mk (homogeneous3 x y z)

/--
@isnad1 id=eq.0h4v.s6.67a11dfd43aa from=translated src=- shape=710bffc4 vocab=d86f5a11
-/
@[simp] theorem coeff_homogeneousSeries (x y z : ℝ) (n : ℕ) :
    coeff n (homogeneousSeries x y z) = homogeneous3 x y z n := coeff_mk _ _

/--
@isnad1 id=eq.0h1v.s5.a3179d8faec1 from=translated src=- shape=c4f3e6af vocab=7a965cb5
-/
@[simp] theorem constantCoeff_linearFactor (a : ℝ) : constantCoeff (linearFactor a) = 1 := by
  simp [linearFactor]

/--
@isnad1 id=eq.0h2v.s7.f6c5fe1a309d from=translated src=- shape=3ef1adb9 vocab=529d5f52
-/
theorem coeff_linearFactor_mul_zero (a : ℝ) (f : PowerSeries ℝ) :
    coeff 0 (linearFactor a * f) = coeff 0 f := by
  simp [linearFactor, sub_mul, mul_assoc]

/--
@isnad1 id=eq.0h3v.s8.054d73cb426d from=translated src=- shape=92f61e51 vocab=5c2bffca
-/
theorem coeff_linearFactor_mul_succ (a : ℝ) (f : PowerSeries ℝ) (n : ℕ) :
    coeff (n + 1) (linearFactor a * f) = coeff (n + 1) f - a * coeff n f := by
  simp [linearFactor, sub_mul, mul_assoc, coeff_succ_X_mul]

/--
@isnad1 id=eq.0h3v.s5.5e8af958e36d from=translated src=- shape=4abbd363 vocab=924e52b5
-/
theorem linearFactor_mul_homogeneousSeries (x y z : ℝ) :
    linearFactor z * homogeneousSeries x y z = mk (homogeneous2 x y) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [coeff_linearFactor_mul_zero, homogeneous3, homogeneous2]
  | succ n =>
    simp only [coeff_linearFactor_mul_succ, coeff_homogeneousSeries, coeff_mk, homogeneous3]
    ring

/--
@isnad1 id=eq.0h2v.s5.b5f74d5daf67 from=translated src=- shape=633ea993 vocab=39989041
-/
theorem linearFactor_mul_homogeneous2 (x y : ℝ) :
    linearFactor y * mk (homogeneous2 x y) = mk (fun n => x ^ n) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [coeff_linearFactor_mul_zero, homogeneous2]
  | succ n =>
    simp only [coeff_linearFactor_mul_succ, coeff_mk, homogeneous2]
    ring

/--
@isnad1 id=eq.0h1v.s5.2f30dc144b3e from=translated src=- shape=fffcdd8f vocab=d7573efc
-/
theorem linearFactor_mul_geometric (x : ℝ) :
    linearFactor x * mk (fun n => x ^ n) = 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [coeff_linearFactor_mul_zero]
  | succ n => simp [coeff_linearFactor_mul_succ, pow_succ, mul_comm]

/--
@isnad1 id=eq.0h3v.s6.957e5439ea62 from=translated src=- shape=50497704 vocab=05b329d1
-/
theorem product_linearFactor_mul_homogeneousSeries (x y z : ℝ) :
    (linearFactor x * linearFactor y * linearFactor z) * homogeneousSeries x y z = 1 := by
  rw [mul_assoc, mul_assoc, linearFactor_mul_homogeneousSeries,
    linearFactor_mul_homogeneous2, linearFactor_mul_geometric]

/-- The generating function is exactly the product of the three geometric inverses.
@isnad1 id=eq.0h3v.s6.df4da52489c5 from=translated src=- shape=b78fa04d vocab=88c759d4
-/
theorem homogeneousSeries_eq_product_inverse (x y z : ℝ) :
    homogeneousSeries x y z = (linearFactor x)⁻¹ * (linearFactor y)⁻¹ * (linearFactor z)⁻¹ := by
  have h : constantCoeff (linearFactor x * linearFactor y * linearFactor z) ≠ 0 := by simp
  have heq : (linearFactor x * linearFactor y * linearFactor z)⁻¹ = homogeneousSeries x y z :=
    (inv_eq_iff_mul_eq_one h).mpr (by simpa only [mul_comm] using product_linearFactor_mul_homogeneousSeries x y z)
  rw [← heq, PowerSeries.mul_inv_rev, PowerSeries.mul_inv_rev]
  ring

/-- The weighted difference is the coefficient of `(1-βw)G`.
@isnad1 id=eq.0h5v.s6.c4799e28fb2b from=translated src=- shape=9aa9d1dd vocab=68d98cab
-/
theorem coeff_linearFactor_homogeneousSeries (β x y z : ℝ) (n : ℕ) :
    coeff n (linearFactor β * homogeneousSeries x y z) = weightedCoefficient β x y z n := by
  cases n with
  | zero => simp [coeff_linearFactor_mul_zero]
  | succ n => simp [coeff_linearFactor_mul_succ, weightedCoefficient, previousHomogeneous3]

end
end EntropyConstrainedMissingMass
