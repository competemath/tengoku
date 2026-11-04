import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.MixtureCurvature
import Tengoku.Seed.MeasureTheory.Constructions.UnitInterval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The elementary simplex integrals

The square parametrization `(u,v) ↦ (u,(1-u)v,(1-u)(1-v))`, with density
`2(1-u)`, represents the uniform probability law on the two-dimensional simplex.
The rational antiderivatives below work even when atom sizes coincide.
-/

open MeasureTheory Set
open scoped Topology

namespace EntropyConstrainedMissingMass
namespace Curvature

/-- The affine scale obtained from barycentric simplex coordinates.-/
def simplexValue (x y z u v : ℝ) : ℝ :=
  u * x + (1 - u) * v * y + (1 - u) * (1 - v) * z

/-- Adding the same location to all three scales shifts the simplex value by
that location because its barycentric coordinates sum to one.
@isnad1 id=eq.0h6v.s5.3ba4593331b2 from=translated src=- shape=2088cf20 vocab=05d3df56
-/
theorem simplexValue_add (x y z s u v : ℝ) :
    simplexValue (s + x) (s + y) (s + z) u v = s + simplexValue x y z u v := by
  unfold simplexValue
  ring

/-- Convexity keeps every simplex scale between common lower and upper bounds.
@isnad1 id=mem.5h7v.s6.18298584644f from=translated src=- shape=0a29180e vocab=419ab760
-/
theorem simplexValue_mem (x y z a b u v : ℝ)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hz : z ∈ Icc a b)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    simplexValue x y z u v ∈ Icc a b := by
  have h2 : 0 ≤ (1 - u) * v := mul_nonneg (by linarith [hu.2]) hv.1
  have h3 : 0 ≤ (1 - u) * (1 - v) :=
    mul_nonneg (by linarith [hu.2]) (by linarith [hv.2])
  constructor
  · have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hx.1 hu.1)
      (mul_le_mul_of_nonneg_left hy.1 h2)) (mul_le_mul_of_nonneg_left hz.1 h3)
    convert h using 1 <;> (try unfold simplexValue) <;> ring
  · have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hx.2 hu.1)
      (mul_le_mul_of_nonneg_left hy.2 h2)) (mul_le_mul_of_nonneg_left hz.2 h3)
    convert h using 1 <;> (try unfold simplexValue) <;> ring

private theorem integral_poly_two (A B C : ℝ) :
    (∫ u in (0 : ℝ)..1, A * u ^ 2 + B * u + C) = A / 3 + B / 2 + C := by
  have hA : IntervalIntegrable (fun u : ℝ => A * u ^ 2) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun u : ℝ => B * u) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hA.add hB) intervalIntegrable_const,
    intervalIntegral.integral_add hA hB, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  norm_num
  ring

private theorem integral_poly_three (A B C D : ℝ) :
    (∫ u in (0 : ℝ)..1, A * u ^ 3 + (B * u ^ 2 + C * u + D)) =
      A / 4 + B / 3 + C / 2 + D := by
  have hA : IntervalIntegrable (fun u : ℝ => A * u ^ 3) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun u : ℝ => B * u ^ 2 + C * u + D) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add hA hB, intervalIntegral.integral_const_mul,
    integral_poly_two]
  norm_num
  ring

private theorem simplex_inner_moments (x y z u : ℝ) :
    (∫ v in (0 : ℝ)..1, simplexValue x y z u v) =
      (z + (x - z) * u) + ((1 - u) * (y - z)) / 2 ∧
    (∫ v in (0 : ℝ)..1, (simplexValue x y z u v) ^ 2) =
      (z + (x - z) * u) ^ 2 + (z + (x - z) * u) * ((1 - u) * (y - z)) +
        ((1 - u) * (y - z)) ^ 2 / 3 := by
  let A := z + (x - z) * u
  let B := (1 - u) * (y - z)
  constructor
  · have heq : (fun v : ℝ => simplexValue x y z u v) =
        (fun v : ℝ => 0 * v ^ 2 + B * v + A) := by funext v; dsimp [A, B, simplexValue]; ring
    rw [heq, integral_poly_two]
    dsimp [A, B]
    ring
  · have heq : (fun v : ℝ => (simplexValue x y z u v) ^ 2) =
        (fun v : ℝ => B ^ 2 * v ^ 2 + (2 * A * B) * v + A ^ 2) := by
      funext v
      dsimp [A, B, simplexValue]
      ring
    rw [heq, integral_poly_two]
    dsimp [A, B]
    ring

/-- The first moment of a uniform simplex scale.
@isnad1 id=eq.0h3v.s7.2d3a22f2b9e6 from=translated src=- shape=cf2db688 vocab=762608cd
-/
theorem simplex_first_moment (x y z : ℝ) :
    (∫ u in (0 : ℝ)..1, 2 * (1 - u) *
      ∫ v in (0 : ℝ)..1, simplexValue x y z u v) = (x + y + z) / 3 := by
  have heq : (fun u : ℝ => 2 * (1 - u) * ∫ v in (0 : ℝ)..1, simplexValue x y z u v) =
      (fun u : ℝ => (-2 * x + y + z) * u ^ 2 + (2 * x - 2 * y - 2 * z) * u + (y + z)) := by
    funext u
    rw [(simplex_inner_moments x y z u).1]
    ring
  rw [heq, integral_poly_two]
  ring

/-- The second moment records nondegeneracy whenever the triple is nonuniform.
@isnad1 id=eq.0h3v.s8.707691928bb3 from=translated src=- shape=6fc958fc vocab=16c37822
-/
theorem simplex_second_moment (x y z : ℝ) :
    (∫ u in (0 : ℝ)..1, 2 * (1 - u) *
      ∫ v in (0 : ℝ)..1, (simplexValue x y z u v) ^ 2) =
      (x ^ 2 + y ^ 2 + z ^ 2 + x * y + x * z + y * z) / 6 := by
  have heq : (fun u : ℝ => 2 * (1 - u) * ∫ v in (0 : ℝ)..1, (simplexValue x y z u v) ^ 2) =
      (fun u : ℝ =>
        (-2 * x ^ 2 + 2 * x * y + 2 * x * z - 2 * y ^ 2 / 3 - 2 * y * z / 3 - 2 * z ^ 2 / 3) * u ^ 3 +
        ((2 * x ^ 2 - 4 * x * y - 4 * x * z + 2 * y ^ 2 + 2 * y * z + 2 * z ^ 2) * u ^ 2 +
        (2 * x * y + 2 * x * z - 2 * y ^ 2 - 2 * y * z - 2 * z ^ 2) * u +
        (2 * y ^ 2 / 3 + 2 * y * z / 3 + 2 * z ^ 2 / 3))) := by
    funext u
    rw [(simplex_inner_moments x y z u).2]
    ring
  rw [heq, integral_poly_three]
  ring

end Curvature
end EntropyConstrainedMissingMass
