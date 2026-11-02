import Tengoku.Seed.Algebra.Field.Rat
import Tengoku.Seed.Algebra.Module.LinearMap.Defs
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
A structural implication from a cubic characteristic identity to the Jordan
identity. The proof uses finite polarization and associative trace, with no
Albert-coordinate expansion.
-/

namespace CubicJordan

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Six times the cubic characteristic identity, with Newton coefficients.-/
def residual (mul : V →ₗ[ℚ] V →ₗ[ℚ] V) (T : V →ₗ[ℚ] ℚ) (e x : V) : V :=
  (6 : ℚ) • mul x (mul x x) - (6 * T x) • mul x x +
    (3 * (T x) ^ 2 - 3 * T (mul x x)) • x -
    ((T x) ^ 3 - 3 * T x * T (mul x x) + 2 * T (mul x (mul x x))) • e

/-- Twice the coefficient of the linear perturbation in the cubic identity.-/
def linearResidual (mul : V →ₗ[ℚ] V →ₗ[ℚ] V)
    (T : V →ₗ[ℚ] ℚ) (e x y : V) : V :=
  (4 : ℚ) • mul x (mul x y) + (2 : ℚ) • mul (mul x x) y -
    (2 * T y) • mul x x - (4 * T x) • mul x y +
    (2 * T x * T y - 2 * T (mul x y)) • x +
    ((T x) ^ 2 - T (mul x x)) • y -
    (((T x) ^ 2 - T (mul x x)) * T y -
      2 * T x * T (mul x y) + 2 * T (mul (mul x x) y)) • e

theorem linearResidual_eq_zero
    (mul : V →ₗ[ℚ] V →ₗ[ℚ] V) (T : V →ₗ[ℚ] ℚ) (e : V)
    (comm : ∀ x y, mul x y = mul y x)
    (assocTrace : ∀ x y z, T (mul (mul x y) z) = T (mul x (mul y z)))
    (char : ∀ x, residual mul T e x = 0) (x y : V) :
    linearResidual mul T e x y = 0 := by
  calc
    linearResidual mul T e x y = (1 / 6 : ℚ) •
        (residual mul T e (x + y) - residual mul T e (x - y) -
          (2 : ℚ) • residual mul T e y) := by
      simp only [linearResidual, residual, map_add, map_sub, map_smul,
        LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul]
      simp only [comm y x, comm y (mul x x), ← assocTrace x x y]
      module
    _ = 0 := by rw [char, char, char]; simp

/-- A commutative unital algebra with associative trace and the cubic Newton
identity is Jordan. This avoids any quartic coordinate expansion.-/
theorem jordan_of_cubic_trace_identity
    (mul : V →ₗ[ℚ] V →ₗ[ℚ] V) (T : V →ₗ[ℚ] ℚ) (e : V)
    (comm : ∀ x y, mul x y = mul y x)
    (unit : ∀ x, mul e x = x)
    (assocTrace : ∀ x y z, T (mul (mul x y) z) = T (mul x (mul y z)))
    (char : ∀ x, residual mul T e x = 0) (x y : V) :
    mul (mul x y) (mul x x) = mul x (mul y (mul x x)) := by
  have unitR (z : V) : mul z e = z := by rw [comm, unit]
  have hB₁ : T (mul x (mul x y)) = T (mul (mul x x) y) :=
    (assocTrace x x y).symm
  have hB₂ : T (mul (mul x x) (mul x y)) =
      T (mul (mul x (mul x x)) y) := by
    rw [← assocTrace, comm (mul x x) x]
  have hlin := linearResidual_eq_zero mul T e comm assocTrace char
  have hj : mul (mul x x) (mul x y) - mul x (mul (mul x x) y) = 0 := by
    calc
      mul (mul x x) (mul x y) - mul x (mul (mul x x) y) =
          (-1 / 2 : ℚ) •
            (mul x (linearResidual mul T e x y) -
              linearResidual mul T e x (mul x y)) -
          (T y / 6) • residual mul T e x +
          ((1 / 6 : ℚ) * T (mul (residual mul T e x) y)) • e := by
        simp only [linearResidual, residual, map_add, map_sub, map_smul,
          LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          smul_eq_mul, unit, unitR, hB₁, hB₂]
        module
      _ = 0 := by rw [hlin, hlin, char]; simp
  have heq := sub_eq_zero.mp hj
  simpa only [comm (mul x y) (mul x x), comm y (mul x x)] using heq

end CubicJordan
