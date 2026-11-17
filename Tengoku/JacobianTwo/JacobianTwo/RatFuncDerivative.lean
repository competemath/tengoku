/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.Seed.Algebra.Polynomial.Derivation
import Tengoku.Seed.FieldTheory.RatFunc.AsPolynomial
import Tengoku.Seed.RingTheory.Polynomial.Wronskian
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The formal derivative on a rational-function field

This file packages the quotient-rule derivative on `K(X)` as a `K`-derivation.
It is the coefficient-field derivative needed for the variable-leading
quadratic-coordinate reduction.
-/

noncomputable section

open Polynomial

namespace JacobianTwo.RatFuncDerivative

variable {K : Type*} [Field K]

/-- The quotient-rule derivative on the rational-function field `K(X)`.-/
def rationalDerivative (x : RatFunc K) : RatFunc K :=
  x.liftOn'
    (fun p q => RatFunc.mk (derivative p * q - p * derivative q) (q ^ 2))
    (by
      intro p q a hq ha
      apply (RatFunc.mk_eq_mk
        (pow_ne_zero 2 (mul_ne_zero ha hq)) (pow_ne_zero 2 hq)).2
      simp only [derivative_mul]
      ring)

/--
@isnad1 id=eq.0h3v.s9.64813bdba105 from=translated src=- shape=4207cfe6 vocab=7e2197b5
-/
theorem rationalDerivative_mk (p q : K[X]) :
    rationalDerivative (RatFunc.mk p q) =
      RatFunc.mk (derivative p * q - p * derivative q) (q ^ 2) := by
  rw [rationalDerivative, RatFunc.liftOn'_mk]
  · intro r
    simp

/--
@isnad1 id=eq.0h2v.s9.b5b81a654e19 from=translated src=- shape=4b3cd0a3 vocab=97d55347
-/
@[simp]
theorem rationalDerivative_algebraMap (p : K[X]) :
    rationalDerivative (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (derivative p) := by
  rw [← RatFunc.mk_one, rationalDerivative_mk]
  simp

/--
@isnad1 id=eq.2h5v.s8.601e735638fd from=translated src=- shape=6b005ff2 vocab=2c8a63bd
-/
theorem mk_add_mk (p r : K[X]) {q s : K[X]} (hq : q ≠ 0) (hs : s ≠ 0) :
    RatFunc.mk p q + RatFunc.mk r s =
      RatFunc.mk (p * s + q * r) (q * s) := by
  simp only [RatFunc.mk_eq_div, map_add, map_mul]
  field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero hs]

/--
@isnad1 id=eq.2h5v.s8.6f356e78f551 from=translated src=- shape=088ef8d3 vocab=50779245
-/
theorem mk_mul_mk (p r : K[X]) {q s : K[X]} (hq : q ≠ 0) (hs : s ≠ 0) :
    RatFunc.mk p q * RatFunc.mk r s = RatFunc.mk (p * r) (q * s) := by
  simp only [RatFunc.mk_eq_div, map_mul]
  field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero hs]

/--
@isnad1 id=eq.0h3v.s6.028c547d4ca9 from=translated src=- shape=667c5061 vocab=3e6d110d
-/
theorem rationalDerivative_add (x y : RatFunc K) :
    rationalDerivative (x + y) = rationalDerivative x + rationalDerivative y := by
  induction x using RatFunc.induction_on' with
  | _ p q hq =>
    induction y using RatFunc.induction_on' with
    | _ r s hs =>
      rw [mk_add_mk p r hq hs,
        rationalDerivative_mk, rationalDerivative_mk, rationalDerivative_mk,
        mk_add_mk _ _ (pow_ne_zero 2 hq) (pow_ne_zero 2 hs)]
      apply (RatFunc.mk_eq_mk
        (pow_ne_zero 2 (mul_ne_zero hq hs))
        (mul_ne_zero (pow_ne_zero 2 hq) (pow_ne_zero 2 hs))).2
      simp only [derivative_add, derivative_mul]
      ring

/--
@isnad1 id=eq.0h1v.s5.d6421a8a18a3 from=translated src=- shape=e9d7c1c6 vocab=b9fd0f5e
-/
@[simp]
theorem rationalDerivative_zero : rationalDerivative (0 : RatFunc K) = 0 := by
  rw [← map_zero (algebraMap K[X] (RatFunc K)), rationalDerivative_algebraMap,
    derivative_zero, map_zero]

/--
@isnad1 id=eq.0h3v.s7.c14cf838fe77 from=translated src=- shape=896086f0 vocab=b231fd61
-/
theorem rationalDerivative_mul (x y : RatFunc K) :
    rationalDerivative (x * y) =
      x * rationalDerivative y + y * rationalDerivative x := by
  induction x using RatFunc.induction_on' with
  | _ p q hq =>
    induction y using RatFunc.induction_on' with
    | _ r s hs =>
      rw [mk_mul_mk p r hq hs,
        rationalDerivative_mk, rationalDerivative_mk, rationalDerivative_mk,
        mk_mul_mk p _ hq (pow_ne_zero 2 hs),
        mk_mul_mk r _ hs (pow_ne_zero 2 hq),
        mk_add_mk _ _
          (mul_ne_zero hq (pow_ne_zero 2 hs))
          (mul_ne_zero hs (pow_ne_zero 2 hq))]
      apply (RatFunc.mk_eq_mk
        (pow_ne_zero 2 (mul_ne_zero hq hs))
        (mul_ne_zero
          (mul_ne_zero hq (pow_ne_zero 2 hs))
          (mul_ne_zero hs (pow_ne_zero 2 hq)))).2
      simp only [derivative_mul]
      ring

/--
@isnad1 id=eq.0h1v.s5.73870ede5b47 from=translated src=- shape=e9d7c1c6 vocab=b9fd0f5e
-/
@[simp]
theorem rationalDerivative_one : rationalDerivative (1 : RatFunc K) = 0 := by
  rw [← map_one (algebraMap K[X] (RatFunc K)), rationalDerivative_algebraMap,
    derivative_one, map_zero]

/--
@isnad1 id=eq.0h2v.s7.f0d3000af0c4 from=translated src=- shape=ffa96d6b vocab=e8c86618
-/
@[simp]
theorem rationalDerivative_algebraMap_base (c : K) :
    rationalDerivative (algebraMap K (RatFunc K) c) = 0 := by
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K) c,
    rationalDerivative_algebraMap]
  simp

/--
@isnad1 id=eq.0h3v.s9.d8a0416e345b from=translated src=- shape=a18a8119 vocab=05535911
-/
theorem rationalDerivative_smul (c : K) (x : RatFunc K) :
    rationalDerivative (c • x) = c • rationalDerivative x := by
  rw [Algebra.smul_def, Algebra.smul_def, rationalDerivative_mul,
    rationalDerivative_algebraMap_base, mul_zero, add_zero]

/-- In characteristic zero, the constants of the quotient-rule derivative on
`K(X)` are exactly the scalar rational functions.
@isnad1 id=iff.0h2v.s7.cacc4e6b3693 from=translated src=- shape=e0f6f476 vocab=fc0b9b7a
-/
theorem rationalDerivative_eq_zero_iff [CharZero K] (x : RatFunc K) :
    rationalDerivative x = 0 ↔ ∃ c : K, x = RatFunc.C c := by
  constructor
  · intro hx
    have hrepr : x = RatFunc.mk x.num x.denom := by
      rw [RatFunc.mk_eq_div, RatFunc.num_div_denom]
    have hmk :
        RatFunc.mk
          (derivative x.num * x.denom - x.num * derivative x.denom)
          (x.denom ^ 2) = 0 := by
      rw [← rationalDerivative_mk, ← hrepr]
      exact hx
    have hnumerator :
        derivative x.num * x.denom - x.num * derivative x.denom = 0 := by
      have hdisj :
          algebraMap K[X] (RatFunc K)
              (derivative x.num * x.denom -
                x.num * derivative x.denom) = 0 ∨
            algebraMap K[X] (RatFunc K) (x.denom ^ 2) = 0 := by
        simpa only [RatFunc.mk_eq_div, div_eq_zero_iff] using hmk
      have hmapped := hdisj.resolve_right
        (RatFunc.algebraMap_ne_zero (pow_ne_zero 2 x.denom_ne_zero))
      apply RatFunc.algebraMap_injective K
      simpa using hmapped
    have hwronskian : wronskian x.num x.denom = 0 := by
      rw [wronskian]
      calc
        x.num * derivative x.denom - derivative x.num * x.denom =
            -(derivative x.num * x.denom -
              x.num * derivative x.denom) := by ring
        _ = 0 := by rw [hnumerator, neg_zero]
    have hderivatives :=
      x.isCoprime_num_denom.wronskian_eq_zero_iff.mp hwronskian
    exact (RatFunc.eq_C_iff x).2 ⟨
      Polynomial.derivative_eq_zero.mp hderivatives.1,
      Polynomial.derivative_eq_zero.mp hderivatives.2⟩
  · rintro ⟨c, rfl⟩
    rw [← RatFunc.algebraMap_eq_C]
    exact rationalDerivative_algebraMap_base c

/-- The formal derivative on `K(X)`, bundled as a `K`-derivation.-/
def rationalDerivativeDerivation : Derivation K (RatFunc K) (RatFunc K) where
  toFun := rationalDerivative
  map_add' := rationalDerivative_add
  map_smul' := rationalDerivative_smul
  leibniz' := rationalDerivative_mul
  map_one_eq_zero' := rationalDerivative_one

/--
@isnad1 id=eq.0h2v.s8.e2d77ab6fbb0 from=translated src=- shape=9a05b684 vocab=d5fafc00
-/
@[simp]
theorem rationalDerivativeDerivation_apply (x : RatFunc K) :
    rationalDerivativeDerivation x = rationalDerivative x := rfl

/--
@isnad1 id=eq.0h2v.s10.e0943b0df056 from=translated src=- shape=cd2b8dba vocab=73b590a5
-/
@[simp]
theorem rationalDerivativeDerivation_algebraMap (p : K[X]) :
    rationalDerivativeDerivation (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (derivative p) :=
  rationalDerivative_algebraMap p

end JacobianTwo.RatFuncDerivative
