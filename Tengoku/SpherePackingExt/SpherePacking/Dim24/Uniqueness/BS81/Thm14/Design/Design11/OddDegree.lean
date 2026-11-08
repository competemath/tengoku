module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Defs
public import Tengoku.Seed.Data.Finset.Basic
public import Tengoku.Seed.Algebra.Ring.Parity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Odd-degree vanishing for antipodal sets

For any antipodal finite set `C` on the unit sphere and any *odd* `k`,
`gegenbauerDoubleSum24 k C = 0`.

This is used to upgrade vanishing for `k=1..10` into vanishing for `k=1..11` (since `11` is odd).
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.BuildSteps
open Finset

/-- Antipodality predicate for finsets: closed under negation.-/
@[expose] public def IsAntipodalFinset {α : Type*} [Neg α] (C : Finset α) : Prop :=
  ∀ u ∈ C, -u ∈ C

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.BuildSteps

namespace SpherePacking.Dim24

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace Uniqueness.BS81.LP
noncomputable section

open Polynomial

lemma gegenbauerVal_neg (lam : ℝ) :
    ∀ n x, gegenbauerVal lam n (-x) = ((-1 : ℝ) ^ n) * gegenbauerVal lam n x
  | 0, x => by
      simp [gegenbauerVal]
  | 1, x => by
      simp [gegenbauerVal]
  | n + 2, x => by
      simp [gegenbauerVal, gegenbauerVal_neg lam n x, gegenbauerVal_neg lam (n + 1) x,
        pow_succ, sub_eq_add_neg, div_eq_mul_inv]
      ring

lemma Gegenbauer24Val_neg (n : ℕ) (x : ℝ) :
    Gegenbauer24Val n (-x) = ((-1 : ℝ) ^ n) * Gegenbauer24Val n x := by
  -- Normalization divides by the constant `C_n(1)`, so parity is unchanged.
  simp [Gegenbauer24Val, gegenbauerVal_neg, mul_assoc, mul_comm]

/-- Parity of `Gegenbauer24`: evaluation at `-x` picks up the factor `(-1)^n`.-/
public lemma Gegenbauer24_eval_neg (n : ℕ) (x : ℝ) :
    (Gegenbauer24 n).eval (-x) = ((-1 : ℝ) ^ n) * (Gegenbauer24 n).eval x := by
  simp [Gegenbauer24_eval_eq, Gegenbauer24Val_neg]

lemma Gegenbauer24_eval_neg_11 (x : ℝ) :
    (Gegenbauer24 11).eval (-x) = - (Gegenbauer24 11).eval x := by
  have hodd : Odd (11 : ℕ) := by decide
  simpa [hodd.neg_one_pow] using (Gegenbauer24_eval_neg (n := 11) (x := x))

end

end Uniqueness.BS81.LP

namespace Uniqueness.BS81.Thm14.BuildSteps.Design11

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Finset
open Uniqueness.BS81.Thm14

open Uniqueness.BS81.LP

lemma gegenbauer24_eval_neg_of_odd (k : ℕ) (hk : Odd k) (x : ℝ) :
    (Gegenbauer24 k).eval (-x) = - (Gegenbauer24 k).eval x := by
  simp [Gegenbauer24_eval_neg, hk.neg_one_pow]

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.BuildSteps.Design11
