/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Data.Nat.Factorization.Basic
import Tengoku.Seed.Data.Nat.Prime.Basic
import Tengoku.Seed.Algebra.EuclideanDomain.Basic
import Tengoku.Seed.Algebra.Order.Field.Power
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Base
import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.Seed.Topology.Algebra.Order.Field
import Tengoku.Seed.Std.Tactic.Init
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.RCases
import Tengoku.Seed.Algebra.Order.Field.Basic
import Tengoku.Seed.Order.Filter.Defs
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith.Frontend
import Tengoku.Seed.Tactic.Positivity.Basic
import Tengoku.Seed.Tactic.Ring.RingNF

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arithmetic lemmas for local-field index calculations

This file contains the pure natural-number cancellation steps used after local-field
norm and value-group arguments have produced an lcm divisibility.

It also contains the elementary `p`-adic valuation estimates used in the local-field structure
development,
the logarithm and exponential estimates for the convergence and valuation behavior of the
logarithm and exponential series.
-/

namespace LocalFieldTheory.DiscreteValuationField

open Filter

section PadicLogArithmetic

variable {p n : ℕ}

/-- Arithmetic estimate for the field-unit logarithm in real logarithmic
form: `v_p(n) <= log_p(n)`.
@isnad1 id=le.0h2v.s4.6b6bc4688113 from=translated src=- shape=48121551 vocab=ff14932e
-/
theorem padicValNat_le_real_logb
    [Fact p.Prime] (n : ℕ) :
    (padicValNat p n : ℝ) ≤ Real.logb p n := by
  exact
    (Nat.cast_le.mpr (padicValNat_le_nat_log (p := p) n)).trans
      (Real.natLog_le_logb n p)

/-- Variant of the logarithmic domination estimate with a fixed real multiple
of the logarithmic term.  This is the form needed after inserting the
ramification index into the valuation of integer denominators.
@isnad1 id=tendsto.1h3v.s6.9a24e36e1456 from=translated src=- shape=1be8655c vocab=1fc4b60d
-/
theorem tendsto_nat_succ_mul_const_sub_const_mul_logb_atTop
    {c C : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) * c -
          C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ))
      atTop atTop := by
  have hhalf : 0 < c / 2 := by positivity
  have htend :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsmall :
      (fun n : ℕ => C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) =o[atTop]
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
    have hlog :
        (fun n : ℕ => Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) =o[atTop]
          (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
      simpa [Function.comp_def] using
        (Real.isLittleO_logb_id_atTop (b := (p : ℝ))).comp_tendsto
          htend
    simpa using hlog.const_mul_left C
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ‖C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)‖ ≤
          (c / 2) * ‖((n + 1 : ℕ) : ℝ)‖ :=
    hsmall.def hhalf
  have hle :
      (fun n : ℕ => (c / 2) * ((n + 1 : ℕ) : ℝ)) ≤ᶠ[atTop]
        (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) * c -
            C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [hbound] with n hn
    have hnnonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hlog_le :
        C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) ≤
          (c / 2) * ((n + 1 : ℕ) : ℝ) := by
      calc
        C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) ≤
            ‖C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)‖ :=
          le_abs_self _
        _ ≤ (c / 2) * ‖((n + 1 : ℕ) : ℝ)‖ := hn
        _ = (c / 2) * ((n + 1 : ℕ) : ℝ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnnonneg]
    calc
      (c / 2) * ((n + 1 : ℕ) : ℝ) =
          ((n + 1 : ℕ) : ℝ) * c -
            (c / 2) * ((n + 1 : ℕ) : ℝ) := by
        ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * c -
          C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) :=
        sub_le_sub_left hlog_le (((n + 1 : ℕ) : ℝ) * c)
  have hlin :
      Tendsto (fun n : ℕ => (c / 2) * ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hhalf htend
  exact tendsto_atTop_mono' atTop hle hlin

end PadicLogArithmetic

end LocalFieldTheory.DiscreteValuationField
