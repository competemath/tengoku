/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Exponentials of iterated-logarithmic budgets

A fixed polynomial in the ceiling logarithm is eventually smaller than its
input, by Cslib's natural exponential-versus-polynomial theorem. Applying
this at the input's ceiling logarithm shows that exponentiating any fixed
iterated-logarithmic polynomial still gives a sublinear function. This keeps
the unbounded Gamma candidate count, rather than replacing it by a fixed
power of the original logarithm.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Filter

theorem sourceReduction_tendsto_clog :
    Tendsto (fun n : Nat => Nat.clog 2 (n + 1)) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (2 ^ N)] with n large
  exact (Nat.le_log_of_pow_le (by decide) large).trans
    ((Nat.log_le_clog 2 n).trans (Nat.clog_mono_right 2 (Nat.le_succ n)))

end Algebraic.Cutwidth.Extractor.Internal
