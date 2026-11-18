import Tengoku.Seed.NumberTheory.ModularForms.DedekindEta
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Summable
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.LogBounds
import Tengoku.Seed.Analysis.Normed.Group.FunctionSeries
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Topology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_exp_logEta.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_exp_logEta

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

open UpperHalfPlane hiding I

open scoped ModularForm MatrixGroups Real Topology

namespace DedekindEtaLog

def logEta (z : ℂ) : ℂ := π * I * z / 12 + ∑' n : ℕ, log (1 - ModularForm.eta_q n z)

lemma summable_log (z : ℍ) : Summable fun n : ℕ => log (1 - ModularForm.eta_q n z) := by
  have h := Complex.summable_log_one_add_of_summable (Summable.of_norm (ModularForm.summable_eta_q z))
  simpa [sub_eq_add_neg] using h

theorem exp_logEta (z : ℍ) : exp (logEta z) = η (z : ℂ) := by
  rw [logEta, exp_add, ModularForm.eta,
    ← Complex.cexp_tsum_eq_tprod (fun n => ModularForm.one_sub_eta_q_ne_zero n z.2) (summable_log z)]
  congr 1
  rw [Function.Periodic.qParam]
  congr 1
  push_cast
  ring

end DedekindEtaLog

end

theorem solution (z : UpperHalfPlane) : Complex.exp (Real.pi * Complex.I * (z : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z : ℂ))) = ModularForm.eta z :=
  DedekindEtaLog.exp_logEta z
