import Tengoku.Seed.NumberTheory.ModularForms.DedekindEta
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Summable
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.LogBounds
import Tengoku.Seed.Analysis.Normed.Group.FunctionSeries
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Topology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_logEta_add_intCast.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_logEta_add_intCast

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

open UpperHalfPlane hiding I

open scoped ModularForm MatrixGroups Real Topology

namespace DedekindEtaLog

def logEta (z : ℂ) : ℂ := π * I * z / 12 + ∑' n : ℕ, log (1 - ModularForm.eta_q n z)

/--
@isnad1 id=eq.0h2v.s6.6af40fe17c5c from=translated src=- shape=39df3e0b vocab=b9e8aef1
-/
theorem logEta_add_int (z : ℂ) (m : ℤ) : logEta (z + m) = logEta z + π * I * m / 12 := by
  have hq : ∀ n : ℕ, ModularForm.eta_q n (z + m) = ModularForm.eta_q n z := by
    intro n
    rw [ModularForm.eta_q_eq_cexp, ModularForm.eta_q_eq_cexp,
      show 2 * π * I * (n + 1) * (z + m) = 2 * π * I * (n + 1) * z + ((n + 1) * m : ℤ) * (2 * π * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [logEta, hq]
  ring

end DedekindEtaLog

end

/--
@isnad1 id=eq.0h2v.s7.6dc1ff42103b from=translated src=- shape=e214be96 vocab=363665e5
-/
theorem solution (z : ℂ) (m : ℤ) : (Real.pi * Complex.I * (z + m) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z + m))) = (Real.pi * Complex.I * z / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n z)) + Real.pi * Complex.I * m / 12 :=
  DedekindEtaLog.logEta_add_int z m
