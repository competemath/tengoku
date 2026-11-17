import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsIntegrallyClosed_integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsIntegrallyClosed_integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit

set_option autoImplicit false

open Polynomial TensorProduct

namespace KummerIntegralClosureKa

variable {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K]

variable (K)

variable {K}

end KummerIntegralClosureKa
