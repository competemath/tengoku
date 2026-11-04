import Tengoku.GeneralStochToDet.stoch_to_det.SharedRace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two-variable input to the multivariate bridge

This is the only multivariate module that names the currently certified
two-variable endpoint.  Future improvements should update `certifiedFactor`
and `T_le_certifiedFactor`; the posterior-compression and multivariate layers
depend only on the derived `oneSidedFactor`.
-/

namespace stoch_to_det
namespace NVarTwoVariableInput

universe u

/-- The multiplicative factor in the imported two-variable theorem.-/
noncomputable def certifiedFactor : Real := 96

/-- One-sided posterior compression pays twice the two-variable factor and
two additional replica-defect units in the bridge ledger.-/
noncomputable def oneSidedFactor : Real := 2 * certifiedFactor + 2

/--
@isnad1 id=eq.0h0v.s3.b7a23ae3745a from=translated src=- shape=ffdda526 vocab=f6ebf9d4
-/
theorem certifiedFactor_eq : certifiedFactor = 96 := rfl

/--
@isnad1 id=eq.0h0v.s3.032789b2ed01 from=translated src=- shape=ffdda526 vocab=ccec0950
-/
theorem oneSidedFactor_eq : oneSidedFactor = 194 := by
  norm_num [oneSidedFactor, certifiedFactor]

/--
@isnad1 id=le.0h0v.s3.3504c3ec85c9 from=translated src=- shape=ff3a10fc vocab=d4e2b25b
-/
theorem oneSidedFactor_nonneg : 0 <= oneSidedFactor := by
  rw [oneSidedFactor_eq]
  norm_num

end NVarTwoVariableInput
end stoch_to_det
