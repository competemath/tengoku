import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open UpperHalfPlane

namespace CuspForm

/--
@isnad1 id=analytic.0h3v.s8.703ec8f2ab6c from=translated src=- shape=514a44fb vocab=b42ace6a
-/
theorem analyticAt_cuspFunction_one_gamma0 {M : ℕ} {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) : AnalyticAt ℂ (cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos
    (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _)

noncomputable def qCoeffLinear (M : ℕ) (k : ℤ) (n : ℕ) :
    CuspForm (CongruenceSubgroup.Gamma0 M) k →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff (⇑f) n
  map_add' f g := by
    show ModularFormClass.qCoeff (⇑(f + g)) n =
      ModularFormClass.qCoeff (⇑f) n + ModularFormClass.qCoeff (⇑g) n
    unfold ModularFormClass.qCoeff
    rw [FunLike.coe_add, UpperHalfPlane.qExpansion_add (analyticAt_cuspFunction_one_gamma0 f)
      (analyticAt_cuspFunction_one_gamma0 g), map_add]
  map_smul' c f := by
    show ModularFormClass.qCoeff (⇑(c • f)) n = c • ModularFormClass.qCoeff (⇑f) n
    unfold ModularFormClass.qCoeff
    rw [show (⇑(c • f) : ℍ → ℂ) = c • (⇑f) from by ext z; rfl,
      UpperHalfPlane.qExpansion_smul (analyticAt_cuspFunction_one_gamma0 f), map_smul]

end CuspForm
