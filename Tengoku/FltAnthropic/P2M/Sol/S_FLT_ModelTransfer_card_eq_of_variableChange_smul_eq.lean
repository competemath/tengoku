import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq

open WeierstrassCurve

/--
@isnad1 id=eq.1h4v.s6.a8279b86fa40 from=translated src=- shape=9940acc6 vocab=ea9b8a16
-/
theorem solution {K : Type*} [Field K] [DecidableEq K]
    {X Y : WeierstrassCurve K} {E : WeierstrassCurve.VariableChange K} (h : E • X = Y) :
    Y.card = X.card :=
  Nat.card_congr (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq h)
