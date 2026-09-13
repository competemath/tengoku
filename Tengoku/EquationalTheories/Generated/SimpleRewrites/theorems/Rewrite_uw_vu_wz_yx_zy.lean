-- Tengoku.EquationalTheories.Generated.SimpleRewrites.theorems.Rewrite_uw_vu_wz_yx_zy: verified translations of equational_theories/Generated/SimpleRewrites/theorems/Rewrite_uw_vu_wz_yx_zy.lean (2 theorems)
import Tengoku.Tactic
import Tengoku.EquationalTheories.Deps.Magma
import Lean
import Tengoku.Data.FunLike.Basic
import Tengoku.Logic.Equiv.Basic
import Tengoku.Data.List.NodupEquivFin
import Tengoku.Data.Set.Defs
import Lean.Elab.Exception
import Lean.Elab.Declaration
import Lean.Util.CollectAxioms
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

namespace SimpleRewrites

theorem Equation3455_implies_Equation3304 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3304 G
:= λ x y z w u => h x x y z w u

theorem Equation4694_implies_Equation4628 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4628 G
:= λ x y z w u => h x x y z w u

end SimpleRewrites

end EquationalTheories
