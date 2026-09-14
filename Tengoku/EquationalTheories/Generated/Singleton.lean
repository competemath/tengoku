-- Tengoku.EquationalTheories.Generated.Singleton: verified translations of equational_theories/Generated/Singleton.lean (9 theorems)
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
import Tengoku.Tactic
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

-- left unwrapped: this module opens an outside namespace block
open EquationalTheories

namespace Singleton

theorem Equation89_implies_Equation2 (G: Type*) [Magma G] (h: Equation89 G) : Equation2 G
:=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation144_implies_Equation2 (G: Type*) [Magma G] (h: Equation144 G) : Equation2 G
:=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation147_implies_Equation2 (G: Type*) [Magma G] (h: Equation147 G) : Equation2 G
:=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation148_implies_Equation2 (G: Type*) [Magma G] (h: Equation148 G) : Equation2 G
:=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation149_implies_Equation2 (G: Type*) [Magma G] (h: Equation149 G) : Equation2 G
:=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation233_implies_Equation2 (G: Type*) [Magma G] (h: Equation233 G) : Equation2 G
:=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation515_implies_Equation2 (G: Type*) [Magma G] (h: Equation515 G) : Equation2 G
:=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation517_implies_Equation2 (G: Type*) [Magma G] (h: Equation517 G) : Equation2 G
:=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation518_implies_Equation2 (G: Type*) [Magma G] (h: Equation518 G) : Equation2 G
:=
  fun a _ ↦ by rw [h a a a, ← h]

end Singleton
