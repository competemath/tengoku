import Tengoku.Seed.RepresentationTheory.Subrepresentation
import Tengoku.Seed.LinearAlgebra.Projectivization.Action
import Tengoku.Seed.LinearAlgebra.Projectivization.Cardinality
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.LinearAlgebra.Charpoly.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Free
import Tengoku.Seed.FieldTheory.Finite.GaloisField
import Tengoku.FltAnthropic.Definitions.Def_Compat_Mathlib430

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

local notation α "^+" M:51 => FixedPoints.addSubgroup M α

set_option autoImplicit false

open Polynomial

namespace CuspidalType

variable (q : ℕ) [Fact q.Prime]

abbrev GL2 : Type := Matrix.GeneralLinearGroup (Fin 2) (ZMod q)

abbrev ProjLine : Type := Projectivization (ZMod q) (Fin 2 → ZMod q)

scoped instance instMulActionProjLine : MulAction (GL2 q) (ProjLine q) :=
  MulAction.compHom (ProjLine q)
    (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod q)).toMonoidHom

def scalarElem : (ZMod q)ˣ →* GL2 q :=
  Units.map (Matrix.scalar (Fin 2) : ZMod q →+* Matrix (Fin 2) (Fin 2) (ZMod q)).toMonoidHom

variable (k : Type*) [Field k]

variable {q} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end CuspidalType
