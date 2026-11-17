import Tengoku.Seed.AlgebraicGeometry.Geometrically.Irreducible
import Tengoku.Seed.AlgebraicGeometry.Fiber
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.RingTheory.Jacobson.Ring
import Tengoku.Seed.RingTheory.TensorProduct.Nontrivial
import Tengoku.Seed.RingTheory.TensorProduct.Free
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.Seed.LinearAlgebra.TensorProduct.Finiteness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace IsAlgClosed
export _root_.IsAlgClosed (lift algebraMap_bijective_of_isIntegral mk)
namespace BaseChangeIrreducible
open _root_.IsAlgClosed

section FiniteType

variable {K : Type u} [Field K]

end FiniteType

section Fields

variable (k : Type u) [Field k] [IsAlgClosed k]

end Fields

section Schemes

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (K : Type u) [Field K] [Algebra k K]

end Schemes

end IsAlgClosed.BaseChangeIrreducible
