import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_existsUnique_lift_fromNormalization_kummer_of_isAffineOpen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.Polynomial open _root_.AlgebraicGeometry.Polynomial open _root_.TopologicalSpace open _root_.Opposite

namespace KummerLift

variable {X : Scheme.{u}} [IsIntegral X]

section KummerAlgebra

variable (k : ℕ) (g : X.functionField)

end KummerAlgebra

def HasValue (U : X.Opens) (s : Γ(X, U)) (t : X.functionField) : Prop :=
  ∀ (x : X) (hx : x ∈ U), algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) = t

section Yside

variable (k : ℕ) (g : X.functionField)

end Yside

section YGlue

variable (k : ℕ) (g : X.functionField)

variable {k g}

end YGlue

section Data

variable (k : ℕ) (g : X.functionField)

variable {k g}

end Data

section Lift

variable (k : ℕ) (g : X.functionField)

variable {k g}

end Lift

section Bridge

variable (k : ℕ) (g : X.functionField)

end Bridge

end KummerLift
