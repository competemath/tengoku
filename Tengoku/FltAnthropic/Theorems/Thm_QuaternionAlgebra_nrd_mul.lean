import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_QuaternionAlgebra_ReducedNorm
import Tengoku.FltAnthropic.P2M.Sol.S_QuaternionAlgebra_nrd_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_QuaternionAlgebra_nrd_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
open Quaternion QuaternionAlgebra
/--
@isnad1 id=eq.0h5v.s7.8d55e3ed23a4 from=translated src=- shape=6f03d6b0 vocab=73df06f5
-/
theorem QuaternionAlgebra.nrd_mul {R : Type*} [CommRing R] {a b : R}
    (x y : ℍ[R, a, b]) : QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by exact @_root_.P2MW.S_QuaternionAlgebra_nrd_mul.solution R _ a b x y
