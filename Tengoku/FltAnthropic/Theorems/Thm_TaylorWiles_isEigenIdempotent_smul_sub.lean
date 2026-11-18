import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Deformations_LocalSplitting
import Tengoku.FltAnthropic.P2M.Sol.S_TaylorWiles_isEigenIdempotent_smul_sub

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_TaylorWiles_isEigenIdempotent_smul_sub.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open Matrix
theorem TaylorWiles.isEigenIdempotent_smul_sub {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b v : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hv : v * (a - b) = 1) :
    TaylorWiles.IsEigenIdempotent M a b (v • (M - b • (1 : Matrix (Fin 2) (Fin 2) A))) := by exact @_root_.P2MW.S_TaylorWiles_isEigenIdempotent_smul_sub.solution A _ M a b v htr hdet hv
