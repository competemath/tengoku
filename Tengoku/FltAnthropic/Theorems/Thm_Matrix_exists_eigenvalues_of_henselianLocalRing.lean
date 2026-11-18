import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.RingTheory.Henselian
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_exists_eigenvalues_of_henselianLocalRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_exists_eigenvalues_of_henselianLocalRing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.3h4v.s9.65b7aacd1f56 from=translated src=- shape=372ec4af vocab=f81e1016
-/
theorem Matrix.exists_eigenvalues_of_henselianLocalRing {A : Type*} [CommRing A] [IsLocalRing A]
    [HenselianLocalRing A] (M : Matrix (Fin 2) (Fin 2) A) {α β : IsLocalRing.ResidueField A}
    (hne : α ≠ β) (htr : IsLocalRing.residue A M.trace = α + β)
    (hdet : IsLocalRing.residue A M.det = α * β) :
    ∃ a b : A, M.trace = a + b ∧ M.det = a * b ∧ IsUnit (a - b) ∧
      IsLocalRing.residue A a = α ∧ IsLocalRing.residue A b = β := by exact @_root_.P2MW.S_Matrix_exists_eigenvalues_of_henselianLocalRing.solution A _ _ _ M α β hne htr hdet
