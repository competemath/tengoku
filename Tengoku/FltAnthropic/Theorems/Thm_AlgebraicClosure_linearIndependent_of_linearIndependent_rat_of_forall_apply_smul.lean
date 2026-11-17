import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicClosure_linearIndependent_of_linearIndependent_rat_of_forall_apply_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicClosure_linearIndependent_of_linearIndependent_rat_of_forall_apply_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=linearin.2h3v.s10.b87079b8413a from=translated src=- shape=786feb7c vocab=b3ef6256
-/
theorem AlgebraicClosure.linearIndependent_of_linearIndependent_rat_of_forall_apply_smul
    {X : Type} [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X]
    {ι : Type} (F : ι → X → AlgebraicClosure ℚ)
    (hF : ∀ (i : ι) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : X),
      F i (σ • x) = σ (F i x))
    (hind : LinearIndependent ℚ F) :
    LinearIndependent (AlgebraicClosure ℚ) F := by exact @_root_.P2MW.S_AlgebraicClosure_linearIndependent_of_linearIndependent_rat_of_forall_apply_smul.solution X _ ι F hF hind
