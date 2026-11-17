import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_linearIndependent_of_constantFieldExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=linearin.4h6v.s9.6692d30c272f from=translated src=- shape=af0a19b8 vocab=02ddcba6
-/
theorem AlgebraicCurve.linearIndependent_of_constantFieldExtension (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {ι : Type*} {b : ι → F} (hb : LinearIndependent K b) :
    LinearIndependent K' (fun i => algebraMap F F' (b i)) := by exact @_root_.P2MW.S_AlgebraicCurve_linearIndependent_of_constantFieldExtension.solution K F K' F' _ _ _ _ _ _ _ _ _ _ _ _ _ hfg hfg' hgen ι b hb
