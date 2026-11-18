import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_exists_div_le_of_le_setAverage_of_nonpos

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_exists_div_le_of_le_setAverage_of_nonpos.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.9h7v.s7.766800e9dd14 from=translated src=- shape=64c6a70d vocab=b8982c5e
-/
theorem MeasureTheory.exists_div_le_of_le_setAverage_of_nonpos {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s E : Set α} {ψ : α → ℝ} {A θ : ℝ}
    (hsm : MeasurableSet s) (hψ : MeasureTheory.IntegrableOn ψ s μ) (hψ0 : ∀ x ∈ s, ψ x ≤ 0)
    (hE : E ⊆ s) (hs0 : μ s ≠ 0) (hs : μ s ≠ ⊤) (hθ : 0 < θ) (hθE : θ * μ.real s ≤ μ.real E)
    (hA : -A ≤ ⨍ x in s, ψ x ∂μ) :
    ∃ x ∈ E, -A / θ ≤ ψ x := by exact @_root_.P2MW.S_MeasureTheory_exists_div_le_of_le_setAverage_of_nonpos.solution α _ μ s E ψ A θ hsm hψ hψ0 hE hs0 hs hθ hθE hA
