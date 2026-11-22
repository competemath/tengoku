import Tengoku.Seed.RingTheory.Norm.Defs
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicHaar
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_InfiniteAdeleRing_exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_InfiniteAdeleRing_exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfiniteAdeleRing NumberField.mixedEmbedding
open scoped Classical ENNReal

/--
@isnad1 id=other.0h2v.s12.09dbcd884e12 from=translated src=- shape=761eb1cc vocab=9349b3a6
-/
theorem NumberField.InfiniteAdeleRing.exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace
    (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL n (InfiniteAdeleRing K))] [BorelSpace (GL n (InfiniteAdeleRing K))] :
    let U : Set (n → n → mixedSpace K) := {e | IsUnit (Matrix.of e)}
    let ρ : (n → n → mixedSpace K) → ℝ≥0∞ := fun e => ENNReal.ofReal |Algebra.norm ℝ (Matrix.of e)|⁻¹
    let Φ : GL n (InfiniteAdeleRing K) → (n → n → mixedSpace K) := fun g i j =>
      ringEquiv_mixedSpace K ((g : Matrix n n (InfiniteAdeleRing K)) i j)
    let Ψ : (n → n → mixedSpace K) → GL n (InfiniteAdeleRing K) := fun e =>
      if h : IsUnit (Matrix.of e) then (h.map (ringEquiv_mixedSpace K).symm.mapMatrix).unit else 1
    ContinuousOn ρ U ∧ (∀ e ∈ U, 0 < ρ e) ∧ (∀ g, Φ g ∈ U) ∧ (∀ g, Ψ (Φ g) = g) ∧
      ∃ μ : Measure (GL n (InfiniteAdeleRing K)), μ.IsHaarMeasure ∧ μ.Regular ∧
        ∀ f : GL n (InfiniteAdeleRing K) → ℝ≥0∞, Measurable f →
          ∫⁻ g, f g ∂μ = ∫⁻ e in U, f (Ψ e) * ρ e ∂volume := by exact @_root_.P2MW.S_NumberField_InfiniteAdeleRing_exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace.solution n _ _ K _ _ _ _
