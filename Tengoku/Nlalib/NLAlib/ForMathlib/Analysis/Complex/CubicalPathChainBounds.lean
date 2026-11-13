import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.CubicalPathChainIntegral
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.CubicalIntegralBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The actual length of a finite cornered path chain

Every native path piece enters with positive multiplicity. Repeated identical
pieces therefore retain their full multiplicity, and actual chain length is
exactly the finite sum of native parameter-speed integrals.
-/

noncomputable section
open Finset Set MeasureTheory
open scoped unitInterval
namespace Complex

/-- The actual total length of the finite path chain is the sum of the
native lengths of its actual pieces, including repetitions and empty families.
No smoothness at the joins is assumed.
@isnad1 id=eq.0h4v.s8.4a275e68d3f6 from=translated src=- shape=31bac8e8 vocab=2ab88ce0
-/
theorem cubicalLength_pathChain_eq_sum {Ω : Set ℂ} {n : ℕ}
    (p : Fin (n + 1) → Ω) (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ)) :
    cubicalLength (Cubical.pathChain p γ) =
      ∑ i : Fin n, ∫ t in (0 : ℝ)..1,
        ‖derivWithin ((γ i).map continuous_subtype_val).extend I t‖ := by
  classical
  have hcoeff (q : C(I, Ω)) : 0 ≤ Cubical.pathChain p γ q := by
    simp only [Cubical.pathChain, Finsupp.finsetSum_apply]
    apply sum_nonneg
    intro i _
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  let L : Cubical.OneChain Ω →ₗ[ℤ] ℝ := Finsupp.linearCombination ℤ (fun q =>
    ∫ t in (0 : ℝ)..1, ‖derivWithin (cubicalPath q).extend I t‖)
  have he : cubicalLength (Cubical.pathChain p γ) = L (Cubical.pathChain p γ) := by
    simp only [cubicalLength, L, Finsupp.linearCombination_apply, Finsupp.sum]
    apply sum_congr rfl
    intro q _
    rw [abs_of_nonneg (by exact_mod_cast hcoeff q), zsmul_eq_mul]
  rw [he]
  simp only [Cubical.pathChain, map_sum, L, Finsupp.linearCombination_single, one_smul,
    cubicalPath_toContinuousMap_extend]

end Complex
