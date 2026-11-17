import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Basic
import Tengoku.Seed.Analysis.Normed.Operator.Basic
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.DenseMultilinearExtension
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.DenseMultilinearFamilyExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proof of Lemma D.5

Uses `denseLinearExtension` (`AlternatingAnalytic/Analysis/DenseMultilinearExtension.lean`) for
part (1) and `exists_denseMultilinearFamilyExtension_of_bound`
(`AlternatingAnalytic/Analysis/DenseMultilinearFamilyExtension.lean`) for part (2).
-/

namespace AlternatingAnalyticChallenge.LemD_5

universe uK uV uY

/-- A linear map `T₀ : V₀ → Y` on a dense subspace with `‖T₀ x‖ ≤ C ‖x‖` extends uniquely to
a continuous map `V → Y`, which is linear and satisfies the same bound.
@isnad1 id=ex.3h6v.s11.9bc59b293ead from=translated src=- shape=cd5086ed vocab=334baea9
-/
theorem part1
    (K : Type uK) [NontriviallyNormedField K]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace K V]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]
    (V₀ : Submodule K V) (hV₀ : Dense (V₀ : Set V)) (C : ℝ) (hC : 0 ≤ C)
    (T₀ : V₀ →ₗ[K] Y) (hT₀ : ∀ x : V₀, ‖T₀ x‖ ≤ C * ‖(x : V)‖) :
    ∃ T : V →L[K] Y, (∀ x : V₀, T x = T₀ x) ∧ (∀ x : V, ‖T x‖ ≤ C * ‖x‖) ∧
      ∀ T' : V → Y, Continuous T' → (∀ x : V₀, T' x = T₀ x) → T' = T := by
  have hd : DenseRange V₀.subtypeₗᵢ := hV₀.denseRange_val
  let T₀c : V₀ →L[K] Y := T₀.mkContinuous C hT₀
  have hT₀c : ‖T₀c‖ ≤ C := LinearMap.mkContinuous_norm_le T₀ hC hT₀
  let T := AlternatingAnalytic.denseLinearExtension V₀.subtypeₗᵢ hd T₀c
  have hTx : ∀ x : V₀, T x = T₀ x := fun x =>
    AlternatingAnalytic.denseLinearExtension_apply V₀.subtypeₗᵢ hd T₀c x
  refine ⟨T, hTx, fun x => ?_, fun T' hT' hT'x => ?_⟩
  · calc ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right
          ((AlternatingAnalytic.norm_denseLinearExtension_le V₀.subtypeₗᵢ hd T₀c).trans hT₀c)
          (norm_nonneg x)
  · exact hd.equalizer hT' T.continuous (funext fun x => (hT'x x).trans (hTx x).symm)

/-- A multilinear map on dense subspaces with `‖M d‖ ≤ C ∏ ‖dᵢ‖` extends uniquely to a
continuous multilinear map of norm at most `C`.
@isnad1 id=ex.3h7v.s12.7c3d9deb0a28 from=translated src=- shape=f04b37cb vocab=c8d87c41
-/
theorem part2
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    {V : Fin k → Type uV} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace K (V i)]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]
    (V₀ : ∀ i, Submodule K (V i)) (hV₀ : ∀ i, Dense (V₀ i : Set (V i))) (C : ℝ) (hC : 0 ≤ C)
    (M : MultilinearMap K (fun i => V₀ i) Y)
    (hM : ∀ d : ∀ i, V₀ i, ‖M d‖ ≤ C * ∏ i, ‖(d i : V i)‖) :
    ∃ M' : ContinuousMultilinearMap K V Y,
      (∀ d : ∀ i, V₀ i, M' (fun i => (d i : V i)) = M d) ∧ ‖M'‖ ≤ C ∧
      ∀ M'' : ContinuousMultilinearMap K V Y,
        (∀ d : ∀ i, V₀ i, M'' (fun i => (d i : V i)) = M d) → M'' = M' := by
  exact AlternatingAnalytic.exists_denseMultilinearFamilyExtension_of_bound
    (fun i => (V₀ i).subtypeₗᵢ) (fun i => (hV₀ i).denseRange_val) M hC hM

end AlternatingAnalyticChallenge.LemD_5
