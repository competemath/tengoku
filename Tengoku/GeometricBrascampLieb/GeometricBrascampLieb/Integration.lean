import Tengoku.Seed.MeasureTheory.Integral.IntegralEqImproper
import Tengoku.Seed.MeasureTheory.Integral.Prod
import Tengoku.Seed.Analysis.Calculus.ParametricIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integration tools for heat-flow monotonicity

Cancellation of spatial derivatives uses Fubini and the fundamental theorem
on the full real line. All integrability assumptions are explicit.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace GeometricBrascampLieb

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]

/-- A derivative in one spatial coordinate has zero integral when the
function and that derivative are integrable on the product space.-/
theorem integral_coordinate_derivative_eq_zero
    {f g : ℝ × X → ℝ}
    (hf : Integrable f (volume.prod μ)) (hg : Integrable g (volume.prod μ))
    (hderiv : ∀ y x, HasDerivAt (fun s => f (s, y)) (g (x, y)) x) :
    ∫ p, g p ∂(volume.prod μ) = 0 := by
  rw [integral_prod_symm g hg]
  have hz : ∀ᵐ y ∂μ, ∫ x, g (x, y) = 0 := by
    filter_upwards [hf.prod_left_ae, hg.prod_left_ae] with y hyf hyg
    exact integral_eq_zero_of_hasDerivAt_of_integrable (hderiv y) hyg hyf
  rw [integral_congr_ae hz, integral_zero]

/-- Transfer coordinate cancellation through a volume-preserving coordinate chart.-/
theorem integral_derivative_eq_zero_of_coordinates
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (e : Y ≃ᵐ ℝ × X) (he : MeasurePreserving e ν (volume.prod μ))
    {f g : Y → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    (hderiv : ∀ y x, HasDerivAt (fun s => f (e.symm (s, y))) (g (e.symm (x, y))) x) :
    ∫ p, g p ∂ν = 0 := by
  rw [← he.symm.integral_comp']
  apply integral_coordinate_derivative_eq_zero (f := fun p => f (e.symm p))
  · exact (he.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
  · exact (he.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hg
  · exact hderiv

omit [SigmaFinite μ] in
/-- The elementary integration step in the heat-flow argument. It is enough
to dominate the actual time derivative locally and prove that its integral is
nonnegative. No assumption about monotonicity is used.-/
theorem monotoneOn_integral_of_local_derivative
    {u du : ℝ → X → ℝ} {I : Set ℝ} (hI : Convex ℝ I) (hIo : IsOpen I)
    (hint : ∀ t ∈ I, Integrable (u t) μ)
    (hdu : ∀ t ∈ I, AEStronglyMeasurable (du t) μ)
    (hderiv : ∀ t ∈ I, ∀ x, HasDerivAt (fun s => u s x) (du t x) t)
    (hdom : ∀ t ∈ I, ∃ V ∈ 𝓝 t, V ⊆ I ∧ ∃ b : X → ℝ,
      Integrable b μ ∧ ∀ s ∈ V, ∀ x, ‖du s x‖ ≤ b x)
    (hpos : ∀ t ∈ I, 0 ≤ ∫ x, du t x ∂μ) :
    MonotoneOn (fun t => ∫ x, u t x ∂μ) I := by
  have hd : ∀ t ∈ I, HasDerivAt (fun s => ∫ x, u s x ∂μ) (∫ x, du t x ∂μ) t := by
    intro t ht
    obtain ⟨V, hV, hVI, b, hb, hbound⟩ := hdom t ht
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV
      (Filter.Eventually.mono (hIo.mem_nhds ht) (fun s hs => (hint s hs).aestronglyMeasurable))
      (hint t ht) (hdu t ht) _ hb _).2
    · exact Filter.Eventually.of_forall fun x s hs => hbound s hs x
    · exact Filter.Eventually.of_forall fun x s hs => hderiv s (hVI hs) x
  apply monotoneOn_of_hasDerivWithinAt_nonneg hI
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).hasDerivWithinAt
  · exact fun t ht => hpos t (interior_subset ht)

end GeometricBrascampLieb
