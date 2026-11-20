import Tengoku.PshdLean.PshLines.PSHD.LeviSlices
import Tengoku.PshdLean.PshLines.PlurisubharmonicAE
import Tengoku.PshdLean.PshLines.Regularization.PshRepresentative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A plurisubharmonic representative from line sections

Step 3 of Proposition 2.1 of `pshd-vibe`, second half. A nonnegative Borel
function which is locally bounded above and subharmonic on every affine
complex-line section of an open set is locally integrable, its Levi
distributions are positive by slicing along complex lines, and the distributional characterization of
plurisubharmonic functions supplies a plurisubharmonic function equal to it
almost everywhere.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A plurisubharmonic representative** (Step 3 of Proposition 2.1). A
nonnegative Borel function which is locally bounded above and subharmonic on
every connected component of every affine complex-line section of an open set
agrees almost everywhere with a plurisubharmonic function.-/
theorem LineSubharmonicOn.exists_plurisubharmonicOn_ae_eq {u : E → ℝ} {D : Set E}
    (hD : IsOpen D) (hl : LineSubharmonicOn u D) (hu : Measurable u)
    (hpos : ∀ x ∈ D, 0 ≤ u x) (hbdd : ∀ p ∈ D, ∃ r > 0, BddAbove (u '' ball p r))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ v : E → EReal, PlurisubharmonicOn v D ∧ ∀ᵐ x ∂μ.restrict D, (u x : EReal) = v x := by
  let Ω : Opens E := ⟨D, hD⟩
  have huL : LocallyIntegrableOn u Ω μ := locallyIntegrableOn_of_bddAbove hD hu hpos hbdd μ
  have hT := LineSubharmonicOn.hasNonnegativeDistributionalLevi_of_slices (Ω := Ω) hl hu hpos
    hbdd μ huL
  obtain ⟨v, hvPsh, hvfin, hvL, hTv⟩ := Regularization.exists_pshRepresentative μ hT
  refine ⟨v, hvPsh, ?_⟩
  filter_upwards [ae_eq_of_regularDistribution_eq μ huL hvL hTv, hvfin] with x hx hfx
  rw [hx]
  exact EReal.coe_toReal hfx.1 hfx.2

end PshLines.PSHD
