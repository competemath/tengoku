import Tengoku.PshdLean.PshLines.PSHD.Main
import Tengoku.PshdLean.PshLines.PSHD.Representative
import Tengoku.PshdLean.PshLines.PSHD.LineRecovery

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The article's route to Proposition 2.1 and Theorem 1.1

Steps 3-4 of the proof of Proposition 2.1 of `pshd-vibe`. After Steps 1-2 the
function is Borel, nonnegative and locally bounded above; Step 3 shows that its
Levi distributions are positive and produces a plurisubharmonic function equal
to it almost everywhere, and Step 4 shows, along a complex line through each
point meeting the exceptional null set in a planar null set, that the two
functions agree at every point. Hence the function itself is upper semicontinuous. This closes the same
dimension induction as the ball-average route, and Theorem 1.1 follows by the
same truncation argument.
-/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace PshLines.PSHD

universe u

/-- **Steps 3-4 of Proposition 2.1.** A nonnegative Borel function which is
locally bounded above and subharmonic on every connected component of every
affine complex-line section of an open set coincides with a plurisubharmonic
function there, and is therefore upper semicontinuous.-/
theorem LineSubharmonicOn.upperSemicontinuousOn_of_pshRepresentative {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [MeasurableSpace E] [BorelSpace E] {u : E → ℝ} {D : Set E} (hD : IsOpen D)
    (hl : LineSubharmonicOn u D) (hu : Measurable u) (hpos : ∀ x ∈ D, 0 ≤ u x)
    (hbdd : ∀ p ∈ D, ∃ r > 0, BddAbove (u '' ball p r)) : UpperSemicontinuousOn u D := by
  let μ : Measure E := Measure.addHaar
  obtain ⟨v, hv, hae⟩ := hl.exists_plurisubharmonicOn_ae_eq hD hu hpos hbdd μ
  have heq := hl.eqOn_of_ae_eq_of_lines hD hv μ hae
  intro x hx c hc
  have hvx : v x < (c : EReal) := by
    rw [← heq x hx]
    exact EReal.coe_lt_coe_iff.mpr hc
  filter_upwards [PlurisubharmonicOn.upperSemicontinuousOn hv x hx _ hvx,
    self_mem_nhdsWithin] with y hy hyD
  rw [← heq y hyD] at hy
  exact EReal.coe_lt_coe_iff.mp hy

/-- The article's route through a plurisubharmonic representative closes
Proposition 2.1.-/
theorem boundedLineSubharmonicUSC_of_pshRepresentative : BoundedLineSubharmonicUSC.{u} :=
  fun hD hl hu hpos hbdd => hl.upperSemicontinuousOn_of_pshRepresentative hD hu hpos hbdd

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Proposition 2.1** (`pshd-vibe`), by the article's argument. A nonnegative
real function on an open set that is subharmonic on every connected component
of every affine complex-line section is plurisubharmonic.-/
theorem LineSubharmonicOn.discPshOn_of_nonneg_of_pshRepresentative [FiniteDimensional ℂ E]
    {u : E → ℝ} {D : Set E} (hD : IsOpen D) (hpos : ∀ x ∈ D, 0 ≤ u x)
    (hl : LineSubharmonicOn u D) :
    DiscPshOn (fun x => (u x : EReal)) D :=
  hl.discPshOn (upperSemicontinuousOn_of_boundedLineSubharmonicUSC
    boundedLineSubharmonicUSC_of_pshRepresentative _ rfl hD hpos hl)

/-- **Theorem 1.1** (`pshd-vibe`), by the article's argument for
Proposition 2.1.-/
theorem discPshOn_of_line_sections_of_pshRepresentative [FiniteDimensional ℂ E]
    {φ : E → EReal} {Ω : Set E} (hΩ : IsOpen Ω) (htop : ∀ x ∈ Ω, φ x ≠ ⊤)
    (hl : ∀ c v : E, v ≠ 0 → ∀ z ∈ (fun t : ℂ ↦ c + t • v) ⁻¹' Ω,
      DiscPshOn (fun t ↦ φ (c + t • v)) (connectedComponentIn ((fun t : ℂ ↦ c + t • v) ⁻¹' Ω) z)) :
    DiscPshOn φ Ω :=
  discPshOn_of_line_sections_of_truncShift htop hl fun m =>
    LineSubharmonicOn.discPshOn_of_nonneg_of_pshRepresentative hΩ
      (fun x hx => truncShift_nonneg (htop x hx) m) (lineSubharmonicOn_truncShift htop hl m)

/-- **Theorem 1.1** (`pshd-vibe`) by the article's argument, in the form of
plurisubharmonic germs.-/
theorem plurisubharmonicOn_of_line_sections_of_pshRepresentative [FiniteDimensional ℂ E]
    {φ : E → EReal} {Ω : Set E} (hΩ : IsOpen Ω) (htop : ∀ x ∈ Ω, φ x ≠ ⊤)
    (hl : ∀ c v : E, v ≠ 0 → ∀ z ∈ (fun t : ℂ ↦ c + t • v) ⁻¹' Ω,
      DiscPshOn (fun t ↦ φ (c + t • v)) (connectedComponentIn ((fun t : ℂ ↦ c + t • v) ⁻¹' Ω) z)) :
    UpperSemicontinuousOn φ Ω ∧ PlurisubharmonicOn φ Ω :=
  have h := discPshOn_of_line_sections_of_pshRepresentative hΩ htop hl
  ⟨h.upperSemicontinuousOn, h.plurisubharmonicOn hΩ⟩

end PshLines.PSHD
