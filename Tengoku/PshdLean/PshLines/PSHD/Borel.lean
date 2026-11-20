import Tengoku.PshdLean.PshLines.PSHD.OpenBorel
import Tengoku.PshdLean.PshLines.PSHD.ComponentSections

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The Borel measurability lemma

Lemma 1.2 of `pshd-vibe`, in the project's planar disc-submean convention.
The horizontal space may be any second-countable metric space.
-/

open Set Metric MeasureTheory

namespace PshLines.PSHD

/-- Borel measurability from horizontal upper semicontinuity and
subharmonicity on every connected component of each vertical section.
@isnad1 id=measurab.4h3v.s8.483cf74d5427 from=translated src=- shape=3ef79d75 vocab=31627fe7
-/
theorem borel_measurable_of_sections
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    {G : Set (X × ℂ)} (hG : IsOpen G) {f : X → ℂ → ℝ}
    (husc : ∀ y, UpperSemicontinuousOn (fun x => f x y) {x | (x, y) ∈ G})
    (hpos : ∀ x y, (x, y) ∈ G → 0 ≤ f x y)
    (hsub : ∀ x y, (x, y) ∈ G → DiscPshOn (fun w => (f x w : EReal))
      (connectedComponentIn {w | (x, w) ∈ G} y)) :
    Measurable (fun p : G => f p.1.1 p.1.2) := by
  apply measurable_on_open_of_discPsh_sections hG husc hpos
  intro x
  apply discPshOn_of_connectedComponentIn
    (hG.preimage (continuous_const.prodMk continuous_id))
  exact hsub x

end PshLines.PSHD
