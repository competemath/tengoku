import Tengoku.SingularityCompleteLean.Singularity.RelativeBoundaryComparison
import Tengoku.SingularityCompleteLean.Singularity.StripSeparation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded-jump coordinate barriers

A coordinate changing by at most L in one jump cannot cross a closed layer
of width L without visiting it. A layer separated from a lower stopping set
also intercepts every first entrance into that set, including its final jump.
-/

noncomputable section
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- A closed layer of one-jump width separates its strict opposite sides.-/
theorem bounded_coordinate_layer_separates (s : Finset Γ) (h : Γ → ℝ) (L t : ℝ)
    (hL : 0 ≤ L)
    (hjump : ∀ x : Γ, ∀ g ∈ s, |h (x*g) - h x| ≤ L)
    (D : Set Γ) (hcover : ∀ x, t ≤ h x → h x ≤ t + L → x ∈ D)
    (x y : Γ) (hx : t + L < h x) (hy : h y < t) :
    SeparatesJumpPaths s D x y := by
  apply separatesJumpPaths_of_invariant_side s D {z | t + L < h z}
    ?_ x y hx ?_
  · intro z g hg _hz hznext hzside
    change t + L < h z at hzside
    change t + L < h (z*g)
    have hb := (abs_le.mp (hjump z g hg)).1
    by_contra! hn
    exact hznext (hcover (z*g) (by linarith) hn)
  · change ¬ t + L < h y
    linarith

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]

end Singularity
