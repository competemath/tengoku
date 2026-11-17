import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Defs/VonNeumannRegular.lean
  Definition 9: Von Neumann regular ring.

  A ring R is von Neumann regular if for every a ∈ R there exists x ∈ R
  such that a * x * a = a.
-/

namespace TubalTensor

/-- **Definition 9**: A ring is *von Neumann regular* if for every element `a`,
    there exists an element `x` such that `a * x * a = a`.-/
class VonNeumannRegular (R : Type*) [Ring R] : Prop where
  vnr : ∀ a : R, ∃ x : R, a * x * a = a

end TubalTensor
