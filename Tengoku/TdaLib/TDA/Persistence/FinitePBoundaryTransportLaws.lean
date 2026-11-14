import Tengoku.TdaLib.TDA.Persistence.FinitePBoundaryTransport
import Tengoku.TdaLib.TDA.Persistence.FinitePMatchingCostLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Distance laws of finite real boundary transport

The rooted optimum over all feasible real reservoir matrices equals the finite
matching optimum. Its self, symmetry, triangle and positive-lifetime separation
laws therefore follow from the matching laws, without assuming an integral plan
or identifying all Borel/Radon couplings. Zero cost identifies occurrence values
with multiplicity, allowing arbitrary changes of labels.
-/

namespace TDA.Persistence

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/--
@isnad1 id=eq.1h3v.s5.0a79698f6793 from=translated src=- shape=1936145e vocab=4273cd30
-/
@[simp] theorem finitePBoundaryTransportCost_self {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) : finitePBoundaryTransportCost p x x = 0 := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_self hp x

/-- Symmetry holds for the supporting algebra at every real exponent.
@isnad1 id=eq.0h5v.s5.9e7a1cea3b06 from=translated src=- shape=1701ac39 vocab=83cedc36
-/
theorem finitePBoundaryTransportCost_comm (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = finitePBoundaryTransportCost p y x := by
  simp only [finitePBoundaryTransportCost_eq_matchingCost, finitePMatchingCost_comm p x y]

/-- The sharp rooted triangle law transfers through the proved finite-plan equality.
@isnad1 id=le.1h7v.s6.672920ba8673 from=translated src=- shape=8e9d1e7e vocab=f554869d
-/
theorem finitePBoundaryTransportCost_triangle {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (z : K → ℝ × ℝ) :
    finitePBoundaryTransportCost p x z ≤
      finitePBoundaryTransportCost p x y + finitePBoundaryTransportCost p y z := by
  simp only [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_triangle hp x y z

/--
@isnad1 id=eq.2h6v.s6.56250cb67e51 from=translated src=- shape=e0427b73 vocab=3fb4045d
-/
theorem finitePBoundaryTransportCost_eq_zero_of_equiv {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (e : I ≃ J) (he : ∀ i, x i = y (e i)) :
    finitePBoundaryTransportCost p x y = 0 := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_eq_zero_of_equiv hp x y e he

/-- Positive lifetimes exclude free deletion of diagonal occurrences.
@isnad1 id=iff.3h5v.s6.95d21fd18e6b from=translated src=- shape=286c105c vocab=a15d8312
-/
theorem finitePBoundaryTransportCost_eq_zero_iff {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    finitePBoundaryTransportCost p x y = 0 ↔ ∃ e : I ≃ J, ∀ i, x i = y (e i) := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_eq_zero_iff hp x y hx hy

end TDA.Persistence
