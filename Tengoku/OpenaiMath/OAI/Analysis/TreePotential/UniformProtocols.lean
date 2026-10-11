import Tengoku.OpenaiMath.OAI.Analysis.TreePotential.EndpointTransfer

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.BlockCalculus
open TreeCalculus

/-- Component trimming with constant 242. Empty heads and roots use the same literal
coordinate projection as in the outer sum. -/

theorem linear_block_trimming_242 {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x=x) (hy : head D y=0) :
    (linearBlockCost n y)^2≤242*((linearBlockCost n (x+y))^2+
      (linearBlockCost n (x-y))^2-2*(linearBlockCost n x)^2) := by
  have hh := linear_block_midpoint_sq hD x y hx
  rw [hy,sub_zero] at hh
  have he := scalar_midpoint_energy hh
  nlinarith [sq_nonneg (linearBlockCost n y)]

end BoundedTreePotentials.BlockCalculus

namespace BoundedTreePotentials.CostHeads
open _root_.OAI.BoundedTreePotentials.Dyadic

end BoundedTreePotentials.CostHeads

namespace BoundedTreePotentials.Dyadic
section ConditionalAverages
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Exact finite conditional expectation over k future fair bits. Histories
are chronological from the right, as in the energy theorems. -/
def conditionalMean (W : List Bool → E) : ℕ → List Bool → E
  | 0,w => W w
  | k+1,w => (1/2 : ℝ) • (conditionalMean W k (false::w)+conditionalMean W k (true::w))

end ConditionalAverages

end BoundedTreePotentials.Dyadic

end

end OAI
