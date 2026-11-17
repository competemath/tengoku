import Tengoku.PaperCLean.PaperCPrel8.RoughKernelAllocation
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Converting the all-prime CRT weight to a threshold power

Every prime of the odd rough kernel lies above the unchanged small-prime
cutoff. This is a product estimate, not a largest-prime estimate.
-/
namespace PaperC.Prel8.RoughKernelExponent
open Finset LargeOddKernel RoughKernelAllocation ArratiaGoldsteinGordonInput
noncomputable section

/-- The number of prime factors is controlled by the logarithm of their product.-/
theorem card_log_le (Y m : ℕ) (hY : 1 < Y) :
    ((largeOddPrimeSupport Y m).card : ℝ)*Real.log Y ≤ Real.log (largeOddKernel Y m) := by
  have hp (p : ℕ) (h : p ∈ largeOddPrimeSupport Y m) : 0 < (p:ℝ) := by
    exact_mod_cast (prime_and_large_of_mem_largeOddPrimeSupport h).1.pos
  simp only [largeOddKernel,Nat.cast_prod,id_eq]
  rw [Real.log_prod (fun p h ↦ (hp p h).ne')]
  calc
    _ = ∑ p ∈ largeOddPrimeSupport Y m, Real.log Y := by simp
    _ ≤ _ := sum_le_sum (fun p h ↦ Real.log_le_log (by exact_mod_cast (show 0<Y by omega))
      (by exact_mod_cast (prime_and_large_of_mem_largeOddPrimeSupport h).2.le))

end
end PaperC.Prel8.RoughKernelExponent
