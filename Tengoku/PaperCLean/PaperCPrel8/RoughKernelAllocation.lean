import Tengoku.PaperCLean.PaperCPrel8.RoughKernelCRT
import Tengoku.PaperCLean.PaperC.Arithmetic.LargeOddKernel
import Tengoku.PaperCLean.PaperC.Probability.ArratiaGoldsteinGordonInput

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The CRT allocation probability for the actual odd rough kernel

Uniform sampling on the Cartesian grid is the law of independent uniform
indices, including zero target blocks. The source vertex is fixed.
-/
namespace PaperC.Prel8.RoughKernelAllocation
open Finset RoughKernelCRT LargeOddKernel ArratiaGoldsteinGordonInput
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Uniform finite-set probabilities are exact normalized event cardinalities.
@isnad1 id=eq.0h3v.s7.658cd864a0b7 from=translated src=- shape=af8a99b9 vocab=7e6e25cd
-/
theorem uniform_finset_probability {α : Type*} (S : Finset α) [Nonempty S] (P : α → Prop) :
    eventProbability (FinitePMF.uniform S) (fun x ↦ P x.val) =
      ((S.filter P).card : ℝ) / S.card := by
  classical
  unfold eventProbability
  simp only [FinitePMF.uniform_prob,Fintype.card_coe]
  rw [← sum_subtype S (fun _ ↦ Iff.rfl) (fun x : α ↦ if P x then (S.card:ℝ)⁻¹ else 0),← sum_filter]
  simp [div_eq_mul_inv]

def grid (n h : ℕ) : Finset (Fin h → ℕ) := Fintype.piFinset (fun _ ↦ Icc 1 n)

/-- The sampling grid has n^h equally likely points.
@isnad1 id=eq.0h2v.s4.b58609e4c6f6 from=translated src=- shape=f0344caf vocab=fbcd6c5a
-/
theorem grid_card (n h : ℕ) : (grid n h).card = n^h := by
  simp [grid,Fintype.card_piFinset,Nat.card_Icc]

/-- Independent uniform target indices on {1,...,n}.-/
def gridLaw (n h : ℕ) (hn : 0 < n) : FinitePMF (grid n h) := by
  letI : Nonempty (grid n h) := ⟨⟨(fun _ ↦ 1),by simp [grid,Fintype.mem_piFinset]; omega⟩⟩
  exact FinitePMF.uniform _

end
end PaperC.Prel8.RoughKernelAllocation
