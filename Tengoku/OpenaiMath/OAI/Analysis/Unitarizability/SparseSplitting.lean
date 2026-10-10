import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.EndpointAssignment
import Tengoku

namespace OAI

/-! Spectral norm bounds imply sparse endpoint assignments.
The input is a bounded convolution operator with its coefficient formula. -/
noncomputable section
namespace Dixmier
open Finset
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {G I : Type*} [Fintype I]

abbrev ScalarL2 (G : Type*) := lp (fun _ : G => ℂ) 2

def indicatorL2 (U : Finset G) : ScalarL2 G := ∑ x ∈ U, lp.single 2 x 1

@[simp] theorem indicatorL2_apply (U : Finset G) (x : G) :
    indicatorL2 U x = if x ∈ U then 1 else 0 := by
  change (∑ i ∈ U, lp.single 2 i (1 : ℂ)) x = _
  rw [lp.coeFn_sum]
  simp [Finset.sum_apply, lp.coeFn_single, Pi.single_apply]

variable [Group G]

def rectangleEdges (s : I → G) (U V : Finset G) : Finset (G × I) :=
  (U ×ˢ univ).filter fun e => e.1 * s e.2 ∈ V

/-- Every finite edge family lies in the rectangle of its endpoints. -/
theorem edges_subset_endpoint_rectangle (s : I → G) (F : Finset (G × I)) :
    F ⊆ rectangleEdges s (F.image Prod.fst) (F.image fun e => e.1 * s e.2) := by
  intro e he
  simp only [rectangleEdges, mem_filter, mem_product, mem_univ, and_true]
  exact ⟨mem_image.mpr ⟨e, he, rfl⟩, mem_image.mpr ⟨e, he, rfl⟩⟩

/-- Arithmetic used in the Hall argument, including its factor one half. -/
theorem sqrt_mul_le_half_add {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u * v) ≤ (u + v) / 2 := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [sq_nonneg (u - v)]

/-- The finite Hall density follows from the rectangular spectral estimate. -/
theorem endpoint_density_of_rectangle_bound (s : I → G) {q : ℝ} {r : ℕ}
    (hq : 0 ≤ q) (hqr : q ≤ r)
    (hrect : ∀ U V : Finset G, ((rectangleEdges s U V).card : ℝ) ≤
      q * Real.sqrt ((U.card : ℝ) * V.card))
    (F : Finset (G × I)) :
    F.card ≤ r * ((F.image Prod.fst).card + (F.image fun e => e.1 * s e.2).card) := by
  let U := F.image Prod.fst
  let V := F.image fun e => e.1 * s e.2
  have he : (F.card : ℝ) ≤ (rectangleEdges s U V).card := by
    exact_mod_cast card_le_card (edges_subset_endpoint_rectangle s F)
  have hsum : (0 : ℝ) ≤ (U.card : ℝ) + V.card := by positivity
  have hhalf : ((U.card : ℝ) + V.card) / 2 ≤ (U.card : ℝ) + V.card := by linarith
  have h : (F.card : ℝ) ≤ (r : ℝ) * ((U.card : ℝ) + V.card) := calc
    _ ≤ q * Real.sqrt ((U.card : ℝ) * V.card) := he.trans (hrect U V)
    _ ≤ q * (((U.card : ℝ) + V.card) / 2) :=
      mul_le_mul_of_nonneg_left (sqrt_mul_le_half_add (by positivity) (by positivity)) hq
    _ ≤ q * ((U.card : ℝ) + V.card) := mul_le_mul_of_nonneg_left hhalf hq
    _ ≤ (r : ℝ) * ((U.card : ℝ) + V.card) := mul_le_mul_of_nonneg_right hqr hsum
  exact_mod_cast h

end Dixmier

end

end OAI
