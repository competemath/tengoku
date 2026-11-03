import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowComponentEquivalence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameSeed.first_components_sum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameSeed.first_component_trace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameSeed.seed_componentSolution` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameSeed.seed_matrices_distinct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameSeed.componentSolution_iff` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# An exact two-solution fibre of the matrix-component system

Over a characteristic-zero field containing a root `z` of `z²+z+1`, take all
three fixed first components to be `I/3`.  The complete normalized component
system on the reconstruction open has precisely the two solutions `zI,z²I`.
The reverse equivalence supplies the raw inverse-adjugate equations, avoiding
a second proof of inverse cancellation.  This is a matrix-system fibre, not
an Albert frame, an automorphism orbit, or a generic-degree assertion.
-/

noncomputable section
namespace AlbertLean.Generic.FourRowFrameSeed

open FourRowComponents
open FourRowUniqueness (GoodSolution reconstructionDenominator)

variable {K : Type*} [Field K]
abbrev Mat3 (K : Type*) := Matrix (Fin 3) (Fin 3) K

def a : Mat3 K := (1 / 3 : K) • 1
def X (r : K) : Mat3 K := r • 1

theorem root_cube (z : K) (hz : z ^ 2 + z + 1 = 0) : z ^ 3 = 1 := by
  linear_combination (z - 1) * hz

theorem root_square_equation (z : K) (hz : z ^ 2 + z + 1 = 0) :
    (z ^ 2) ^ 2 + z ^ 2 + 1 = 0 := by
  linear_combination (z ^ 2 - z + 1) * hz

variable [CharZero K]

theorem a_det_ne_zero : (a : Mat3 K).det ≠ 0 := by
  rw [a, Matrix.det_smul]
  norm_num

theorem first_components_sum : (a : Mat3 K) + a + a = 1 := by
  dsimp [a]
  module

theorem first_component_trace : Matrix.trace (a : Mat3 K) = 1 := by
  simp [a, Matrix.trace_smul, Matrix.trace_one]

/-- The fixed first components give `U=V=I`.-/
theorem component_parameters :
    componentU (a : Mat3 K) a a = 1 ∧ componentV (a : Mat3 K) a = 1 := by
  have hadj : (a : Mat3 K).adjugate.det ≠ 0 := by
    rw [Matrix.det_adjugate]
    exact pow_ne_zero 2 a_det_ne_zero
  constructor <;>
    simp only [componentU, componentV, FourRowFrameReduction.frameU,
      FourRowFrameReduction.frameV, add_sub_cancel_right,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hadj)]

/-- A cyclotomic root gives a good quadratic solution at the fixed parameters.-/
theorem seed_goodSolution (z : K) (hz : z ^ 2 + z + 1 = 0) :
    GoodSolution (1 : Mat3 K) 1 1 1 (X z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm : (X z) ^ 2 + X z * 1 + 1 = (z ^ 2 + z + 1) • (1 : Mat3 K) := by
      simp only [X, pow_two, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
        smul_smul, add_smul, one_smul]
    rw [hm, hz, zero_smul]
  · rw [X, Matrix.det_smul]
    simpa only [Fintype.card_fin, Matrix.det_one, mul_one] using root_cube z hz
  · have hm : (1 : Mat3 K) + X z = (1 + z) • 1 := by simp [X, add_smul]
    rw [hm, Matrix.det_smul]
    simp only [Fintype.card_fin, Matrix.det_one, mul_one]
    linear_combination (z + 2) * hz
  · have hden : reconstructionDenominator (1 : Mat3 K) 1 1 1 (Matrix.trace (X z)) =
        (-3 : K) • 1 := by
      simp only [reconstructionDenominator, one_pow, sub_self, zero_add]
      module
    rw [hden, Matrix.det_smul]
    norm_num

/-- The good solution reconstructs all raw component equations.-/
theorem seed_componentSolution (z : K) (hz : z ^ 2 + z + 1 = 0) :
    ComponentSolution a a a (X z) := by
  apply FourRowComponentEquivalence.components_of_goodSolution
    a a a (X z) a_det_ne_zero a_det_ne_zero a_det_ne_zero
  rw [component_parameters.1, component_parameters.2, div_self a_det_ne_zero]
  exact seed_goodSolution z hz

theorem seed_matrices_distinct (z : K) (hz : z ^ 2 + z + 1 = 0) :
    X z ≠ X (z ^ 2) := by
  intro h
  have heq : z = z ^ 2 := by
    simpa [X] using congrFun (congrFun h 0) 0
  have hprod : z * (z - 1) = 0 := by
    calc
      z * (z - 1) = z ^ 2 - z := by ring
      _ = 0 := sub_eq_zero.mpr heq.symm
  rcases mul_eq_zero.mp hprod with hz0 | hsub
  · rw [hz0] at hz
    norm_num at hz
  · rw [sub_eq_zero.mp hsub] at hz
    norm_num at hz

/-- Exact classification of this component fibre: both branches exist and
there are no others on the stated reconstruction open.-/
theorem componentSolution_iff (z : K) (hz : z ^ 2 + z + 1 = 0) (W : Mat3 K) :
    ComponentSolution a a a W ↔ W = X z ∨ W = X (z ^ 2) := by
  have hx := seed_componentSolution z hz
  have hy := seed_componentSolution (z ^ 2) (root_square_equation z hz)
  constructor
  · intro hw
    rcases three_componentSolutions_pairwise_eq a a a
        a_det_ne_zero a_det_ne_zero a_det_ne_zero W (X z) (X (z ^ 2)) hw hx hy
        with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (seed_matrices_distinct z hz h).elim
  · rintro (rfl | rfl)
    · exact hx
    · exact hy

end AlbertLean.Generic.FourRowFrameSeed
