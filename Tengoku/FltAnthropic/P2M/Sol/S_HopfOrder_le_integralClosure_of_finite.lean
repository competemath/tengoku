import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfOrder_le_integralClosure_of_finite.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfOrder_le_integralClosure_of_finite

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w

open scoped TensorProduct

/--
@isnad1 id=le.0h3v.s7.ce3701b654d5 from=translated src=- shape=cdc3b500 vocab=ba532c6e
-/
theorem solution
    {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]
    (S : Subalgebra R A) [Module.Finite R S] : S ≤ integralClosure R A := by
  intro x hx
  rw [mem_integralClosure_iff]
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have h : IsIntegral R (⟨x, hx⟩ : S) := Algebra.IsIntegral.isIntegral _
  exact h.map S.val
