import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfOrder_finite_sup_and_span_sup_eq_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfOrder_finite_sup_and_span_sup_eq_top

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w

open scoped TensorProduct

/--
@isnad1 id=and.1h5v.s10.1bcdd39a4536 from=translated src=- shape=17467f92 vocab=828818b9
-/
theorem solution
    {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] {S S' : Subalgebra R A}
    [Module.Finite R S] [Module.Finite R S'] (hspan : Submodule.span K (S : Set A) = ⊤) :
    Module.Finite R ↥(S ⊔ S') ∧ Submodule.span K ((S ⊔ S' : Subalgebra R A) : Set A) = ⊤ := by
  refine ⟨Subalgebra.finite_sup S S', ?_⟩
  refine eq_top_iff.mpr ?_
  rw [← hspan]
  exact Submodule.span_mono (fun x hx => (le_sup_left : S ≤ S ⊔ S') hx)
