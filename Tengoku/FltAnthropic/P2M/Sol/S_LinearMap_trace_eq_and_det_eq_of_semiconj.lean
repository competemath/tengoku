import Tengoku.Seed.LinearAlgebra.Trace
import Tengoku.Seed.LinearAlgebra.Determinant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LinearMap_trace_eq_and_det_eq_of_semiconj.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LinearMap_trace_eq_and_det_eq_of_semiconj

/--
@isnad1 id=and.1h6v.s10.4fc57a925ce0 from=translated src=- shape=4f9d8708 vocab=4863ee76
-/
theorem solution {R : Type*} {M : Type*} {N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (f : Module.End R M) (g : Module.End R N) (h : ∀ x : M, e (f x) = g (e x)) : LinearMap.trace R M f = LinearMap.trace R N g ∧ LinearMap.det f = LinearMap.det g := by
  have hg : g = e.conj f := by
    ext y
    rw [LinearEquiv.conj_apply]
    simp [h]
  subst hg
  exact ⟨(LinearMap.trace_conj' f e).symm, (LinearMap.det_conj f e).symm⟩
