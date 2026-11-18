import Tengoku.Seed.LinearAlgebra.Basis.Defs
import Tengoku.Seed.RingTheory.Ideal.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_Basis_repr_apply_mem_of_mem_ideal_smul_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_Basis_repr_apply_mem_of_mem_ideal_smul_top

/--
@isnad1 id=mem.1h7v.s9.63b449cdc1b6 from=translated src=- shape=c656f6f0 vocab=fb39062b
-/
theorem solution {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] {κ : Type*} (b : Module.Basis κ R N) (I : Ideal R) {x : N} (hx : x ∈ (I • ⊤ : Submodule R N)) (k : κ) :
    b.repr x k ∈ I := by
  refine Submodule.smul_induction_on hx (fun a ha n _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ ha
  · rw [map_add, Finsupp.add_apply]
    exact I.add_mem hx hy
