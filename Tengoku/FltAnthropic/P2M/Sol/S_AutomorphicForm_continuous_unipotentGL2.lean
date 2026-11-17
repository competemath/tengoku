import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_continuous_unipotentGL2.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_continuous_unipotentGL2

open AutomorphicForm

namespace M4aP3B
namespace CTU

variable {R : Type*} [CommRing R]

/--
@isnad1 id=eq.0h2v.s7.d24fd74a1f32 from=translated src=- shape=4fb0e637 vocab=420e4e4a
-/
theorem unipotentGL2_inv (x : R) : (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

end M4aP3B.CTU

/--
@isnad1 id=continuo.0h1v.s7.a9a7b0a1ab84 from=translated src=- shape=a8f35fde vocab=49462922
-/
theorem solution {R : Type*} [CommRing R] [TopologicalSpace R]
    [ContinuousNeg R] : Continuous fun x : R => AutomorphicForm.unipotentGL2 x := by
  have hval : Continuous fun x : R =>
      ((AutomorphicForm.unipotentGL2 x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    refine continuous_matrix fun i j => ?_
    simp only [AutomorphicForm.unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp only [M4aP3B.CTU.unipotentGL2_inv]
  exact hval.comp continuous_neg

