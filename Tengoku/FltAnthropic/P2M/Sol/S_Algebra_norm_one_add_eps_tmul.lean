import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_norm_one_add_eps_tmul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_norm_one_add_eps_tmul

set_option autoImplicit false

universe u

open scoped TensorProduct

/--
@isnad1 id=eq.0h3v.s11.2fb577fd06c8 from=translated src=- shape=7d1b97c1 vocab=c0b7f49a
-/
theorem solution
    (A' B : Type u) [CommRing A'] [CommRing B] [Algebra A' B] [Module.Free A' B] [Module.Finite A' B] (f : B) :
    Algebra.norm (DualNumber A') ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f) =
      1 + TrivSqZeroExt.inr (Algebra.trace A' B f) := by
  classical
  let b := Module.Free.chooseBasis A' B
  let b' : Module.Basis (Module.Free.ChooseBasisIndex A' B) (DualNumber A') (DualNumber A' ⊗[A'] B) :=
    Algebra.TensorProduct.basis (DualNumber A') b
  have hM : ∀ g : B, Algebra.leftMulMatrix b' ((1 : DualNumber A') ⊗ₜ[A'] g)
      = (Algebra.leftMulMatrix b g).map (algebraMap A' (DualNumber A')) := by
    intro g
    have hlmul : Algebra.lmul (DualNumber A') (DualNumber A' ⊗[A'] B) ((1 : DualNumber A') ⊗ₜ[A'] g)
        = (Algebra.lmul A' B g).baseChange (DualNumber A') := by
      apply b'.ext
      intro k
      simp [b', Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
    rw [Algebra.leftMulMatrix_apply, hlmul, LinearMap.toMatrix_baseChange, Algebra.leftMulMatrix_apply]
  have hone : Algebra.leftMulMatrix (R := DualNumber A') (S := DualNumber A' ⊗[A'] B) b' 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, hM 1, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f
      = (DualNumber.eps : DualNumber A') • ((1 : DualNumber A') ⊗ₜ[A'] f) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hadd : Algebra.leftMulMatrix b' ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f)
      = 1 + (DualNumber.eps : DualNumber A') • (Algebra.leftMulMatrix b f).map (algebraMap A' (DualNumber A')) := by
    rw [h1]
    simp only [map_add, map_smul, hone, hM]
  rw [Algebra.norm_eq_matrix_det b', hadd, Matrix.det_one_add_smul,
    pow_two, DualNumber.eps_mul_eps, mul_zero, add_zero,
    ← AddMonoidHom.map_trace (algebraMap A' (DualNumber A')), ← Algebra.trace_eq_matrix_trace b f,
    DualNumber.inr_eq_smul_eps, Algebra.smul_def]
