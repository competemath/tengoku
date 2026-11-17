import Tengoku.Seed.RingTheory.TensorProduct.Basic
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basis
import Tengoku.Seed.LinearAlgebra.LinearIndependent.Basic
import Tengoku.Seed.Algebra.Algebra.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars

open scoped TensorProduct

theorem solution
    (R : Type) (K : Type) (A : Type) [CommRing R] [CommRing K] [Algebra R K] [CommRing A]
    [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (hinj : Function.Injective (algebraMap R K))
    {n : ℕ} (b : Module.Basis (Fin n) K A) :
    LinearIndependent R ((b.tensorProduct (b.tensorProduct b)) :
      Fin n × Fin n × Fin n → A ⊗[K] (A ⊗[K] A)) :=
  (b.tensorProduct (b.tensorProduct b)).linearIndependent.restrict_scalars
    (Algebra.algebraMap_eq_smul_one' (R := R) (A := K) ▸ hinj)
