import Tengoku.Seed.LinearAlgebra.Charpoly.ToMatrix
import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.Coeff
import Tengoku.Seed.LinearAlgebra.Trace
import Tengoku.Seed.LinearAlgebra.Determinant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LinearMap_charpoly_of_finrank_eq_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LinearMap_charpoly_of_finrank_eq_two

open Polynomial

theorem solution {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) : f.charpoly = X ^ 2 - C (LinearMap.trace R M f) * X + C (LinearMap.det f) := by
  let b := Module.finBasisOfFinrankEq R M h
  rw [← f.charpoly_toMatrix b, Matrix.charpoly_fin_two, ← LinearMap.trace_eq_matrix_trace R b f,
    LinearMap.det_toMatrix b f]
