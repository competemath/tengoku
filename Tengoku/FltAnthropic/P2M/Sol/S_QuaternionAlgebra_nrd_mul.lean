import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_QuaternionAlgebra_ReducedNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_QuaternionAlgebra_nrd_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_QuaternionAlgebra_nrd_mul
open scoped Quaternion
open QuaternionAlgebra

/--
@isnad1 id=eq.0h5v.s7.8d55e3ed23a4 from=translated src=- shape=6f03d6b0 vocab=73df06f5
-/
theorem solution {R : Type*} [CommRing R] {a b : R}
    (x y : ℍ[R, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [mk_mul_mk, nrd_mk]
  ring
