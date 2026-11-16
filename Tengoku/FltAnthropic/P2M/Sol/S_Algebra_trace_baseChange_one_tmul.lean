import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_trace_baseChange_one_tmul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_trace_baseChange_one_tmul

open scoped TensorProduct

namespace Ws10Flat

section
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (S : Type*) [CommRing S] [Algebra A S]

theorem trace_baseChange_one_tmul [Module.Free A B] [Module.Finite A B] (x : B) :
    Algebra.trace S (S ⊗[A] B) (1 ⊗ₜ x) = algebraMap A S (Algebra.trace A B x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  refine TensorProduct.AlgebraTensorModule.ext fun s y => ?_
  change (1 ⊗ₜ[A] x) * (s ⊗ₜ[A] y) = LinearMap.baseChange S (Algebra.lmul A B x) (s ⊗ₜ[A] y)
  rw [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

end

end Ws10Flat

theorem solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (S : Type*) [CommRing S] [Algebra A S]
    [Module.Free A B] [Module.Finite A B] (x : B) :
    Algebra.trace S (TensorProduct A S B) (1 ⊗ₜ[A] x) = algebraMap A S (Algebra.trace A B x) :=
  Ws10Flat.trace_baseChange_one_tmul S x
