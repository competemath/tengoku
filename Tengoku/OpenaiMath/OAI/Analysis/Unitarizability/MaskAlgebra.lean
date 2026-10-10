import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.Masked
import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.SparseMask

namespace OAI

/-! Sparse masks yield operator conjugation identities, and the
constant mask has a rank-one collision kernel. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
open scoped ComplexConjugate
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq ℂ := Classical.decEq ℂ

def constant (v : I → Fibre K) (s : I → G) : Space G K →L[ℂ] Space G K :=
  operator v s (fun _ _ => 1) (fun _ _ => by simp)

theorem basis_inner_right (v : Fibre K) (b : K) :
    inner ℂ v (EuclideanSpace.basisFun K ℂ b) = conj (v b) := by
  rw [← EuclideanSpace.basisFun_inner K ℂ v b, inner_conj_symm]

omit [Group G] [Fintype I] in
theorem bool_mask_norm (a : G → I → Bool) (x : G) (i : I) : ‖boolComplex (a x i)‖ ≤ 1 := by
  cases a x i <;> simp [boolComplex]

def oriented (v : I → Fibre K) (s : I → G) (a : G → I → Bool) : Space G K →L[ℂ] Space G K :=
  operator v s (fun x i => boolComplex (a x i)) (bool_mask_norm a)

end Masked
end Dixmier

end

end OAI
