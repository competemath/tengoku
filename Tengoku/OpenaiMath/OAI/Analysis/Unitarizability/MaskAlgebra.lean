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

theorem operator_sub (v : I → Fibre K) (s : I → G) (c d : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (hd : ∀ x i, ‖d x i‖ ≤ 1)
    (hcd : ∀ x i, ‖c x i - d x i‖ ≤ 1) :
    operator v s c hc - operator v s d hd = operator v s (fun x i => c x i-d x i) hcd := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change operator v s c hc ξ x - operator v s d hd ξ x = _
  simp only [operator_apply, sub_mul, sub_smul, Finset.sum_sub_distrib]

theorem conjugate_operator (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (g : G) :
    conjugate KernelObstruction.translation g (operator v s c hc) =
      operator v s (fun x i => c (g⁻¹*x) i) (fun _ i => hc _ i) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change KernelObstruction.translation g (operator v s c hc (KernelObstruction.translation g⁻¹ ξ)) x = _
  simp only [KernelObstruction.translation_apply, operator_apply, inv_inv,
    ← mul_assoc, mul_inv_cancel, one_mul]

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

theorem difference_operator (v : I → Fibre K) (s : I → G) (a : G → I → Bool) (g : G) :
    coboundary KernelObstruction.translation (oriented v s a) g =
      operator v s (fun x i => boolComplex (a x i) - boolComplex (a (g⁻¹*x) i))
        (fun _ _ => difference_mask_norm _ _) := by
  rw [coboundary, oriented, conjugate_operator]
  exact operator_sub _ _ _ _ _ _ _

end Masked
end Dixmier

end

end OAI
