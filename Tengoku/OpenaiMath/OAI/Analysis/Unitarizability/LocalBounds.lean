import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.MaskAlgebra

namespace OAI

/-! Individual block row and column bounds from the endpoint assignment. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq ℂ := Classical.decEq ℂ

def rowMask (a : G → I → Bool) (x₀ x : G) (i : I) : ℂ :=
  if x = x₀ then boolComplex (a x i) else 0

def columnMask (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I) : ℂ :=
  if x * s i = y₀ then 1 - boolComplex (a x i) else 0

omit [Group G] [Fintype I] in
theorem rowMask_norm (a : G → I → Bool) (x₀ x : G) (i : I) : ‖rowMask a x₀ x i‖ ≤ 1 := by
  unfold rowMask
  split_ifs
  · exact bool_mask_norm a x i
  · simp

omit [Group G] [Fintype I] in
theorem complement_norm (a : G → I → Bool) (x : G) (i : I) : ‖1 - boolComplex (a x i)‖ ≤ 1 := by
  cases a x i <;> simp [boolComplex]

omit [Fintype I] in
theorem columnMask_norm (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I) :
    ‖columnMask a s y₀ x i‖ ≤ 1 := by
  unfold columnMask
  split_ifs
  · exact complement_norm a x i
  · simp

omit [Group G] in
theorem rowMask_support (a : G → I → Bool) (x₀ x : G) (i : I) (h : rowMask a x₀ x i ≠ 0) :
    i ∈ rowOnes a x₀ := by
  unfold rowMask at h
  split_ifs at h with he
  · subst x
    cases ha : a x₀ i <;> simp_all [boolComplex, rowOnes]
  · exact (h rfl).elim

theorem columnMask_support (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I)
    (h : columnMask a s y₀ x i ≠ 0) : i ∈ columnZeros a s y₀ := by
  unfold columnMask at h
  split_ifs at h with he
  · have hx : y₀ * (s i)⁻¹ = x := by rw [← he, mul_inv_cancel_right]
    cases ha : a x i <;> simp_all [boolComplex, columnZeros]
  · exact (h rfl).elim

end Masked
end Dixmier

end

end OAI
