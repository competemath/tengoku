/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.CrystalBasis.KashiwaraOperators
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basic
import Tengoku.Seed.LinearAlgebra.Eigenspace.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tensor products of integrable `U_q(𝔰𝔩₂)`-modules

For integrable `U_q(𝔰𝔩₂)`-modules `M₁`, `M₂` (`QuantumGroup.IntegrableSl2`) we put an integrable
structure on `M₁ ⊗ M₂` (`QuantumGroup.IntegrableSl2.tensor`) by Kashiwara's coproduct
([Kas] §1.2):
`E = E ⊗ K⁻¹ + 1 ⊗ E`, `F = F ⊗ 1 + K ⊗ F`, `K = K ⊗ K`,
where `K` acts on `Mⁿ` by `qⁿ` (`QuantumGroup.IntegrableSl2.K`). The graded pieces of `M₁ ⊗ M₂`
are the eigenspaces of `K ⊗ K`.

The coproduct of `U = U_q(𝔤)` used in this library ([Lus] 3.1.4) is
`Δ E = E ⊗ 1 + K̃ ⊗ E`, `Δ F = F ⊗ K̃⁻¹ + 1 ⊗ F`; on `M₁ ⊗ M₂` it is Kashiwara's coproduct for the
parameter `q⁻¹` on `M₂ ⊗ M₁`, transported by the flip.

## Main definitions

* `IntegrableSl2.K`, `IntegrableSl2.Kinv`: `qⁿ` and `q⁻ⁿ` on `Mⁿ`.
* `IntegrableSl2.tensor`: the tensor product.

## Main results

* `IntegrableSl2.tensorE_tmul`, `IntegrableSl2.tensorF_tmul`: the action on `x ⊗ y`,
  `x ∈ M₁ᵃ`, `y ∈ M₂ᵇ`: `E (x ⊗ y) = q⁻ᵇ E x ⊗ y + x ⊗ E y`, `F (x ⊗ y) = F x ⊗ y + qᵃ x ⊗ F y`.
* `IntegrableSl2.tensor_dF_tmul`, `IntegrableSl2.tensor_dE_tmul`: the divided powers,
  `F^{(r)} (x ⊗ y) = Σ_{m+n=r} q^{na - mn} F^{(m)} x ⊗ F^{(n)} y` and
  `E^{(t)} (x ⊗ y) = Σ_{n+m=t} q^{-nb - nm} E^{(n)} x ⊗ E^{(m)} y` (cf. [Kas] (1.2)).
* `IntegrableSl2.tmul_mem_tensor_wt`: `x ⊗ y ∈ (M₁ ⊗ M₂)^{a+b}`.

## References

* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §1.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §3.1.
-/

open TensorProduct

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  (V : IntegrableSl2 q M)

/-! ### The operators `K`, `K⁻¹` -/

/-- `K` acts on `Mⁿ` by `qⁿ`.-/
noncomputable def K : Module.End k M :=
  DirectSum.toModule k ℤ M (fun n ↦ q ^ n • (V.wt n).subtype) ∘ₗ V.decompose.toLinearMap

/-- `K⁻¹` acts on `Mⁿ` by `q⁻ⁿ`.-/
noncomputable def Kinv : Module.End k M :=
  DirectSum.toModule k ℤ M (fun n ↦ q ^ (-n) • (V.wt n).subtype) ∘ₗ V.decompose.toLinearMap

variable {V}

/-! ### Linear maps out of a tensor product -/

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
  {V₁ : IntegrableSl2 q M₁} {V₂ : IntegrableSl2 q M₂}

/-! ### The operators on `M₁ ⊗ M₂` -/

variable (V₁ V₂)

/-- `E ⊗ K⁻¹ + 1 ⊗ E`.-/
noncomputable def tensorE : Module.End k (M₁ ⊗[k] M₂) := map V₁.E V₂.Kinv + map 1 V₂.E

/-- `F ⊗ 1 + K ⊗ F`.-/
noncomputable def tensorF : Module.End k (M₁ ⊗[k] M₂) := map V₁.F 1 + map V₁.K V₂.F

/-- `K ⊗ K`.-/
noncomputable def tensorK : Module.End k (M₁ ⊗[k] M₂) := map V₁.K V₂.K

/-- `K⁻¹ ⊗ K⁻¹`.-/
noncomputable def tensorKinv : Module.End k (M₁ ⊗[k] M₂) := map V₁.Kinv V₂.Kinv

variable {V₁ V₂}

section Tmul

variable {a b : ℤ} {x : M₁} {y : M₂} (hx : x ∈ V₁.wt a) (hy : y ∈ V₂.wt b)
include hx hy

end Tmul

/-! ### Commutation relations -/

section Relations

variable (V₁ V₂) (hq0 : q ≠ 0)
include hq0

end Relations

/-! ### The tensor product -/

section Structure

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)

include hq0 hq in
lemma zpow_injective : Function.Injective fun n : ℤ ↦ q ^ n := by
  intro m n h
  by_contra hne
  refine zpow_ne_one_of_pow_ne_one hq (sub_ne_zero.2 hne) ?_
  simp only at h
  rw [zpow_sub₀ hq0, h, div_self (zpow_ne_zero _ hq0)]

omit [Module k M] in
lemma pow_apply_eq_zero_of_le' {N : Type*} [AddCommGroup N] [Module k N] {f : Module.End k N}
    {x : N} {n m : ℕ} (h : (f ^ n) x = 0) (hnm : n ≤ m) : (f ^ m) x = 0 := by
  rw [← Nat.sub_add_cancel hnm, pow_add, Module.End.mul_apply, h, map_zero]

end Structure

/-! ### Divided powers on pure tensors -/

section DividedPowers

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)

end DividedPowers

end IntegrableSl2

end LieLean.QuantumGroup
