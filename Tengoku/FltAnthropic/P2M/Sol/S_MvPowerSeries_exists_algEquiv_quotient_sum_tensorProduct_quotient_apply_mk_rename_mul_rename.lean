import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_exists_algEquiv_quotient_sum_tensorProduct_quotient_apply_mk_rename_mul_rename.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_exists_algEquiv_quotient_sum_tensorProduct_quotient_apply_mk_rename_mul_rename

set_option autoImplicit false

universe u v w x

open scoped TensorProduct
open Finsupp

noncomputable section

namespace TQ

section Curry

variable {σ τ : Type v} {R : Type u} [CommRing R]

def curryFun (f : MvPowerSeries (σ ⊕ τ) R) : MvPowerSeries σ (MvPowerSeries τ R) :=
  fun d₁ d₂ => f (d₁.sumElim d₂)

def uncurryFun (g : MvPowerSeries σ (MvPowerSeries τ R)) : MvPowerSeries (σ ⊕ τ) R :=
  fun d => g (d.comapDomain Sum.inl Sum.inl_injective.injOn) (d.comapDomain Sum.inr Sum.inr_injective.injOn)

omit [CommRing R] in
theorem uncurryFun_curryFun [CommRing R] (f : MvPowerSeries (σ ⊕ τ) R) : uncurryFun (curryFun f) = f := by
  funext d
  change f (sumElim (d.comapDomain Sum.inl Sum.inl_injective.injOn) (d.comapDomain Sum.inr Sum.inr_injective.injOn)) = f d
  rw [comapDomain_sumElim_comapDomain]

theorem curryFun_uncurryFun (g : MvPowerSeries σ (MvPowerSeries τ R)) : curryFun (uncurryFun g) = g := by
  funext d₁ d₂
  change g ((d₁.sumElim d₂).comapDomain Sum.inl Sum.inl_injective.injOn) ((d₁.sumElim d₂).comapDomain Sum.inr Sum.inr_injective.injOn) = g d₁ d₂
  rw [comapDomain_inl_sumElim, comapDomain_inr_sumElim]

def curryLinearEquiv : MvPowerSeries (σ ⊕ τ) R ≃ₗ[R] MvPowerSeries σ (MvPowerSeries τ R) where
  toFun := curryFun
  invFun := uncurryFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := uncurryFun_curryFun
  right_inv := curryFun_uncurryFun

end Curry

namespace Eng
open MvPowerSeries

section L0

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R]

end L0

section Bridges

variable {σ : Type w} {R : Type u} [CommRing R]

end Bridges

end Eng

section ModCoeff

variable {S : Type u} [CommRing S] {σ : Type v} {ι : Type w} [Fintype ι]
  {A : Type x} [CommRing A] [Algebra S A] (φ : ι → A)

end ModCoeff

end TQ
