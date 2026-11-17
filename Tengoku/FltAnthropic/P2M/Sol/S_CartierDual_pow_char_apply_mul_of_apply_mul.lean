import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CartierDual_pow_char_apply_mul_of_apply_mul.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CartierDual_pow_char_apply_mul_of_apply_mul

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace CartierDual
export _root_.Tengoku.FltAnthropic.CartierDual (toDual toDual_apply one_apply comul_pairing tmul_eq_of_pairing_eq)
namespace FrobPrimC12
open _root_.Tengoku.FltAnthropic.CartierDual

variable {k : Type u} [CommRing k] {B : Type v} [CommRing B] [Bialgebra k B] [Module.Free k B] [Module.Finite k B]

private noncomputable def pair (x : CartierDual k B ⊗[k] CartierDual k B) : B ⊗[k] B →ₗ[k] k :=
  TensorProduct.dualDistrib k B B
    (TensorProduct.map (CartierDual.toDual k B).toLinearMap (CartierDual.toDual k B).toLinearMap x)

omit [Module.Free k B] [Module.Finite k B] in
private theorem pair_add (x y : CartierDual k B ⊗[k] CartierDual k B) : pair (x + y) = pair x + pair y := by
  simp only [pair, map_add]

omit [Module.Free k B] [Module.Finite k B] in
private theorem pair_tmul (φ ψ : CartierDual k B) (a b : B) : pair (φ ⊗ₜ[k] ψ) (a ⊗ₜ[k] b) = φ a * ψ b := by
  simp only [pair, TensorProduct.map_tmul, LinearEquiv.coe_toLinearMap, TensorProduct.dualDistrib_apply,
    CartierDual.toDual_apply]

private theorem comul_eq_of_apply_mul (δ : CartierDual k B)
    (hδ : ∀ a b : B, δ (a * b) = δ a * Coalgebra.counit (R := k) b + Coalgebra.counit (R := k) a * δ b) :
    Coalgebra.comul (R := k) δ = δ ⊗ₜ[k] (1 : CartierDual k B) + (1 : CartierDual k B) ⊗ₜ[k] δ := by
  refine CartierDual.tmul_eq_of_pairing_eq fun a b => ?_
  change pair (Coalgebra.comul (R := k) δ) (a ⊗ₜ[k] b) = pair (δ ⊗ₜ[k] 1 + 1 ⊗ₜ[k] δ) (a ⊗ₜ[k] b)
  rw [show pair (Coalgebra.comul (R := k) δ) (a ⊗ₜ[k] b) = δ (a * b) from CartierDual.comul_pairing δ a b,
    pair_add, LinearMap.add_apply, pair_tmul, pair_tmul, CartierDual.one_apply, CartierDual.one_apply, hδ]

private theorem apply_mul_of_comul_eq (δ : CartierDual k B)
    (h : Coalgebra.comul (R := k) δ = δ ⊗ₜ[k] (1 : CartierDual k B) + (1 : CartierDual k B) ⊗ₜ[k] δ) (a b : B) :
    δ (a * b) = δ a * Coalgebra.counit (R := k) b + Coalgebra.counit (R := k) a * δ b := by
  rw [← CartierDual.comul_pairing δ a b]
  change pair (Coalgebra.comul (R := k) δ) (a ⊗ₜ[k] b) = _
  rw [h, pair_add, LinearMap.add_apply, pair_tmul, pair_tmul, CartierDual.one_apply, CartierDual.one_apply]

end CartierDual.FrobPrimC12

theorem solution
    (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (B : Type v) [CommRing B] [Bialgebra k B] [Module.Free k B] [Module.Finite k B]
    (δ : CartierDual k B)
    (hδ : ∀ a b : B, δ (a * b) = δ a * Coalgebra.counit (R := k) b + Coalgebra.counit (R := k) a * δ b)
    (a b : B) :
    (δ ^ p) (a * b) = (δ ^ p) a * Coalgebra.counit (R := k) b + Coalgebra.counit (R := k) a * (δ ^ p) b := by
  classical
  have hpp : p.Prime := Fact.out
  have hprim := CartierDual.FrobPrimC12.comul_eq_of_apply_mul δ hδ
  apply CartierDual.FrobPrimC12.apply_mul_of_comul_eq

  have hcp : Coalgebra.comul (R := k) (δ ^ p) = (Coalgebra.comul (R := k) δ) ^ p := Bialgebra.comul_pow δ p
  rw [hcp, hprim]
  have hcomm : Commute (δ ⊗ₜ[k] (1 : CartierDual k B)) ((1 : CartierDual k B) ⊗ₜ[k] δ) := by
    change δ ⊗ₜ[k] (1 : CartierDual k B) * ((1 : CartierDual k B) ⊗ₜ[k] δ) =
      (1 : CartierDual k B) ⊗ₜ[k] δ * (δ ⊗ₜ[k] (1 : CartierDual k B))
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rcases subsingleton_or_nontrivial (CartierDual k B ⊗[k] CartierDual k B) with hs | hn
  · exact Subsingleton.elim _ _
  · haveI : CharP (CartierDual k B ⊗[k] CartierDual k B) p := by
      refine (CharP.charP_iff_prime_eq_zero hpp).2 ?_
      have h := map_natCast (algebraMap k (CartierDual k B ⊗[k] CartierDual k B)) p
      rw [CharP.cast_eq_zero, map_zero] at h
      exact h.symm
    have key := add_pow_char_of_commute (p := p) hcomm
    convert key using 2
    · exact ((Algebra.TensorProduct.tmul_pow δ (1 : CartierDual k B) p).trans (by rw [one_pow])).symm
    · exact ((Algebra.TensorProduct.tmul_pow (1 : CartierDual k B) δ p).trans (by rw [one_pow])).symm
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
