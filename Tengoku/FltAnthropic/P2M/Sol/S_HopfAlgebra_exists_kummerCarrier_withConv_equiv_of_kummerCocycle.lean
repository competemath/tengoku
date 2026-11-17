import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_exists_kummerCarrier_withConv_equiv_of_kummerCocycle.lean`: wrote out 10 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 5 `p2m_export`, 5 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_exists_kummerCarrier_withConv_equiv_of_kummerCocycle

set_option autoImplicit false

open scoped TensorProduct
open Polynomial

namespace HopfAlgebra
export _root_.HopfAlgebra (mk ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul)
open _root_.HopfAlgebra

universe u v

structure KummerDatum (O : Type u) [CommRing O] (n : ℕ) (Λ : Type v) [AddCommGroup Λ] where

  u : Λ → O

  c : Λ → Λ → O
  isUnit_u : ∀ l, IsUnit (u l)
  u_zero : u 0 = 1
  c_pow_mul : ∀ l l', c l l' ^ n * (u l * u l') = u (l + l')
  c_zero_left : ∀ l, c 0 l = 1
  c_comm : ∀ l l', c l l' = c l' l
  c_assoc : ∀ l l' l'', c l l' * c (l + l') l'' = c l (l' + l'') * c l' l''

namespace KummerDatum

variable {O : Type u} [CommRing O] {n : ℕ} {Λ : Type v} [AddCommGroup Λ]
variable (D : KummerDatum O n Λ)

theorem c_zero_right (l : Λ) : D.c l 0 = 1 := by rw [D.c_comm, D.c_zero_left]

variable [Fintype Λ] [DecidableEq Λ]

variable {L : Type*} [CommRing L] [Algebra O L]

end KummerDatum

end HopfAlgebra

namespace HopfAlgebra
export _root_.HopfAlgebra (mk ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul)
open _root_.HopfAlgebra

open scoped TensorProduct
open Polynomial

universe u v
variable {O : Type u} [CommRing O] {n : ℕ} {Λ : Type u} [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ]
  (D : KummerDatum O n Λ)

end HopfAlgebra

namespace HopfAlgebra
export _root_.HopfAlgebra (mk ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul)
open _root_.HopfAlgebra

open scoped TensorProduct
open Polynomial

universe u v
variable {O : Type u} [CommRing O] {n : ℕ} {Λ : Type u} [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ]
  (D : KummerDatum O n Λ)

end HopfAlgebra

namespace HopfAlgebra
export _root_.HopfAlgebra (mk ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul)
open _root_.HopfAlgebra

open scoped TensorProduct
open Polynomial

universe u v
variable {O : Type u} [CommRing O] {n : ℕ} {Λ : Type u} [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ]
  (D : KummerDatum O n Λ)

end HopfAlgebra

namespace HopfAlgebra
export _root_.HopfAlgebra (mk ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul)
open _root_.HopfAlgebra

open scoped TensorProduct
open Polynomial

universe u v
variable {O : Type u} [CommRing O] {n : ℕ} {Λ : Type u} [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ]
  (D : KummerDatum O n Λ)

end HopfAlgebra
