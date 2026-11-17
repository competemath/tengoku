import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_ModpRealization
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualInstances

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open Function Tengoku.FltAnthropic.CartierDual

universe u v

namespace HopfAlgebra
namespace FrobeniusUntwist
open _root_.HopfAlgebra

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

/--
@isnad1 id=eq.0h4v.s12.7c621f00eb92 from=translated src=- shape=6f1f6778 vocab=9b4357ee
-/
theorem toDual_pow (φ : CartierDual k A) (m : ℕ) :
    CartierDual.toDual k A (φ ^ m) = (WithConv.toConv (CartierDual.toDual k A φ) ^ m).ofConv := by
  induction m with
  | zero =>
    refine LinearMap.ext fun a => ?_
    rw [pow_zero, pow_zero, LinearMap.convOne_apply, Algebra.algebraMap_self_apply]
    exact CartierDual.one_apply a
  | succ m ih =>
    rw [pow_succ, CartierDual.toDual_mul, ih, WithConv.toConv_ofConv, ← pow_succ]

/--
@isnad1 id=eq.0h5v.s11.1234a1cb3146 from=translated src=- shape=2cc42d3e vocab=2fb316d6
-/
theorem convPow_apply (β : WithConv (A →ₗ[k] k)) (m : ℕ) (x : A) :
    (β ^ m).ofConv x = ((CartierDual.ofDual k A β.ofConv) ^ m) x := by
  have : (β ^ m).ofConv = CartierDual.toDual k A ((CartierDual.ofDual k A β.ofConv) ^ m) := by
    rw [toDual_pow, CartierDual.toDual_ofDual, WithConv.toConv_ofConv]
  rw [this]; rfl

/--
@isnad1 id=eq.0h6v.s12.901641eca639 from=translated src=- shape=dc032c48 vocab=044cdef0
-/
theorem convPow_mul_convPow_apply (β γ : WithConv (A →ₗ[k] k)) (m : ℕ) (x : A) :
    (β ^ m * γ ^ m).ofConv x =
      ((CartierDual.ofDual k A β.ofConv) ^ m * (CartierDual.ofDual k A γ.ofConv) ^ m) x := by
  have : β ^ m * γ ^ m = WithConv.toConv (CartierDual.toDual k A
      ((CartierDual.ofDual k A β.ofConv) ^ m * (CartierDual.ofDual k A γ.ofConv) ^ m)) := by
    rw [CartierDual.toDual_mul, toDual_pow, toDual_pow, CartierDual.toDual_ofDual,
      CartierDual.toDual_ofDual, WithConv.toConv_ofConv, WithConv.toConv_ofConv,
      WithConv.toConv_ofConv]
  rw [this]; rfl

/--
@isnad1 id=eq.0h4v.s9.8b20bbe8b729 from=translated src=- shape=2f2d8564 vocab=60d1b816
-/
theorem mul_apply_one (φ ψ : CartierDual k A) : (φ * ψ) 1 = φ 1 * ψ 1 := by
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply]
  rfl

/--
@isnad1 id=eq.0h4v.s9.7cfd5af8135a from=translated src=- shape=c73e2f02 vocab=c5abb4ed
-/
theorem pow_apply_one (φ : CartierDual k A) (m : ℕ) : (φ ^ m) 1 = (φ 1) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, CartierDual.one_apply, Bialgebra.counit_one]
  | succ m ih => rw [pow_succ, mul_apply_one, ih, pow_succ]

/--
@isnad1 id=eq.0h5v.s9.a34a38020c46 from=translated src=- shape=30c9c7fe vocab=65e1b8e8
-/
theorem smul_apply' (c : k) (φ : CartierDual k A) (x : A) : (c • φ) x = c * φ x := rfl

/--
@isnad1 id=eq.0h5v.s9.22837abf8735 from=translated src=- shape=03625dd4 vocab=27dde2ac
-/
theorem add_apply' (φ ψ : CartierDual k A) (x : A) : (φ + ψ) x = φ x + ψ x := rfl

/--
@isnad1 id=injectiv.0h2v.s9.4a8c7faee3d3 from=translated src=- shape=497db901 vocab=729f7a8a
-/
theorem algebraMap_injective : Injective (algebraMap k (CartierDual k A)) := by
  intro r s h
  have := congrArg (fun φ : CartierDual k A => φ 1) h
  simpa only [CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul] using this

/--
@isnad1 id=charp.0h3v.s8.99f9d6adde81 from=translated src=- shape=78092e0a vocab=46f185b9
-/
scoped instance instCharP : CharP (CartierDual k A) p :=
  charP_of_injective_algebraMap algebraMap_injective p

/--
@isnad1 id=eq.1h3v.s13.36bb57a310f1 from=translated src=- shape=7434b639 vocab=77bed6b2
-/
theorem tmul_ext {z : A ⊗[k] A}
    (h : ∀ φ ψ : Module.Dual k A, TensorProduct.dualDistrib k A A (φ ⊗ₜ[k] ψ) z = 0) : z = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro F
  obtain ⟨w, rfl⟩ := (TensorProduct.dualDistribEquiv k A A).surjective F
  change TensorProduct.dualDistrib k A A w z = 0
  induction w with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | tmul φ ψ => exact h φ ψ

section Main

variable [PerfectField k] (n : ℕ) (a : A)
variable (ha : ∀ φ ψ : CartierDual k A,
  (φ ^ p ^ n * ψ ^ p ^ n) a = (φ ^ p ^ n) a * (ψ ^ p ^ n) 1 + (φ ^ p ^ n) 1 * (ψ ^ p ^ n) a)

abbrev Fr : k ≃+* k := iterateFrobeniusEquiv k p n

/--
@isnad1 id=eq.0h4v.s7.402b71f5adac from=translated src=- shape=b9c0279d vocab=05bb03d7
-/
theorem Fr_apply (c : k) : Fr (k := k) (p := p) n c = c ^ p ^ n :=
  iterateFrobeniusEquiv_def k p n c

def L : CartierDual k A →ₗ[k] k where
  toFun φ := (Fr (k := k) (p := p) n).symm ((φ ^ p ^ n) a)
  map_add' φ ψ := by
    rw [← map_add]
    congr 1
    rw [add_pow_char_pow, add_apply']
  map_smul' c φ := by
    rw [RingHom.id_apply, smul_eq_mul, smul_pow, smul_apply']
    apply (Fr (k := k) (p := p) n).injective
    rw [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply, Fr_apply]

def xx : A :=
  (Module.evalEquiv k A).symm (L (k := k) (p := p) n a ∘ₗ (CartierDual.ofDual k A).toLinearMap)

/--
@isnad1 id=eq.0h6v.s9.02971756fcc0 from=translated src=- shape=547ac1d6 vocab=f4fe170e
-/
theorem apply_xx (φ : CartierDual k A) :
    φ (xx (k := k) (p := p) n a) = (Fr (k := k) (p := p) n).symm ((φ ^ p ^ n) a) := by
  have := Module.apply_evalEquiv_symm_apply k A (CartierDual.toDual k A φ)
    (L (k := k) (p := p) n a ∘ₗ (CartierDual.ofDual k A).toLinearMap)
  exact this

/--
@isnad1 id=eq.0h6v.s9.f9c85403b1ee from=translated src=- shape=fad2a754 vocab=d3ff7f56
-/
theorem apply_xx_pow (φ : CartierDual k A) :
    (φ (xx (k := k) (p := p) n a)) ^ p ^ n = (φ ^ p ^ n) a := by
  rw [apply_xx, ← Fr_apply (k := k) (p := p) n, RingEquiv.apply_symm_apply]

include ha in

/--
@isnad1 id=eq.1h7v.s11.3e8ddf5ed058 from=translated src=- shape=a5969eeb vocab=9cfa95f1
-/
theorem mul_apply_xx (φ ψ : CartierDual k A) :
    (φ * ψ) (xx (k := k) (p := p) n a) =
      φ (xx (k := k) (p := p) n a) * ψ 1 + φ 1 * ψ (xx (k := k) (p := p) n a) := by
  apply (Fr (k := k) (p := p) n).injective
  rw [Fr_apply, map_add, map_mul, map_mul, Fr_apply, Fr_apply, Fr_apply, Fr_apply, apply_xx_pow,
    apply_xx_pow, apply_xx_pow, ← pow_apply_one, ← pow_apply_one, mul_pow]
  exact ha φ ψ

include ha in
/--
@isnad1 id=mem.1h5v.s11.2d5e2ef9dd4e from=translated src=- shape=b73161b6 vocab=b8141d7e
-/
theorem xx_mem_primitives : xx (k := k) (p := p) n a ∈ primitives k A := by
  change Coalgebra.comul (R := k) (xx (k := k) (p := p) n a) - (xx (k := k) (p := p) n a) ⊗ₜ[k] 1
    - 1 ⊗ₜ[k] (xx (k := k) (p := p) n a) = 0
  refine tmul_ext fun φ ψ => ?_
  rw [map_sub, map_sub, TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply]
  have := CartierDual.mul_apply (CartierDual.ofDual k A φ) (CartierDual.ofDual k A ψ)
    (xx (k := k) (p := p) n a)
  rw [CartierDual.toDual_ofDual, CartierDual.toDual_ofDual] at this
  rw [← this, mul_apply_xx n a ha]
  change φ _ * ψ 1 + φ 1 * ψ _ - φ _ * ψ 1 - φ 1 * ψ _ = 0
  ring

include ha in
/--
@isnad1 id=ex.1h5v.s12.874214171751 from=translated src=- shape=909b4116 vocab=f27d368f
-/
theorem main : ∃ x ∈ primitives k A, ∀ β : WithConv (A →ₗ[k] k),
    (β.ofConv x) ^ p ^ n = (β ^ p ^ n).ofConv a :=
  ⟨xx (k := k) (p := p) n a, xx_mem_primitives n a ha, fun β => by
    rw [convPow_apply]
    exact apply_xx_pow n a (CartierDual.ofDual k A β.ofConv)⟩

end Main

end HopfAlgebra.FrobeniusUntwist
open scoped _root_.P2MW.S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply.HopfAlgebra _root_.P2MW.S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply.HopfAlgebra.FrobeniusUntwist
open scoped _root_.P2MW.S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply.HopfAlgebra

/--
@isnad1 id=ex.1h5v.s13.bf133cb0fe5b from=translated src=- shape=d18210f8 vocab=1dd159cb
-/
theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (a : A)
    (ha : ∀ β γ : WithConv (A →ₗ[k] k),
      (β ^ p ^ n * γ ^ p ^ n).ofConv a =
        (β ^ p ^ n).ofConv a * (γ ^ p ^ n).ofConv 1 +
          (β ^ p ^ n).ofConv 1 * (γ ^ p ^ n).ofConv a) :
    ∃ x ∈ primitives k A, ∀ β : WithConv (A →ₗ[k] k),
      (β.ofConv x) ^ p ^ n = (β ^ p ^ n).ofConv a := by
  refine HopfAlgebra.FrobeniusUntwist.main n a fun φ ψ => ?_
  have h := ha (WithConv.toConv (CartierDual.toDual k A φ))
    (WithConv.toConv (CartierDual.toDual k A ψ))
  rw [HopfAlgebra.FrobeniusUntwist.convPow_mul_convPow_apply,
    HopfAlgebra.FrobeniusUntwist.convPow_apply, HopfAlgebra.FrobeniusUntwist.convPow_apply,
    HopfAlgebra.FrobeniusUntwist.convPow_apply, HopfAlgebra.FrobeniusUntwist.convPow_apply] at h
  simpa only [WithConv.ofConv_toConv, CartierDual.ofDual_toDual] using h
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
