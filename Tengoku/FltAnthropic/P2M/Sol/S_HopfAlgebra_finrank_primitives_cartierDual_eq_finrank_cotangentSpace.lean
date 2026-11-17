import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_ModpRealization
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualInstances

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

universe u v

namespace PRIMCOUNT

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]

local notation "ε" => Coalgebra.counit (R := k) (A := A)

/--
@isnad1 id=iff.0h3v.s11.ccacdff0acd5 from=translated src=- shape=c7084a9b vocab=403636bd
-/
theorem mem_primitives_iff (φ : CartierDual k A) :
    φ ∈ primitives k (CartierDual k A) ↔ ∀ a b : A, φ (a * b) = φ a * ε b + ε a * φ b := by
  have hmem : φ ∈ primitives k (CartierDual k A) ↔
      Coalgebra.comul (R := k) φ = φ ⊗ₜ[k] (1 : CartierDual k A) + (1 : CartierDual k A) ⊗ₜ[k] φ := by
    change φ ∈ LinearMap.ker _ ↔ _
    erw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, sub_sub]
    exact ⟨fun h => sub_eq_zero.mp h, fun h => sub_eq_zero.mpr h⟩
  have hpair : ∀ a b : A, TensorProduct.dualDistrib k A A
      (TensorProduct.map (CartierDual.toDual k A).toLinearMap (CartierDual.toDual k A).toLinearMap
        (φ ⊗ₜ[k] (1 : CartierDual k A) + (1 : CartierDual k A) ⊗ₜ[k] φ)) (a ⊗ₜ[k] b) = φ a * ε b + ε a * φ b := by
    intro a b
    rw [map_add, TensorProduct.map_tmul, TensorProduct.map_tmul, map_add, LinearMap.add_apply,
      TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply]
    rfl
  rw [hmem]
  constructor
  · intro h a b
    rw [← CartierDual.comul_pairing φ a b, h, hpair]
  · intro h
    exact CartierDual.tmul_eq_of_pairing_eq fun a b => by rw [CartierDual.comul_pairing, hpair, h]

variable {k A}

/--
@isnad1 id=eq.1h3v.s11.1bbd92726b55 from=translated src=- shape=da72889b vocab=def62ce0
-/
theorem apply_one_eq_zero {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) : φ 1 = 0 := by
  have h := (mem_primitives_iff k A φ).1 hφ 1 1
  rw [mul_one, Bialgebra.counit_one, mul_one, one_mul] at h

  have : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

/--
@isnad1 id=eq.2h5v.s11.495744714aa9 from=translated src=- shape=05c6e9ac vocab=615a17ea
-/
theorem apply_mul_of_counit_eq_zero {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) (a x : A)
    (hx : ε x = 0) : φ (a * x) = ε a * φ x := by
  rw [(mem_primitives_iff k A φ).1 hφ, hx, mul_zero, zero_add]

/--
@isnad1 id=eq.3h5v.s11.43e589342274 from=translated src=- shape=b3e49d4a vocab=615a17ea
-/
theorem apply_mul_eq_zero {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) (x y : A)
    (hx : ε x = 0) (hy : ε y = 0) : φ (x * y) = 0 := by
  rw [apply_mul_of_counit_eq_zero hφ x y hy, hx, zero_mul]

variable (k A)

abbrev I : Ideal A := RingHom.ker (Bialgebra.counitAlgHom k A)

omit [Coalgebra.IsCocomm k A] [Module.Finite k A] in
/--
@isnad1 id=iff.0h3v.s8.8d11457b3970 from=translated src=- shape=8617e384 vocab=0dd10f69
-/
theorem mem_I {x : A} : x ∈ I k A ↔ ε x = 0 := RingHom.mem_ker

omit [Coalgebra.IsCocomm k A] [Module.Finite k A] in
/--
@isnad1 id=mem.0h3v.s9.ef93aede0bdb from=translated src=- shape=68d2456e vocab=e5702acc
-/
theorem sub_algebraMap_counit_mem (a : A) : a - algebraMap k A (ε a) ∈ I k A := by
  rw [mem_I, map_sub]
  change ε a - Bialgebra.counitAlgHom k A (algebraMap k A (ε a)) = 0
  rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

noncomputable def restrictI (φ : CartierDual k A) : ↥(I k A) →ₗ[k] k :=
  (CartierDual.toDual k A φ).comp ((I k A).subtype.restrictScalars k)

omit [Coalgebra.IsCocomm k A] [Module.Finite k A] in
/--
@isnad1 id=eq.0h4v.s9.c2d005ef8754 from=translated src=- shape=223b658d vocab=9ca78bda
-/
@[scoped simp] theorem restrictI_apply (φ : CartierDual k A) (x : ↥(I k A)) : restrictI k A φ x = φ x := rfl

/--
@isnad1 id=le.1h3v.s12.2ae53b2fdc48 from=translated src=- shape=669a420a vocab=b4d02340
-/
theorem restrictI_vanishes {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) :
    ((I k A) • ⊤ : Submodule A ↥(I k A)).restrictScalars k ≤ LinearMap.ker (restrictI k A φ) := by
  intro x hx
  rw [Submodule.restrictScalars_mem] at hx
  rw [LinearMap.mem_ker, restrictI_apply]
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    change φ (a • (y : A)) = 0
    rw [smul_eq_mul]
    exact apply_mul_eq_zero hφ a y ((mem_I k A).1 ha) ((mem_I k A).1 y.2)
  · intro x y hx hy
    change φ ((x : A) + y) = 0
    rw [map_add]
    change φ x + φ y = 0
    rw [hx, hy, add_zero]

noncomputable def toCotDual {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) :
    Module.Dual k (cotangentSpace k A) :=
  ((((I k A) • ⊤ : Submodule A ↥(I k A)).restrictScalars k).liftQ (restrictI k A φ) (restrictI_vanishes k A hφ)).comp
    (Submodule.Quotient.restrictScalarsEquiv k ((I k A) • ⊤ : Submodule A ↥(I k A))).symm.toLinearMap

/--
@isnad1 id=eq.1h4v.s12.904cab80137c from=translated src=- shape=faffe721 vocab=35e63fe6
-/
theorem toCotDual_toCotangent {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) (x : ↥(I k A)) :
    toCotDual k A hφ ((I k A).toCotangent x) = φ x := by
  change ((((I k A) • ⊤ : Submodule A ↥(I k A)).restrictScalars k).liftQ (restrictI k A φ) (restrictI_vanishes k A hφ))
    ((Submodule.Quotient.restrictScalarsEquiv k ((I k A) • ⊤ : Submodule A ↥(I k A))).symm (Submodule.Quotient.mk x)) = φ x
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]
  rfl

noncomputable def ofCotDualFun (ψ : Module.Dual k (cotangentSpace k A)) : A →ₗ[k] k where
  toFun a := ψ ((I k A).toCotangent ⟨a - algebraMap k A (ε a), sub_algebraMap_counit_mem k A a⟩)
  map_add' a b := by
    rw [← map_add, ← map_add]
    congr 2
    apply Subtype.ext
    change a + b - algebraMap k A (ε (a + b)) = (a - algebraMap k A (ε a)) + (b - algebraMap k A (ε b))
    rw [map_add, map_add]; abel
  map_smul' c a := by
    rw [RingHom.id_apply, ← map_smul, ← LinearMap.map_smul_of_tower]
    congr 2
    apply Subtype.ext
    change c • a - algebraMap k A (ε (c • a)) = c • (a - algebraMap k A (ε a))
    rw [map_smul, smul_eq_mul, smul_sub, Algebra.smul_def, Algebra.smul_def, map_mul]

/--
@isnad1 id=mem.0h3v.s12.c0fb3968b3b6 from=translated src=- shape=b1fd5adc vocab=ae164ab8
-/
theorem ofCotDualFun_mem (ψ : Module.Dual k (cotangentSpace k A)) :
    CartierDual.ofDual k A (ofCotDualFun k A ψ) ∈ primitives k (CartierDual k A) := by
  rw [mem_primitives_iff]
  intro a b
  change ofCotDualFun k A ψ (a * b) = ofCotDualFun k A ψ a * ε b + ε a * ofCotDualFun k A ψ b
  change ψ ((I k A).toCotangent ⟨a * b - algebraMap k A (ε (a * b)), _⟩) =
    ψ ((I k A).toCotangent ⟨a - algebraMap k A (ε a), _⟩) * ε b + ε a * ψ ((I k A).toCotangent ⟨b - algebraMap k A (ε b), _⟩)
  have hlin : ∀ (c : k) (y : ↥(I k A)), c • (I k A).toCotangent y = (I k A).toCotangent (c • y) := fun c y =>
    (((I k A).toCotangent.restrictScalars k).map_smul c y).symm
  rw [mul_comm (ψ _) (ε b)]
  change _ = ε b • ψ ((I k A).toCotangent ⟨a - algebraMap k A (ε a), sub_algebraMap_counit_mem k A a⟩) +
    ε a • ψ ((I k A).toCotangent ⟨b - algebraMap k A (ε b), sub_algebraMap_counit_mem k A b⟩)
  rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← LinearMap.map_add ψ, hlin, hlin, ← LinearMap.map_add]
  congr 1
  rw [Ideal.toCotangent_eq]

  have key : (a * b - algebraMap k A (ε (a * b))) - (ε b • (a - algebraMap k A (ε a)) + ε a • (b - algebraMap k A (ε b)))
      = (a - algebraMap k A (ε a)) * (b - algebraMap k A (ε b)) := by
    rw [Bialgebra.counit_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  change ((a * b - algebraMap k A (ε (a * b))) - (ε b • (a - algebraMap k A (ε a)) + ε a • (b - algebraMap k A (ε b))) : A) ∈ (I k A) ^ 2
  rw [key, pow_two]
  exact Ideal.mul_mem_mul (sub_algebraMap_counit_mem k A a) (sub_algebraMap_counit_mem k A b)

/--
@isnad1 id=finite.0h2v.s9.dc7a522e9a68 from=translated src=- shape=25ad0757 vocab=e4d32d29
-/
scoped instance finite_cotangent : Module.Finite k (cotangentSpace k A) := by
  haveI : IsNoetherian k A := IsNoetherian.iff_fg.2 inferInstance
  haveI : Module.Finite k ↥(I k A) := Module.IsNoetherian.finite k _
  exact Module.Finite.of_surjective (((I k A).toCotangent).restrictScalars k) (I k A).toCotangent_surjective

noncomputable def primEquiv : ↥(primitives k (CartierDual k A)) ≃ₗ[k] Module.Dual k (cotangentSpace k A) where
  toFun φ := toCotDual k A φ.2
  map_add' φ ψ := by
    apply LinearMap.ext; intro c
    obtain ⟨x, rfl⟩ := (I k A).toCotangent_surjective c
    rw [LinearMap.add_apply, toCotDual_toCotangent, toCotDual_toCotangent, toCotDual_toCotangent]
    rfl
  map_smul' c φ := by
    apply LinearMap.ext; intro d
    obtain ⟨x, rfl⟩ := (I k A).toCotangent_surjective d
    rw [RingHom.id_apply, LinearMap.smul_apply, toCotDual_toCotangent, toCotDual_toCotangent]
    rfl
  invFun ψ := ⟨CartierDual.ofDual k A (ofCotDualFun k A ψ), ofCotDualFun_mem k A ψ⟩
  left_inv φ := by
    apply Subtype.ext
    apply CartierDual.ext
    intro a
    change ofCotDualFun k A (toCotDual k A φ.2) a = φ.1 a
    change toCotDual k A φ.2 ((I k A).toCotangent ⟨a - algebraMap k A (ε a), _⟩) = φ.1 a
    rw [toCotDual_toCotangent]
    change φ.1 (a - algebraMap k A (ε a)) = φ.1 a
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, apply_one_eq_zero φ.2, smul_zero, sub_zero]
  right_inv ψ := by
    apply LinearMap.ext; intro c
    obtain ⟨x, rfl⟩ := (I k A).toCotangent_surjective c
    rw [toCotDual_toCotangent]
    change ofCotDualFun k A ψ x = ψ ((I k A).toCotangent x)
    change ψ ((I k A).toCotangent ⟨(x : A) - algebraMap k A (ε x), _⟩) = ψ ((I k A).toCotangent x)
    congr 2
    apply Subtype.ext
    change (x : A) - algebraMap k A (ε x) = x
    rw [(mem_I k A).1 x.2, map_zero, sub_zero]

end PRIMCOUNT
open scoped _root_.P2MW.S_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace.PRIMCOUNT

/--
@isnad1 id=eq.0h2v.s12.4a7b688cd4ce from=translated src=- shape=f8533865 vocab=b65e7d2e
-/
theorem solution
    (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
    [Module.Finite k A] :
    Module.finrank k ↥(primitives k (CartierDual k A)) = Module.finrank k (cotangentSpace k A) := by
  rw [LinearEquiv.finrank_eq (PRIMCOUNT.primEquiv k A)]
  exact Subspace.dual_finrank_eq
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
