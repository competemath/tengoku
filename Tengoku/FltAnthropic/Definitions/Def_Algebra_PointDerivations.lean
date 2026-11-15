import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u v w w'

namespace Algebra

def PointDerivations (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] (ev : A →+* k)
    (M : Type w) [AddCommGroup M] [Module k M] : Submodule k (A →ₗ[k] M) where
  carrier := {D | ∀ a b : A, D (a * b) = ev a • D b + ev b • D a}
  add_mem' := by
    intro D D' hD hD' a b
    simp only [LinearMap.add_apply, hD a b, hD' a b, smul_add]
    abel
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro c D hD a b
    simp only [LinearMap.smul_apply, hD a b, smul_add, smul_comm c]

namespace PointDerivations

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] {ev : A →+* k}
  {M : Type w} [AddCommGroup M] [Module k M] {M' : Type w'} [AddCommGroup M'] [Module k M']

/--
@isnad1 id=iff.0h5v.s10.8fa05658eee8 from=translated src=- shape=8b6844ae vocab=00185b37
-/
theorem mem_iff (D : A →ₗ[k] M) : D ∈ PointDerivations k A ev M ↔ ∀ a b : A, D (a * b) = ev a • D b + ev b • D a :=
  Iff.rfl

/--
@isnad1 id=eq.1h7v.s10.e5093618492b from=translated src=- shape=5f5645f4 vocab=00185b37
-/
theorem apply_mul {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (a b : A) :
    D (a * b) = ev a • D b + ev b • D a := hD a b

/--
@isnad1 id=eq.1h5v.s9.18140185b8c9 from=translated src=- shape=1b7cd405 vocab=3b63ac7c
-/
theorem apply_one {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, show ev 1 = 1 from map_one ev, one_smul] at h

  have h2 : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/--
@isnad1 id=eq.1h6v.s9.06c8e5a34f1f from=translated src=- shape=1c7f9f8f vocab=a5ca6bff
-/
theorem apply_algebraMap {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (c : k) : D (algebraMap k A c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, apply_one hD, smul_zero]

/--
@isnad1 id=eq.1h5v.s8.7338006e7461 from=translated src=- shape=7714a6d8 vocab=a627ae81
-/
theorem ev_smul (hev : ev.comp (algebraMap k A) = RingHom.id k) (c : k) (a : A) : ev (c • a) = c * ev a := by
  rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply, hev, RingHom.id_apply]

def map (ev : A →+* k) (φ : M →ₗ[k] M') : ↥(PointDerivations k A ev M) →ₗ[k] ↥(PointDerivations k A ev M') where
  toFun D := ⟨φ.comp D.1, fun a b => by simp only [LinearMap.comp_apply, D.2 a b, map_add, map_smul]⟩
  map_add' D D' := by ext a; simp
  map_smul' c D := by ext a; simp

/--
@isnad1 id=eq.0h8v.s13.a2e67cf6e698 from=translated src=- shape=dfabbe2d vocab=d47def81
-/
@[simp] theorem map_apply_coe (ev : A →+* k) (φ : M →ₗ[k] M') (D : ↥(PointDerivations k A ev M)) (a : A) :
    (map ev φ D : A →ₗ[k] M') a = φ (D.1 a) := rfl

/--
@isnad1 id=eq.0h5v.s13.1ccaa2fbdec9 from=translated src=- shape=5f7f4e13 vocab=4c63d65f
-/
theorem map_id (ev : A →+* k) (D : ↥(PointDerivations k A ev M)) : map ev (LinearMap.id : M →ₗ[k] M) D = D := by
  ext a; rfl

/--
@isnad1 id=eq.0h9v.s14.f9525ee51806 from=translated src=- shape=f9ec044e vocab=0fabd161
-/
theorem map_comp {M'' : Type w} [AddCommGroup M''] [Module k M''] (ev : A →+* k) (φ : M →ₗ[k] M') (ψ : M' →ₗ[k] M'')
    (D : ↥(PointDerivations k A ev M)) : map ev (ψ.comp φ) D = map ev ψ (map ev φ D) := by
  ext a; rfl

end PointDerivations

end Algebra
