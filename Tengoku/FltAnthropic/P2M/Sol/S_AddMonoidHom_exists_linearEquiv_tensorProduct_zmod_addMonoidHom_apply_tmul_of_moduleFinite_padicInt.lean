import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AddMonoidHom_exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AddMonoidHom_exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HomTensorZMod

variable (p : ℕ) [Fact p.Prime] (P : Type*) [AddCommGroup P] [Module ℤ_[p] P]

def pSub : AddSubgroup P := (LinearMap.range (DistribSMul.toLinearMap ℤ_[p] P (p : ℤ_[p]))).toAddSubgroup

/--
@isnad1 id=mem.0h3v.s6.3a7c6db90fc2 from=translated src=- shape=242c6239 vocab=7c037e50
-/
theorem nsmul_mem_pSub (x : P) : p • x ∈ pSub p P := by
  refine ⟨x, ?_⟩
  change (p : ℤ_[p]) • x = p • x
  exact Nat.cast_smul_eq_nsmul ℤ_[p] p x

abbrev V : Type _ := P ⧸ pSub p P

scoped instance moduleV : Module (ZMod p) (V p P) := QuotientAddGroup.zmodModule (nsmul_mem_pSub p P)

/--
@isnad1 id=ex.0h2v.s7.486cf6021e50 from=translated src=- shape=f269229d vocab=0a0a82fe
-/
theorem exists_eq_natCast_add_mul (r : ℤ_[p]) : ∃ (n : ℕ) (r' : ℤ_[p]), r = n + p * r' := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec 1 r)
  refine ⟨r.appr 1, c, ?_⟩
  rw [pow_one] at hc
  linear_combination hc

/--
@isnad1 id=finite.0h2v.s6.7c4347df63ee from=translated src=- shape=3088ac73 vocab=70989139
-/
scoped instance finiteV [Module.Finite ℤ_[p] P] : Module.Finite (ZMod p) (V p P) := by
  obtain ⟨s, hs⟩ := (‹Module.Finite ℤ_[p] P›).fg_top
  classical
  refine ⟨⟨s.image (QuotientAddGroup.mk' (pSub p P)), ?_⟩⟩
  rw [eq_top_iff]
  rintro v -
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (pSub p P) v
  have hx : x ∈ Submodule.span ℤ_[p] (s : Set P) := by rw [hs]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    obtain ⟨n, c', rfl⟩ := exists_eq_natCast_add_mul p c
    have h' : ((n : ℤ_[p]) + p * c') • y = n • y + p • (c' • y) := by
      rw [add_smul, Nat.cast_smul_eq_nsmul, mul_smul, Nat.cast_smul_eq_nsmul]
    have hp0 : QuotientAddGroup.mk' (pSub p P) (p • (c' • y)) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (nsmul_mem_pSub p P _)
    rw [h', map_add, hp0, add_zero, map_nsmul]
    exact Submodule.smul_of_tower_mem _ n hy

section Lift

variable {P}
variable (W : Type*) [AddCommGroup W] [Module (ZMod p) W]

/--
@isnad1 id=eq.1h5v.s7.22957f914bd6 from=translated src=- shape=62091315 vocab=7d879cd8
-/
theorem apply_eq_zero_of_mem_pSub (φ : P →+ W) (x : P) (hx : x ∈ pSub p P) : φ x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  change φ ((p : ℤ_[p]) • y) = 0
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]

def liftEquiv : (P →+ W) ≃ₗ[ZMod p] (V p P →ₗ[ZMod p] W) where
  toFun φ := (QuotientAddGroup.lift (pSub p P) φ (apply_eq_zero_of_mem_pSub p W φ)).toZModLinearMap p
  invFun ψ := ψ.toAddMonoidHom.comp (QuotientAddGroup.mk' (pSub p P))
  map_add' φ ψ := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (pSub p P) v
    rfl
  map_smul' c φ := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (pSub p P) v
    rfl
  left_inv φ := by ext x; rfl
  right_inv ψ := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (pSub p P) v
    rfl

/--
@isnad1 id=eq.0h5v.s10.6bf6a3cd3a02 from=translated src=- shape=098ee54a vocab=7134da27
-/
theorem liftEquiv_apply_mk (φ : P →+ W) (x : P) :
    liftEquiv p W φ (QuotientAddGroup.mk' (pSub p P) x) = φ x := rfl

/--
@isnad1 id=eq.0h5v.s11.e6ded08d7d2b from=translated src=- shape=f358d9ab vocab=db67ec89
-/
theorem liftEquiv_symm_apply (ψ : V p P →ₗ[ZMod p] W) (x : P) :
    (liftEquiv p W).symm ψ x = ψ (QuotientAddGroup.mk' (pSub p P) x) := rfl

end Lift

section Main

variable (B : Type*) [CommRing B] [Algebra (ZMod p) B]

def toB : (P →+ ZMod p) →ₗ[ZMod p] (P →+ B) where
  toFun φ := (algebraMap (ZMod p) B).toAddMonoidHom.comp φ
  map_add' φ ψ := by ext x; simp
  map_smul' c φ := by
    ext x
    simp [Algebra.smul_def]

def E : B ⊗[ZMod p] (P →+ ZMod p) →ₗ[B] (P →+ B) :=
  (toB p P B).liftBaseChange B

omit [Module ℤ_[p] P] in
/--
@isnad1 id=eq.0h6v.s10.d0aa70f32dca from=translated src=- shape=204a0703 vocab=e8a39106
-/
theorem E_tmul (b : B) (φ : P →+ ZMod p) (x : P) : E p P B (b ⊗ₜ[ZMod p] φ) x = b * algebraMap (ZMod p) B (φ x) :=
  rfl

variable [Module.Finite ℤ_[p] P]

def Ecomp : B ⊗[ZMod p] (P →+ ZMod p) ≃ₗ[ZMod p] (P →+ B) :=
  ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) (liftEquiv p (ZMod p))).restrictScalars
      (ZMod p)).trans <|
    (TensorProduct.comm (ZMod p) B (Module.Dual (ZMod p) (V p P))).trans <|
      (dualTensorHomEquiv (ZMod p) (V p P) B).trans (liftEquiv p B).symm

/--
@isnad1 id=eq.0h6v.s11.02821dba3176 from=translated src=- shape=9eadf1e9 vocab=ff085cd2
-/
theorem Ecomp_tmul (b : B) (φ : P →+ ZMod p) (x : P) :
    Ecomp p P B (b ⊗ₜ[ZMod p] φ) x = b * algebraMap (ZMod p) B (φ x) := by
  simp only [Ecomp, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, TensorProduct.comm_tmul]
  rw [liftEquiv_symm_apply, dualTensorHomEquiv, LinearEquiv.ofBijective_apply, dualTensorHom_apply,
    liftEquiv_apply_mk, Algebra.smul_def, mul_comm]

/--
@isnad1 id=eq.0h4v.s12.eea2b6b42472 from=translated src=- shape=48e0dbbb vocab=4deb009b
-/
theorem E_eq_Ecomp (z : B ⊗[ZMod p] (P →+ ZMod p)) : E p P B z = Ecomp p P B z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b φ => exact AddMonoidHom.ext fun x => (E_tmul p P B b φ x).trans (Ecomp_tmul p P B b φ x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/--
@isnad1 id=bijectiv.0h3v.s10.34c168ba1bce from=translated src=- shape=1a9b6b2f vocab=6f32a8b6
-/
theorem E_bijective : Function.Bijective (E p P B) := by
  have : (E p P B : B ⊗[ZMod p] (P →+ ZMod p) → (P →+ B)) = Ecomp p P B := funext (E_eq_Ecomp p P B)
  rw [this]
  exact (Ecomp p P B).bijective

def Eequiv : B ⊗[ZMod p] (P →+ ZMod p) ≃ₗ[B] (P →+ B) :=
  LinearEquiv.ofBijective (E p P B) (E_bijective p P B)

/--
@isnad1 id=eq.0h6v.s11.dda7da08b6fe from=translated src=- shape=841a8d59 vocab=1aec2427
-/
theorem Eequiv_tmul (b : B) (φ : P →+ ZMod p) (x : P) :
    Eequiv p P B (b ⊗ₜ[ZMod p] φ) x = b * algebraMap (ZMod p) B (φ x) :=
  rfl

end Main

end HomTensorZMod
open scoped _root_.P2MW.S_AddMonoidHom_exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt.HomTensorZMod

/--
@isnad1 id=ex.0h3v.s12.508d7e333a05 from=translated src=- shape=423c17fe vocab=7acc34fd
-/
theorem solution
    (p : ℕ) [Fact p.Prime] (P : Type*) [AddCommGroup P] [Module ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (B : Type*) [CommRing B] [Algebra (ZMod p) B] :
    ∃ e : B ⊗[ZMod p] (P →+ ZMod p) ≃ₗ[B] (P →+ B),
      ∀ (b : B) (φ : P →+ ZMod p) (x : P), e (b ⊗ₜ[ZMod p] φ) x = b * algebraMap (ZMod p) B (φ x) :=
  ⟨HomTensorZMod.Eequiv p P B, HomTensorZMod.Eequiv_tmul p P B⟩
