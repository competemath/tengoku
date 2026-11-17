import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CohCarrier_HeckeData
import Tengoku.FltAnthropic.Theorems.Thm_CohCarrier_HeckeData_finite_ML_and_free_ML

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem
attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing
attribute [-simp] IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

noncomputable section

open CohCarrier IsLocalRing

namespace TWExt

section Residue

variable {𝒪 : Type} [CommRing 𝒪] {V : Type} [AddCommGroup V] [Module 𝒪 V]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)

abbrev Loc : Type := Localization D.mTheta.primeCompl

/--
@isnad1 id=ne.0h5v.s9.027eb3925aac from=translated src=- shape=538c4608 vocab=1ff52d38
-/
theorem thetaTilde_ne_zero_of_mem (s : D.mTheta.primeCompl) : D.thetaTilde (s : D.FreeAlg) ≠ 0 :=
  fun h => s.2 (by
    show (s : D.FreeAlg) ∈ RingHom.ker D.thetaTilde.toRingHom
    exact h)

/--
@isnad1 id=iff.0h5v.s9.cd649d7658dd from=translated src=- shape=9a837c67 vocab=51aa871b
-/
theorem mem_primeCompl_iff (f : D.FreeAlg) : f ∈ D.mTheta.primeCompl ↔ D.thetaTilde f ≠ 0 := by
  show f ∉ RingHom.ker D.thetaTilde.toRingHom ↔ _
  rw [RingHom.mem_ker]
  rfl

def Θ : Loc D →+* k :=
  IsLocalization.lift (M := D.mTheta.primeCompl) (g := D.thetaTilde.toRingHom)
    (fun s => isUnit_iff_ne_zero.mpr (thetaTilde_ne_zero_of_mem D s))

end Residue

section LocMod

variable {R : Type} [CommRing R] {S : Submonoid R} {M : Type} [AddCommGroup M] [Module R M]

/--
@isnad1 id=isunit.0h4v.s10.bb98f64768c8 from=translated src=- shape=b0617eb4 vocab=5f7429cf
-/
theorem isUnit_smul_loc (s : S) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule S M)) s) :=
  IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S M) s

end LocMod

section Car

def Car (F M : Type) [Semiring F] [AddCommGroup M] (_m : Module F M) : Type := M

variable {F M : Type} [CommRing F] [AddCommGroup M] (m : Module F M)

scoped instance : AddCommGroup (Car F M m) := inferInstanceAs (AddCommGroup M)
scoped instance instModuleCar : Module F (Car F M m) := m
scoped instance instModuleBaseCar {A : Type} [CommRing A] [Module A M] : Module A (Car F M m) :=
  inferInstanceAs (Module A M)

def toCar {A : Type} [CommRing A] [Module A M] : M →ₗ[A] Car F M m := LinearMap.id

def ofCar {A : Type} [CommRing A] [Module A M] : Car F M m →ₗ[A] M := LinearMap.id

end Car

section Setting

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {k : Type} [Field k] [Algebra 𝒪 k]
  {V : Type} [AddCommGroup V] [Module 𝒪 V]
  (DV DE : HeckeData 𝒪 V k) (σ : DV.Gen ⊕ Unit ≃ DE.Gen)
  (hop : ∀ g : DV.Gen, DE.op (σ (Sum.inl g)) = DV.op g) (z₀ : DV.FreeAlg)

local notation "FV" => DV.FreeAlg
local notation "FE" => DE.FreeAlg
local notation "SV" => DV.mTheta.primeCompl
local notation "SE" => DE.mTheta.primeCompl

local notation "Z♭" => DE.op (σ (Sum.inr ()))

/--
@isnad1 id=eq.0h6v.s8.28ce84212429 from=translated src=- shape=0b656e2b vocab=d01ddf6f
-/
theorem X_smul_V (g : DV.Gen) (v : V) : (MvPolynomial.X g : FV) • v = DV.op g v := by
  show DV.opAlgHom (MvPolynomial.X g) v = _; rw [HeckeData.opAlgHom_X]

/--
@isnad1 id=eq.0h6v.s8.28ce84212429 from=translated src=- shape=0b656e2b vocab=d01ddf6f
-/
theorem X_smul_E (γ : DE.Gen) (v : V) : (MvPolynomial.X γ : FE) • v = DE.op γ v := by
  show DE.opAlgHom (MvPolynomial.X γ) v = _; rw [HeckeData.opAlgHom_X]

include hop in
/--
@isnad1 id=eq.1h7v.s9.038d60005860 from=translated src=- shape=04357b52 vocab=1c35d74f
-/
theorem Z_comm (g : DV.Gen) : Z♭ * DV.op g = DV.op g * Z♭ := by
  rw [← hop]; exact DE.comm _ _

include hop in
/--
@isnad1 id=eq.1h8v.s10.1a3a2504bef8 from=translated src=- shape=23262f89 vocab=ec32f83d
-/
theorem Z_smulF (f : FV) (v : V) : Z♭ (f • v) = f • Z♭ v := by
  induction f using MvPolynomial.induction_on generalizing v with
  | C a =>
    rw [show (MvPolynomial.C a : FV) = algebraMap 𝒪 FV a from rfl, algebraMap_smul, algebraMap_smul,
      LinearMap.map_smul]
  | add p q hp hq => rw [add_smul, map_add, hp, hq, add_smul]
  | mul_X p g hp =>
    rw [mul_smul, hp, X_smul_V, mul_smul, X_smul_V, ← Module.End.mul_apply, Z_comm DV DE σ hop g,
      Module.End.mul_apply]

def ZF : V →ₗ[FV] V :=
  { Z♭ with map_smul' := fun f v => Z_smulF DV DE σ hop f v }

def ZL : DV.ML →ₗ[Loc DV] DV.ML := LocalizedModule.map DV.mTheta.primeCompl (ZF DV DE σ hop)

/--
@isnad1 id=eq.1h8v.s12.588dc9618c58 from=translated src=- shape=c32c8d76 vocab=70866dc3
-/
theorem ZL_mk (v : V) (s : SV) : ZL DV DE σ hop (LocalizedModule.mk v s) = LocalizedModule.mk (Z♭ v) s := by
  rw [ZL, LocalizedModule.map_mk]; rfl

def ρV : FV →ₐ[𝒪] Module.End 𝒪 DV.ML := Algebra.lsmul 𝒪 𝒪 DV.ML

/--
@isnad1 id=eq.0h6v.s12.4b65abf98940 from=translated src=- shape=0c0f694c vocab=f62624d3
-/
@[scoped simp] theorem ρV_apply (f : FV) (x : DV.ML) : ρV DV f x = f • x := rfl

def opML : DE.Gen → Module.End 𝒪 DV.ML := fun γ =>
  Sum.elim (fun g => ρV DV (MvPolynomial.X g)) (fun _ => (ZL DV DE σ hop).restrictScalars 𝒪) (σ.symm γ)

/--
@isnad1 id=eq.1h7v.s12.98c2781f09ba from=translated src=- shape=6d185ac1 vocab=0f4588d0
-/
theorem opML_inl (g : DV.Gen) : opML DV DE σ hop (σ (Sum.inl g)) = ρV DV (MvPolynomial.X g) := by simp [opML]
/--
@isnad1 id=eq.1h6v.s11.1de46c88beb5 from=translated src=- shape=e4830dcc vocab=a121769d
-/
theorem opML_inr : opML DV DE σ hop (σ (Sum.inr ())) = (ZL DV DE σ hop).restrictScalars 𝒪 := by simp [opML]

/--
@isnad1 id=eq.1h8v.s13.2855bb9653e2 from=translated src=- shape=4ca6f888 vocab=a57b6fa7
-/
theorem ZL_smulF (f : FV) (x : DV.ML) : ZL DV DE σ hop (f • x) = f • ZL DV DE σ hop x := by
  rw [← IsScalarTower.algebraMap_smul (Loc DV) f x, LinearMap.map_smul, IsScalarTower.algebraMap_smul]

/--
@isnad1 id=eq.1h8v.s12.ee3443cdfa94 from=translated src=- shape=a8703224 vocab=f8f883d9
-/
theorem opML_comm (γ γ' : DE.Gen) :
    opML DV DE σ hop γ * opML DV DE σ hop γ' = opML DV DE σ hop γ' * opML DV DE σ hop γ := by
  obtain ⟨x, rfl⟩ := σ.surjective γ
  obtain ⟨x', rfl⟩ := σ.surjective γ'
  apply LinearMap.ext; intro y
  rcases x with g | u <;> rcases x' with g' | u'
  · simp only [opML_inl, Module.End.mul_apply, ρV_apply, ← mul_smul, mul_comm]
  · obtain rfl : u' = () := rfl
    simp only [opML_inl, opML_inr, Module.End.mul_apply, ρV_apply, LinearMap.restrictScalars_apply, ZL_smulF]
  · obtain rfl : u = () := rfl
    simp only [opML_inl, opML_inr, Module.End.mul_apply, ρV_apply, LinearMap.restrictScalars_apply, ZL_smulF]
  · rfl

abbrev DML : HeckeData 𝒪 DV.ML k :=
  { Gen := DE.Gen, op := opML DV DE σ hop, comm := opML_comm DV DE σ hop, θbar := DE.θbar }

@[reducible] def modN : Module FE DV.ML := (DML DV DE σ hop).moduleFreeAlg

local notation "N♯" => Car FE DV.ML (modN DV DE σ hop)

/--
@isnad1 id=isscalar.1h6v.s14.a0303bb13fe2 from=translated src=- shape=395331a1 vocab=985183ec
-/
scoped instance instTowerN : IsScalarTower 𝒪 FE N♯ := (DML DV DE σ hop).V_isScalarTower

/--
@isnad1 id=eq.1h8v.s14.b90a9a30f33d from=translated src=- shape=a56777bb vocab=26fc715d
-/
theorem X_smul_N (γ : DE.Gen) (x : N♯) :
    (MvPolynomial.X γ : FE) • x = toCar (A := 𝒪) (modN DV DE σ hop) (opML DV DE σ hop γ (ofCar (A := 𝒪) (modN DV DE σ hop) x)) := by
  show (DML DV DE σ hop).opAlgHom (MvPolynomial.X γ) x = _
  rw [HeckeData.opAlgHom_X]; rfl

/--
@isnad1 id=eq.1h8v.s14.a4a849591a43 from=translated src=- shape=ebcd1a7e vocab=2ddbebe7
-/
theorem X_inl_smul_N (g : DV.Gen) (x : N♯) :
    (MvPolynomial.X (σ (Sum.inl g)) : FE) • x =
      toCar (A := 𝒪) (modN DV DE σ hop) ((MvPolynomial.X g : FV) • ofCar (A := 𝒪) (modN DV DE σ hop) x) := by
  rw [X_smul_N, opML_inl]; rfl

/--
@isnad1 id=eq.1h7v.s14.89a735ae5eef from=translated src=- shape=91718cc2 vocab=2234a797
-/
theorem X_inr_smul_N (x : N♯) :
    (MvPolynomial.X (σ (Sum.inr ())) : FE) • x =
      toCar (A := 𝒪) (modN DV DE σ hop) (ZL DV DE σ hop (ofCar (A := 𝒪) (modN DV DE σ hop) x)) := by
  rw [X_smul_N, opML_inr]; rfl

/--
@isnad1 id=eq.1h8v.s14.13500f251f26 from=translated src=- shape=65082e92 vocab=b5865e99
-/
theorem C_smul_N (a : 𝒪) (x : N♯) : (MvPolynomial.C a : FE) • x = a • x := by
  rw [show (MvPolynomial.C a : FE) = algebraMap 𝒪 FE a from rfl, algebraMap_smul]

/--
@isnad1 id=eq.1h7v.s13.a800da3f9313 from=translated src=- shape=f6fb1208 vocab=8a8304f5
-/
@[scoped simp] theorem ofCar_toCar_N (y : DV.ML) :
    ofCar (A := 𝒪) (modN DV DE σ hop) (toCar (A := 𝒪) (modN DV DE σ hop) y) = y := rfl
/--
@isnad1 id=eq.1h8v.s14.d3e65133dd32 from=translated src=- shape=a5b1bdb3 vocab=614367c8
-/
theorem toCar_add (y y' : DV.ML) : toCar (A := 𝒪) (modN DV DE σ hop) (y + y') =
    toCar (A := 𝒪) (modN DV DE σ hop) y + toCar (A := 𝒪) (modN DV DE σ hop) y' := rfl
/--
@isnad1 id=injectiv.1h6v.s12.a8c7b3478e0a from=translated src=- shape=3b3b32f7 vocab=48f8f35f
-/
theorem toCar_injective : Function.Injective (toCar (A := 𝒪) (modN DV DE σ hop)) := fun _ _ h => h

def ren : FV →ₐ[𝒪] FE := MvPolynomial.rename (fun g => σ (Sum.inl g))

def sub : FE →ₐ[𝒪] FV :=
  MvPolynomial.aeval (fun γ => Sum.elim (fun g => MvPolynomial.X g) (fun _ => z₀) (σ.symm γ))

/--
@isnad1 id=eq.0h7v.s9.cbdb1d1a849a from=translated src=- shape=e0600205 vocab=712b2c14
-/
@[scoped simp] theorem ren_X (g : DV.Gen) : ren DV DE σ (MvPolynomial.X g) = MvPolynomial.X (σ (Sum.inl g)) := by
  simp [ren]
/--
@isnad1 id=eq.0h8v.s9.e3cba0863d3a from=translated src=- shape=b4e35081 vocab=2f1fabe6
-/
@[scoped simp] theorem sub_X_inl (g : DV.Gen) : sub DV DE σ z₀ (MvPolynomial.X (σ (Sum.inl g))) = MvPolynomial.X g := by
  simp [sub]
/--
@isnad1 id=eq.0h7v.s9.1e5a36356429 from=translated src=- shape=17302124 vocab=e068e79d
-/
@[scoped simp] theorem sub_X_inr : sub DV DE σ z₀ (MvPolynomial.X (σ (Sum.inr ()))) = z₀ := by
  simp [sub]

/--
@isnad1 id=eq.1h8v.s14.f4434ef595b6 from=translated src=- shape=a2989671 vocab=f67c19df
-/
theorem ren_smul_N (p : FV) (x : N♯) :
    ren DV DE σ p • x = toCar (A := 𝒪) (modN DV DE σ hop) (p • ofCar (A := 𝒪) (modN DV DE σ hop) x) := by
  induction p using MvPolynomial.induction_on generalizing x with
  | C a =>
    rw [ren, MvPolynomial.rename_C, C_smul_N, show (MvPolynomial.C a : FV) = algebraMap 𝒪 FV a from rfl,
      algebraMap_smul]; rfl
  | add p q hp hq => rw [map_add, add_smul, hp, hq, add_smul, toCar_add]
  | mul_X p g hp =>
    rw [map_mul, ren_X, mul_smul, X_inl_smul_N, hp, ofCar_toCar_N, mul_smul]

/--
@isnad1 id=ex.0h8v.s10.477ebb6de6cf from=translated src=- shape=d6196edd vocab=e2019417
-/
theorem exists_decomp (f : FE) : ∃ h : FE,
    f = ren DV DE σ (sub DV DE σ z₀ f) + (MvPolynomial.X (σ (Sum.inr ())) - ren DV DE σ z₀) * h := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp [ren, sub]⟩
  | add p q hp hq =>
    obtain ⟨h₁, e₁⟩ := hp; obtain ⟨h₂, e₂⟩ := hq
    exact ⟨h₁ + h₂, by rw [map_add, map_add, mul_add]; nth_rw 1 [e₁]; nth_rw 1 [e₂]; ring⟩
  | mul_X p γ hp =>
    obtain ⟨h, e⟩ := hp
    obtain ⟨x, rfl⟩ := σ.surjective γ
    rcases x with g | u
    · refine ⟨h * MvPolynomial.X (σ (Sum.inl g)), ?_⟩
      rw [map_mul, sub_X_inl, map_mul, ren_X]; nth_rw 1 [e]; ring
    · obtain rfl : u = () := rfl
      refine ⟨ren DV DE σ (sub DV DE σ z₀ p) + h * MvPolynomial.X (σ (Sum.inr ())), ?_⟩
      rw [map_mul, sub_X_inr, map_mul]
      nth_rw 1 [e]; ring

def fN : V →ₗ[FE] N♯ :=
  { toCar (A := 𝒪) (modN DV DE σ hop) ∘ₗ DV.toMLₒ with
    map_smul' := fun f v => by
      induction f using MvPolynomial.induction_on generalizing v with
      | C a =>
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
        rw [show (MvPolynomial.C a : FE) = algebraMap 𝒪 FE a from rfl, algebraMap_smul, algebraMap_smul,
          LinearMap.map_smul]
      | add p q hp hq =>
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply] at hp hq ⊢
        rw [add_smul, map_add, hp, hq, add_smul]
      | mul_X p γ hp =>
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply] at hp ⊢
        rw [mul_smul, hp, mul_smul]
        congr 1
        obtain ⟨x, rfl⟩ := σ.surjective γ
        rcases x with g | u
        · rw [X_inl_smul_N, LinearMap.comp_apply, LinearMap.comp_apply, ofCar_toCar_N, X_smul_E, hop,
            HeckeData.toMLₒ_apply, HeckeData.toMLₒ_apply, ← X_smul_V DV g v, LinearMap.map_smul]
        · obtain rfl : u = () := rfl
          rw [X_inr_smul_N, LinearMap.comp_apply, LinearMap.comp_apply, ofCar_toCar_N, X_smul_E,
            HeckeData.toMLₒ_apply, HeckeData.toMLₒ_apply]
          congr 1
          show DV.toML (Z♭ v) = ZL DV DE σ hop (LocalizedModule.mk v 1)
          rw [ZL_mk]; rfl }

/--
@isnad1 id=eq.1h7v.s13.a8c308793b8e from=translated src=- shape=7f481bd8 vocab=edf292ee
-/
theorem fN_apply (v : V) : fN DV DE σ hop v = toCar (A := 𝒪) (modN DV DE σ hop) (DV.toML v) := rfl

def mN : Submodule 𝒪 DV.ML := (maximalIdeal 𝒪) • ⊤

/--
@isnad1 id=mem.1h6v.s11.e2b094b71467 from=translated src=- shape=59eb9ea2 vocab=abc30b65
-/
theorem smul_mem_mN_of_mem {a : 𝒪} (ha : a ∈ maximalIdeal 𝒪) (y : DV.ML) : a • y ∈ mN DV :=
  Submodule.smul_mem_smul ha Submodule.mem_top

/--
@isnad1 id=mem.1h6v.s11.2a1f6b5b928d from=translated src=- shape=a5d923d7 vocab=71874b95
-/
theorem loc_smul_mem_mN (r : Loc DV) {y : DV.ML} (hy : y ∈ mN DV) : r • y ∈ mN DV := by
  refine Submodule.smul_induction_on hy (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
  · rw [smul_comm]; exact smul_mem_mN_of_mem DV ha _
  · rw [smul_add]; exact Submodule.add_mem _ hy hy'

/--
@isnad1 id=mem.1h6v.s12.8b359c92b247 from=translated src=- shape=a5d923d7 vocab=fb712e81
-/
theorem F_smul_mem_mN (f : FV) {y : DV.ML} (hy : y ∈ mN DV) : f • y ∈ mN DV := by
  rw [← IsScalarTower.algebraMap_smul (Loc DV) f y]; exact loc_smul_mem_mN DV _ hy

/--
@isnad1 id=mem.2h7v.s12.62ba3b99b522 from=translated src=- shape=7d0fd5a8 vocab=be4f84b5
-/
theorem ZL_mem_mN {y : DV.ML} (hy : y ∈ mN DV) : ZL DV DE σ hop y ∈ mN DV := by
  refine Submodule.smul_induction_on hy (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
  · rw [LinearMap.map_smul_of_tower]; exact smul_mem_mN_of_mem DV ha _
  · rw [map_add]; exact Submodule.add_mem _ hy hy'

/--
@isnad1 id=mem.2h8v.s14.a5a0b0f6532d from=translated src=- shape=c18ba29b vocab=ba2f45a4
-/
theorem FE_smul_mem_mN (f : FE) {x : N♯} (hx : ofCar (A := 𝒪) (modN DV DE σ hop) x ∈ mN DV) :
    ofCar (A := 𝒪) (modN DV DE σ hop) (f • x) ∈ mN DV := by
  induction f using MvPolynomial.induction_on generalizing x with
  | C a => rw [C_smul_N]; exact Submodule.smul_mem _ a hx
  | add p q hp hq => rw [add_smul]; exact Submodule.add_mem _ (hp hx) (hq hx)
  | mul_X p γ hp =>
    rw [mul_smul]
    apply hp
    obtain ⟨y, rfl⟩ := σ.surjective γ
    rcases y with g | u
    · rw [X_inl_smul_N, ofCar_toCar_N]; exact F_smul_mem_mN DV _ hx
    · obtain rfl : u = () := rfl
      rw [X_inr_smul_N, ofCar_toCar_N]; exact ZL_mem_mN DV DE σ hop hx

def NL : Module.End 𝒪 DV.ML := (ZL DV DE σ hop).restrictScalars 𝒪 - (ρV DV z₀ : Module.End 𝒪 DV.ML)

/--
@isnad1 id=eq.1h8v.s12.d0b9756f87fa from=translated src=- shape=b5aa97f4 vocab=66b5418d
-/
theorem NL_apply (y : DV.ML) : NL DV DE σ hop z₀ y = ZL DV DE σ hop y - z₀ • y := rfl

/--
@isnad1 id=eq.1h8v.s14.bbf695bb3780 from=translated src=- shape=b1589fac vocab=abf26e1e
-/
theorem Xz_sub_smul_N (x : N♯) :
    ((MvPolynomial.X (σ (Sum.inr ())) : FE) - ren DV DE σ z₀) • x =
      toCar (A := 𝒪) (modN DV DE σ hop) (NL DV DE σ hop z₀ (ofCar (A := 𝒪) (modN DV DE σ hop) x)) := by
  rw [sub_smul, X_inr_smul_N, ren_smul_N]; rfl

/--
@isnad1 id=eq.1h8v.s12.332c019b3198 from=translated src=- shape=ceb2e7e4 vocab=8d007868
-/
theorem toML_Zsub (v : V) :
    DV.toML ((Z♭ - DV.opAlgHom z₀) v) = (NL DV DE σ hop z₀) (DV.toML v) := by
  rw [LinearMap.sub_apply, NL_apply, map_sub, show DV.opAlgHom z₀ v = z₀ • v from rfl, LinearMap.map_smul]
  congr 1
  show DV.toML (Z♭ v) = ZL DV DE σ hop (LocalizedModule.mk v 1)
  rw [ZL_mk]; rfl

/--
@isnad1 id=eq.1h9v.s13.be5f12275952 from=translated src=- shape=ca05c7a7 vocab=3f763a31
-/
theorem toML_Zsub_pow (n : ℕ) (v : V) :
    DV.toML (((Z♭ - DV.opAlgHom z₀) ^ n) v) =
      (NL DV DE σ hop z₀ ^ n) (DV.toML v) := by
  induction n generalizing v with
  | zero => rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, toML_Zsub DV DE σ hop, ← Module.End.mul_apply, ← pow_succ]

/--
@isnad1 id=eq.1h9v.s14.4f38c5ca20fd from=translated src=- shape=22e781fd vocab=e91b0fa5
-/
theorem Xz_sub_pow_smul_N (n : ℕ) (x : N♯) :
    (((MvPolynomial.X (σ (Sum.inr ())) : FE) - ren DV DE σ z₀) ^ n) • x =
      toCar (A := 𝒪) (modN DV DE σ hop) ((NL DV DE σ hop z₀ ^ n)
        (ofCar (A := 𝒪) (modN DV DE σ hop) x)) := by
  induction n generalizing x with
  | zero => rw [pow_zero, one_smul, pow_zero, Module.End.one_apply]; rfl
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, Xz_sub_smul_N, ofCar_toCar_N, pow_succ', Module.End.mul_apply]

/--
@isnad1 id=eq.1h9v.s12.55ad9129ed16 from=translated src=- shape=5390ffce vocab=ddf48c4b
-/
theorem NL_loc_smul (r : Loc DV) (y : DV.ML) :
    (NL DV DE σ hop z₀) (r • y) = r • (NL DV DE σ hop z₀) y := by
  rw [NL_apply, NL_apply, LinearMap.map_smul, smul_sub, ← IsScalarTower.algebraMap_smul (Loc DV) z₀ (r • y),
    ← IsScalarTower.algebraMap_smul (Loc DV) z₀ y, ← mul_smul, mul_comm, mul_smul]

/--
@isnad1 id=eq.1h10v.s13.fffce7064a48 from=translated src=- shape=3c8b8cb8 vocab=0d255216
-/
theorem NL_pow_loc_smul (n : ℕ) (r : Loc DV) (y : DV.ML) :
    (NL DV DE σ hop z₀ ^ n) (r • y) =
      r • (NL DV DE σ hop z₀ ^ n) y := by
  induction n generalizing y with
  | zero => rw [pow_zero, Module.End.one_apply, Module.End.one_apply]
  | succ n ih => rw [pow_succ, Module.End.mul_apply, NL_loc_smul, ih, ← Module.End.mul_apply, ← pow_succ]

variable (n : ℕ)
  (hnil : ∀ v : V, DV.toML (((DE.op (σ (Sum.inr ())) - DV.opAlgHom z₀) ^ n) v) ∈
    (maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 DV.ML))

include hnil in

/--
@isnad1 id=mem.2h9v.s13.898e83664e06 from=translated src=- shape=179baf4d vocab=9c9bb4c3
-/
theorem NL_pow_mem (y : DV.ML) : (NL DV DE σ hop z₀ ^ n) y ∈ mN DV := by
  induction y using LocalizedModule.induction_on with
  | h v t =>
    have : (LocalizedModule.mk v t : DV.ML) = Localization.mk 1 t • DV.toML v := by
      show _ = _ • LocalizedModule.mk v 1
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [this, NL_pow_loc_smul]
    exact loc_smul_mem_mN DV _ (by rw [← toML_Zsub_pow]; exact hnil v)

include hnil in
/--
@isnad1 id=mem.2h9v.s14.36ecf6e3ff44 from=translated src=- shape=229be8b0 vocab=9bde731f
-/
theorem Xz_sub_pow_smul_mem (x : N♯) :
    ofCar (A := 𝒪) (modN DV DE σ hop) ((((MvPolynomial.X (σ (Sum.inr ())) : FE) - ren DV DE σ z₀) ^ n) • x) ∈
      mN DV := by
  rw [Xz_sub_pow_smul_N]; exact NL_pow_mem DV DE σ hop z₀ n hnil _

variable (hθ : ∀ g : DV.Gen, DE.θbar (σ (Sum.inl g)) = DV.θbar g)
  (hz : DE.θbar (σ (Sum.inr ())) = DV.thetaTilde z₀)

include hθ hz in
/--
@isnad1 id=eq.2h8v.s10.f653fdf120c3 from=translated src=- shape=6d4b5991 vocab=4fa2d55a
-/
theorem thetaTilde_sub (f : FE) : DV.thetaTilde (sub DV DE σ z₀ f) = DE.thetaTilde f := by
  suffices h : DV.thetaTilde.comp (sub DV DE σ z₀) = DE.thetaTilde from congrArg (fun φ => φ f) h
  apply MvPolynomial.algHom_ext
  intro γ
  obtain ⟨x, rfl⟩ := σ.surjective γ
  rcases x with g | u
  · rw [AlgHom.comp_apply, sub_X_inl, HeckeData.thetaTilde, MvPolynomial.aeval_X, HeckeData.thetaTilde,
      MvPolynomial.aeval_X, hθ]
  · obtain rfl : u = () := rfl
    rw [AlgHom.comp_apply, sub_X_inr, ← hz]
    show _ = MvPolynomial.aeval DE.θbar (MvPolynomial.X (σ (Sum.inr ())))
    rw [MvPolynomial.aeval_X]

include hθ hz in
/--
@isnad1 id=mem.2h8v.s10.262e2c61ca0c from=translated src=- shape=4e745385 vocab=1174e1f7
-/
theorem sub_mem (s : SE) : sub DV DE σ z₀ (s : FE) ∈ SV := by
  rw [mem_primeCompl_iff, thetaTilde_sub DV DE σ z₀ hθ hz]; exact thetaTilde_ne_zero_of_mem DE s

/--
@isnad1 id=surjecti.1h5v.s10.3c093ef893b9 from=translated src=- shape=3e658cbe vocab=42a8f0d6
-/
theorem smul_surjective_of_mem {p : FV} (hp : p ∈ SV) : Function.Surjective (fun y : DV.ML => p • y) := by
  have hu := isUnit_smul_loc (M := V) (⟨p, hp⟩ : SV)
  rw [Module.End.isUnit_iff] at hu
  exact hu.2

include hθ hz hnil in

/--
@isnad1 id=ex.4h10v.s14.4c060245c523 from=translated src=- shape=046947a8 vocab=930fc524
-/
theorem exists_sub_smul_mem (s : SE) (x : N♯) :
    ∃ y : N♯, ofCar (A := 𝒪) (modN DV DE σ hop) (x - (s : FE) • y) ∈ mN DV := by
  obtain ⟨h, e⟩ := exists_decomp DV DE σ z₀ (s : FE)
  set a : FE := ren DV DE σ (sub DV DE σ z₀ s) with ha
  set b : FE := -((MvPolynomial.X (σ (Sum.inr ())) - ren DV DE σ z₀) * h) with hb
  have hs : (s : FE) = a - b := by rw [ha, hb, sub_neg_eq_add]; exact e

  have hsurj : Function.Surjective (fun y : N♯ => a ^ n • y) := by
    intro y
    obtain ⟨y', hy'⟩ := smul_surjective_of_mem DV (pow_mem (sub_mem DV DE σ z₀ hθ hz s) n)
      (ofCar (A := 𝒪) (modN DV DE σ hop) y)
    refine ⟨toCar (A := 𝒪) (modN DV DE σ hop) y', ?_⟩
    show a ^ n • _ = y
    rw [ha, ← map_pow, ren_smul_N, ofCar_toCar_N]
    exact congrArg _ hy'
  obtain ⟨x'', hx''⟩ := hsurj x
  set P : FE := ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)
  refine ⟨P • x'', ?_⟩
  have key : (s : FE) * P = a ^ n - b ^ n := by rw [hs, mul_comm]; exact geom_sum₂_mul a b n
  rw [← mul_smul, key]
  have hsub : (a ^ n - b ^ n) • x'' = a ^ n • x'' - b ^ n • x'' := sub_smul _ _ _
  rw [hsub, ← hx'', sub_sub_cancel]
  show ofCar (A := 𝒪) (modN DV DE σ hop) (b ^ n • x'') ∈ mN DV
  rw [hb, neg_pow, mul_pow, mul_smul, mul_comm, mul_smul]
  exact FE_smul_mem_mN DV DE σ hop _ (FE_smul_mem_mN DV DE σ hop _ (Xz_sub_pow_smul_mem DV DE σ hop z₀ n hnil _))

include hθ in
/--
@isnad1 id=eq.1h7v.s10.e71a888ab01b from=translated src=- shape=2c02a91b vocab=66700d11
-/
theorem thetaTilde_ren (q : FV) : DE.thetaTilde (ren DV DE σ q) = DV.thetaTilde q := by
  suffices h : DE.thetaTilde.comp (ren DV DE σ) = DV.thetaTilde from congrArg (fun φ => φ q) h
  apply MvPolynomial.algHom_ext
  intro g
  rw [AlgHom.comp_apply, ren_X, HeckeData.thetaTilde, MvPolynomial.aeval_X, HeckeData.thetaTilde,
    MvPolynomial.aeval_X, hθ]

include hθ in
/--
@isnad1 id=mem.1h7v.s10.11dc56ec7da2 from=translated src=- shape=bb7815b3 vocab=bf337f73
-/
theorem ren_mem (t : SV) : ren DV DE σ (t : FV) ∈ SE := by
  rw [mem_primeCompl_iff, thetaTilde_ren DV DE σ hθ]; exact thetaTilde_ne_zero_of_mem DV t

include hop in

/--
@isnad1 id=eq.1h8v.s10.37e0f12ce9aa from=translated src=- shape=2e7aea98 vocab=8465b87c
-/
theorem ren_smul_V (q : FV) (v : V) : (ren DV DE σ q : FE) • v = q • v := by
  induction q using MvPolynomial.induction_on generalizing v with
  | C a =>
    rw [ren, MvPolynomial.rename_C, show (MvPolynomial.C a : FE) = algebraMap 𝒪 FE a from rfl, algebraMap_smul,
      show (MvPolynomial.C a : FV) = algebraMap 𝒪 FV a from rfl, algebraMap_smul]
  | add p q hp hq => rw [map_add, add_smul, hp, hq, add_smul]
  | mul_X p g hp => rw [map_mul, ren_X, mul_smul, X_smul_E, hop, ← X_smul_V DV, hp, mul_smul]

section Units

variable [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Module.Finite 𝒪 V]
  (hk : Function.Surjective (algebraMap 𝒪 k))

include hk hθ hz hnil in

/--
@isnad1 id=bijectiv.5h9v.s14.aa2d6dcfcf1a from=translated src=- shape=36932be7 vocab=13c73ff0
-/
theorem smul_bijective (s : SE) : Function.Bijective (fun x : N♯ => (s : FE) • x) := by
  haveI hfin : Module.Finite 𝒪 N♯ := (CohCarrier.HeckeData.finite_ML_and_free_ML hk DV).1
  let φ : N♯ →ₗ[𝒪] N♯ := (LinearMap.lsmul FE N♯ (s : FE)).restrictScalars 𝒪
  have hφ : ∀ x, φ x = (s : FE) • x := fun _ => rfl

  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top (R := 𝒪) (M := N♯))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro x _
    obtain ⟨y, hy⟩ := exists_sub_smul_mem DV DE σ hop z₀ n hnil hθ hz s x
    rw [show x = φ y + (x - (s : FE) • y) by rw [hφ, add_sub_cancel]]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self φ y) hy
  have hinj : Function.Injective φ := OrzechProperty.injective_of_surjective_endomorphism φ hsurj
  exact ⟨hinj, hsurj⟩

include hk hθ hz hnil in

/--
@isnad1 id=islocali.5h8v.s13.8c71d597af01 from=translated src=- shape=07184191 vocab=7e333530
-/
theorem isLocalizedModule_fN : IsLocalizedModule DE.mTheta.primeCompl (fN DV DE σ hop) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    exact smul_bijective DV DE σ hop z₀ n hnil hθ hz hk s
  surj y := by
    induction' hy : ofCar (A := 𝒪) (modN DV DE σ hop) y using LocalizedModule.induction_on with v t
    refine ⟨(v, ⟨ren DV DE σ (t : FV), ren_mem DV DE σ hθ t⟩), ?_⟩
    show (ren DV DE σ (t : FV) : FE) • y = _
    rw [ren_smul_N, hy, fN_apply, LocalizedModule.smul'_mk]
    congr 1
    show (LocalizedModule.mk ((t : FV) • v) t : DV.ML) = LocalizedModule.mk v 1
    rw [LocalizedModule.mk_eq]; exact ⟨1, by simp [Submonoid.smul_def]⟩
  exists_of_eq {v₁ v₂} h := by
    have h' : (LocalizedModule.mk v₁ 1 : DV.ML) = LocalizedModule.mk v₂ 1 := toCar_injective DV DE σ hop h
    rw [LocalizedModule.mk_eq] at h'
    obtain ⟨u, hu⟩ := h'
    refine ⟨⟨ren DV DE σ (u : FV), ren_mem DV DE σ hθ u⟩, ?_⟩
    simp only [Submonoid.smul_def, one_smul] at hu
    show (ren DV DE σ (u : FV) : FE) • v₁ = (ren DV DE σ (u : FV) : FE) • v₂
    rw [ren_smul_V DV DE σ hop, ren_smul_V DV DE σ hop]
    exact hu

end Units

end Setting

section Main

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  {k : Type} [Field k] [Algebra 𝒪 k]
  {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]

/--
@isnad1 id=ex.5h8v.s14.b3a14b7b0e9e from=translated src=- shape=9d860aa4 vocab=b753e774
-/
theorem main (hk : Function.Surjective (algebraMap 𝒪 k))
    (DV DE : HeckeData 𝒪 V k) (σ : DV.Gen ⊕ Unit ≃ DE.Gen)
    (hop : ∀ g : DV.Gen, DE.op (σ (Sum.inl g)) = DV.op g)
    (hθ : ∀ g : DV.Gen, DE.θbar (σ (Sum.inl g)) = DV.θbar g)
    (z₀ : DV.FreeAlg) (hz : DE.θbar (σ (Sum.inr ())) = DV.thetaTilde z₀)
    (n : ℕ) (hnil : ∀ v : V, DV.toML (((DE.op (σ (Sum.inr ())) - DV.opAlgHom z₀) ^ n) v) ∈
      (maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 DV.ML)) :
    ∃ e : DE.ML ≃ₗ[𝒪] DV.ML, ∀ (g : DV.Gen) (x : DE.ML),
      e ((MvPolynomial.X (σ (Sum.inl g)) : DE.FreeAlg) • x) = (MvPolynomial.X g : DV.FreeAlg) • e x := by
  haveI := isLocalizedModule_fN DV DE σ hop z₀ n hnil hθ hz hk
  let iso := IsLocalizedModule.iso DE.mTheta.primeCompl (fN DV DE σ hop)
  let c : Car DE.FreeAlg DV.ML (modN DV DE σ hop) ≃ₗ[𝒪] DV.ML :=
    { ofCar (A := 𝒪) (modN DV DE σ hop) with
      invFun := toCar (A := 𝒪) (modN DV DE σ hop)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨(iso.restrictScalars 𝒪).trans c, fun g x => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.map_smul, X_inl_smul_N]
  rfl

end Main

end TWExt
open scoped _root_.P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.TWExt

open CohCarrier IsLocalRing in
/--
@isnad1 id=ex.5h8v.s14.75d69b7ac32f from=translated src=- shape=fe44e1cb vocab=b753e774
-/
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]

    (DV DE : HeckeData 𝒪 V k) (σ : DV.Gen ⊕ Unit ≃ DE.Gen)
    (hop : ∀ g : DV.Gen, DE.op (σ (Sum.inl g)) = DV.op g)
    (hθ : ∀ g : DV.Gen, DE.θbar (σ (Sum.inl g)) = DV.θbar g)

    (z₀ : DV.FreeAlg) (hz : DE.θbar (σ (Sum.inr ())) = DV.thetaTilde z₀)

    (n : ℕ) (hnil : ∀ v : V, DV.toML (((DE.op (σ (Sum.inr ())) - DV.opAlgHom z₀) ^ n) v) ∈
      (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 DV.ML)) :
    ∃ e : DE.ML ≃ₗ[𝒪] DV.ML, ∀ (g : DV.Gen) (x : DE.ML),
      e ((MvPolynomial.X (σ (Sum.inl g)) : DE.FreeAlg) • x) = (MvPolynomial.X g : DV.FreeAlg) • e x :=
  TWExt.main hk DV DE σ hop hθ z₀ hz n hnil

end
open scoped _root_.P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.TWExt
