import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_exists_linearMap_baseChange_of_galoisStable_plane.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_exists_linearMap_baseChange_of_galoisStable_plane

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

noncomputable section

namespace LattC4

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
  {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Free O M]

variable (O K M) in

def iota : M →ₗ[O] K ⊗[O] M := TensorProduct.mk O K M 1

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [Module.Finite O M]
  [Module.Free O M] in
/--
@isnad1 id=eq.0h4v.s8.9c236b97b09c from=translated src=- shape=1388acc6 vocab=dbb22503
-/
@[scoped simp] theorem iota_apply (m : M) : iota O K M m = (1 : K) ⊗ₜ[O] m := rfl

/--
@isnad1 id=islocali.0h3v.s7.54c13e077957 from=translated src=- shape=3e999186 vocab=1437bb54
-/
scoped instance isLocalizedModule_iota : IsLocalizedModule (nonZeroDivisors O) (iota O K M) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K (iota O K M)).mpr
    (TensorProduct.isBaseChange O M K)

omit [Module.Finite O M] in
/--
@isnad1 id=injectiv.0h3v.s8.bba0dba4f9f1 from=translated src=- shape=a484f3e8 vocab=16237222
-/
theorem iota_injective : Function.Injective (iota O K M) :=
  (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors O) (iota O K M)).mpr fun c =>
    Module.IsTorsionFree.isSMulRegular (isRegular_iff_ne_zero'.mpr (nonZeroDivisors.coe_ne_zero c))

omit [Module.Finite O M] [Module.Free O M] in

/--
@isnad1 id=ex.0h4v.s9.eda7ebf56abd from=translated src=- shape=7fcc477e vocab=b6ee7523
-/
theorem exists_iota_eq_smul (x : K ⊗[O] M) :
    ∃ (a : O) (m : M), a ≠ 0 ∧ iota O K M m = algebraMap O K a • x := by
  obtain ⟨⟨m, s⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors O) (iota O K M) x
  refine ⟨(s : O), m, nonZeroDivisors.coe_ne_zero s, ?_⟩
  rw [algebraMap_smul, ← h]
  rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [Module.Finite O M]
  [Module.Free O M] in
/--
@isnad1 id=eq.0h5v.s10.462086a4f95f from=translated src=- shape=f693d16b vocab=eafe90b5
-/
theorem baseChange_iota (f : M →ₗ[O] M) (m : M) :
    f.baseChange K (iota O K M m) = iota O K M (f m) := by
  rw [iota_apply, LinearMap.baseChange_tmul, iota_apply]

variable (W : Submodule K (K ⊗[O] M))

def latt : Submodule O M := (W.restrictScalars O).comap (iota O K M)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [Module.Finite O M]
  [Module.Free O M] in
/--
@isnad1 id=iff.0h5v.s9.74c9fc1a4021 from=translated src=- shape=95996423 vocab=ac3200f9
-/
theorem mem_latt (m : M) : m ∈ latt W ↔ iota O K M m ∈ W := Iff.rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [Module.Finite O M] [Module.Free O M] in
/--
@isnad1 id=mem.2h6v.s8.9bab95321c54 from=translated src=- shape=95821465 vocab=019fed1d
-/
theorem latt_saturated {a : O} (ha : a ≠ 0) {m : M} (h : a • m ∈ latt W) : m ∈ latt W := by
  rw [mem_latt] at h ⊢
  rw [map_smul, ← algebraMap_smul K a] at h
  have haK : algebraMap O K a ≠ 0 := fun h' =>
    ha (IsFractionRing.injective O K (by rw [h', map_zero]))
  have h2 := W.smul_mem (algebraMap O K a)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ haK, one_smul] at h2

/--
@isnad1 id=free.0h4v.s8.97969d9b8b0e from=translated src=- shape=f428adb1 vocab=1c49abe8
-/
scoped instance latt_free : Module.Free O (latt W) := Module.free_of_finite_type_torsion_free'

def psi : K ⊗[O] latt W →ₗ[K] K ⊗[O] M := ((latt W).subtype).baseChange K

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [Module.Finite O M]
  [Module.Free O M] in
/--
@isnad1 id=eq.0h6v.s11.66ac56d3e97b from=translated src=- shape=4fe001fa vocab=79ac4192
-/
theorem psi_tmul (k : K) (v : latt W) : psi W (k ⊗ₜ[O] v) = k • iota O K M (v : M) := by
  simp only [psi, LinearMap.baseChange_tmul, Submodule.coe_subtype, iota_apply]
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

omit [IsDomain O] [IsDiscreteValuationRing O] [Module.Finite O M] [Module.Free O M] in
/--
@isnad1 id=injectiv.0h4v.s10.0a9af78a7554 from=translated src=- shape=4a028725 vocab=3c5e10ee
-/
theorem psi_injective : Function.Injective (psi W) := by
  haveI : Module.Flat O K := IsLocalization.flat K (nonZeroDivisors O)
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := K) (latt W).subtype
    (latt W).injective_subtype
  intro x y hxy
  apply h
  have hx : (LinearMap.lTensor K (latt W).subtype) x = psi W x := by
    rw [psi, LinearMap.baseChange_eq_ltensor]
  have hy : (LinearMap.lTensor K (latt W).subtype) y = psi W y := by
    rw [psi, LinearMap.baseChange_eq_ltensor]
  rw [hx, hy, hxy]

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [Module.Finite O M]
  [Module.Free O M] in
/--
@isnad1 id=mem.0h5v.s11.89170cc5d93c from=translated src=- shape=61c7185f vocab=b34e237a
-/
theorem psi_mem (x : K ⊗[O] latt W) : psi W x ∈ W := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact W.zero_mem
  | tmul k v =>
    rw [psi_tmul]
    exact W.smul_mem k ((mem_latt W (v : M)).mp v.2)
  | add x y hx hy => rw [map_add]; exact W.add_mem hx hy

omit [Module.Finite O M] [Module.Free O M] in
/--
@isnad1 id=eq.0h4v.s9.dc767a29441b from=translated src=- shape=ad06fb53 vocab=86b72380
-/
theorem range_psi : LinearMap.range (psi W) = W := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact psi_mem W x
  · intro w hw
    obtain ⟨a, m, ha, hm⟩ := exists_iota_eq_smul (O := O) w
    have haK : algebraMap O K a ≠ 0 := fun h' =>
      ha (IsFractionRing.injective O K (by rw [h', map_zero]))
    have hmL : m ∈ latt W := by
      rw [mem_latt, hm]
      exact W.smul_mem _ hw
    refine ⟨(algebraMap O K a)⁻¹ ⊗ₜ[O] ⟨m, hmL⟩, ?_⟩
    rw [psi_tmul]
    change (algebraMap O K a)⁻¹ • iota O K M m = w
    rw [hm, smul_smul, inv_mul_cancel₀ haK, one_smul]

def Phi : K ⊗[O] latt W ≃ₗ[K] W :=
  (LinearEquiv.ofInjective (psi W) (psi_injective W)).trans (LinearEquiv.ofEq _ _ (range_psi W))

omit [Module.Finite O M] [Module.Free O M] in
/--
@isnad1 id=eq.0h5v.s12.f50479d28d54 from=translated src=- shape=19cc23f1 vocab=fd7437a1
-/
theorem Phi_apply_coe (x : K ⊗[O] latt W) : ((Phi W x : W) : K ⊗[O] M) = psi W x := rfl

/--
@isnad1 id=eq.1h4v.s10.74771f6daece from=translated src=- shape=39184ac6 vocab=0d461ca9
-/
theorem finrank_latt (hrank : Module.finrank K W = 2) : Module.finrank O (latt W) = 2 := by
  rw [← Module.finrank_baseChange (R := K), (Phi W).finrank_eq, hrank]

variable (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End O M)
  (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W, (ρM σ).baseChange K w ∈ W)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [Module.Finite O M]
  [Module.Free O M] in
include hW in
/--
@isnad1 id=mem.2h7v.s12.4476c60314e8 from=translated src=- shape=4e5d2c09 vocab=1c26c6ac
-/
theorem rho_mem_latt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∀ m ∈ latt W, ρM σ m ∈ latt W := by
  intro m hm
  rw [mem_latt] at hm ⊢
  rw [← baseChange_iota]
  exact hW σ _ hm

def rhoL : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End O (latt W) where
  toFun σ := (ρM σ).restrict (rho_mem_latt W ρM hW σ)
  map_one' := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [LinearMap.restrict_apply, map_one, Module.End.one_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [LinearMap.restrict_apply, map_mul, Module.End.mul_apply]

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [Module.Finite O M]
  [Module.Free O M] in
/--
@isnad1 id=eq.1h7v.s12.1d95442d1f70 from=translated src=- shape=64d1587f vocab=93f549ac
-/
@[scoped simp] theorem coe_rhoL_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : latt W) :
    ((rhoL W ρM hW σ v : latt W) : M) = ρM σ (v : M) := rfl

omit [Module.Finite O M] [Module.Free O M] in

/--
@isnad1 id=galoisac.2h5v.s11.acebd3bfc198 from=translated src=- shape=2367e223 vocab=15c68a56
-/
theorem rhoL_isAdicContinuous (hcont : GaloisActionIsAdicContinuous O ρM) :
    GaloisActionIsAdicContinuous O (rhoL W ρM hW) := by
  intro n
  obtain ⟨L, hL, h⟩ := hcont n
  refine ⟨L, hL, fun σ hσ v => ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpow : IsLocalRing.maximalIdeal O ^ n = Ideal.span {ϖ ^ n} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hv := h σ hσ (v : M)
  rw [hpow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hv
  obtain ⟨b, -, hb⟩ := hv

  have hdiff : ρM σ (v : M) - (v : M) ∈ latt W :=
    (latt W).sub_mem (rho_mem_latt W ρM hW σ _ v.2) v.2
  have hϖn : ϖ ^ n ≠ 0 := pow_ne_zero n hϖ.ne_zero
  have hbL : b ∈ latt W := latt_saturated W hϖn (hb ▸ hdiff)
  rw [hpow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨⟨b, hbL⟩, Submodule.mem_top, Subtype.ext ?_⟩
  simp only [SetLike.val_smul, Submodule.coe_sub, coe_rhoL_apply]
  exact hb

omit [IsFractionRing O K] in

/--
@isnad1 id=eq.1h3v.s10.4ee942edd3db from=translated src=- shape=d39b1a4e vocab=99d6c20a
-/
theorem charpoly_eq_of_finrank_eq_two {V : Type} [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Module.Free K V] (h2 : Module.finrank K V = 2) (f : V →ₗ[K] V) :
    LinearMap.charpoly f = X ^ 2 - C (LinearMap.trace K V f) * X + C (LinearMap.det f) := by
  classical
  let b : Module.Basis (Fin 2) K V := Module.finBasisOfFinrankEq K V h2
  rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace K b f, LinearMap.det_toMatrix b f]

omit [Module.Finite O M] [Module.Free O M] in

/--
@isnad1 id=eq.1h6v.s14.2095d8da35f6 from=translated src=- shape=0a2a9a39 vocab=e5cad01a
-/
theorem Phi_conj (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (Phi W).conj ((rhoL W ρM hW σ).baseChange K) = ((ρM σ).baseChange K).restrict (hW σ) := by
  have key : ∀ x : K ⊗[O] latt W,
      ((Phi W ((rhoL W ρM hW σ).baseChange K x) : W) : K ⊗[O] M) =
        (ρM σ).baseChange K ((Phi W x : W) : K ⊗[O] M) := by
    intro x
    rw [Phi_apply_coe, Phi_apply_coe]
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul k v =>
      rw [LinearMap.baseChange_tmul, psi_tmul, psi_tmul, map_smul, baseChange_iota, coe_rhoL_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.restrict_apply]
  change ((Phi W ((rhoL W ρM hW σ).baseChange K ((Phi W).symm w)) : W) : K ⊗[O] M) =
    (ρM σ).baseChange K (w : K ⊗[O] M)
  rw [key, LinearEquiv.apply_symm_apply]

/--
@isnad1 id=eq.2h6v.s15.629e7518017c from=translated src=- shape=d9503877 vocab=84c8ab27
-/
theorem charpoly_map (hrank : Module.finrank K W = 2) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (LinearMap.charpoly (rhoL W ρM hW σ)).map (algebraMap O K) =
      X ^ 2 - C (LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ))) * X
        + C (LinearMap.det (M := ↥W) (((ρM σ).baseChange K).restrict (hW σ))) := by
  have h2 : Module.finrank K (K ⊗[O] latt W) = 2 := by
    rw [Module.finrank_baseChange, finrank_latt W hrank]
  rw [← LinearMap.charpoly_baseChange, charpoly_eq_of_finrank_eq_two h2, ← Phi_conj W ρM hW σ,
    LinearMap.trace_conj' (N := ↥W) _ (Phi W), LinearEquiv.conj_apply, LinearMap.comp_assoc,
    LinearMap.det_conj (N := ↥W) _ (Phi W)]

end LattC4
open scoped _root_.P2MW.S_GaloisRepAdic_exists_linearMap_baseChange_of_galoisStable_plane.LattC4

end
open scoped _root_.P2MW.S_GaloisRepAdic_exists_linearMap_baseChange_of_galoisStable_plane.LattC4

open LattC4 in
/--
@isnad1 id=ex.3h5v.s15.de0b3044840c from=translated src=- shape=164ac374 vocab=c9d79422
-/
theorem solution
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Free O M]
    (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End O M)
    (hcont : GaloisActionIsAdicContinuous O ρM)
    (W : Submodule K (K ⊗[O] M)) (hrank : Module.finrank K W = 2)
    (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W,
      (ρM σ).baseChange K w ∈ W) :
    ∃ (ρ : GaloisRepAdic O) (e : ρ.V →ₗ[O] K ⊗[O] M),
      Function.Injective e ∧
      (∀ v : ρ.V, e v ∈ W) ∧
      (∀ w ∈ W, ∃ (a : O) (v : ρ.V), a ≠ 0 ∧ e v = algebraMap O K a • w) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V),
        e (ρ.ρ σ v) = (ρM σ).baseChange K (e v)) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (LinearMap.charpoly (ρ.ρ σ)).map (algebraMap O K) =
          X ^ 2 - C (LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ))) * X
            + C (LinearMap.det (M := ↥W) (((ρM σ).baseChange K).restrict (hW σ)))) := by
  let ρ : GaloisRepAdic O :=
    { V := latt W
      finrank_eq := finrank_latt W hrank
      ρ := rhoL W ρM hW
      isAdicContinuous := rhoL_isAdicContinuous W ρM hW hcont }
  refine ⟨ρ, (iota O K M).comp (latt W).subtype, ?_, ?_, ?_, ?_, ?_⟩
  · exact iota_injective.comp (latt W).injective_subtype
  · intro v
    exact (mem_latt W (v : M)).mp v.2
  · intro w hw
    obtain ⟨a, m, ha, hm⟩ := exists_iota_eq_smul (O := O) w
    have hmL : m ∈ latt W := by
      rw [mem_latt, hm]
      exact W.smul_mem _ hw
    exact ⟨a, ⟨m, hmL⟩, ha, hm⟩
  · intro σ v
    change iota O K M (ρM σ (v : M)) = (ρM σ).baseChange K (iota O K M (v : M))
    rw [baseChange_iota]
  · intro σ
    exact charpoly_map W ρM hW hrank σ
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
