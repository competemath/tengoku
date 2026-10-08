/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, David Gross, Davood Haji Taghi Tehrani
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Basic
public import Tengoku.Seed.LinearAlgebra.PiTensorProduct.Basic

/-!
# Projective seminorm on the tensor of a finite family of normed spaces.

Let `𝕜` be a normed field and `E` be a family of normed `𝕜`-vector spaces `Eᵢ`,
indexed by a finite type `ι`. We define a seminorm on `⨂[𝕜] i, Eᵢ`, which we call the
"projective seminorm". For `x` an element of `⨂[𝕜] i, Eᵢ`, its projective seminorm is the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`.

In particular, every norm `‖.‖` on `⨂[𝕜] i, Eᵢ` satisfying `‖⨂ₜ[𝕜] i, m i‖ ≤ Π i, ‖m i‖`
for every `m` in `Π i, Eᵢ` is bounded above by the projective seminorm.

## Main definitions

* `PiTensorProduct.projectiveSeminorm`: The projective seminorm on `⨂[𝕜] i, Eᵢ`.
* `PiTensorProduct.liftEquiv`: The bijection between `ContinuousMultilinearMap 𝕜 E F`
  and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`, as a continuous linear equivalence.
* `PiTensorProduct.liftIsometry`: The bijection between `ContinuousMultilinearMap 𝕜 E F`
  and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`, as an isometric linear equivalence.
* `PiTensorProduct.tprodL`: The canonical continuous multilinear map from `E = Πᵢ Eᵢ`
  to `⨂[𝕜] i, Eᵢ`.
* `PiTensorProduct.mapL`: The continuous linear map from `⨂[𝕜] i, Eᵢ` to `⨂[𝕜] i, E'ᵢ`
  induced by a family of continuous linear maps `Eᵢ →L[𝕜] E'ᵢ`.
* `PiTensorProduct.mapLMultilinear`: The continuous multilinear map from
  `Πᵢ (Eᵢ →L[𝕜] E'ᵢ)` to `(⨂[𝕜] i, Eᵢ) →L[𝕜] (⨂[𝕜] i, E'ᵢ)` sending a family
  `f` to `PiTensorProduct.mapL f`.

## Main results

* `PiTensorProduct.norm_eval_le_projectiveSeminorm`: If `f` is a continuous multilinear map on
  `E = Π i, Eᵢ` and `x` is in `⨂[𝕜] i, Eᵢ`, then `‖f.lift x‖ ≤ projectiveSeminorm x * ‖f‖`.
* `PiTensorProduct.mapL_opNorm`: If `f` is a family of continuous linear maps
  `fᵢ : Eᵢ →L[𝕜] Fᵢ`, then `‖PiTensorProduct.mapL f‖ ≤ ∏ i, ‖fᵢ‖`.
* `PiTensorProduct.opNorm_mapLMultilinear_le` : If `F` is a normed vecteor space, then
  `‖mapLMultilinear 𝕜 E F‖ ≤ 1`.

## TODO
* If the base field is `ℝ` or `ℂ` (or more generally if the injection of `Eᵢ` into its bidual is
  an isometry for every `i`), then we have `projectiveSeminorm ⨂ₜ[𝕜] i, mᵢ = Π i, ‖mᵢ‖`.
* If all `Eᵢ` are separated and satisfy `SeparatingDual`, then the seminorm on
  `⨂[𝕜] i, Eᵢ` is a norm.
* Adapt the remaining functoriality constructions/properties from `PiTensorProduct`.

-/

@[expose] public section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*}
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)]

open scoped TensorProduct

namespace PiTensorProduct

section NormedField

variable [NormedField 𝕜]

/-- A lift of the projective seminorm to `FreeAddMonoid (𝕜 × Π i, Eᵢ)`, useful to prove the
properties of `projectiveSeminorm`. -/
def projectiveSeminormAux : FreeAddMonoid (𝕜 × Π i, E i) → ℝ :=
  fun p ↦ (p.toList.map (fun p ↦ ‖p.1‖ * ∏ i, ‖p.2 i‖)).sum

/--
@isnad1 id=le.0h4v.s5.0a6faf7c5ac2 from=seed src=0 shape=33dfb94d vocab=88640bce
-/
theorem projectiveSeminormAux_nonneg (p : FreeAddMonoid (𝕜 × Π i, E i)) :
    0 ≤ projectiveSeminormAux p := by
  refine List.sum_nonneg fun a ↦ ?_
  simp only [List.mem_map, Prod.exists, forall_exists_index, and_imp]
  intro x m _ h
  simpa [← h] using by positivity

/--
@isnad1 id=le.0h5v.s7.b531b2af0904 from=seed src=0 shape=c7b9c020 vocab=f2516159
-/
theorem projectiveSeminormAux_add_le (p q : FreeAddMonoid (𝕜 × Π i, E i)) :
    projectiveSeminormAux (p + q) ≤ projectiveSeminormAux p + projectiveSeminormAux q := by
  simp [projectiveSeminormAux]

/--
@isnad1 id=eq.0h5v.s8.6d7834dd6163 from=seed src=0 shape=6293166b vocab=1b75e7c3
-/
theorem projectiveSeminormAux_smul (p : FreeAddMonoid (𝕜 × Π i, E i)) (a : 𝕜) :
    projectiveSeminormAux (p.map (fun (y : 𝕜 × Π i, E i) ↦ (a * y.1, y.2))) =
    ‖a‖ * projectiveSeminormAux p := by
  simp [projectiveSeminormAux, Function.comp_def, mul_assoc, List.sum_map_mul_left]

variable [∀ i, NormedSpace 𝕜 (E i)]

/--
@isnad1 id=bddbelow.0h4v.s8.73225d8ad420 from=seed src=0 shape=3761ac3b vocab=5305a148
-/
theorem bddBelow_projectiveSemiNormAux (x : ⨂[𝕜] i, E i) :
    BddBelow (Set.range (fun (p : lifts x) ↦ projectiveSeminormAux p.1)) :=
  ⟨0, by simp [mem_lowerBounds, projectiveSeminormAux_nonneg]⟩

noncomputable instance : Norm (⨂[𝕜] i, E i) :=
  ⟨fun x ↦ iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.val)⟩

/--
@isnad1 id=eq.0h4v.s8.a8c1ad027d86 from=seed src=0 shape=015d1946 vocab=211de5cd
-/
theorem norm_def (x : ⨂[𝕜] i, E i) :
    ‖x‖ = iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.val) := rfl

@[deprecated (since := "2026-06-10")] alias projectiveSeminormFun := norm

/--
@isnad1 id=eq.0h3v.s8.c5d3e5721e85 from=seed src=0 shape=ba0b3d3b vocab=f6b61485
-/
theorem projectiveSeminorm_zero : ‖(0 : ⨂[𝕜] i, E i)‖ = 0 :=
  le_antisymm (ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨0, lifts_zero⟩)
    (le_ciInf (fun p ↦ projectiveSeminormAux_nonneg p.val))

/--
@isnad1 id=le.0h5v.s9.06d472e6fd8c from=seed src=0 shape=d86f32ab vocab=c1cc6cf6
-/
theorem projectiveSeminorm_add_le (x y : ⨂[𝕜] i, E i) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  le_ciInf_add_ciInf (fun p q ↦ ciInf_le_of_le (bddBelow_projectiveSemiNormAux _)
    ⟨p.1 + q.1, lifts_add p.2 q.2⟩ (projectiveSeminormAux_add_le p.1 q.1))

/--
@isnad1 id=le.0h5v.s8.95bb8ec480df from=seed src=0 shape=d6325b4b vocab=37bb4663
-/
theorem projectiveSeminorm_smul_le (a : 𝕜) (x : ⨂[𝕜] i, E i) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ := by
  simp only [norm_def, Real.mul_iInf_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun p ↦ ?_
  simpa [projectiveSeminormAux_smul] using
    ciInf_le_of_le (bddBelow_projectiveSemiNormAux _) ⟨_, lifts_smul p.2 a⟩ (le_refl _)

/-- The projective seminorm on `⨂[𝕜] i, Eᵢ`. It sends an element `x` of `⨂[𝕜] i, Eᵢ` to the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`. -/
noncomputable def projectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) := .ofSMulLE
    norm projectiveSeminorm_zero projectiveSeminorm_add_le projectiveSeminorm_smul_le

noncomputable instance : SeminormedAddCommGroup (⨂[𝕜] i, E i) :=
  fast_instance% AddGroupSeminorm.toSeminormedAddCommGroup projectiveSeminorm.toAddGroupSeminorm

noncomputable instance : NormedSpace 𝕜 (⨂[𝕜] i, E i) := ⟨projectiveSeminorm_smul_le⟩

/--
@isnad1 id=eq.0h4v.s9.a62b4e778fe2 from=seed src=0 shape=a40b4da2 vocab=8f6920f7
-/
@[deprecated norm_def (since := "2026-06-10")]
theorem projectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    projectiveSeminorm x = iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.1) := rfl

/--
@isnad1 id=le.0h4v.s9.f01030af1917 from=seed src=0 shape=c64d8bef vocab=db550971
-/
theorem projectiveSeminorm_tprod_le (m : Π i, E i) :
    ‖(⨂ₜ[𝕜] i, m i)‖ ≤ ∏ i, ‖m i‖ := by
   have hle := ciInf_le (bddBelow_projectiveSemiNormAux (⨂ₜ[𝕜] i, m i))
    ⟨FreeAddMonoid.of (1, m), by simp [mem_lifts_iff]⟩
   grw [norm_def, hle]
   simp [projectiveSeminormAux]

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]

/--
@isnad1 id=le.0h6v.s11.020daa5129e8 from=seed src=0 shape=b9f0646c vocab=1f115cc9
-/
theorem norm_eval_le_projectiveSeminorm {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G) (x : ⨂[𝕜] i, E i) :
    ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * ‖x‖ := by
  rw [norm_def, mul_comm, Real.iInf_mul_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun ⟨p, hp⟩ ↦ ?_
  rw! [← ((mem_lifts_iff x p).mp hp), ← List.sum_map_hom, ← Multiset.sum_coe]
  grw [norm_multiset_sum_le]
  simp only [mul_comm, ← smul_eq_mul, List.smul_sum, projectiveSeminormAux]
  refine List.Forall₂.sum_le_sum ?_
  simpa [norm_smul, ← mul_assoc, mul_comm ‖f‖ _] using
    fun a m _ ↦ mul_le_mul_of_nonneg_left (f.le_opNorm _) (norm_nonneg _)

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F)

/-- The linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
induced by `PiTensorProduct.lift`, for every normed space `F`.
-/
@[simps]
noncomputable def liftEquiv : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F where
  toFun f := LinearMap.mkContinuous (lift f.toMultilinearMap) ‖f‖ fun x ↦
    norm_eval_le_projectiveSeminorm f x
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp
  invFun l := MultilinearMap.mkContinuous (lift.symm l.toLinearMap) ‖l‖ fun x ↦
    ContinuousLinearMap.le_opNorm_of_le _ (projectiveSeminorm_tprod_le x)
  left_inv f := by ext; simp
  right_inv l := by
    rw [← ContinuousLinearMap.coe_inj]
    ext; simp

/-- For a normed space `F`, we have constructed in `PiTensorProduct.liftEquiv` the canonical
linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
(induced by `PiTensorProduct.lift`). Here we give the upgrade of this equivalence to
an isometric linear equivalence; in particular, it is a continuous linear equivalence. -/
noncomputable def liftIsometry : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F :=
  LinearIsometryEquiv.ofBounds (liftEquiv 𝕜 E F)
  (fun f ↦ LinearMap.mkContinuous_norm_le _ (norm_nonneg f) (norm_eval_le_projectiveSeminorm f))
  (fun f ↦ by
      rw [liftEquiv_symm_apply]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

variable {𝕜 E F}

/--
@isnad1 id=eq.0h6v.s13.9ff71426d40e from=seed src=0 shape=d3e7f9c5 vocab=6fbd0e06
-/
@[simp]
theorem liftIsometry_apply_apply (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
    liftIsometry 𝕜 E F f x = lift f.toMultilinearMap x := by
  simp [LinearIsometryEquiv.ofBounds, liftIsometry]

variable (𝕜) in
/-- The canonical continuous multilinear map from `E = Πᵢ Eᵢ` to `⨂[𝕜] i, Eᵢ`. -/
@[simps! toFun]
noncomputable def tprodL : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i) :=
  (liftIsometry 𝕜 E _).symm (ContinuousLinearMap.id 𝕜 _)

/--
@isnad1 id=eq.0h3v.s9.7d127d5682c0 from=seed src=0 shape=aa8c3e97 vocab=e6d200d3
-/
@[simp]
theorem tprodL_coe : (tprodL 𝕜).toMultilinearMap = tprod 𝕜 (s := E) := by
  ext; simp

/--
@isnad1 id=eq.0h5v.s12.1e1f5d277138 from=seed src=0 shape=c081e722 vocab=6790002c
-/
@[simp]
theorem liftIsometry_symm_apply (l : (⨂[𝕜] i, E i) →L[𝕜] F) :
    (liftIsometry 𝕜 E F).symm l = l.compContinuousMultilinearMap (tprodL 𝕜) := by
  rfl

/--
@isnad1 id=eq.0h3v.s13.5710255f7c7a from=seed src=0 shape=629edf0e vocab=a0ea403b
-/
@[simp]
theorem liftIsometry_tprodL :
    liftIsometry 𝕜 E _ (tprodL 𝕜) = ContinuousLinearMap.id 𝕜 (⨂[𝕜] i, E i) := by
  ext; simp

section map

variable {E' E'' : ι → Type*}
variable [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
variable [∀ i, SeminormedAddCommGroup (E'' i)] [∀ i, NormedSpace 𝕜 (E'' i)]
variable (g : Π i, E' i →L[𝕜] E'' i) (f : Π i, E i →L[𝕜] E' i)

/-- Let `Eᵢ` and `E'ᵢ` be two families of normed `𝕜`-vector spaces.
Let `f` be a family of continuous `𝕜`-linear maps between `Eᵢ` and `E'ᵢ`, i.e.
`f : Πᵢ Eᵢ →L[𝕜] E'ᵢ`, then there is an induced continuous linear map
`⨂ᵢ Eᵢ → ⨂ᵢ E'ᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`. -/
noncomputable def mapL : (⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i :=
  liftIsometry 𝕜 E _ <| (tprodL 𝕜).compContinuousLinearMap f

/--
@isnad1 id=eq.0h5v.s10.aa6942ed9dc6 from=seed src=0 shape=859409c1 vocab=b9078eca
-/
@[simp]
theorem mapL_coe : (mapL f).toLinearMap = map (fun i ↦ (f i).toLinearMap) := by
  ext; simp [mapL]

/--
@isnad1 id=eq.0h6v.s11.abb9e57641c9 from=seed src=0 shape=3093c795 vocab=f3359aaa
-/
@[simp]
theorem mapL_apply (x : ⨂[𝕜] i, E i) : mapL f x = map (fun i ↦ (f i).toLinearMap) x := by
  rfl

/-- Given submodules `pᵢ ⊆ Eᵢ`, this is the natural map: `⨂[𝕜] i, pᵢ → ⨂[𝕜] i, Eᵢ`.
This is the continuous version of `PiTensorProduct.mapIncl`. -/
@[simp]
noncomputable def mapLIncl (p : Π i, Submodule 𝕜 (E i)) : (⨂[𝕜] i, p i) →L[𝕜] ⨂[𝕜] i, E i :=
  mapL fun (i : ι) ↦ (p i).subtypeL

/--
@isnad1 id=eq.0h7v.s11.7b91e6459cde from=seed src=0 shape=7c7f51f9 vocab=e9408ddb
-/
theorem mapL_comp : mapL (fun (i : ι) ↦ g i ∘L f i) = mapL g ∘L mapL f := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

/--
@isnad1 id=eq.0h7v.s13.491e1ca38c72 from=seed src=0 shape=c833e226 vocab=b0a8238d
-/
theorem liftIsometry_comp_mapL (h : ContinuousMultilinearMap 𝕜 E' F) :
    liftIsometry 𝕜 E' F h ∘L mapL f = liftIsometry 𝕜 E F (h.compContinuousLinearMap f) := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

/--
@isnad1 id=eq.0h3v.s9.758fc89d0603 from=seed src=0 shape=ba23fa60 vocab=7c2823f7
-/
@[simp]
theorem mapL_id : mapL (fun i ↦ ContinuousLinearMap.id 𝕜 (E i)) = ContinuousLinearMap.id _ _ := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

/--
@isnad1 id=eq.0h3v.s11.73566572e77e from=seed src=0 shape=d53351e2 vocab=eb6849b4
-/
@[simp]
theorem mapL_one : mapL (fun (i : ι) ↦ (1 : E i →L[𝕜] E i)) = 1 :=
  mapL_id

/--
@isnad1 id=eq.0h5v.s12.868b805f6101 from=seed src=0 shape=d1c2d34f vocab=1d73c67b
-/
theorem mapL_mul (f₁ f₂ : Π i, E i →L[𝕜] E i) :
    mapL (fun i ↦ f₁ i * f₂ i) = mapL f₁ * mapL f₂ :=
  mapL_comp f₁ f₂

/-- Upgrading `PiTensorProduct.mapL` to a `MonoidHom` when `E = E'`. -/
@[simps]
noncomputable def mapLMonoidHom : (Π i, E i →L[𝕜] E i) →* ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E i) where
  toFun := mapL
  map_one' := mapL_one
  map_mul' := mapL_mul

/--
@isnad1 id=eq.0h5v.s12.0b7f8c425ceb from=seed src=0 shape=46fc58f9 vocab=168046bf
-/
@[simp]
protected theorem mapL_pow (f : Π i, E i →L[𝕜] E i) (n : ℕ) :
    mapL (f ^ n) = mapL f ^ n := MonoidHom.map_pow mapLMonoidHom f n

-- We redeclare `ι` here, and later dependent arguments,
-- to avoid the `[Fintype ι]` assumption present throughout the rest of the file.
open Function in
private theorem mapL_add_smul_aux {ι : Type*}
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {E' : ι → Type*} [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
    (f : (i : ι) → E i →L[𝕜] E' i) [DecidableEq ι] (i : ι) (u : E i →L[𝕜] E' i) :
    (fun j ↦ (update f i u j).toLinearMap) =
      update (fun j ↦ (f j).toLinearMap) i u.toLinearMap := by
  grind

open Function in
/--
@isnad1 id=eq.0h8v.s12.958a1a5d32fb from=seed src=0 shape=1d896f40 vocab=ca5f0bbe
-/
protected theorem mapL_add [DecidableEq ι] (i : ι) (u v : E i →L[𝕜] E' i) :
    mapL (update f i (u + v)) = mapL (update f i u) + mapL (update f i v) := by
  ext
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_add]

open Function in
/--
@isnad1 id=eq.0h8v.s12.8ec7f52b015c from=seed src=0 shape=9f529a2f vocab=3ca24c0b
-/
protected theorem mapL_smul [DecidableEq ι] (i : ι) (c : 𝕜) (u : E i →L[𝕜] E' i) :
    mapL (update f i (c • u)) = c • mapL (update f i u) := by
  ext
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_smul]

/--
@isnad1 id=le.0h5v.s10.7d0b7de50399 from=seed src=0 shape=0f6651e8 vocab=49e82eee
-/
theorem opNorm_mapL : ‖mapL f‖ ≤ ∏ i, ‖f i‖ := by
  refine (ContinuousLinearMap.opNorm_le_iff (by positivity)).mpr fun x ↦ ?_
  apply le_trans (norm_eval_le_projectiveSeminorm ..) (mul_le_mul_of_nonneg_right _ (norm_nonneg x))
  refine (ContinuousMultilinearMap.opNorm_le_iff (by positivity)).mpr fun m ↦ ?_
  apply le_trans (projectiveSeminorm_tprod_le fun i ↦ f i (m i))
  rw [← Finset.prod_mul_distrib]
  gcongr
  exact ContinuousLinearMap.le_opNorm _ _

variable (𝕜 E E')

/-- The tensor of a family of linear maps from `Eᵢ` to `E'ᵢ`, as a continuous multilinear map of
the family. -/
@[simps! toFun_apply]
noncomputable def mapLMultilinear : ContinuousMultilinearMap 𝕜 (fun (i : ι) ↦ E i →L[𝕜] E' i)
    ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i) :=
  MultilinearMap.mkContinuous
  { toFun := mapL
    map_update_smul' := fun _ _ _ _ ↦ PiTensorProduct.mapL_smul _ _ _ _
    map_update_add' := fun _ _ _ _ ↦ PiTensorProduct.mapL_add _ _ _ _ }
  1 (fun f ↦ by rw [one_mul]; exact opNorm_mapL f)

variable {𝕜 E E'}

/--
@isnad1 id=le.0h4v.s12.9e0e348e8a4f from=seed src=0 shape=f6a7cebd vocab=3d2381ad
-/
theorem opNorm_mapLMultilinear_le : ‖mapLMultilinear 𝕜 E E'‖ ≤ 1 :=
  MultilinearMap.mkContinuous_norm_le _ zero_le_one _

end map

end NontriviallyNormedField

end PiTensorProduct
