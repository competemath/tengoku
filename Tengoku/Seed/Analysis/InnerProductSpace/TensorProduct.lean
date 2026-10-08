/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint
public import Tengoku.Seed.RingTheory.TensorProduct.Finite
import Tengoku.Seed.Analysis.InnerProductSpace.GramMatrix
import Tengoku.Seed.Analysis.InnerProductSpace.Positive
import Tengoku.Seed.Algebra.Order.Star.Real

/-!

# Inner product space structure on tensor product spaces

This file provides the inner product space structure on tensor product spaces.

We define the inner product on `E ⊗ F` by `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`, when `E` and `F` are
inner product spaces.

## Main definitions:

* `TensorProduct.instNormedAddCommGroup`: the normed additive group structure on tensor products,
  where `‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖`.
* `TensorProduct.instInnerProductSpace`: the inner product space structure on tensor products, where
  `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`.
* `TensorProduct.mapIsometry`: the linear isometry version of `TensorProduct.map f g` when
  `f` and `g` are linear isometries.
* `TensorProduct.congrIsometry`: the linear isometry equivalence version of
  `TensorProduct.congr f g` when `f` and `g` are linear isometry equivalences.
* `TensorProduct.mapInclIsometry`: the linear isometry version of `TensorProduct.mapIncl`.
* `TensorProduct.commIsometry`: the linear isometry version of `TensorProduct.comm`.
* `TensorProduct.lidIsometry`: the linear isometry version of `TensorProduct.lid`.
* `TensorProduct.assocIsometry`: the linear isometry version of `TensorProduct.assoc`.
* `TensorProduct.mapL`: the continuous version of `TensorProduct.map f g` when
  `f` and `g` are continuous linear maps.
* `OrthonormalBasis.tensorProduct`: the orthonormal basis of the tensor product of two orthonormal
  bases.

## TODO:

* Define the normed space without needing inner products, this should be analogous to
  `Mathlib/Analysis/NormedSpace/PiTensorProduct/InjectiveSeminorm.lean`.

-/

@[expose] public section

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open scoped TensorProduct

namespace TensorProduct

instance instInner : Inner 𝕜 (E ⊗[𝕜] F) where inner x y :=
  ((lift <| mapBilinear (.id 𝕜) E F 𝕜 𝕜).compr₂ (.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x y

/--
@isnad1 id=eq.0h5v.s13.e451111853f8 from=seed src=0 shape=61f6d62d vocab=9a4422e8
-/
lemma inner_def (x y : E ⊗[𝕜] F) :
    inner 𝕜 x y = ((lift <| mapBilinear (.id 𝕜) E F 𝕜 𝕜).compr₂
      (.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x y := rfl

variable (𝕜) in
/--
@isnad1 id=eq.0h7v.s8.bf3c7d29f4ef from=seed src=0 shape=f7a37f46 vocab=5b3d9cb7
-/
@[simp] theorem inner_tmul (x x' : E) (y y' : F) :
    inner 𝕜 (x ⊗ₜ[𝕜] y) (x' ⊗ₜ[𝕜] y') = inner 𝕜 x x' * inner 𝕜 y y' := rfl

/--
@isnad1 id=eq.0h9v.s11.009e78eb3c7a from=seed src=0 shape=ceceaf06 vocab=5fb3f305
-/
@[simp] lemma inner_map_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x y : E ⊗[𝕜] F) :
    inner 𝕜 (map f.toLinearMap g.toLinearMap x) (map f.toLinearMap g.toLinearMap y) = inner 𝕜 x y :=
  x.induction_on (by simp [inner_def]) (y.induction_on (by simp [inner_def]) (by simp)
    (by simp_all [inner_def])) (by simp_all [inner_def])

/--
@isnad1 id=eq.0h7v.s13.04f01628486c from=seed src=0 shape=8fe6298f vocab=207f0d12
-/
lemma inner_mapIncl_mapIncl (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) (x y : E' ⊗[𝕜] F') :
    inner 𝕜 (mapIncl E' F' x) (mapIncl E' F' y) = inner 𝕜 x y :=
  inner_map_map E'.subtypeₗᵢ F'.subtypeₗᵢ x y

open scoped ComplexOrder
open Module

/-- This holds in any inner product space, but we need this to set up the instance.
This is a helper lemma for showing that this inner product is positive definite. -/
private theorem inner_self {ι ι' : Type*} [Fintype ι] [Fintype ι'] (x : E ⊗[𝕜] F)
    (e : OrthonormalBasis ι 𝕜 E) (f : OrthonormalBasis ι' 𝕜 F) :
    inner 𝕜 x x = ∑ i, ‖(e.toBasis.tensorProduct f.toBasis).repr x i‖ ^ 2 := by
  classical
  have : x = ∑ i : ι, ∑ j : ι', (e.toBasis.tensorProduct f.toBasis).repr x (i, j) • e i ⊗ₜ f j := by
    conv_lhs => rw [← (e.toBasis.tensorProduct f.toBasis).sum_repr x]
    simp [← Finset.sum_product', Basis.tensorProduct_apply']
  conv_lhs => rw [this]
  simp only [inner_def, map_sum, LinearMap.sum_apply]
  simp [OrthonormalBasis.inner_eq_ite, ← Finset.sum_product', RCLike.mul_conj]

set_option backward.privateInPublic true in
private theorem inner_definite (x : E ⊗[𝕜] F) (hx : inner 𝕜 x x = 0) : x = 0 := by
  /-
  The way we prove this is by noting that every element of a tensor product lies
  in the tensor product of some finite submodules.
  So for `x : E ⊗ F`, there exists finite submodules `E', F'` such that `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl_mapIncl` and `inner_self`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y : E' ⊗ F', rfl : mapIncl E' F' y = x⟩ := Set.singleton_subset_iff.mp hz
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  have (i) (j) : (e.toBasis.tensorProduct f.toBasis).repr y (i, j) = 0 := by
    rw [inner_mapIncl_mapIncl, inner_self y e f, RCLike.ofReal_eq_zero,
      Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at hx
    simpa using hx (i, j)
  have : y = 0 := by simp [(e.toBasis.tensorProduct f.toBasis).ext_elem_iff, this]
  rw [this, map_zero]

set_option backward.privateInPublic true in
private protected theorem re_inner_self_nonneg (x : E ⊗[𝕜] F) :
    0 ≤ RCLike.re (inner 𝕜 x x) := by
  /-
  Similarly to the above proof, for `x : E ⊗ F`, there exists finite submodules `E', F'` such that
  `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl_mapIncl` and `inner_self`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hz
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  rw [inner_mapIncl_mapIncl, inner_self y e f, RCLike.ofReal_re]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (E ⊗[𝕜] F) :=
  letI : InnerProductSpace.Core 𝕜 (E ⊗[𝕜] F) :=
  { conj_inner_symm x y :=
      x.induction_on (by simp [inner]) (y.induction_on (by simp [inner]) (by simp)
        (by simp_all [inner])) (by simp_all [inner])
    add_left _ _ _ := LinearMap.map_add₂ _ _ _ _
    smul_left _ _ _ := LinearMap.map_smulₛₗ₂ _ _ _ _
    definite := TensorProduct.inner_definite
    re_inner_nonneg := TensorProduct.re_inner_self_nonneg }
  this.toNormedAddCommGroup

instance instInnerProductSpace : InnerProductSpace 𝕜 (E ⊗[𝕜] F) := .ofCore _

/--
@isnad1 id=eq.0h5v.s8.1860ccbef3aa from=seed src=0 shape=f090b143 vocab=3cc89250
-/
@[simp] theorem norm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[𝕜] y‖ = ‖x‖ * ‖y‖ := by
  simpa using congr(√(RCLike.re $(inner_tmul 𝕜 x x y y)))

/--
@isnad1 id=eq.0h5v.s8.eeebd9c9758e from=seed src=0 shape=f090b143 vocab=5aedf221
-/
@[simp] theorem nnnorm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[𝕜] y‖₊ = ‖x‖₊ * ‖y‖₊ := by simp [← NNReal.coe_inj]

/--
@isnad1 id=eq.0h5v.s9.1c8dfc1f904e from=seed src=0 shape=f090b143 vocab=d436d0be
-/
@[simp] theorem enorm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[𝕜] y‖ₑ = ‖x‖ₑ * ‖y‖ₑ := ENNReal.coe_inj.mpr <| by simp

/--
@isnad1 id=le.0h7v.s8.d6c8dcd3e6dc from=seed src=0 shape=e4e204b8 vocab=c70f3798
-/
theorem dist_tmul_le (x x' : E) (y y' : F) :
    dist (x ⊗ₜ[𝕜] y) (x' ⊗ₜ y') ≤ ‖x‖ * ‖y‖ + ‖x'‖ * ‖y'‖ := by
  grw [dist_eq_norm, norm_sub_le]; simp

/--
@isnad1 id=le.0h7v.s9.c80a3a395cfc from=seed src=0 shape=e4e204b8 vocab=4e159519
-/
theorem nndist_tmul_le (x x' : E) (y y' : F) :
    nndist (x ⊗ₜ[𝕜] y) (x' ⊗ₜ y') ≤ ‖x‖₊ * ‖y‖₊ + ‖x'‖₊ * ‖y'‖₊ := by
  grw [nndist_eq_nnnorm, nnnorm_sub_le]; simp

/--
@isnad1 id=le.0h7v.s10.0cc4a1d3877e from=seed src=0 shape=e4e204b8 vocab=754742b2
-/
theorem edist_tmul_le (x x' : E) (y y' : F) :
    edist (x ⊗ₜ[𝕜] y) (x' ⊗ₜ y') ≤ ‖x‖ₑ * ‖y‖ₑ + ‖x'‖ₑ * ‖y'‖ₑ := by
  grw [edist_eq_enorm_sub, enorm_sub_le]; simp

/-- In `ℝ` or `ℂ` fields, the inner product on tensor products is essentially just the inner product
with multiplication instead of tensors, i.e., `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a * b, c * d⟫`. -/
theorem _root_.RCLike.inner_tmul_eq (a b c d : 𝕜) :
    inner 𝕜 (a ⊗ₜ[𝕜] b) (c ⊗ₜ[𝕜] d) = inner 𝕜 (a * b) (c * d) := by
  simp; ring

/-- Given `x, y : E ⊗ F`, `x = y` iff `⟪x, a ⊗ₜ b⟫ = ⟪y, a ⊗ₜ b⟫` for all `a, b`.
@isnad1 id=iff.0h5v.s9.055ebc60b402 from=seed src=0 shape=e7a2c44b vocab=061a4259
-/
protected theorem ext_iff_inner_right {x y : E ⊗[𝕜] F} :
    x = y ↔ ∀ a b, inner 𝕜 x (a ⊗ₜ[𝕜] b) = inner 𝕜 y (a ⊗ₜ[𝕜] b) :=
  ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ innerSL_inj.mp <| ContinuousLinearMap.coe_inj.mp <| ext' h⟩

/-- Given `x, y : E ⊗ F`, `x = y` iff `⟪a ⊗ₜ b, x⟫ = ⟪a ⊗ₜ b, y⟫` for all `a, b`.
@isnad1 id=iff.0h5v.s9.79784362390f from=seed src=0 shape=4960c912 vocab=061a4259
-/
protected theorem ext_iff_inner_left {x y : E ⊗[𝕜] F} :
    x = y ↔ ∀ a b, inner 𝕜 (a ⊗ₜ b) x = inner 𝕜 (a ⊗ₜ b) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    TensorProduct.ext_iff_inner_right (x := x) (y := y)

/-- Given `x, y : E ⊗ F ⊗ G`, `x = y` iff `⟪x, a ⊗ₜ b ⊗ₜ c⟫ = ⟪y, a ⊗ₜ b ⊗ₜ c⟫` for all `a, b, c`.

See also `ext_iff_inner_right_threefold'` for when `x, y : E ⊗ (F ⊗ G)`.
@isnad1 id=iff.0h6v.s10.8738cbb39b03 from=seed src=0 shape=f5314561 vocab=061a4259
-/
theorem ext_iff_inner_right_threefold {x y : E ⊗[𝕜] F ⊗[𝕜] G} :
    x = y ↔ ∀ a b c, inner 𝕜 x (a ⊗ₜ[𝕜] b ⊗ₜ[𝕜] c) = inner 𝕜 y (a ⊗ₜ[𝕜] b ⊗ₜ[𝕜] c) :=
  ⟨fun h _ _ _ ↦ h ▸ rfl, fun h ↦ innerSL_inj.mp (ContinuousLinearMap.coe_inj.mp (ext_threefold h))⟩

/-- Given `x, y : E ⊗ F ⊗ G`, `x = y` iff `⟪a ⊗ₜ b ⊗ₜ c, x⟫ = ⟪a ⊗ₜ b ⊗ₜ c, y⟫` for all `a, b, c`.

See also `ext_iff_inner_left_threefold'` for when `x, y : E ⊗ (F ⊗ G)`.
@isnad1 id=iff.0h6v.s10.22871af54cb7 from=seed src=0 shape=961b01e4 vocab=061a4259
-/
theorem ext_iff_inner_left_threefold {x y : E ⊗[𝕜] F ⊗[𝕜] G} :
    x = y ↔ ∀ a b c, inner 𝕜 (a ⊗ₜ b ⊗ₜ c) x = inner 𝕜 (a ⊗ₜ b ⊗ₜ c) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold (x := x) (y := y)

variable (𝕜 E F) in
/-- The canonical continuous bilinear map `E → F → E ⊗ F`. This is the continuous version of
`mk`. -/
noncomputable def mkL : E →L[𝕜] F →L[𝕜] E ⊗[𝕜] F := (mk 𝕜 E F).mkContinuous₂ 1 fun _ _ ↦ by simp

/--
@isnad1 id=eq.0h4v.s13.a201414f3c08 from=seed src=0 shape=3f389465 vocab=821993ff
-/
@[simp] lemma coe_mkL_apply (x : E) : ⇑(mkL 𝕜 E F x) = mk 𝕜 E F x := rfl
/--
@isnad1 id=eq.0h3v.s14.b1a34f7f6232 from=seed src=0 shape=9ea9a29b vocab=3f37bf5d
-/
@[simp] lemma toLinearMap₁₂_mkL : (mkL 𝕜 E F).toLinearMap₁₂ = mk 𝕜 E F := rfl
/--
@isnad1 id=eq.0h4v.s12.4b84c5900f23 from=seed src=0 shape=2d0615c1 vocab=37c9655d
-/
@[simp] lemma toLinearMap_mkL_apply (x : E) : (mkL 𝕜 E F x).toLinearMap = mk 𝕜 E F x := rfl
/--
@isnad1 id=eq.0h5v.s12.f81c7ea233e7 from=seed src=0 shape=ef0dfc7a vocab=3adf5a9b
-/
lemma mkL_apply_apply (x : E) (y : F) : mkL 𝕜 E F x y = x ⊗ₜ y := rfl

/--
@isnad1 id=continuo.0h3v.s8.7e49602be4ba from=seed src=0 shape=ce7f7440 vocab=386142d5
-/
@[fun_prop] lemma continuous_tmul : Continuous fun x : E × F ↦ x.1 ⊗ₜ[𝕜] x.2 :=
  (mkL 𝕜 E F).continuous₂

section isometry

/-- The tensor product map of two linear isometries is a linear isometry. In particular, this is
the linear isometry version of `TensorProduct.map f g` when `f` and `g` are linear isometries. -/
noncomputable def mapIsometry (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) :
    E ⊗[𝕜] F →ₗᵢ[𝕜] G ⊗[𝕜] H :=
  map f.toLinearMap g.toLinearMap |>.isometryOfInner <| inner_map_map _ _

/--
@isnad1 id=eq.0h8v.s11.d91dda74178f from=seed src=0 shape=0189df29 vocab=d87b0843
-/
@[simp] lemma mapIsometry_apply (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    mapIsometry f g x = map f.toLinearMap g.toLinearMap x := rfl

/--
@isnad1 id=eq.0h7v.s10.8a78e42ebd6d from=seed src=0 shape=02b207d5 vocab=a81abb08
-/
@[simp] lemma toLinearMap_mapIsometry (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) :
    (mapIsometry f g).toLinearMap = map f.toLinearMap g.toLinearMap := rfl

/--
@isnad1 id=eq.0h8v.s10.a783a7a628cc from=seed src=0 shape=65f26810 vocab=07deb927
-/
@[simp] lemma norm_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    ‖map f.toLinearMap g.toLinearMap x‖ = ‖x‖ := mapIsometry f g |>.norm_map x
/--
@isnad1 id=eq.0h8v.s11.e3f6a7f2977f from=seed src=0 shape=65f26810 vocab=63008924
-/
@[simp] lemma nnnorm_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    ‖map f.toLinearMap g.toLinearMap x‖₊ = ‖x‖₊ := mapIsometry f g |>.nnnorm_map x
/--
@isnad1 id=eq.0h8v.s11.4fc89b5f1f40 from=seed src=0 shape=65f26810 vocab=96b66a48
-/
@[simp] lemma enorm_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    ‖map f.toLinearMap g.toLinearMap x‖ₑ = ‖x‖ₑ := mapIsometry f g |>.enorm_map x

/--
@isnad1 id=eq.0h3v.s9.224d6332318d from=seed src=0 shape=044929c4 vocab=e0794fae
-/
@[simp] lemma mapIsometry_id_id :
    mapIsometry (.id : E →ₗᵢ[𝕜] E) (.id : F →ₗᵢ[𝕜] F) = .id := by ext; simp

variable (E) in
/-- This is the natural linear isometry induced by `f : F ≃ₗᵢ G`. -/
noncomputable def _root_.LinearIsometry.lTensor (f : F →ₗᵢ[𝕜] G) :
    E ⊗[𝕜] F →ₗᵢ[𝕜] E ⊗[𝕜] G := mapIsometry .id f

variable (G) in
/-- This is the natural linear isometry induced by `f : E ≃ₗᵢ F`. -/
noncomputable def _root_.LinearIsometry.rTensor (f : E →ₗᵢ[𝕜] F) :
    E ⊗[𝕜] G →ₗᵢ[𝕜] F ⊗[𝕜] G := mapIsometry f .id

lemma _root_.LinearIsometry.lTensor_def (f : F →ₗᵢ[𝕜] G) :
    f.lTensor E = mapIsometry .id f := rfl

lemma _root_.LinearIsometry.rTensor_def (f : E →ₗᵢ[𝕜] F) :
    f.rTensor G = mapIsometry f .id := rfl

@[simp] lemma _root_.LinearIsometry.toLinearMap_lTensor (f : F →ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearMap = f.toLinearMap.lTensor E := rfl

@[simp] lemma _root_.LinearIsometry.toLinearMap_rTensor (f : E →ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearMap = f.toLinearMap.rTensor G := rfl

@[simp] lemma _root_.LinearIsometry.lTensor_apply (f : F →ₗᵢ[𝕜] G) (x : E ⊗[𝕜] F) :
    f.lTensor E x = f.toLinearMap.lTensor E x := rfl

@[simp] lemma _root_.LinearIsometry.rTensor_apply (f : E →ₗᵢ[𝕜] F) (x : E ⊗[𝕜] G) :
    f.rTensor G x = f.toLinearMap.rTensor G x := rfl

/-- The tensor product of two linear isometry equivalences is a linear isometry equivalence.
In particular, this is the linear isometry equivalence version of `TensorProduct.congr f g` when `f`
and `g` are linear isometry equivalences. -/
noncomputable def congrIsometry (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    E ⊗[𝕜] F ≃ₗᵢ[𝕜] G ⊗[𝕜] H :=
  congr f.toLinearEquiv g.toLinearEquiv |>.isometryOfInner <|
    inner_map_map f.toLinearIsometry g.toLinearIsometry

/--
@isnad1 id=eq.0h8v.s12.db3685fb1cef from=seed src=0 shape=12937ee7 vocab=17a5b7aa
-/
@[simp] lemma congrIsometry_apply (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    congrIsometry f g x = congr (σ₁₂ := .id _) f g x := rfl

/--
@isnad1 id=eq.0h7v.s10.3dc7296703ed from=seed src=0 shape=1afb2856 vocab=5e0d4b93
-/
lemma congrIsometry_symm (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometry f g).symm = congrIsometry f.symm g.symm := rfl

/--
@isnad1 id=eq.0h7v.s10.6093f584c1d0 from=seed src=0 shape=7cd24c28 vocab=c408be02
-/
@[simp] lemma toLinearEquiv_congrIsometry (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometry f g).toLinearEquiv = congr f.toLinearEquiv g.toLinearEquiv := rfl

/--
@isnad1 id=eq.0h3v.s9.d8252a71e9b6 from=seed src=0 shape=51230ea1 vocab=90671eba
-/
@[simp] lemma congrIsometry_refl_refl :
    congrIsometry (.refl 𝕜 E) (.refl 𝕜 F) = .refl 𝕜 (E ⊗ F) :=
  LinearIsometryEquiv.toLinearEquiv_inj.mp <| LinearEquiv.toLinearMap_inj.mp <| by ext; simp

variable (E) in
/-- This is the natural linear isometric equivalence induced by `f : F ≃ₗᵢ G`. -/
noncomputable def _root_.LinearIsometryEquiv.lTensor (f : F ≃ₗᵢ[𝕜] G) :
    E ⊗[𝕜] F ≃ₗᵢ[𝕜] E ⊗[𝕜] G := congrIsometry (.refl 𝕜 E) f

variable (G) in
/-- This is the natural linear isometric equivalence induced by `f : E ≃ₗᵢ F`. -/
noncomputable def _root_.LinearIsometryEquiv.rTensor (f : E ≃ₗᵢ[𝕜] F) :
    E ⊗[𝕜] G ≃ₗᵢ[𝕜] F ⊗[𝕜] G := congrIsometry f (.refl 𝕜 G)

lemma _root_.LinearIsometryEquiv.lTensor_def (f : F ≃ₗᵢ[𝕜] G) :
    f.lTensor E = congrIsometry (.refl 𝕜 E) f := rfl

lemma _root_.LinearIsometryEquiv.rTensor_def (f : E ≃ₗᵢ[𝕜] F) :
    f.rTensor G = congrIsometry f (.refl 𝕜 G) := rfl

lemma _root_.LinearIsometryEquiv.symm_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).symm = f.symm.lTensor E := rfl

lemma _root_.LinearIsometryEquiv.symm_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).symm = f.symm.rTensor G := rfl

@[simp] lemma _root_.LinearIsometryEquiv.toLinearEquiv_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearEquiv = f.toLinearEquiv.lTensor E := rfl

@[simp] lemma _root_.LinearIsometryEquiv.toLinearIsometry_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearIsometry = f.toLinearIsometry.lTensor E := rfl

@[simp] lemma _root_.LinearIsometryEquiv.toLinearEquiv_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearEquiv = f.toLinearEquiv.rTensor G := rfl

@[simp] lemma _root_.LinearIsometryEquiv.toLinearIsometry_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearIsometry = f.toLinearIsometry.rTensor G := rfl

@[simp] lemma _root_.LinearIsometryEquiv.lTensor_apply (f : F ≃ₗᵢ[𝕜] G) (x : E ⊗[𝕜] F) :
    f.lTensor E x = f.toLinearEquiv.lTensor E x := rfl

@[simp] lemma _root_.LinearIsometryEquiv.rTensor_apply (f : E ≃ₗᵢ[𝕜] F) (x : E ⊗[𝕜] G) :
    f.rTensor G x = f.toLinearEquiv.rTensor G x := rfl

/-- The linear isometry version of `TensorProduct.mapIncl`. -/
noncomputable def mapInclIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    E' ⊗[𝕜] F' →ₗᵢ[𝕜] E ⊗[𝕜] F :=
  mapIsometry E'.subtypeₗᵢ F'.subtypeₗᵢ

/--
@isnad1 id=eq.0h6v.s13.956ff53addaa from=seed src=0 shape=2957eaed vocab=b7c15e32
-/
@[simp] lemma mapInclIsometry_apply (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
    (x : E' ⊗[𝕜] F') : mapInclIsometry E' F' x = mapIncl E' F' x := rfl

/--
@isnad1 id=eq.0h5v.s12.6c71d95883c5 from=seed src=0 shape=f4a999c7 vocab=f681fb56
-/
@[simp] lemma toLinearMap_mapInclIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    (mapInclIsometry E' F').toLinearMap = mapIncl E' F' := rfl

/--
@isnad1 id=eq.0h5v.s11.f9e49dccca35 from=seed src=0 shape=bcd1d218 vocab=59bdc1f1
-/
@[simp] theorem inner_comm_comm (x y : E ⊗[𝕜] F) :
    inner 𝕜 (TensorProduct.comm 𝕜 E F x) (TensorProduct.comm 𝕜 E F y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [mul_comm])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E F) in
/-- The linear isometry equivalence version of `TensorProduct.comm`. -/
noncomputable def commIsometry : E ⊗[𝕜] F ≃ₗᵢ[𝕜] F ⊗[𝕜] E :=
  TensorProduct.comm 𝕜 E F |>.isometryOfInner inner_comm_comm

/--
@isnad1 id=eq.0h4v.s11.71cb2543ab4e from=seed src=0 shape=8c504b52 vocab=3e0cd47d
-/
@[simp] lemma commIsometry_apply (x : E ⊗[𝕜] F) :
    commIsometry 𝕜 E F x = TensorProduct.comm 𝕜 E F x := rfl
/--
@isnad1 id=eq.0h3v.s9.a5505a453456 from=seed src=0 shape=cc2d2fdb vocab=ce627c77
-/
@[simp] lemma commIsometry_symm :
    (commIsometry 𝕜 E F).symm = commIsometry 𝕜 F E := rfl

/--
@isnad1 id=eq.0h3v.s10.114c7c4a8f51 from=seed src=0 shape=1a06c0c5 vocab=a2bbf405
-/
@[simp] lemma toLinearEquiv_commIsometry :
    (commIsometry 𝕜 E F).toLinearEquiv = TensorProduct.comm 𝕜 E F := rfl

/--
@isnad1 id=eq.0h4v.s11.c4db4031159a from=seed src=0 shape=743223e0 vocab=c03f64cd
-/
@[simp] lemma norm_comm (x : E ⊗[𝕜] F) :
    ‖TensorProduct.comm 𝕜 E F x‖ = ‖x‖ := commIsometry 𝕜 E F |>.norm_map x
/--
@isnad1 id=eq.0h4v.s11.2fdf25bd520d from=seed src=0 shape=743223e0 vocab=3f31ca21
-/
@[simp] lemma nnnorm_comm (x : E ⊗[𝕜] F) :
    ‖TensorProduct.comm 𝕜 E F x‖₊ = ‖x‖₊ := commIsometry 𝕜 E F |>.nnnorm_map x
/--
@isnad1 id=eq.0h4v.s11.0d7e75b33d7c from=seed src=0 shape=743223e0 vocab=c60e3eb1
-/
@[simp] lemma enorm_comm (x : E ⊗[𝕜] F) :
    ‖TensorProduct.comm 𝕜 E F x‖ₑ = ‖x‖ₑ := commIsometry 𝕜 E F |>.toLinearIsometry.enorm_map x

/--
@isnad1 id=eq.0h4v.s11.2ca6619ff040 from=seed src=0 shape=1f9af9b7 vocab=832567b7
-/
@[simp] theorem inner_lid_lid (x y : 𝕜 ⊗[𝕜] E) :
    inner 𝕜 (TensorProduct.lid 𝕜 E x) (TensorProduct.lid 𝕜 E y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [inner_smul_left, inner_smul_right, mul_assoc])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E) in
/-- The linear isometry equivalence version of `TensorProduct.lid`. -/
noncomputable def lidIsometry : 𝕜 ⊗[𝕜] E ≃ₗᵢ[𝕜] E :=
  TensorProduct.lid 𝕜 E |>.isometryOfInner inner_lid_lid

/--
@isnad1 id=eq.0h2v.s9.e0e892d8a725 from=seed src=0 shape=cc9bbcd6 vocab=c4039fb8
-/
@[simp] lemma toLinearEquiv_lidIsometry :
    (lidIsometry 𝕜 E).toLinearEquiv = TensorProduct.lid 𝕜 E := rfl

/--
@isnad1 id=eq.0h2v.s13.69f6fe5c563e from=seed src=0 shape=a1629c22 vocab=a147411a
-/
lemma toContinuousLinearMap_symm_lidIsometry :
    (lidIsometry 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap = mkL 𝕜 𝕜 E 1 := rfl

/--
@isnad1 id=eq.0h3v.s11.f19587c9779e from=seed src=0 shape=dbd4142d vocab=fddb85eb
-/
@[simp] lemma lidIsometry_apply (x : 𝕜 ⊗[𝕜] E) : lidIsometry 𝕜 E x = TensorProduct.lid 𝕜 E x := rfl
/--
@isnad1 id=eq.0h3v.s10.b0da2bc58636 from=seed src=0 shape=d15d1c66 vocab=782869f3
-/
@[simp] lemma lidIsometry_symm_apply (x : E) : (lidIsometry 𝕜 E).symm x = 1 ⊗ₜ x := rfl

/--
@isnad1 id=eq.0h3v.s10.9a4d736f0200 from=seed src=0 shape=c36aeb66 vocab=0a64f7a1
-/
@[simp] lemma norm_lid (x) : ‖TensorProduct.lid 𝕜 E x‖ = ‖x‖ := (lidIsometry 𝕜 E).norm_map x
/--
@isnad1 id=eq.0h3v.s10.11ff51ae712d from=seed src=0 shape=c36aeb66 vocab=53ec18a1
-/
@[simp] lemma nnnorm_lid (x) : ‖TensorProduct.lid 𝕜 E x‖₊ = ‖x‖₊ := lidIsometry 𝕜 E |>.nnnorm_map x

/--
@isnad1 id=eq.0h3v.s10.192febfa5f9e from=seed src=0 shape=c36aeb66 vocab=9ae3deae
-/
@[simp] lemma enorm_lid (x : 𝕜 ⊗[𝕜] E) :
    ‖TensorProduct.lid 𝕜 E x‖ₑ = ‖x‖ₑ := lidIsometry 𝕜 E |>.toLinearIsometry.enorm_map x

/--
@isnad1 id=eq.0h4v.s11.f58499151b58 from=seed src=0 shape=5d8bce1e vocab=9b7c19b6
-/
@[simp] theorem inner_rid_rid (x y : E ⊗[𝕜] 𝕜) :
    inner 𝕜 (TensorProduct.rid 𝕜 E x) (TensorProduct.rid 𝕜 E y) = inner 𝕜 x y := by
  simp [← lid_comm]

variable (𝕜 E) in
/-- The linear isometry equivalence version of `TensorProduct.rid`. -/
noncomputable def ridIsometry : E ⊗[𝕜] 𝕜 ≃ₗᵢ[𝕜] E :=
  TensorProduct.rid 𝕜 E |>.isometryOfInner inner_rid_rid

/--
@isnad1 id=eq.0h2v.s9.8f85ea2eb0a4 from=seed src=0 shape=20960310 vocab=b5936f63
-/
@[simp] lemma toLinearEquiv_ridIsometry :
    (ridIsometry 𝕜 E).toLinearEquiv = TensorProduct.rid 𝕜 E := rfl

/--
@isnad1 id=eq.0h2v.s14.a44a48c4b284 from=seed src=0 shape=4d444947 vocab=f90e38fa
-/
lemma toContinuousLinearMap_symm_ridIsometry :
    (ridIsometry 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap = (mkL 𝕜 E 𝕜).flip 1 := rfl

/--
@isnad1 id=eq.0h3v.s11.5e7d7ffa6e89 from=seed src=0 shape=86624ddd vocab=5aa25a85
-/
@[simp] lemma ridIsometry_apply (x) : ridIsometry 𝕜 E x = TensorProduct.rid 𝕜 E x := rfl
/--
@isnad1 id=eq.0h3v.s10.4863dbc337ec from=seed src=0 shape=e2d08bf3 vocab=cb41c49f
-/
@[simp] lemma symm_ridIsometry_apply (x) : (ridIsometry 𝕜 E).symm x = x ⊗ₜ 1 := rfl

/--
@isnad1 id=eq.0h1v.s9.5ee2fa57effe from=seed src=0 shape=d6a53e8e vocab=2508275d
-/
lemma lidIsometry_eq_ridIsometry : lidIsometry 𝕜 𝕜 = ridIsometry 𝕜 𝕜 := by ext; simp [lid_eq_rid]

/--
@isnad1 id=eq.0h3v.s10.3780cedc00c8 from=seed src=0 shape=05e58b58 vocab=82d93f97
-/
@[simp] lemma norm_rid (x) : ‖TensorProduct.rid 𝕜 E x‖ = ‖x‖ := (ridIsometry 𝕜 E).norm_map x
/--
@isnad1 id=eq.0h3v.s10.50610e042e87 from=seed src=0 shape=05e58b58 vocab=142aaca2
-/
@[simp] lemma nnnorm_rid (x) : ‖TensorProduct.rid 𝕜 E x‖₊ = ‖x‖₊ := by simp [← NNReal.coe_inj]

/--
@isnad1 id=eq.0h3v.s10.9c7ef08b2b91 from=seed src=0 shape=05e58b58 vocab=901999bd
-/
@[simp] lemma enorm_rid (x) : ‖TensorProduct.rid 𝕜 E x‖ₑ = ‖x‖ₑ :=
  ridIsometry 𝕜 E |>.toLinearIsometry.enorm_map x

/--
@isnad1 id=eq.0h2v.s10.2e6f6285ff6b from=seed src=0 shape=87ec4228 vocab=c4bb0505
-/
@[simp] lemma commIsometry_trans_lidIsometry :
    (commIsometry 𝕜 E 𝕜).trans (lidIsometry 𝕜 E) = ridIsometry 𝕜 E := by ext; simp

/--
@isnad1 id=eq.0h2v.s10.27b3880608dc from=seed src=0 shape=46ca679b vocab=c4bb0505
-/
@[simp] lemma commIsometry_trans_ridIsometry :
    (commIsometry 𝕜 𝕜 E).trans (ridIsometry 𝕜 E) = lidIsometry 𝕜 E := by ext; simp

/--
@isnad1 id=eq.0h6v.s13.ca4309de878e from=seed src=0 shape=e9d7e290 vocab=5b9fcc07
-/
@[simp] theorem inner_assoc_assoc (x y : E ⊗[𝕜] F ⊗[𝕜] G) :
    inner 𝕜 (TensorProduct.assoc 𝕜 E F G x) (TensorProduct.assoc 𝕜 E F G y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun a _ =>
    y.induction_on (by simp) (fun c _ =>
      a.induction_on (by simp) (fun _ _ =>
        c.induction_on (by simp) (by simp [mul_assoc])
        fun _ _ h1 h2 => by simp only [add_tmul, inner_add_right, map_add, h1, h2])
      fun _ _ h1 h2 => by simp only [add_tmul, inner_add_left, map_add, h1, h2])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E F G) in
/-- The linear isometry equivalence version of `TensorProduct.assoc`. -/
noncomputable def assocIsometry : E ⊗[𝕜] F ⊗[𝕜] G ≃ₗᵢ[𝕜] E ⊗[𝕜] (F ⊗[𝕜] G) :=
  TensorProduct.assoc 𝕜 E F G |>.isometryOfInner inner_assoc_assoc

/--
@isnad1 id=eq.0h5v.s13.d882e446c4c9 from=seed src=0 shape=f7b61048 vocab=6904d08e
-/
@[simp] lemma assocIsometry_apply (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    assocIsometry 𝕜 E F G x = TensorProduct.assoc 𝕜 E F G x := rfl

/--
@isnad1 id=eq.0h5v.s13.b50310a2a3ac from=seed src=0 shape=821c9bb6 vocab=85348946
-/
@[simp] lemma assocIsometry_symm_apply (x : E ⊗[𝕜] (F ⊗[𝕜] G)) :
    (assocIsometry 𝕜 E F G).symm x = (TensorProduct.assoc 𝕜 E F G).symm x := rfl

/--
@isnad1 id=eq.0h4v.s12.0b3b970c7770 from=seed src=0 shape=0de51fc6 vocab=696fae54
-/
@[simp] lemma toLinearEquiv_assocIsometry :
    (assocIsometry 𝕜 E F G).toLinearEquiv = TensorProduct.assoc 𝕜 E F G := rfl

/--
@isnad1 id=eq.0h5v.s12.640c29e88ed0 from=seed src=0 shape=be0ac4bc vocab=13d29231
-/
@[simp] lemma norm_assoc (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    ‖TensorProduct.assoc 𝕜 E F G x‖ = ‖x‖ := assocIsometry 𝕜 E F G |>.norm_map x

/--
@isnad1 id=eq.0h5v.s12.6ce283873eb4 from=seed src=0 shape=be0ac4bc vocab=20fe58d5
-/
@[simp] lemma nnnorm_assoc (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    ‖TensorProduct.assoc 𝕜 E F G x‖₊ = ‖x‖₊ := assocIsometry 𝕜 E F G |>.nnnorm_map x

/--
@isnad1 id=eq.0h5v.s13.cfa8af69ce3a from=seed src=0 shape=be0ac4bc vocab=c17a7829
-/
@[simp] lemma enorm_assoc (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    ‖TensorProduct.assoc 𝕜 E F G x‖ₑ = ‖x‖ₑ := assocIsometry 𝕜 E F G |>.toLinearIsometry.enorm_map x

end isometry

end TensorProduct

namespace ContinuousLinearMap

open TensorProduct

variable (G)

/-- `LinearMap.rTensor` as a continuous linear map, i.e. the continuous linear map `f` extended to
the map `x ⊗ₜ[𝕜] y ↦ f(x) ⊗ₜ[𝕜] y`. -/
noncomputable def rTensor (f : E →L[𝕜] F) : (E ⊗[𝕜] G) →L[𝕜] (F ⊗[𝕜] G) :=
  (f.toLinearMap.rTensor G).mkContinuous ‖f‖ fun x ↦ by
    /-
    Any tensor `x` can be written as a linear combination of pure tensors, `x = ∑ e n ⊗ₜ g n`. This
    induces three Gram matrices, one based on `e`, one on `f ∘ e` and one on `g`. Up to a constant,
    the `e`-based Gram matrix is larger than the `f ∘ e`-based one. This implies the existence of
    a matrix, whose form is used to show that `‖f‖ ^ 2 * ‖x‖ ^ 2 - ‖f x‖ ^ 2` is a sum of
    nonnegative terms.
    -/
    obtain ⟨n, e, g, hx⟩ := exists_sum_tmul_eq x
    obtain ⟨c, hc_supp, hc⟩ := Submodule.mem_span_set.mp
      ((span_tmul_eq_top 𝕜 E G) ▸ Submodule.mem_top (x := x))
    obtain ⟨m, A, hA⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp
      (Matrix.posSemidef_opNorm_smul_gram_sub_gram e f)
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simp_rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add, ← Matrix.ext_iff, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.gram_apply, Function.comp_apply] at hA
    simp_rw [mul_pow, hx, map_sum, LinearMap.rTensor_tmul, coe_coe,
      ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_sum, sum_inner, inner_tmul, ← hA, sub_mul,
      Finset.sum_sub_distrib, map_sub, ← RCLike.smul_re, Finset.smul_sum, smul_mul_assoc,
      sub_le_self_iff, Matrix.sum_apply, mul_comm, Finset.mul_sum]
    simp_rw +singlePass [Finset.sum_comm_cycle, Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply,
      ← mul_left_comm, ← mul_assoc, ← starRingEnd_self_apply (A _ _), ← inner_smul_left]
    simp [mul_comm, ← inner_smul_right, ← sum_inner, ← inner_sum, Finset.sum_nonneg]

variable {G} in
/--
@isnad1 id=eq.0h6v.s11.bf2103657261 from=seed src=0 shape=e7a2ad28 vocab=7e7e1345
-/
@[simp] lemma rTensor_apply (f : E →L[𝕜] F) (x : E ⊗ G) :
    f.rTensor G x = f.toLinearMap.rTensor G x := rfl

variable {G} in
/--
@isnad1 id=eq.0h7v.s11.fd5a54f32d66 from=seed src=0 shape=fbdb3d9f vocab=39b3665e
-/
lemma rTensor_tmul (f : E →L[𝕜] F) (m : E) (n : G) : f.rTensor G (m ⊗ₜ n) = f m ⊗ₜ n := rfl

/--
@isnad1 id=eq.0h5v.s10.a4373c860ffc from=seed src=0 shape=22a9337c vocab=e396515a
-/
@[simp] lemma toLinearMap_rTensor (f : E →L[𝕜] F) :
    (f.rTensor G).toLinearMap = f.toLinearMap.rTensor G := rfl

@[simp] lemma _root_.LinearIsometry.toContinuousLinearMap_rTensor (f : E →ₗᵢ[𝕜] F) :
    (f.rTensor G).toContinuousLinearMap = f.toContinuousLinearMap.rTensor G := rfl

/--
@isnad1 id=le.0h5v.s10.ac5a9eb6a9f3 from=seed src=0 shape=a8cb51f7 vocab=6ff38d03
-/
theorem norm_rTensor_le (f : E →L[𝕜] F) : ‖f.rTensor G‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/--
@isnad1 id=eq.0h6v.s12.a2aa0a15ae94 from=seed src=0 shape=8c560485 vocab=99617005
-/
@[simp] lemma rTensor_add (f₁ f₂ : E →L[𝕜] F) :
    (f₁ + f₂).rTensor G = f₁.rTensor G + f₂.rTensor G := by ext; simp

/--
@isnad1 id=eq.0h6v.s12.3296ffdc591a from=seed src=0 shape=c9ebfe04 vocab=6105a033
-/
@[simp] lemma rTensor_smul (r : 𝕜) (f : E →L[𝕜] F) :
    (r • f).rTensor G = r • f.rTensor G := by ext; simp

/--
@isnad1 id=eq.0h3v.s10.7723e2a7b8e2 from=seed src=0 shape=5ce2cfa3 vocab=91b9d975
-/
@[simp] lemma rTensor_id : (.id 𝕜 E : E →L[𝕜] E).rTensor G = .id 𝕜 _ := by ext; simp
/--
@isnad1 id=eq.0h3v.s11.74bb0f74ed37 from=seed src=0 shape=156b693d vocab=e4ece0fd
-/
@[simp] lemma rTensor_one : (1 : E →L[𝕜] E).rTensor G = 1 := rTensor_id _
/--
@isnad1 id=eq.0h4v.s12.cd70add9a313 from=seed src=0 shape=7ba4e6b6 vocab=e4ece0fd
-/
@[simp] lemma rTensor_zero : (0 : E →L[𝕜] F).rTensor G = 0 := by ext; simp
/--
@isnad1 id=eq.0h5v.s11.eb4a193adaf0 from=seed src=0 shape=124fd5b2 vocab=a7cc3877
-/
@[simp] lemma rTensor_neg (f : E →L[𝕜] F) : (-f).rTensor G = -f.rTensor G := by ext; simp

/--
@isnad1 id=eq.0h6v.s12.309325afcf6a from=seed src=0 shape=8c560485 vocab=8c41a6de
-/
@[simp] lemma rTensor_sub (f₁ f₂ : E →L[𝕜] F) :
    (f₁ - f₂).rTensor G = f₁.rTensor G - f₂.rTensor G := by ext; simp

/--
@isnad1 id=eq.0h7v.s11.f578ca96a48d from=seed src=0 shape=6e9fe866 vocab=ca0fbab1
-/
lemma rTensor_comp (f₁ : E →L[𝕜] F) (f₂ : H →L[𝕜] E) :
    (f₁ ∘L f₂).rTensor G = f₁.rTensor G ∘L f₂.rTensor G := by ext; simp [LinearMap.rTensor_comp]

/--
@isnad1 id=eq.0h5v.s12.ffc656896b4f from=seed src=0 shape=01b7aa6c vocab=abffd116
-/
lemma rTensor_mul (f₁ f₂ : E →L[𝕜] E) : (f₁ * f₂).rTensor G = f₁.rTensor G * f₂.rTensor G :=
  rTensor_comp _ _ _

/--
@isnad1 id=eq.0h5v.s12.2a39c3d16836 from=seed src=0 shape=a8d0ee9b vocab=1969d844
-/
@[simp] lemma rTensor_pow (f : E →L[𝕜] E) (n : ℕ) : (f ^ n).rTensor G = (f.rTensor G) ^ n := by
  simp [← coe_inj]

/-- `LinearMap.lTensor` as a continuous linear map, i.e. the continuous linear map `g` extended to
the map `x ⊗ₜ[𝕜] y ↦ x ⊗ₜ[𝕜] g(y)`. -/
noncomputable def lTensor (g : E →L[𝕜] F) : (G ⊗[𝕜] E) →L[𝕜] (G ⊗[𝕜] F) :=
  commIsometry 𝕜 F G ∘L g.rTensor G ∘L commIsometry 𝕜 G E

variable {G} in
/--
@isnad1 id=eq.0h6v.s11.5f9966975591 from=seed src=0 shape=8c52e970 vocab=ca0c02a4
-/
@[simp] lemma lTensor_apply (g : G →L[𝕜] H) (x : E ⊗ G) :
    g.lTensor E x = g.toLinearMap.lTensor E x := by
  simp [lTensor, ← LinearMap.comm_comp_rTensor_comp_comm_eq]

/--
@isnad1 id=eq.0h7v.s11.cdd9b939cba6 from=seed src=0 shape=7d5b8ae8 vocab=6b71965e
-/
lemma lTensor_tmul (g : E →L[𝕜] F) (m : G) (n : E) : g.lTensor G (m ⊗ₜ n) = m ⊗ₜ g n := rfl

/--
@isnad1 id=eq.0h5v.s12.dc206dd40271 from=seed src=0 shape=d19c96bc vocab=8353d088
-/
theorem commIsometry_comp_lTensor_comp_commIsometry_eq (g : E →L[𝕜] F) :
    commIsometry 𝕜 F G ∘L g.rTensor G ∘L commIsometry 𝕜 G E = g.lTensor G :=
  rfl

/--
@isnad1 id=eq.0h5v.s12.43324b64d9fe from=seed src=0 shape=b6a7e506 vocab=8353d088
-/
theorem commIsometry_comp_rTensor_comp_commIsometry_eq (f : E →L[𝕜] F) :
    commIsometry 𝕜 G F ∘L f.lTensor G ∘L commIsometry 𝕜 E G = f.rTensor G := by
  ext; simp [lTensor]

/--
@isnad1 id=eq.0h5v.s12.41e93517c3ba from=seed src=0 shape=9e9a7873 vocab=8353d088
-/
theorem lTensor_comp_commIsometry (f : E →L[𝕜] F) :
    f.lTensor G ∘L commIsometry 𝕜 E G = commIsometry 𝕜 F G ∘L f.rTensor G := by
  ext; simp [lTensor]

/--
@isnad1 id=eq.0h5v.s12.6ee5face8f59 from=seed src=0 shape=821dc21b vocab=8353d088
-/
theorem rTensor_comp_commIsometry (g : E →L[𝕜] F) :
    g.rTensor G ∘L commIsometry 𝕜 G E = commIsometry 𝕜 G F ∘L g.lTensor G := by
  ext; simp [lTensor]

/--
@isnad1 id=eq.0h5v.s10.982a85fa4faa from=seed src=0 shape=17ece134 vocab=ddd1cb4d
-/
@[simp] lemma toLinearMap_lTensor (g : E →L[𝕜] F) :
    (g.lTensor G).toLinearMap = g.toLinearMap.lTensor G := by ext; simp

@[simp] lemma _root_.LinearIsometry.toContinuousLinearMap_lTensor (g : E →ₗᵢ[𝕜] F) :
    (g.lTensor G).toContinuousLinearMap = g.toContinuousLinearMap.lTensor G := by ext; simp

/--
@isnad1 id=le.0h5v.s10.7fe12483a1b9 from=seed src=0 shape=0a670963 vocab=512b8af6
-/
theorem norm_lTensor_le (g : E →L[𝕜] F) : ‖g.lTensor G‖ ≤ ‖g‖ := by
  simp_rw [lTensor, ← LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry]
  grw [opNorm_comp_le, opNorm_comp_le, LinearIsometry.norm_toContinuousLinearMap_le,
    LinearIsometry.norm_toContinuousLinearMap_le, mul_one, one_mul, norm_rTensor_le]

/--
@isnad1 id=eq.0h6v.s12.20862f8cc2a1 from=seed src=0 shape=a0b93a55 vocab=da721b08
-/
@[simp] lemma lTensor_add (f₁ f₂ : E →L[𝕜] F) :
    (f₁ + f₂).lTensor G = f₁.lTensor G + f₂.lTensor G := by ext; simp

/--
@isnad1 id=eq.0h6v.s12.38396282c463 from=seed src=0 shape=a9cfd3b3 vocab=b2ff2fc5
-/
@[simp] lemma lTensor_smul (r : 𝕜) (f : E →L[𝕜] F) : (r • f).lTensor G = r • f.lTensor G := by
  ext; simp

/--
@isnad1 id=eq.0h3v.s10.b97e24236ea6 from=seed src=0 shape=5dca7ce3 vocab=da7b4ac9
-/
@[simp] lemma lTensor_id : (.id 𝕜 E : E →L[𝕜] E).lTensor G = .id 𝕜 _ := by ext; simp
/--
@isnad1 id=eq.0h3v.s11.ecb9be2ad872 from=seed src=0 shape=e8283f36 vocab=1f139c21
-/
@[simp] lemma lTensor_one : (1 : E →L[𝕜] E).lTensor G = 1 := lTensor_id _
/--
@isnad1 id=eq.0h4v.s12.329f1085f290 from=seed src=0 shape=3aa8c475 vocab=1f139c21
-/
@[simp] lemma lTensor_zero : (0 : E →L[𝕜] F).lTensor G = 0 := by ext; simp
/--
@isnad1 id=eq.0h5v.s11.8312268870d7 from=seed src=0 shape=a1e207e3 vocab=2ab62bba
-/
@[simp] lemma lTensor_neg (f : E →L[𝕜] F) : (-f).lTensor G = -f.lTensor G := by ext; simp

/--
@isnad1 id=eq.0h6v.s12.fc8462646a1a from=seed src=0 shape=a0b93a55 vocab=ecf57e13
-/
@[simp] lemma lTensor_sub (f₁ f₂ : E →L[𝕜] F) :
    (f₁ - f₂).lTensor G = f₁.lTensor G - f₂.lTensor G := by ext; simp

/--
@isnad1 id=eq.0h7v.s11.06ca1c47cea5 from=seed src=0 shape=fcec5bf8 vocab=692a6ef2
-/
lemma lTensor_comp (f₁ : E →L[𝕜] F) (f₂ : H →L[𝕜] E) :
    (f₁ ∘L f₂).lTensor G = f₁.lTensor G ∘L f₂.lTensor G := by ext; simp [LinearMap.lTensor_comp]

/--
@isnad1 id=eq.0h5v.s12.59b2d4313029 from=seed src=0 shape=75eef599 vocab=c57f212d
-/
lemma lTensor_mul (f₁ f₂ : E →L[𝕜] E) : (f₁ * f₂).lTensor G = f₁.lTensor G * f₂.lTensor G :=
  lTensor_comp _ _ _

/--
@isnad1 id=eq.0h5v.s12.ea9cf63a24a6 from=seed src=0 shape=3598791d vocab=61c8e60e
-/
@[simp] lemma lTensor_pow (f : E →L[𝕜] E) (n : ℕ) : (f ^ n).lTensor G = (f.lTensor G) ^ n := by
  simp [← coe_inj]

end ContinuousLinearMap

namespace TensorProduct

/-- `TensorProduct.map` as a continuous linear map, i.e. the continuous linear map
`x ⊗ₜ[𝕜] y ↦ f(x) ⊗ₜ[𝕜] g(y)` formed from the continuous linear maps `f` and `g`. -/
noncomputable def mapL (f : E →L[𝕜] F) (g : G →L[𝕜] H) : (E ⊗[𝕜] G) →L[𝕜] (F ⊗[𝕜] H) :=
  f.rTensor H ∘L g.lTensor E

/--
@isnad1 id=le.0h7v.s11.49e77d7b2b2d from=seed src=0 shape=e0c48693 vocab=80135998
-/
theorem norm_mapL_le (f : E →L[𝕜] F) (g : G →L[𝕜] H) : ‖mapL f g‖ ≤ ‖f‖ * ‖g‖ := by
  grw [mapL, ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.norm_rTensor_le,
    ContinuousLinearMap.norm_lTensor_le]

/--
@isnad1 id=eq.0h8v.s11.ba217658786e from=seed src=0 shape=ef8a54ff vocab=85e731d4
-/
@[simp] lemma mapL_apply (f : E →L[𝕜] F) (g : G →L[𝕜] H) (x) :
    mapL f g x = map f.toLinearMap g.toLinearMap x := by
  simp [mapL, ← LinearMap.rTensor_comp_lTensor]

/--
@isnad1 id=eq.0h9v.s11.db21106d6155 from=seed src=0 shape=ff21c347 vocab=696b2e91
-/
lemma mapL_tmul (f : E →L[𝕜] F) (g : G →L[𝕜] H) (m : E) (n : G) :
    mapL f g (m ⊗ₜ n) = f m ⊗ₜ g n := rfl

/--
@isnad1 id=eq.0h6v.s12.1b5baff5fccd from=seed src=0 shape=51854d5b vocab=7f48fda9
-/
@[simp] lemma mapL_zero_left (f : E →L[𝕜] F) : mapL (0 : G →L[𝕜] H) f = 0 := by simp [mapL]
/--
@isnad1 id=eq.0h6v.s12.e1706ed9bf8f from=seed src=0 shape=64ba8cf0 vocab=7f48fda9
-/
@[simp] lemma mapL_zero_right (f : E →L[𝕜] F) : mapL f (0 : G →L[𝕜] H) = 0 := by simp [mapL]
/--
@isnad1 id=eq.0h3v.s10.588b542d08b2 from=seed src=0 shape=6a660b6b vocab=49f57aad
-/
@[simp] lemma mapL_id_id : mapL (.id 𝕜 E) (.id 𝕜 G) = .id 𝕜 _ := by simp [mapL]

/--
@isnad1 id=eq.0h7v.s12.010ca49575ca from=seed src=0 shape=c9110d3b vocab=8e4ec70a
-/
lemma mapL_comp_commIsometry (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL f g ∘L commIsometry 𝕜 G E = commIsometry 𝕜 H F ∘L mapL g f := by ext; simp [map_comm]

/--
@isnad1 id=eq.0h8v.s12.5d17e8382abe from=seed src=0 shape=ef726d50 vocab=88abca5a
-/
lemma mapL_add_left (f₁ f₂ : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL (f₁ + f₂) g = mapL f₁ g + mapL f₂ g := by ext; simp [map_add_left]

/--
@isnad1 id=eq.0h8v.s12.7b4b3dae5bd4 from=seed src=0 shape=b5c51304 vocab=88abca5a
-/
lemma mapL_add_right (f : E →L[𝕜] F) (g₁ g₂ : G →L[𝕜] H) :
    mapL f (g₁ + g₂) = mapL f g₁ + mapL f g₂ := by ext; simp [map_add_right]

/--
@isnad1 id=eq.0h8v.s12.d234f608f389 from=seed src=0 shape=ad349214 vocab=bd40c656
-/
lemma mapL_smul_left (r : 𝕜) (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL (r • f) g = r • mapL f g := by ext; simp [map_smul_left]

/--
@isnad1 id=eq.0h8v.s12.1260ecdbff32 from=seed src=0 shape=3c8e8afa vocab=bd40c656
-/
lemma mapL_smul_right (r : 𝕜) (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL f (r • g) = r • mapL f g := by ext; simp [map_smul_right]

/--
@isnad1 id=eq.0h7v.s11.f6e925f480e7 from=seed src=0 shape=b0484309 vocab=3b90908f
-/
@[simp] lemma toLinearMap_mapL (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    (mapL f g).toLinearMap = map f g := by ext; simp

/--
@isnad1 id=eq.0h7v.s11.d646ffcc9bfc from=seed src=0 shape=9aab173a vocab=cbaaf3d5
-/
@[simp] lemma toContinuousLinearMap_mapIsometry (f : E →ₗᵢ[𝕜] F) (g : G →ₗᵢ[𝕜] H) :
    (mapIsometry f g).toContinuousLinearMap =
      mapL f.toContinuousLinearMap g.toContinuousLinearMap := by
  ext; simp

section comp

variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace 𝕜 A] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 B]

/--
@isnad1 id=eq.0h11v.s11.5faf45870228 from=seed src=0 shape=5a3e659f vocab=b128bc8d
-/
lemma mapL_comp (f₁ : E →L[𝕜] F) (f₂ : A →L[𝕜] E) (g₁ : G →L[𝕜] H) (g₂ : B →L[𝕜] G) :
    mapL (f₁ ∘L f₂) (g₁ ∘L g₂) = mapL f₁ g₁ ∘L mapL f₂ g₂ := by ext; simp [map_map]

/--
@isnad1 id=eq.0h7v.s12.e0e878f39160 from=seed src=0 shape=0d832358 vocab=07e54b8c
-/
lemma mapL_mul (f₁ f₂ : E →L[𝕜] E) (g₁ g₂ : F →L[𝕜] F) :
    mapL (f₁ * f₂) (g₁ * g₂) = mapL f₁ g₁ * mapL f₂ g₂ := mapL_comp _ _ _ _

/--
@isnad1 id=eq.0h6v.s13.a9a4a132d142 from=seed src=0 shape=9c6ae7eb vocab=5ec8a336
-/
@[simp] lemma mapL_pow (f : E →L[𝕜] E) (g : F →L[𝕜] F) (n : ℕ) :
    (mapL f g) ^ n = mapL (f ^ n) (g ^ n) := by simp [← ContinuousLinearMap.coe_inj]

@[simp] lemma _root_.ContinuousLinearMap.mapL_comp_rTensor (f₁ : E →L[𝕜] F) (f₂ : A →L[𝕜] E)
    (g : G →L[𝕜] H) : mapL f₁ g ∘L f₂.rTensor G = mapL (f₁ ∘L f₂) g := by ext; simp

@[simp] lemma _root_.ContinuousLinearMap.mapL_comp_lTensor (f : E →L[𝕜] F) (g₁ : G →L[𝕜] H)
    (g₂ : A →L[𝕜] G) : mapL f g₁ ∘L g₂.lTensor E = mapL f (g₁ ∘L g₂) := by ext; simp

@[simp] lemma _root_.ContinuousLinearMap.rTensor_comp_mapL (f₁ : E →L[𝕜] F) (f₂ : A →L[𝕜] E)
    (g : G →L[𝕜] H) : f₁.rTensor H ∘L mapL f₂ g = mapL (f₁ ∘L f₂) g := by ext; simp

@[simp] lemma _root_.ContinuousLinearMap.lTensor_comp_mapL (f : E →L[𝕜] F) (g₁ : G →L[𝕜] H)
    (g₂ : A →L[𝕜] G) : g₁.lTensor F ∘L mapL f g₂ = mapL f (g₁ ∘L g₂) := by ext; simp

end comp

variable (G) in
theorem _root_.ContinuousLinearMap.rTensor_eq_mapL (f : E →L[𝕜] F) :
    f.rTensor G = mapL f (.id 𝕜 G) := by simp [mapL]

variable (E) in
theorem _root_.ContinuousLinearMap.lTensor_eq_mapL (g : G →L[𝕜] H) :
    g.lTensor E = mapL (.id 𝕜 E) g := by simp [mapL]

@[simp] lemma _root_.ContinuousLinearMap.lTensor_comp_rTensor (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    f.lTensor H ∘L g.rTensor E = mapL g f := by ext; simp [← LinearMap.lTensor_comp_rTensor]

@[simp] lemma _root_.ContinuousLinearMap.rTensor_comp_lTensor (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    f.rTensor H ∘L g.lTensor E = mapL f g := rfl

/--
@isnad1 id=eq.0h7v.s15.1aef29a9bd40 from=seed src=0 shape=bebad8e1 vocab=7769c69b
-/
@[simp] theorem adjoint_mapL [CompleteSpace E] [CompleteSpace G] [CompleteSpace (E ⊗[𝕜] G)]
    [CompleteSpace F] [CompleteSpace H] [CompleteSpace (F ⊗[𝕜] H)]
    (f : E →L[𝕜] F) (g : G →L[𝕜] H) : (mapL f g).adjoint = mapL f.adjoint g.adjoint := by
  apply ContinuousLinearMap.coe_inj.mp <| ext' ?_
  simp [TensorProduct.ext_iff_inner_right, ContinuousLinearMap.adjoint_inner_left]

set_option backward.isDefEq.respectTransparency.types false in
variable (G) in
@[simp] theorem _root_.ContinuousLinearMap.adjoint_rTensor [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E ⊗[𝕜] G)] [CompleteSpace (F ⊗[𝕜] G)] [CompleteSpace F] (f : E →L[𝕜] F) :
    (f.rTensor G).adjoint = f.adjoint.rTensor G := by simp [ContinuousLinearMap.rTensor_eq_mapL]

set_option backward.isDefEq.respectTransparency.types false in
variable (E) in
@[simp] theorem _root_.ContinuousLinearMap.adjoint_lTensor [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E ⊗[𝕜] H)] [CompleteSpace (E ⊗[𝕜] G)] [CompleteSpace H] (g : G →L[𝕜] H) :
    (g.lTensor E).adjoint = g.adjoint.lTensor E := by simp [ContinuousLinearMap.lTensor_eq_mapL]

open LinearMap

/--
@isnad1 id=eq.0h7v.s15.bcb8b2ff71a3 from=seed src=0 shape=1df2d014 vocab=f8d050e9
-/
@[simp] theorem adjoint_map [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →ₗ[𝕜] F) (g : G →ₗ[𝕜] H) :
    (map f g).adjoint = map f.adjoint g.adjoint :=
  ext' fun _ _ => by simp [TensorProduct.ext_iff_inner_right, adjoint_inner_left]

@[simp] theorem _root_.LinearMap.adjoint_rTensor [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] (f : E →ₗ[𝕜] F) :
    (f.rTensor G).adjoint = f.adjoint.rTensor G := by simp [rTensor]

@[simp] theorem _root_.LinearMap.adjoint_lTensor [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] (f : E →ₗ[𝕜] F) :
    (f.lTensor G).adjoint = f.adjoint.lTensor G := by simp [lTensor]

/-- Given `x, y : E ⊗ (F ⊗ G)`, `x = y` iff `⟪x, a ⊗ₜ (b ⊗ₜ c)⟫ = ⟪y, a ⊗ₜ (b ⊗ₜ c)⟫` for all
`a, b, c`.

See also `ext_iff_inner_right_threefold` for when `x, y : E ⊗ F ⊗ G`.
@isnad1 id=iff.0h6v.s10.d00a277af605 from=seed src=0 shape=63689214 vocab=061a4259
-/
theorem ext_iff_inner_right_threefold' {x y : E ⊗[𝕜] (F ⊗[𝕜] G)} :
    x = y ↔ ∀ a b c, inner 𝕜 x (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) = inner 𝕜 y (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) := by
  simp only [← (assocIsometry 𝕜 E F G).symm.injective.eq_iff,
    ext_iff_inner_right_threefold, LinearIsometryEquiv.inner_map_eq_flip]
  simp

/-- Given `x, y : E ⊗ (F ⊗ G)`, `x = y` iff `⟪a ⊗ₜ (b ⊗ₜ c), x⟫ = ⟪a ⊗ₜ (b ⊗ₜ c), y⟫` for all
`a, b, c`.

See also `ext_iff_inner_left_threefold` for when `x, y : E ⊗ F ⊗ G`.
@isnad1 id=iff.0h6v.s10.2daafceaa8fe from=seed src=0 shape=63219fc4 vocab=061a4259
-/
theorem ext_iff_inner_left_threefold' {x y : E ⊗[𝕜] (F ⊗[𝕜] G)} :
    x = y ↔ ∀ a b c, inner 𝕜 (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) x = inner 𝕜 (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold' (x := x) (y := y)

end TensorProduct

section orthonormal
variable {ι₁ ι₂ : Type*}

open Module

/-- The tensor product of two orthonormal vectors is orthonormal.
@isnad1 id=orthonor.2h7v.s8.b30b66da5646 from=seed src=0 shape=de919a76 vocab=1ac7ae06
-/
theorem Orthonormal.tmul
    {b₁ : ι₁ → E} {b₂ : ι₂ → F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 fun i : ι₁ × ι₂ ↦ b₁ i.1 ⊗ₜ[𝕜] b₂ i.2 := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [orthonormal_iff_ite.mp, hb₁, hb₂, ← ite_and, and_comm]

/-- The tensor product of two orthonormal bases is orthonormal.
@isnad1 id=orthonor.2h7v.s10.641b67cc8867 from=seed src=0 shape=86b76000 vocab=538980f5
-/
theorem Orthonormal.basisTensorProduct
    {b₁ : Basis ι₁ 𝕜 E} {b₂ : Basis ι₂ 𝕜 F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 (b₁.tensorProduct b₂) := by
  convert! hb₁.tmul hb₂
  exact b₁.tensorProduct_apply' b₂ _

namespace OrthonormalBasis
variable [Fintype ι₁] [Fintype ι₂]

/-- The orthonormal basis of the tensor product of two orthonormal bases. -/
protected noncomputable def tensorProduct
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    OrthonormalBasis (ι₁ × ι₂) 𝕜 (E ⊗[𝕜] F) :=
  (b₁.toBasis.tensorProduct b₂.toBasis).toOrthonormalBasis
    (b₁.orthonormal.basisTensorProduct b₂.orthonormal)

/--
@isnad1 id=eq.0h9v.s8.3b9affdf0498 from=seed src=0 shape=e10cbf84 vocab=92359df6
-/
@[simp]
lemma tensorProduct_apply
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (i : ι₁) (j : ι₂) :
    b₁.tensorProduct b₂ (i, j) = b₁ i ⊗ₜ[𝕜] b₂ j := by simp [OrthonormalBasis.tensorProduct]

/--
@isnad1 id=eq.0h8v.s9.8c554a1712c1 from=seed src=0 shape=95097d14 vocab=f8ca723d
-/
lemma tensorProduct_apply'
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (i : ι₁ × ι₂) :
    b₁.tensorProduct b₂ i = b₁ i.1 ⊗ₜ[𝕜] b₂ i.2 := tensorProduct_apply _ _ _ _

/--
@isnad1 id=eq.0h11v.s12.e133f66962c7 from=seed src=0 shape=b9212590 vocab=c781626a
-/
@[simp]
lemma tensorProduct_repr_tmul_apply (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
    (x : E) (y : F) (i : ι₁) (j : ι₂) :
    (b₁.tensorProduct b₂).repr (x ⊗ₜ[𝕜] y) (i, j) = b₂.repr y j * b₁.repr x i := by
  simp [OrthonormalBasis.tensorProduct]

/--
@isnad1 id=eq.0h10v.s12.a6da8eec6b4a from=seed src=0 shape=3eb53931 vocab=986b7060
-/
lemma tensorProduct_repr_tmul_apply'
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (x : E) (y : F) (i : ι₁ × ι₂) :
    (b₁.tensorProduct b₂).repr (x ⊗ₜ[𝕜] y) i = b₂.repr y i.2 * b₁.repr x i.1 :=
  tensorProduct_repr_tmul_apply _ _ _ _ _ _

/--
@isnad1 id=eq.0h7v.s9.7745145e2e98 from=seed src=0 shape=9034cd09 vocab=d6c52bd4
-/
@[simp]
lemma toBasis_tensorProduct (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    (b₁.tensorProduct b₂).toBasis = b₁.toBasis.tensorProduct b₂.toBasis := by
  simp [OrthonormalBasis.tensorProduct]

end OrthonormalBasis
end orthonormal
