/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.RCLike.Basic
public import Tengoku.Seed.Topology.ContinuousMap.Compact
public import Tengoku.Seed.Topology.ContinuousMap.Ordered
import Tengoku.Seed.Topology.ContinuousMap.Units

/-! # Mapping `C(X, ℝ)` to `C(X, 𝕜)` and back

This file contains the definitions for `ContinuousMap.realToRCLike` and
`ContinuousMap.rclikeToReal`, which map `C(X, ℝ)` to `C(X, 𝕜)` and back for any `RCLike 𝕜`. -/

@[expose] public section

namespace ContinuousMap
variable {X : Type*} (𝕜 : Type*) [TopologicalSpace X] [RCLike 𝕜]

/-- Lifting `C(X, ℝ)` to `C(X, 𝕜)` using `RCLike.ofReal`. -/
@[simps] def realToRCLike (f : C(X, ℝ)) : C(X, 𝕜) where toFun x := RCLike.ofReal (f x)

/--
@isnad1 id=isselfad.0h3v.s6.6af7e15b4c07 from=seed src=0 shape=5566f8cc vocab=2c067e80
-/
@[simp, grind .] lemma isSelfAdjoint_realToRCLike {f : C(X, ℝ)} :
    IsSelfAdjoint (f.realToRCLike 𝕜) := by ext; simp

/--
@isnad1 id=eq.0h3v.s7.795d9abb51f8 from=seed src=0 shape=cf5d95a5 vocab=92f0496d
-/
@[simp] lemma spectrum_realToRCLike (f : C(X, ℝ)) :
    spectrum ℝ (f.realToRCLike 𝕜) = spectrum ℝ f := by
  ext; simp [spectrum.mem_iff, isUnit_iff_forall_isUnit, RCLike.ext_iff (K := 𝕜), Algebra.smul_def]

open ComplexOrder

set_option backward.isDefEq.respectTransparency.types false in
variable (X) in
/-- `ContinuousMap.realToRCLike` as an order embedding. -/
@[simps] def realToRCLikeOrderEmbedding : C(X, ℝ) ↪o C(X, 𝕜) where
  toFun := realToRCLike 𝕜
  inj' f g hfg := by ext x; simpa using congr($hfg x)
  map_rel_iff' := by simp [le_def]

variable (X) in
/--
@isnad1 id=monotone.0h2v.s6.9c70c0ed8900 from=seed src=0 shape=76c8feeb vocab=505509d7
-/
lemma realToRCLike_monotone : Monotone (realToRCLike (X := X) 𝕜) :=
  realToRCLikeOrderEmbedding X 𝕜 |>.monotone

variable (X) in
/--
@isnad1 id=strictmo.0h2v.s6.ed4bf66d5dc3 from=seed src=0 shape=76c8feeb vocab=dc3440b0
-/
lemma realToRCLike_strictMono : StrictMono (realToRCLike (X := X) 𝕜) :=
  realToRCLikeOrderEmbedding X 𝕜 |>.strictMono

variable (X) in
/--
@isnad1 id=injectiv.0h2v.s5.8ff15ab6c01d from=seed src=0 shape=76c8feeb vocab=a71776e2
-/
@[simp] lemma realToRCLike_injective : (realToRCLike (X := X) 𝕜).Injective :=
  realToRCLikeOrderEmbedding X 𝕜 |>.injective

/--
@isnad1 id=iff.0h4v.s6.e0071612190d from=seed src=0 shape=ff12a6b1 vocab=ed3935af
-/
@[simp] lemma realToRCLike_inj {f g : C(X, ℝ)} :
    realToRCLike 𝕜 f = realToRCLike 𝕜 g ↔ f = g :=
  realToRCLikeOrderEmbedding X 𝕜 |>.eq_iff_eq

/--
@isnad1 id=iff.0h4v.s7.41cc3797200c from=seed src=0 shape=ff12a6b1 vocab=3dc63fa9
-/
@[simp] lemma realToRCLike_le_realToRCLike_iff {f g : C(X, ℝ)} :
    realToRCLike 𝕜 f ≤ realToRCLike 𝕜 g ↔ f ≤ g :=
  realToRCLikeOrderEmbedding X 𝕜 |>.le_iff_le

/--
@isnad1 id=iff.0h4v.s7.13e644a01a99 from=seed src=0 shape=ff12a6b1 vocab=75afb6ef
-/
@[simp] lemma realToRCLike_lt_realToRCLike_iff {f g : C(X, ℝ)} :
    realToRCLike 𝕜 f < realToRCLike 𝕜 g ↔ f < g :=
  realToRCLikeOrderEmbedding X 𝕜 |>.lt_iff_lt

variable (X) in
/--
@isnad1 id=isometry.0h2v.s7.13e3b294b7ee from=seed src=0 shape=1118701a vocab=12abef08
-/
@[simp] theorem isometry_realToRCLike [CompactSpace X] : Isometry (realToRCLike 𝕜 (X := X)) :=
  .of_dist_eq fun f g ↦ by simp [dist_eq_norm, norm_eq_iSup_norm, ← map_sub]

variable (X) in
/--
@isnad1 id=continuo.0h2v.s6.142eacc32dca from=seed src=0 shape=76c8feeb vocab=a80364b0
-/
@[simp, fun_prop] lemma continuous_realToRCLike : Continuous (realToRCLike 𝕜 (X := X)) :=
  continuous_postcomp { toFun x := RCLike.ofReal x }

variable (X) in
/-- `ContinuousMap.realToRCLike` as a ⋆-algebra map. -/
noncomputable def realToRCLikeStarAlgHom : C(X, ℝ) →⋆ₐ[ℝ] C(X, 𝕜) :=
  compStarAlgHom X (RCLike.ofRealStarAlgHom 𝕜) RCLike.continuous_ofReal

/--
@isnad1 id=eq.0h3v.s9.338b84e394fa from=seed src=0 shape=9c7ed81c vocab=99271a37
-/
@[simp] lemma realToRCLikeStarAlgHom_apply (f : C(X, ℝ)) :
    realToRCLikeStarAlgHom X 𝕜 f = f.realToRCLike 𝕜 := rfl

/--
@isnad1 id=eq.0h3v.s7.f9de77ea24bf from=seed src=0 shape=6325be4c vocab=e12baef2
-/
lemma realToRCLike_star (f : C(X, ℝ)) : (star f).realToRCLike 𝕜 = star (f.realToRCLike 𝕜) :=
  map_star (realToRCLikeStarAlgHom X 𝕜) f

/--
@isnad1 id=eq.0h4v.s7.12ec7d860d1d from=seed src=0 shape=2644f00c vocab=4ad01b65
-/
@[simp] lemma realToRCLike_mul (f g : C(X, ℝ)) :
    (f * g).realToRCLike 𝕜 = f.realToRCLike 𝕜 * g.realToRCLike 𝕜 :=
  map_mul (realToRCLikeStarAlgHom X 𝕜) f g

variable {𝕜} in
/-- Mapping `C(X, 𝕜)` to `C(X, ℝ)` using `RCLike.re`. -/
@[simps] def rclikeToReal (f : C(X, 𝕜)) : C(X, ℝ) where toFun x := RCLike.re (f x)

variable (X) in
/--
@isnad1 id=monotone.0h2v.s6.2dc944840314 from=seed src=0 shape=97ebdb0a vocab=917fa3f1
-/
lemma rclikeToReal_monotone : Monotone (rclikeToReal (X := X) (𝕜 := 𝕜)) := by
  intro a b; simp_all [le_def, RCLike.le_iff_re_im (K := 𝕜)]

variable (X) in
/--
@isnad1 id=continuo.0h2v.s6.052efff10630 from=seed src=0 shape=97ebdb0a vocab=14658f51
-/
@[simp, fun_prop] lemma continuous_rclikeToReal : Continuous (rclikeToReal (X := X) (𝕜 := 𝕜)) :=
  continuous_postcomp { toFun x := RCLike.re x }

/--
@isnad1 id=eq.0h3v.s5.96021c481842 from=seed src=0 shape=8c34faf6 vocab=55861928
-/
@[simp] theorem rclikeToReal_realToRCLike (f : C(X, ℝ)) :
    (f.realToRCLike 𝕜).rclikeToReal = f := by ext; simp

variable {𝕜} in
/--
@isnad1 id=eq.1h3v.s7.de782ecdb315 from=seed src=0 shape=0b4865fe vocab=b515861e
-/
@[aesop safe apply, grind =]
theorem IsSelfAdjoint.realToRCLike_rclikeToReal {f : C(X, 𝕜)} (hf : IsSelfAdjoint f) :
    f.rclikeToReal.realToRCLike 𝕜 = f := by
  ext
  simp only [realToRCLike_apply, rclikeToReal_apply, ← RCLike.conj_eq_iff_re]
  conv_rhs => rw [← hf.star_eq]
  simp

variable (X) in
open ContinuousMap in
/--
@isnad1 id=eq.0h2v.s7.0e76b093a09e from=seed src=0 shape=d7fc4e84 vocab=8cfb43cc
-/
theorem range_realToRCLike_eq_isSelfAdjoint :
    .range (realToRCLike 𝕜) = {f : C(X, 𝕜) | IsSelfAdjoint f} :=
  le_antisymm (fun _ ⟨_, h⟩ ↦ by simp [← h]) fun f hf ↦
    ⟨f.rclikeToReal, hf.realToRCLike_rclikeToReal⟩

end ContinuousMap
