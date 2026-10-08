/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
public import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic

/-!
# Derivatives of operations on continuous alternating maps

In this file we prove formulas for the derivatives of

- `ContinuousAlternatingMap.compContinuousLinearMap`, the pullback of a continuous alternating map
  along a continuous linear map;
- application of a `ContinuousAlternatingMap` as a function of both the map and the vectors.
-/

public section

variable {𝕜 ι E F G H : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

open ContinuousAlternatingMap
open scoped Topology

section CompContinuousLinearMap

variable
  {f : E → G [⋀^ι]→L[𝕜] H} {f' : E →L[𝕜] G [⋀^ι]→L[𝕜] H}
  {g : E → F →L[𝕜] G} {g' : E →L[𝕜] F →L[𝕜] G}
  {s : Set E} {x : E}

/-!
### Derivative of the pullback

In this section we prove a formula for the derivative
of the pullback of a continuous alternating map along a continuous linear map,
as a function of both maps.
-/

/--
@isnad1 id=iff.0h8v.s11.e1da02a55dd4 from=seed src=0 shape=4112e557 vocab=867c6685
-/
theorem ContinuousAlternatingMap.hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff [Finite ι] :
    HasStrictFDerivAt (toContinuousMultilinearMap ∘ f) (toContinuousMultilinearMapCLM 𝕜 ∘L f') x ↔
      HasStrictFDerivAt f f' x := by
  cases nonempty_fintype ι
  constructor <;> intro h
  · rw [hasStrictFDerivAt_iff_isLittleOTVS] at h ⊢
    refine Asymptotics.IsBigOTVS.trans_isLittleOTVS ?_ h
    simp only [Function.comp_apply, ← toContinuousMultilinearMapCLM_apply 𝕜,
      ContinuousLinearMap.comp_apply, ← map_sub]
    apply LinearMap.isBigOTVS_rev_comp
    simp [isEmbedding_toContinuousMultilinearMap.nhds_eq_comap]
  · exact (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x h

section HasFDerivAt

variable [Fintype ι] [DecidableEq ι]

/--
@isnad1 id=hasstric.0h6v.s14.fad5f7d80e52 from=seed src=0 shape=29ad2a92 vocab=9e4e9d2f
-/
theorem ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg : (G [⋀^ι]→L[𝕜] H) × (F →L[𝕜] G)) :
    HasStrictFDerivAt
      (fun fg : (G [⋀^ι]→L[𝕜] H) × (F →L[𝕜] G) ↦ fg.1.compContinuousLinearMap fg.2)
      (compContinuousLinearMapCLM fg.2 ∘L .fst _ _ _ +
        fg.1.fderivCompContinuousLinearMap fg.2 ∘L .snd _ _ _)
      fg := by
  rw [← hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff]
  have H₁ := ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg.1.1, fun _ : ι ↦ fg.2)
  have H₂ := ((toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt (x := fg.1))
  have H₃ := hasStrictFDerivAt_pi.mpr fun i : ι ↦ hasStrictFDerivAt_id (𝕜 := 𝕜) fg.2
  exact H₁.comp fg (H₂.prodMap fg H₃)

/--
@isnad1 id=hasstric.2h11v.s12.c42aac42c996 from=seed src=0 shape=2c30b893 vocab=10828f90
-/
theorem HasStrictFDerivAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x :=
  hasStrictFDerivAt_compContinuousLinearMap (f x, g x) |>.comp x (hf.prodMk hg)

/--
@isnad1 id=hasfderi.2h11v.s12.0c6222e1b158 from=seed src=0 shape=2c30b893 vocab=c40c8b8a
-/
theorem HasFDerivAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x := by
  convert!
    hasStrictFDerivAt_compContinuousLinearMap (f x, (g x)) |>.hasFDerivAt |>.comp x (hf.prodMk hg)

/--
@isnad1 id=hasfderi.2h12v.s12.75fd86db8c5f from=seed src=0 shape=5d5f466d vocab=d2905870
-/
theorem HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun x ↦ (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') s x := by
  convert!
    hasStrictFDerivAt_compContinuousLinearMap (f x, (g x)) |>.hasFDerivAt |>.comp_hasFDerivWithinAt
      x (hf.prodMk hg)

/--
@isnad1 id=eq.3h10v.s12.81c7e2a87a4f from=seed src=0 shape=a0eda8b9 vocab=e430188e
-/
theorem fderivWithin_continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) s x =
      compContinuousLinearMapCLM (g x) ∘L fderivWithin 𝕜 f s x +
        (f x).fderivCompContinuousLinearMap (g x) ∘L fderivWithin 𝕜 g s x :=
  hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivWithinAt)
    |>.fderivWithin hs

/--
@isnad1 id=eq.2h9v.s12.f1e19435aea4 from=seed src=0 shape=cda70109 vocab=f384e969
-/
theorem fderiv_continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) x =
      compContinuousLinearMapCLM (g x) ∘L fderiv 𝕜 f x +
        (f x).fderivCompContinuousLinearMap (g x) ∘L fderiv 𝕜 g x :=
  hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivAt) |>.fderiv

end HasFDerivAt

/-!
### Differentiability of the pullback

In this section we prove that the pullback of a continuous alternating map
along a continuous linear map is differentiable with respect to a parameter,
provided that both maps are differentiable.
-/

variable [Finite ι]

/--
@isnad1 id=differen.2h10v.s10.49f27f85a21b from=seed src=0 shape=d5ec44d2 vocab=0991f135
-/
theorem DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) :
    DifferentiableWithinAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivWithinAt
    |>.differentiableWithinAt

/--
@isnad1 id=differen.2h9v.s10.6b90633cf01e from=seed src=0 shape=99374d45 vocab=7b15350f
-/
theorem DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun x ↦ (f x).compContinuousLinearMap (g x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivAt
    |>.differentiableAt

end CompContinuousLinearMap

/-!
### Derivative of a continuous alternating map applied to a tuple of vectors

In this section we prove the formula for the derivative `D_xf(x; g_0(x), ..., g_n(x))`.
-/

section Apply

variable {f : E → F [⋀^ι]→L[𝕜] G} {f' : E →L[𝕜] F [⋀^ι]→L[𝕜] G}
  {g : ι → E → F} {g' : ι → E →L[𝕜] F}
  {s : Set E} {x : E}

section HasFDerivAt

variable [Fintype ι] [DecidableEq ι]

namespace ContinuousAlternatingMap

/--
@isnad1 id=hasstric.0h6v.s8.90c0969222e1 from=seed src=0 shape=fe54fa93 vocab=c5116fe2
-/
theorem hasStrictFDerivAt (f : E [⋀^ι]→L[𝕜] F) (x : ι → E) :
    HasStrictFDerivAt f (f.1.linearDeriv x) x :=
  f.1.hasStrictFDerivAt x

/--
@isnad1 id=hasfderi.0h6v.s8.f1fbb85b174d from=seed src=0 shape=fe54fa93 vocab=6086dda0
-/
theorem hasFDerivAt (f : E [⋀^ι]→L[𝕜] F) (x : ι → E) : HasFDerivAt f (f.1.linearDeriv x) x :=
  f.1.hasFDerivAt x

/--
@isnad1 id=hasfderi.0h7v.s8.bc55839a0c2b from=seed src=0 shape=34831a26 vocab=2cdcb006
-/
theorem hasFDerivWithinAt (f : E [⋀^ι]→L[𝕜] F) (s : Set (ι → E)) (x : ι → E) :
    HasFDerivWithinAt f (f.1.linearDeriv x) s x :=
  (f.hasFDerivAt x).hasFDerivWithinAt

end ContinuousAlternatingMap

/--
@isnad1 id=hasstric.2h10v.s11.3b5941141439 from=seed src=0 shape=78dbd767 vocab=89369c92
-/
theorem HasStrictFDerivAt.continuousAlternatingMap_apply (hf : HasStrictFDerivAt f f' x)
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt
      (fun x ↦ f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      x :=
  (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x hf
    |>.continuousMultilinearMap_apply hg

/--
@isnad1 id=hasfderi.2h10v.s11.e5d3c9034c55 from=seed src=0 shape=78dbd767 vocab=eebea83a
-/
theorem HasFDerivAt.continuousAlternatingMap_apply (hf : HasFDerivAt f f' x)
    (hg : ∀ i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt
      (fun x ↦ f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      x :=
  (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp x hf
    |>.continuousMultilinearMap_apply hg

/--
@isnad1 id=hasfderi.2h11v.s11.81b1bbbd0dd5 from=seed src=0 shape=c0781133 vocab=71883d67
-/
theorem HasFDerivWithinAt.continuousAlternatingMap_apply (hf : HasFDerivWithinAt f f' s x)
    (hg : ∀ i, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt
      (fun x ↦ f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      s x :=
  (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x hf
    |>.continuousMultilinearMap_apply hg

/--
@isnad1 id=eq.3h9v.s11.4647d23672da from=seed src=0 shape=962f14b0 vocab=95caaee4
-/
theorem fderivWithin_continuousAlternatingMap_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x ↦ f x (g · x)) s x =
      apply 𝕜 F G (g · x) ∘L fderivWithin 𝕜 f s x +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L fderivWithin 𝕜 (g i) s x :=
  hf.hasFDerivWithinAt.continuousAlternatingMap_apply (fun i ↦ (hg i).hasFDerivWithinAt)
    |>.fderivWithin hs

/--
@isnad1 id=eq.3h10v.s11.0268b47129ec from=seed src=0 shape=8ddb9186 vocab=f2d9baf5
-/
theorem fderivWithin_continuousAlternatingMap_apply_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x) (hs : UniqueDiffWithinAt 𝕜 s x) (dx : E) :
    fderivWithin 𝕜 (fun x ↦ f x (g · x)) s x dx =
      fderivWithin 𝕜 f s x dx (g · x) +
        ∑ i, f x (Function.update (g · x) i (fderivWithin 𝕜 (g i) s x dx)) := by
  simp [fderivWithin_continuousAlternatingMap_apply, *]

/--
@isnad1 id=eq.2h8v.s11.8cadadbdf45a from=seed src=0 shape=61185d4b vocab=9fb63e4d
-/
theorem fderiv_continuousAlternatingMap_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (fun x ↦ f x (g · x)) x =
      apply 𝕜 F G (g · x) ∘L fderiv 𝕜 f x +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L fderiv 𝕜 (g i) x :=
  hf.hasFDerivAt.continuousAlternatingMap_apply (fun i ↦ (hg i).hasFDerivAt) |>.fderiv

/--
@isnad1 id=eq.2h9v.s11.c10396ede869 from=seed src=0 shape=8eb74a5d vocab=441241f2
-/
theorem fderiv_continuousAlternatingMap_apply_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) (dx : E) :
    fderiv 𝕜 (fun x ↦ f x (g · x)) x dx =
      fderiv 𝕜 f x dx (g · x) +
        ∑ i, f x (Function.update (g · x) i (fderiv 𝕜 (g i) x dx)) := by
  simp [fderiv_continuousAlternatingMap_apply, *]

end HasFDerivAt

variable [Finite ι]

/--
@isnad1 id=differen.2h9v.s9.f2a719673da9 from=seed src=0 shape=e78f52c2 vocab=cbc220d8
-/
theorem DifferentiableWithinAt.continuousAlternatingMap_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : ∀ i, DifferentiableWithinAt 𝕜 (g i) s x) :
    DifferentiableWithinAt 𝕜 (fun x ↦ f x (g · x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousAlternatingMap_apply (fun i ↦ (hg i).hasFDerivWithinAt)
    |>.differentiableWithinAt

/--
@isnad1 id=differen.2h8v.s9.22309dd5fc28 from=seed src=0 shape=63205d1e vocab=3014ebea
-/
theorem DifferentiableAt.continuousAlternatingMap_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) : DifferentiableAt 𝕜 (fun x ↦ f x (g · x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousAlternatingMap_apply (fun i ↦ (hg i).hasFDerivAt)
    |>.differentiableAt

/--
@isnad1 id=differen.2h8v.s9.3f25d4fb96e7 from=seed src=0 shape=5f32857d vocab=d91da474
-/
theorem DifferentiableOn.continuousAlternatingMap_apply (hf : DifferentiableOn 𝕜 f s)
    (hg : ∀ i, DifferentiableOn 𝕜 (g i) s) : DifferentiableOn 𝕜 (fun x ↦ f x (g · x)) s :=
  fun x hx ↦ (hf x hx).continuousAlternatingMap_apply (hg · x hx)

/--
@isnad1 id=differen.2h7v.s9.32d91546f2c2 from=seed src=0 shape=cbf0dd40 vocab=6ff77abd
-/
theorem Differentiable.continuousAlternatingMap_apply (hf : Differentiable 𝕜 f)
    (hg : ∀ i, Differentiable 𝕜 (g i)) : Differentiable 𝕜 (fun x ↦ f x (g · x)) :=
  fun x ↦ (hf x).continuousAlternatingMap_apply (hg · x)

/--
@isnad1 id=differen.0h5v.s8.b31d1b3f467a from=seed src=0 shape=84ba9feb vocab=aecf2c17
-/
theorem ContinuousAlternatingMap.differentiable (f : E [⋀^ι]→L[𝕜] F) : Differentiable 𝕜 f := by
  cases nonempty_fintype ι
  apply Differentiable.continuousAlternatingMap_apply <;> fun_prop

end Apply
