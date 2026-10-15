/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Tengoku.LeanPool.LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1
public import Tengoku

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H2`

An upstream-friendly **definition** of a Euclidean `H²`-type space built from `L²`.

This is a “graph-closure” Sobolev-style construction analogous to `Euclidean.H1`: we take `C²`
compactly supported functions, map them to their `L²` classes together with their gradient and
Hessian, and define `H²` as the topological closure of the range inside an ambient `L²` product.

No Rellich/elliptic regularity theorems are proved here; this file is purely definitional/API.
-/

@[expose] public section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory
open MeasureTheory

section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceH2 : MeasurableSpace E := borel E
/--
@isnad1 id=borelspa.0h1v.s4.3e40b7dd3ffc from=translated src=- shape=c6850a32 vocab=1fa15ae3
-/
local instance instBorelSpaceH2 : BorelSpace E := ⟨rfl⟩
/--
@isnad1 id=opensmea.0h1v.s4.782c24d26569 from=translated src=- shape=c6850a32 vocab=220a3419
-/
local instance instOpensMeasurableSpaceH2 : OpensMeasurableSpace E := by infer_instance

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

/-- Square-integrable functions taking values in continuous linear endomorphisms. -/
abbrev L2EE : Type _ := ↥(E →₂[μ] (E →L[ℝ] E))
/-- The product space containing a function and its first two derivatives. -/
abbrev H2Target : Type _ := L2ℝ (μ := μ) × (L2E (μ := μ) × L2EE (μ := μ))

/-- `C²` real-valued functions on `E` with compact support, as a submodule of `E → ℝ`. -/
def C2c : Submodule ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ 2 f ∧ HasCompactSupport f}
  zero_mem' := by
    refine ⟨contDiff_const, ?_⟩
    simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : E => (0 : ℝ)))
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, ?_⟩
    exact (HasCompactSupport.smul_left (f := fun _ : E => c) hf.2)

omit [CompleteSpace E] in
/--
@isnad1 id=le.0h1v.s6.92bebf209363 from=translated src=- shape=b8f7a10e vocab=4e27c7ce
-/
lemma C2c_le_C1c : C2c (E := E) ≤ C1c (E := E) := by
  intro f hf
  refine ⟨hf.1.of_le ?_, hf.2⟩
  -- `ContDiff 2` implies `ContDiff 1`.
  decide

/-- The coercion map `C²_c →ₗ C¹_c`. -/
noncomputable def C2cToC1cLinear : ↥(C2c (E := E)) →ₗ[ℝ] ↥(C1c (E := E)) :=
  Submodule.inclusion (C2c_le_C1c (E := E))

/-- The pointwise Hessian (as an `E →L E`-valued function), defined as `fderiv` of `grad`. -/
noncomputable def hess (f : E → ℝ) : E → (E →L[ℝ] E) :=
  fun x => fderiv ℝ (grad (E := E) f) x

/--
@isnad1 id=contdiff.1h2v.s6.4246baafde4f from=translated src=- shape=9dfb37a0 vocab=86c7716d
-/
lemma contDiff_grad_of_contDiff2 {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (grad (E := E) f) := by
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (m := 1) (n := 2) (by decide)
  have hfderiv' : ContDiff ℝ 1 fun x => (fderiv ℝ f x : StrongDual ℝ E) := by
    exact hfderiv
  exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp hfderiv'

/--
@isnad1 id=continuo.1h2v.s7.0d0ab2e81ab1 from=translated src=- shape=f456eef2 vocab=873e1ed2
-/
lemma continuous_hess {f : E → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (hess (E := E) f) := by
  have hgrad : ContDiff ℝ 1 (grad (E := E) f) := contDiff_grad_of_contDiff2 (E := E) hf
  have hcont : Continuous (fderiv ℝ (grad (E := E) f)) := hgrad.continuous_fderiv one_ne_zero
  exact hcont

/--
@isnad1 id=hascompa.1h2v.s7.29f606a03819 from=translated src=- shape=e64024d9 vocab=9fdc7306
-/
lemma hasCompactSupport_hess {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (hess (E := E) f) := by
  have hcs_grad : HasCompactSupport (grad (E := E) f) := hasCompactSupport_grad (E := E) hf
  have : HasCompactSupport (fderiv ℝ (grad (E := E) f)) := hcs_grad.fderiv ℝ
  exact this

/--
@isnad1 id=memlp.1h3v.s9.1863ee66b9d4 from=translated src=- shape=30c7c470 vocab=a8801053
-/
lemma memLp_hess_of_mem_C2c {f : E → ℝ} (hf : f ∈ C2c (E := E)) :
    MemLp (hess (E := E) f) 2 μ := by
  have hcont : Continuous (hess (E := E) f) := continuous_hess (E := E) hf.1
  have hcs : HasCompactSupport (hess (E := E) f) := hasCompactSupport_hess (E := E) (f := f) hf.2
  exact hcont.memLp_of_hasCompactSupport (μ := μ) (p := (2 : ℝ≥0∞)) hcs

/--
@isnad1 id=eq.2h3v.s9.f011704a994e from=translated src=- shape=b2bfc1c1 vocab=f06c8fa2
-/
lemma hess_add {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    hess (E := E) (f + g) = hess (E := E) f + hess (E := E) g := by
  funext x
  have hgradFun : grad (E := E) (f + g) = grad (E := E) f + grad (E := E) g := by
    funext y
    have hdfy : DifferentiableAt ℝ f y :=
      (hf.differentiable (by decide)).differentiableAt
    have hdgy : DifferentiableAt ℝ g y :=
      (hg.differentiable (by decide)).differentiableAt
    simp [grad, fderiv_add hdfy hdgy, map_add]
  have hgradf : DifferentiableAt ℝ (grad (E := E) f) x :=
    ((contDiff_grad_of_contDiff2 (E := E) hf).differentiable one_ne_zero).differentiableAt
  have hgradg : DifferentiableAt ℝ (grad (E := E) g) x :=
    ((contDiff_grad_of_contDiff2 (E := E) hg).differentiable one_ne_zero).differentiableAt
  simp [hess, hgradFun, fderiv_add hgradf hgradg]

/--
@isnad1 id=eq.1h3v.s9.bb1df6916f3b from=translated src=- shape=c08e73d5 vocab=206c3ef6
-/
lemma hess_smul (c : ℝ) {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    hess (E := E) (c • f) = c • hess (E := E) f := by
  funext x
  have hgradFun : grad (E := E) (c • f) = c • grad (E := E) f := by
    funext y
    have hdfy : DifferentiableAt ℝ f y :=
      (hf.differentiable (by decide)).differentiableAt
    simp [grad, fderiv_const_smul hdfy, map_smul]
  have hgradf : DifferentiableAt ℝ (grad (E := E) f) x :=
    ((contDiff_grad_of_contDiff2 (E := E) hf).differentiable one_ne_zero).differentiableAt
  simp [hess, hgradFun, fderiv_const_smul hgradf]

/-- The `L²` class of the Hessian of a `C²` compactly supported function. -/
noncomputable def toL2Hess (f : ↥(C2c (E := E))) : L2EE (μ := μ) :=
  (memLp_hess_of_mem_C2c (μ := μ) (E := E) f.2).toLp (hess (E := E) f.1)

private lemma toL2Hess_add (f g : ↥(C2c (E := E))) :
    toL2Hess (μ := μ) (E := E) (f + g) =
      toL2Hess (μ := μ) (E := E) f + toL2Hess (μ := μ) (E := E) g := by
  apply Lp.ext
  have hf : (toL2Hess (μ := μ) (E := E) f : E → (E →L[ℝ] E)) =ᵐ[μ] hess (E := E) f.1 :=
    (memLp_hess_of_mem_C2c (μ := μ) (E := E) f.2).coeFn_toLp
  have hg : (toL2Hess (μ := μ) (E := E) g : E → (E →L[ℝ] E)) =ᵐ[μ] hess (E := E) g.1 :=
    (memLp_hess_of_mem_C2c (μ := μ) (E := E) g.2).coeFn_toLp
  have hfg :
      (toL2Hess (μ := μ) (E := E) (f + g) : E → (E →L[ℝ] E)) =ᵐ[μ]
        hess (E := E) (f.1 + g.1) :=
    (memLp_hess_of_mem_C2c (μ := μ) (E := E) (f + g).2).coeFn_toLp
  refine hfg.trans ?_
  filter_upwards
    [Lp.coeFn_add (toL2Hess (μ := μ) (E := E) f) (toL2Hess (μ := μ) (E := E) g), hf, hg]
    with x hxadd hxf hxg
  have hhess :
      hess (E := E) (f.1 + g.1) x =
        hess (E := E) f.1 x + hess (E := E) g.1 x := by
    have := hess_add (E := E) f.2.1 g.2.1
    simpa using congrArg (fun h => h x) this
  calc
    hess (E := E) (f.1 + g.1) x = hess (E := E) f.1 x + hess (E := E) g.1 x := hhess
    _ =
        (toL2Hess (μ := μ) (E := E) f : E → (E →L[ℝ] E)) x +
          (toL2Hess (μ := μ) (E := E) g : E → (E →L[ℝ] E)) x := by
        simp [hxf, hxg]
    _ =
        ((toL2Hess (μ := μ) (E := E) f + toL2Hess (μ := μ) (E := E) g : L2EE (μ := μ)) :
            E → (E →L[ℝ] E)) x := by
        simpa [Pi.add_apply] using hxadd.symm

private lemma toL2Hess_smul (c : ℝ) (f : ↥(C2c (E := E))) :
    toL2Hess (μ := μ) (E := E) (c • f) = c • toL2Hess (μ := μ) (E := E) f := by
  apply Lp.ext
  have hf : (toL2Hess (μ := μ) (E := E) f : E → (E →L[ℝ] E)) =ᵐ[μ] hess (E := E) f.1 :=
    (memLp_hess_of_mem_C2c (μ := μ) (E := E) f.2).coeFn_toLp
  have hcf :
      (toL2Hess (μ := μ) (E := E) (c • f) : E → (E →L[ℝ] E)) =ᵐ[μ]
        hess (E := E) (c • f.1) :=
    (memLp_hess_of_mem_C2c (μ := μ) (E := E) (c • f).2).coeFn_toLp
  refine hcf.trans ?_
  filter_upwards [Lp.coeFn_smul c (toL2Hess (μ := μ) (E := E) f), hf] with x hxsmul hxf
  have hhess : hess (E := E) (c • f.1) x = c • hess (E := E) f.1 x := by
    have := hess_smul (E := E) (c := c) (f := f.1) f.2.1
    simpa using congrArg (fun h => h x) this
  calc
    hess (E := E) (c • f.1) x = c • hess (E := E) f.1 x := hhess
    _ = c • (toL2Hess (μ := μ) (E := E) f : E → (E →L[ℝ] E)) x := by
      simp [hxf]
    _ =
        ((c • toL2Hess (μ := μ) (E := E) f : L2EE (μ := μ)) : E → (E →L[ℝ] E)) x := by
        simpa [Pi.smul_apply] using hxsmul.symm

/-- Linear map sending `C²_c` functions to the `L²` class of their Hessian. -/
noncomputable def toL2HessLinear : ↥(C2c (E := E)) →ₗ[ℝ] L2EE (μ := μ) where
  toFun := toL2Hess (μ := μ) (E := E)
  map_add' := by exact toL2Hess_add (μ := μ) (E := E)
  map_smul' := by exact toL2Hess_smul (μ := μ) (E := E)

/-- Linear map `C²_c → L²` (via the inclusion `C²_c ⊆ C¹_c`). -/
noncomputable def toL2FromC2cLinear : ↥(C2c (E := E)) →ₗ[ℝ] L2ℝ (μ := μ) :=
  (toL2Linear (μ := μ) (E := E)).comp (C2cToC1cLinear (E := E))

/-- Linear map `C²_c → L²(E)` for gradients (via the inclusion `C²_c ⊆ C¹_c`). -/
noncomputable def toL2GradFromC2cLinear : ↥(C2c (E := E)) →ₗ[ℝ] L2E (μ := μ) :=
  (toL2GradLinear (μ := μ) (E := E)).comp (C2cToC1cLinear (E := E))

/-- The graph map `f ↦ (f, ∇f, Hess f)` into `L² × (L²(E) × L²(E →L E))`. -/
noncomputable def graph2 : ↥(C2c (E := E)) →ₗ[ℝ] H2Target (μ := μ) :=
  (toL2FromC2cLinear (μ := μ) (E := E)).prod
    ((toL2GradFromC2cLinear (μ := μ) (E := E)).prod (toL2HessLinear (μ := μ) (E := E)))

/-- The Euclidean `H²` space (as a closed submodule of `L² × (L²(E) × L²(E →L E))`). -/
noncomputable def h2 : Submodule ℝ (H2Target (μ := μ)) :=
  (LinearMap.range (graph2 (μ := μ) (E := E))).topologicalClosure

/-- The continuous embedding `H² → L²`. -/
noncomputable def h2ToL2 : (↥(h2 (μ := μ) (E := E))) →L[ℝ] L2ℝ (μ := μ) :=
  (ContinuousLinearMap.fst ℝ (L2ℝ (μ := μ)) (L2E (μ := μ) × L2EE (μ := μ))).comp
    (Submodule.subtypeL (h2 (μ := μ) (E := E)))

/-- The continuous gradient map `H² → L²(E)`. -/
noncomputable def h2ToL2Grad : (↥(h2 (μ := μ) (E := E))) →L[ℝ] L2E (μ := μ) :=
  (ContinuousLinearMap.fst ℝ (L2E (μ := μ)) (L2EE (μ := μ))).comp
    ((ContinuousLinearMap.snd ℝ (L2ℝ (μ := μ)) (L2E (μ := μ) × L2EE (μ := μ))).comp
      (Submodule.subtypeL (h2 (μ := μ) (E := E))))

/-- The continuous Hessian map `H² → L²(E →L E)`. -/
noncomputable def h2ToL2Hess : (↥(h2 (μ := μ) (E := E))) →L[ℝ] L2EE (μ := μ) :=
  (ContinuousLinearMap.snd ℝ (L2E (μ := μ)) (L2EE (μ := μ))).comp
    ((ContinuousLinearMap.snd ℝ (L2ℝ (μ := μ)) (L2E (μ := μ) × L2EE (μ := μ))).comp
      (Submodule.subtypeL (h2 (μ := μ) (E := E))))

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
