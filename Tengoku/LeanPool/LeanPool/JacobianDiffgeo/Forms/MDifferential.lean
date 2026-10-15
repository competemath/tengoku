/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Forms.Analyticity
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Bridges
public import Tengoku

/-!
# The differential of a holomorphic function (CC1, design §2.4)

Unit: holomorphic-forms (`docs/design/holomorphic-forms.md`). `RS.mdifferential f hf` is the
holomorphic 1-form `df` of a holomorphic function `f : X → ℂ`; in every maximal-atlas chart its
coefficient is the planar derivative of the chart composite
(`RS.coeffIn_mdifferential : coeffIn e (df) = deriv (f ∘ e.symm)` on `e.target`).

Also provides `RS.Form1.smulFun` (multiplication of a form by a holomorphic function, used by
canonical-forms) with its coefficient formula.

Holomorphic 1-forms only — no meromorphic machinery here (meromorphic 1-forms are later
`f • η` pairs in canonical-forms/meromorphic-trace).
-/

@[expose] public section

open scoped ContDiff Manifold Bundle
open Set IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The underlying covector section of the differential: `x ↦ d f_x`, crossing the
`TangentSpace ↦ Bundle.Trivial` defeq in the codomain. -/
def mdifferentialSection (f : X → ℂ) (x : X) :
    TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x :=
  (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x : TangentSpace 𝓘(ℂ) x →L[ℂ] TangentSpace 𝓘(ℂ) (f x))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The raw chart coefficient of the differential section is the derivative of the chart
composite.
@isnad1 id=eq.3h4v.s8.c4263586dfad from=translated src=- shape=e84bd9f4 vocab=079bc9d6
-/
theorem coeffInFun_mdifferentialSection {f : X → ℂ} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) {z : ℂ} (hz : z ∈ e.target)
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (e.symm z)) :
    coeffInFun e (mdifferentialSection f) z = deriv (f ∘ ⇑e.symm) z := by
  have hesymm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) z :=
    (contMDiffAt_symm_of_mem_maximalAtlas he hz).mdifferentiableAt (by simp)
  calc coeffInFun e (mdifferentialSection f) z
      = tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) f (e.symm z)
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) z (1 : ℂ))) := rfl
    _ = deriv (f ∘ ⇑e.symm) z := tangentCoord_mfderiv_comp hf hesymm

/-- The differential of a holomorphic function, as a holomorphic 1-form. -/
def mdifferential (f : X → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : Form1 X :=
  Form1.ofSectionAnalytic (mdifferentialSection f) (fun x => by
    have hb : AnalyticAt ℂ (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      contMDiffAt_iff_analyticAt_comp_chartAt.mp (hf x)
    have heq : coeffInFun (chartAt ℂ x) (mdifferentialSection f) =ᶠ[nhds (chartAt ℂ x x)]
        deriv (f ∘ ⇑(chartAt ℂ x).symm) := by
      filter_upwards [(chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with z hz
      exact coeffInFun_mdifferentialSection (chart_mem_maximalAtlas x) hz
        ((hf _).mdifferentiableAt (by simp))
    exact hb.deriv.congr heq.symm)

/-- Chart-coefficient formula for the differential: `coeffIn e (df) = deriv (f ∘ e.symm)` on
`e.target` (CC1's `d`-rule).
@isnad1 id=eqon.2h3v.s8.361c86a80c91 from=translated src=- shape=a467c592 vocab=1e0dbce4
-/
theorem coeffIn_mdifferential {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) {f : X → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Set.EqOn (coeffIn e (mdifferential f hf)) (deriv (f ∘ ⇑e.symm)) e.target :=
  fun _z hz => coeffInFun_mdifferentialSection he hz ((hf _).mdifferentiableAt (by simp))

/-- Preferred-chart coefficient of the differential.
@isnad1 id=eq.1h3v.s8.1cb8138e24c4 from=translated src=- shape=0350bde8 vocab=34496daa
-/
theorem coeffAt_mdifferential (f : X → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x : X) :
    coeffAt x (mdifferential f hf) = deriv (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
  coeffIn_mdifferential (chart_mem_maximalAtlas x) hf (mem_chart_target ℂ x)

/-! ### `ℂ`-linearity of the differential

The smoothness proofs of the combined functions are taken as hypotheses (no smooth-algebra
instances needed; the value of `mdifferential` does not depend on the proof argument). -/

/--
@isnad1 id=eq.3h3v.s11.dab38158e608 from=translated src=- shape=8512b970 vocab=867f529d
-/
@[simp]
theorem mdifferential_add {f g : X → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (hfg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (f + g)) :
    mdifferential (f + g) hfg = mdifferential f hf + mdifferential g hg := by
  refine Form1.ext_coeffAt fun x => ?_
  have hdf : DifferentiableAt ℂ (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (contMDiffAt_iff_analyticAt_comp_chartAt.mp (hf x)).differentiableAt
  have hdg : DifferentiableAt ℂ (g ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (contMDiffAt_iff_analyticAt_comp_chartAt.mp (hg x)).differentiableAt
  have hcomp : (f + g) ∘ ⇑(chartAt ℂ x).symm =
      (f ∘ ⇑(chartAt ℂ x).symm) + (g ∘ ⇑(chartAt ℂ x).symm) := rfl
  rw [coeffAt_add, coeffAt_mdifferential, coeffAt_mdifferential, coeffAt_mdifferential,
    hcomp, deriv_add hdf hdg]

/--
@isnad1 id=eq.2h3v.s11.e8809b301bbb from=translated src=- shape=45be9626 vocab=16f71afc
-/
@[simp]
theorem mdifferential_smul (c : ℂ) {f : X → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hcf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (c • f)) :
    mdifferential (c • f) hcf = c • mdifferential f hf := by
  refine Form1.ext_coeffAt fun x => ?_
  have hdf : DifferentiableAt ℂ (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (contMDiffAt_iff_analyticAt_comp_chartAt.mp (hf x)).differentiableAt
  have hcomp : (c • f) ∘ ⇑(chartAt ℂ x).symm = c • (f ∘ ⇑(chartAt ℂ x).symm) := rfl
  rw [coeffAt_smul, coeffAt_mdifferential, coeffAt_mdifferential, hcomp,
    deriv_const_smul c hdf, smul_eq_mul]

/--
@isnad1 id=eq.0h2v.s11.e575837a8312 from=translated src=- shape=a4beac71 vocab=8093ccdf
-/
@[simp]
theorem mdifferential_const (c : ℂ) :
    mdifferential (fun _ : X => c) contMDiff_const = 0 := by
  refine Form1.ext_coeffAt fun x => ?_
  rw [coeffAt_mdifferential, coeffAt_zero]
  have hcomp : (fun _ : X => c) ∘ ⇑(chartAt ℂ x).symm = fun _ => c := rfl
  rw [hcomp, deriv_const]

/-! ### Multiplication of a form by a holomorphic function -/

end RS

end
