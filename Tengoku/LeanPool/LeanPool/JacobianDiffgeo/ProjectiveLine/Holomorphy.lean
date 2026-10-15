/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.ProjectiveLine.Charts
public import Tengoku
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Bridges

/-!
# Holomorphy transfer kit for `ℙ¹` (CC5)

Unit: projective-line (`docs/design/projective-line.md` §3.3). For a Riemann surface
`Z` (`ChartedSpace ℂ Z` + `IsManifold 𝓘(ℂ) ω Z`, no compactness/connectedness needed
anywhere) this file converts holomorphy of maps `Z → OnePoint ℂ` into planar
`AnalyticAt`/`MeromorphicAt` statements read in `coeChart`/`invChart`:

* `contMDiff_coe`: the coercion `ℂ → ℙ¹` is holomorphic;
* `ContMDiffAt.onePointCoe`/`ContMDiff.onePointCoe`: the "no poles" lift constructor;
* `contMDiffAt_iff_analyticAt_of_ne_infty`/`_of_eq_infty`: chart-iff lemmas at a finite value
  resp. at `∞`;
* `contMDiffAt_of_pole`: the **pole constructor** (planar; pre-`ℳ X` layer) — a function
  agreeing near `z₀` with a meromorphic `g` having a genuine pole, sent to `∞` at `z₀`, is
  holomorphic into `ℙ¹`;
* `meromorphicAt_coeChart_comp`: the converse atom — a holomorphic map into `ℙ¹` is
  chart-locally meromorphic;
* `contMDiff_inversion`/`inversionDiffeomorph`: inversion is a biholomorphic involution.
-/

@[expose] public section

open scoped ContDiff Manifold OnePoint
open Set Filter Topology OnePoint

namespace RS.P1

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

/-- The coercion `ℂ → ℙ¹` is holomorphic.
@isnad1 id=contmdif.0h0v.s6.31b5ad73a295 from=translated src=- shape=307391ff vocab=2f64f99f
-/
theorem contMDiff_coe : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℂ → OnePoint ℂ) := by
  intro z
  rw [RS.contMDiffAt_iff_analyticAt_writtenInExtChartAt]
  refine ⟨continuous_coe.continuousAt, ?_⟩
  have hchart : chartAt ℂ ((z : ℂ) : OnePoint ℂ) = coeChart := chartAt_coe z
  have hfun : writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) z ((↑) : ℂ → OnePoint ℂ) = id := by
    funext w
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
      Function.comp_id, Function.id_comp, id_eq, chartAt_self_eq, hchart]
    exact coeChart_apply_coe _
  rw [hfun]
  exact analyticAt_id

omit [IsManifold 𝓘(ℂ, ℂ) ω Z] in
/-- Holomorphic lift of a holomorphic function (the "no poles" constructor).
@isnad1 id=contmdif.1h3v.s7.b4d5bb4b2923 from=translated src=- shape=4ec76fb2 vocab=99a90758
-/
theorem ContMDiffAt.onePointCoe {g : Z → ℂ} {x : Z} (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g x) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun z => ((g z : ℂ) : OnePoint ℂ)) x :=
  (contMDiff_coe (g x)).comp x hg

omit [IsManifold 𝓘(ℂ, ℂ) ω Z] in
/--
@isnad1 id=contmdif.1h2v.s7.9a51345ff419 from=translated src=- shape=2c2f6ca6 vocab=5d27feb3
-/
theorem ContMDiff.onePointCoe {g : Z → ℂ} (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => ((g z : ℂ) : OnePoint ℂ)) :=
  fun x => ContMDiffAt.onePointCoe (hg x)

omit [IsManifold 𝓘(ℂ, ℂ) ω Z] in
/-- Holomorphy at a finite value, read in the `coeChart`.
@isnad1 id=iff.1h3v.s8.eb5acc441cc8 from=translated src=- shape=061dfd1c vocab=15453b80
-/
theorem contMDiffAt_iff_analyticAt_of_ne_infty {f : Z → OnePoint ℂ} {x : Z}
    (h : f x ≠ (∞ : OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔ ContinuousAt f x ∧
      AnalyticAt ℂ (⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
  obtain ⟨w, hw⟩ := ne_infty_iff_exists.mp h
  have hchart : chartAt ℂ (f x) = coeChart := by rw [← hw]; exact chartAt_coe w
  have hpt : extChartAt 𝓘(ℂ) x x = chartAt ℂ x x := by rw [extChartAt_coe]; simp
  rw [RS.contMDiffAt_iff_analyticAt_writtenInExtChartAt]
  have hfun : writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f = ⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm := by
    funext y
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
      Function.comp_id, Function.id_comp, hchart]
  rw [hfun, hpt]

omit [IsManifold 𝓘(ℂ, ℂ) ω Z] in
/-- Holomorphy at `∞`, read in the `invChart` ("`1/f` is analytic").
@isnad1 id=iff.1h3v.s8.fbac9a07b243 from=translated src=- shape=061dfd1c vocab=10cdca11
-/
theorem contMDiffAt_iff_analyticAt_of_eq_infty {f : Z → OnePoint ℂ} {x : Z}
    (h : f x = (∞ : OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔ ContinuousAt f x ∧
      AnalyticAt ℂ (⇑invChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
  have hchart : chartAt ℂ (f x) = invChart := by rw [h]; exact chartAt_infty
  have hpt : extChartAt 𝓘(ℂ) x x = chartAt ℂ x x := by rw [extChartAt_coe]; simp
  rw [RS.contMDiffAt_iff_analyticAt_writtenInExtChartAt]
  have hfun : writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f = ⇑invChart ∘ f ∘ ⇑(chartAt ℂ x).symm := by
    funext y
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
      Function.comp_id, Function.id_comp, hchart]
  rw [hfun, hpt]

/-- `(↑)` sends `cobounded ℂ` to `𝓝 ∞`.
@isnad1 id=tendsto.0h0v.s5.48df8952d8c6 from=translated src=- shape=c122176e vocab=100d1a23
-/
theorem tendsto_coe_cobounded :
    Tendsto ((↑) : ℂ → OnePoint ℂ) (Bornology.cobounded ℂ) (𝓝 (∞ : OnePoint ℂ)) := by
  rw [Metric.cobounded_eq_cocompact]
  exact tendsto_coe_cocompact

omit [IsManifold 𝓘(ℂ, ℂ) ω Z] in
/-- Converse atom: a holomorphic map to `ℙ¹` is chart-locally meromorphic (CC3's currency).
@isnad1 id=meromorp.1h3v.s8.fc135c413681 from=translated src=- shape=f3233a4b vocab=fe983830
-/
theorem meromorphicAt_coeChart_comp {f : Z → OnePoint ℂ} {x : Z}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    MeromorphicAt (⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
  have hGψ : (⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm : ℂ → ℂ) =
      (⇑invChart ∘ f ∘ ⇑(chartAt ℂ x).symm)⁻¹ := by
    funext y
    change coeChart (f ((chartAt ℂ x).symm y)) = (invChart (f ((chartAt ℂ x).symm y)))⁻¹
    induction (f ((chartAt ℂ x).symm y)) using OnePoint.rec with
    | infty => simp
    | coe w => simp
  by_cases hfx : f x = (∞ : OnePoint ℂ)
  · have hψan : AnalyticAt ℂ (⇑invChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      ((contMDiffAt_iff_analyticAt_of_eq_infty hfx).1 hf).2
    rw [hGψ]
    exact hψan.meromorphicAt.inv
  · have hGan : AnalyticAt ℂ (⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      ((contMDiffAt_iff_analyticAt_of_ne_infty hfx).1 hf).2
    exact hGan.meromorphicAt

/-- The inversion is holomorphic, hence a biholomorphic involution of `ℙ¹`.
@isnad1 id=contmdif.0h0v.s6.74e1567c4e8d from=translated src=- shape=68cd23f6 vocab=198e13f1
-/
theorem contMDiff_inversion : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω inversion := by
  intro p
  induction p using OnePoint.rec with
  | infty =>
    have hval : inversion (∞ : OnePoint ℂ) ≠ (∞ : OnePoint ℂ) := by simp
    rw [contMDiffAt_iff_analyticAt_of_ne_infty hval, chartAt_infty]
    refine ⟨continuous_inversion.continuousAt, ?_⟩
    have hfun : (⇑coeChart ∘ inversion ∘ ⇑invChart.symm : ℂ → ℂ) = id := by
      funext w
      change coeChart (inversion (invChart.symm w)) = w
      rw [invChart_symm_apply, inversion_involutive]
      exact coeChart_apply_coe w
    rw [hfun]
    exact analyticAt_id
  | coe z =>
    by_cases hz : z = 0
    · subst hz
      have hval : inversion ((0 : ℂ) : OnePoint ℂ) = (∞ : OnePoint ℂ) := by simp
      rw [contMDiffAt_iff_analyticAt_of_eq_infty hval, chartAt_coe]
      refine ⟨continuous_inversion.continuousAt, ?_⟩
      have hfun : (⇑invChart ∘ inversion ∘ ⇑coeChart.symm : ℂ → ℂ) = id := by
        funext w
        change invChart (inversion (coeChart.symm w)) = w
        rw [coeChart_symm_apply]
        exact invChart_inversion_coe w
      rw [hfun]
      exact analyticAt_id
    · have hval : inversion ((z : ℂ) : OnePoint ℂ) ≠ (∞ : OnePoint ℂ) := by simp [inversion_coe hz]
      rw [contMDiffAt_iff_analyticAt_of_ne_infty hval, chartAt_coe]
      refine ⟨continuous_inversion.continuousAt, ?_⟩
      have hfun : (⇑coeChart ∘ inversion ∘ ⇑coeChart.symm : ℂ → ℂ) = Inv.inv := by
        funext w
        change coeChart (inversion (coeChart.symm w)) = w⁻¹
        rw [coeChart_symm_apply]
        exact coeChart_inversion_coe w
      rw [hfun]
      exact analyticAt_inv hz

/-- Inversion as a self-inverse holomorphic involution of `ℙ¹`. -/
noncomputable def inversionDiffeomorph : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (OnePoint ℂ) (OnePoint ℂ) ω where
  toFun := inversion
  invFun := inversion
  left_inv := inversion_involutive
  right_inv := inversion_involutive
  contMDiff_toFun := contMDiff_inversion
  contMDiff_invFun := contMDiff_inversion

/--
@isnad1 id=eq.0h0v.s8.3488a23d6c29 from=translated src=- shape=b6641a5d vocab=8d1a7cd1
-/
@[simp] theorem inversionDiffeomorph_apply : ⇑inversionDiffeomorph = inversion := rfl

end RS.P1
