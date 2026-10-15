/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku

/-!
# Inversion on the Riemann sphere (CC5)

Unit: projective-line (`docs/design/projective-line.md` §3.1). `ℙ¹ := OnePoint ℂ`.

This file defines `inversion : OnePoint ℂ → OnePoint ℂ`, the map `z ↦ z⁻¹` extended by
`∞ ↦ 0` and `0 ↦ ∞`, proves it is a continuous involution, and packages it as a
self-inverse homeomorphism `inversionHomeomorph`. The continuity proof is the `𝓝 ∞`
filter work referenced by the design's task brief ("verify `OnePoint.nhds_infty_eq`").

Main declarations: `inversion`, `inversion_involutive`, `inversion_eq_infty_iff`,
`tendsto_coe_cocompact`, `tendsto_coe_inv_nhdsNE_zero`, `continuous_inversion`,
`inversionHomeomorph`.
-/

@[expose] public section

open scoped OnePoint
open Set Filter Topology OnePoint

namespace RS.P1

/-- Inversion `z ↦ z⁻¹` on the Riemann sphere, with `∞ ↦ 0` and `0 ↦ ∞`. -/
noncomputable def inversion : OnePoint ℂ → OnePoint ℂ :=
  fun p => p.elim ((0 : ℂ) : OnePoint ℂ)
    fun z => if z = 0 then (∞ : OnePoint ℂ) else ((z⁻¹ : ℂ) : OnePoint ℂ)

/--
@isnad1 id=eq.0h0v.s3.a4df93df6375 from=translated src=- shape=aa6b87f7 vocab=23196720
-/
@[simp] theorem inversion_infty : inversion ∞ = ((0 : ℂ) : OnePoint ℂ) := rfl

/--
@isnad1 id=eq.0h0v.s3.ab388436cd5d from=translated src=- shape=e639d8aa vocab=23196720
-/
@[simp] theorem inversion_coe_zero : inversion ((0 : ℂ) : OnePoint ℂ) = ∞ := by
  simp [inversion]

/--
@isnad1 id=eq.1h1v.s4.863887ff714b from=translated src=- shape=5d40eec3 vocab=e968540a
-/
theorem inversion_coe {z : ℂ} (hz : z ≠ 0) :
    inversion (z : OnePoint ℂ) = ((z⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [inversion, hz]

/--
@isnad1 id=involuti.0h0v.s2.1bdf757dcfbf from=translated src=- shape=545db28e vocab=5883050b
-/
theorem inversion_involutive : Function.Involutive inversion := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp
    · rw [inversion_coe hz, inversion_coe (inv_ne_zero hz), inv_inv]

/--
@isnad1 id=eq.0h1v.s3.ebe84ed0a20c from=translated src=- shape=e9e6e124 vocab=8e1c0fea
-/
@[simp] theorem inversion_inversion (p : OnePoint ℂ) : inversion (inversion p) = p :=
  inversion_involutive p

/--
@isnad1 id=iff.0h1v.s4.0a05ac48edc7 from=translated src=- shape=78aae03f vocab=23196720
-/
theorem inversion_eq_infty_iff {p : OnePoint ℂ} :
    inversion p = ∞ ↔ p = ((0 : ℂ) : OnePoint ℂ) := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp
    · simp [inversion_coe hz, hz]

/-- `(↑)` sends `cocompact ℂ` to `𝓝 ∞` (mathlib's `tendsto_coe_infty` re-based off
`coclosedCompact` for downstream convenience).
@isnad1 id=tendsto.0h0v.s5.d1b2723d1ef8 from=translated src=- shape=c122176e vocab=6f3f8fe2
-/
theorem tendsto_coe_cocompact :
    Tendsto ((↑) : ℂ → OnePoint ℂ) (Filter.cocompact ℂ) (𝓝 (∞ : OnePoint ℂ)) := by
  rw [← Filter.coclosedCompact_eq_cocompact]
  exact tendsto_coe_infty

/-- The `𝓝 ∞` filter work, packaged: `z ↦ ↑(z⁻¹)` blows up at `0`.
@isnad1 id=tendsto.0h0v.s6.bb7a76d429ae from=translated src=- shape=02836ec9 vocab=0e9a6228
-/
theorem tendsto_coe_inv_nhdsNE_zero :
    Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] (0 : ℂ)) (𝓝 (∞ : OnePoint ℂ)) := by
  have h2 : Tendsto ((↑) : ℂ → OnePoint ℂ) (Bornology.cobounded ℂ) (𝓝 ∞) := by
    rw [Metric.cobounded_eq_cocompact]
    exact tendsto_coe_cocompact
  exact h2.comp Filter.tendsto_inv₀_nhdsNE_zero

/--
@isnad1 id=continuo.0h0v.s5.ba7f17039418 from=translated src=- shape=3ec79756 vocab=c669ec22
-/
theorem continuous_inversion : Continuous inversion := by
  rw [continuous_iff_continuousAt]
  intro p
  induction p using OnePoint.rec with
  | infty =>
    rw [continuousAt_infty']
    simp only [inversion_infty]
    rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    have hmem : ({(0 : ℂ)}ᶜ : Set ℂ) ∈ Bornology.cobounded ℂ :=
      Bornology.isBounded_def.mp Bornology.isBounded_singleton
    have heq : (inversion ∘ ((↑) : ℂ → OnePoint ℂ)) =ᶠ[Bornology.cobounded ℂ]
        (((↑) : ℂ → OnePoint ℂ) ∘ Inv.inv) := by
      filter_upwards [hmem] with z hz
      have hz' : z ≠ 0 := hz
      simp only [Function.comp_apply]
      exact inversion_coe hz'
    exact (tendsto_congr' heq).2
      ((continuous_coe.tendsto (0 : ℂ)).comp Filter.tendsto_inv₀_cobounded)
  | coe z =>
    rw [continuousAt_coe]
    by_cases hz : z = 0
    · subst hz
      have hval : (inversion ∘ ((↑) : ℂ → OnePoint ℂ)) (0 : ℂ) = ∞ := by
        simp [Function.comp_apply]
      rw [ContinuousAt, hval, ← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
      refine ⟨?_, ?_⟩
      · have heq : (inversion ∘ ((↑) : ℂ → OnePoint ℂ)) =ᶠ[𝓝[≠] (0 : ℂ)]
            (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) := by
          filter_upwards [self_mem_nhdsWithin] with w hw
          have hw' : w ≠ 0 := hw
          simp only [Function.comp_apply]
          exact inversion_coe hw'
        exact (tendsto_congr' heq).2 tendsto_coe_inv_nhdsNE_zero
      · simpa [hval] using
          tendsto_pure_nhds (inversion ∘ ((↑) : ℂ → OnePoint ℂ)) (0 : ℂ)
    · have heq : (((↑) : ℂ → OnePoint ℂ) ∘ Inv.inv) =ᶠ[𝓝 z] (inversion ∘ ((↑) : ℂ → OnePoint ℂ)) :=
        by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        simp only [Function.comp_apply]
        exact (inversion_coe hw).symm
      exact (continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)).congr heq

/-- Inversion as a self-inverse homeomorphism of the Riemann sphere. -/
noncomputable def inversionHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := inversion
  invFun := inversion
  left_inv := inversion_involutive
  right_inv := inversion_involutive
  continuous_toFun := continuous_inversion
  continuous_invFun := continuous_inversion

/--
@isnad1 id=eq.0h0v.s6.ec66d6a592bc from=translated src=- shape=5766a950 vocab=54220676
-/
@[simp] theorem inversionHomeomorph_apply : ⇑inversionHomeomorph = inversion := rfl

/--
@isnad1 id=eq.0h0v.s6.387d1fa3068c from=translated src=- shape=7b2863dd vocab=d9ea5893
-/
@[simp] theorem inversionHomeomorph_symm : inversionHomeomorph.symm = inversionHomeomorph := rfl

end RS.P1
