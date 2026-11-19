/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.SchwartzModularOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The lacunary quadratic Carleson operator on the paper's full test domain

For a bounded, compactly supported measurable input, every positive symmetric
truncation is an ordinary integral.  We take the `limsup` of their norms along
the canonical cofinal sequence `epsilon_m = 1 / (m + 1)`, then the supremum
over dyadic modulations.  This gives an everywhere-defined measurable
extended-nonnegative representative without inserting an arbitrary value when
a pointwise principal value is unavailable.

Whenever the symmetric principal value exists, the `limsup` equals its norm.
In particular, the operator agrees pointwise with the distributionally defined
operator on every Schwartz function.
-/

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology

namespace QuadraticCarleson

set_option autoImplicit false

/-- The canonical decreasing positive truncation radii.-/
noncomputable def principalValueRadius (m : ℕ) : ℝ :=
  1 / ((m : ℝ) + 1)

/--
@isnad1 id=lt.0h1v.s3.d37286d505c7 from=translated src=- shape=b9369acb vocab=fd9c36a0
-/
theorem principalValueRadius_pos (m : ℕ) : 0 < principalValueRadius m := by
  unfold principalValueRadius
  positivity

/--
@isnad1 id=tendsto.0h0v.s4.7b4eb80c0b81 from=translated src=- shape=d35a1368 vocab=4852c6a1
-/
theorem tendsto_principalValueRadius :
    Tendsto principalValueRadius atTop (nhdsWithin 0 (Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?tendsto, ?mem⟩
  · change Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) + 1)) atTop (nhds 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Eventually.of_forall fun m ↦ principalValueRadius_pos m

/-- Norm of one ordinary symmetric truncation, valued in `ENNReal`.-/
noncomputable def quadraticHilbertL0TruncNorm
    (modulation : ℝ) (f : L0Infinity) (m : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ‖quadraticHilbertTrunc modulation (principalValueRadius m) f x‖

/--
@isnad1 id=measurab.0h3v.s4.69eed9a9462e from=translated src=- shape=994b5192 vocab=0cbf9dd6
-/
theorem measurable_quadraticHilbertTrunc_l0
    (modulation epsilon : ℝ) (f : L0Infinity) :
    Measurable (quadraticHilbertTrunc modulation epsilon f) := by
  have hf : Measurable (fun p : ℝ × ℝ ↦ f (p.1 - p.2)) :=
    f.measurable_toFun.comp (measurable_fst.sub measurable_snd)
  have hm : Measurable (fun p : ℝ × ℝ ↦
      f (p.1 - p.2) * phase (modulation * p.2 ^ 2) / (p.2 : ℂ)) := by
    unfold phase
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict {t : ℝ | epsilon < |t|})).measurable

/--
@isnad1 id=measurab.0h3v.s3.e0d2f6aa0e60 from=translated src=- shape=5a9be14c vocab=cb149bf5
-/
theorem measurable_quadraticHilbertL0TruncNorm
    (modulation : ℝ) (f : L0Infinity) (m : ℕ) :
    Measurable (quadraticHilbertL0TruncNorm modulation f m) := by
  exact ENNReal.continuous_ofReal.measurable.comp
    (measurable_quadraticHilbertTrunc_l0 modulation (principalValueRadius m) f).norm

/-- Canonical magnitude of the fixed-modulation principal value.  At points
where the principal value exists, this is exactly its norm.-/
noncomputable def quadraticHilbertL0Limsup
    (modulation : ℝ) (f : L0Infinity) (x : ℝ) : ℝ≥0∞ :=
  limsup (fun m : ℕ ↦ quadraticHilbertL0TruncNorm modulation f m x) atTop

/--
@isnad1 id=measurab.0h2v.s3.0c90b9e8f00e from=translated src=- shape=ded0e42c vocab=d08ad739
-/
theorem measurable_quadraticHilbertL0Limsup
    (modulation : ℝ) (f : L0Infinity) :
    Measurable (quadraticHilbertL0Limsup modulation f) := by
  exact Measurable.limsup fun m ↦
    measurable_quadraticHilbertL0TruncNorm modulation f m

/-- The lacunary quadratic Carleson operator on all of `L0Infinity`.-/
noncomputable def lacunaryQuadraticCarlesonL0
    (f : L0Infinity) (x : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℤ, quadraticHilbertL0Limsup (dyadicModulation n) f x

/--
@isnad1 id=measurab.0h1v.s3.34c7bd5a2669 from=translated src=- shape=7000f90d vocab=e70ce14e
-/
theorem measurable_lacunaryQuadraticCarlesonL0 (f : L0Infinity) :
    Measurable (lacunaryQuadraticCarlesonL0 f) := by
  exact Measurable.iSup fun n : ℤ ↦
    measurable_quadraticHilbertL0Limsup (dyadicModulation n) f

/-- The full-domain measurable operator used in the paper's modular estimate.-/
noncomputable def lacunaryL0Operator : NonnegativeOperator where
  toFun := lacunaryQuadraticCarlesonL0
  measurable_toFun := measurable_lacunaryQuadraticCarlesonL0

/-- Along the canonical cofinal truncations, every established principal
value is recovered exactly.
@isnad1 id=eq.1h4v.s4.d672038b3407 from=translated src=- shape=c43fd841 vocab=f6e6c851
-/
theorem quadraticHilbertL0Limsup_eq_of_principalValue
    (modulation : ℝ) (f : L0Infinity) (x : ℝ) (z : ℂ)
    (hz : HasQuadraticPrincipalValue modulation f x z) :
    quadraticHilbertL0Limsup modulation f x = ENNReal.ofReal ‖z‖ := by
  have hcomplex : Tendsto
      (fun m : ℕ ↦ quadraticHilbertTrunc modulation (principalValueRadius m) f x)
      atTop (nhds z) := hz.comp tendsto_principalValueRadius
  have hnorm : Tendsto
      (fun m : ℕ ↦ ‖quadraticHilbertTrunc modulation (principalValueRadius m) f x‖)
      atTop (nhds ‖z‖) := hcomplex.norm
  have hennreal : Tendsto
      (fun m : ℕ ↦ quadraticHilbertL0TruncNorm modulation f m x)
      atTop (nhds (ENNReal.ofReal ‖z‖)) := by
    exact (ENNReal.continuous_ofReal.tendsto ‖z‖).comp hnorm
  exact hennreal.limsup_eq

/--
@isnad1 id=eq.1h3v.s6.62a1afb1306d from=translated src=- shape=f83296fb vocab=a1fefc98
-/
theorem quadraticHilbertL0Limsup_compactSchwartz
    (modulation : ℝ) (f : 𝓢(ℝ, ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ)) (x : ℝ) :
    quadraticHilbertL0Limsup modulation (compactSchwartzToL0Infinity f hf) x =
      ENNReal.ofReal ‖quadraticHilbertSchwartz modulation f x‖ := by
  apply quadraticHilbertL0Limsup_eq_of_principalValue
  exact hasQuadraticPrincipalValue_schwartz modulation f x

/-- Exact pointwise agreement with the distributional Schwartz operator.
@isnad1 id=eq.1h2v.s6.ccc5030f8c14 from=translated src=- shape=40db2f4c vocab=c19802a7
-/
theorem lacunaryQuadraticCarlesonL0_compactSchwartz
    (f : 𝓢(ℝ, ℂ)) (hf : HasCompactSupport (f : ℝ → ℂ)) (x : ℝ) :
    lacunaryQuadraticCarlesonL0 (compactSchwartzToL0Infinity f hf) x =
      lacunaryQuadraticCarlesonSchwartz f x := by
  unfold lacunaryQuadraticCarlesonL0 lacunaryQuadraticCarlesonSchwartz
  congr 1
  funext n
  exact quadraticHilbertL0Limsup_compactSchwartz (dyadicModulation n) f hf x

/--
@isnad1 id=eq.1h2v.s6.7a5a184f745e from=translated src=- shape=42884082 vocab=9a6e8f59
-/
theorem lacunaryL0Operator_agrees_on_compactSchwartz
    (f : 𝓢(ℝ, ℂ)) (hf : HasCompactSupport (f : ℝ → ℂ)) (x : ℝ) :
    lacunaryL0Operator (compactSchwartzToL0Infinity f hf) x =
      lacunarySchwartzOperator f x :=
  lacunaryQuadraticCarlesonL0_compactSchwartz f hf x

end QuadraticCarleson
