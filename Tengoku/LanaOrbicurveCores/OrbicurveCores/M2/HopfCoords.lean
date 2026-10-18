/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.M2.Setup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hopf coordinates on `SL(2, ℝ)`

We parametrise (almost all of) `SL(2, ℝ)` by `(x, u, s) ∈ ℝ³` and a sign:

  `hopf (x, u, s) = [[x eˢ, (x u - 1) e⁻ˢ], [eˢ, u e⁻ˢ]]`.

The first column spans the line of `x ∈ ℙ¹(ℝ)` and the second column the line of
`y = x - 1/u`. In these coordinates

* right multiplication by `unip t = [[1, t], [0, 1]]` is the shear `u ↦ u + e²ˢ t`;
* right multiplication by `diagA σ = diag(e^σ, e^{-σ})` is the translation `s ↦ s + σ`;
* left multiplication by `γ = [[a, b], [c, d]]` is, up to sign and off the null set
  `c x + d = 0`, the map `(x, u, s) ↦ (γ x, α² u - c α, s + log |α|)` with `α = c x + d`.

All three preserve Lebesgue measure on `ℝ³`, so `hopfMeasure`, the push-forward of Lebesgue
measure under `hopf` and `-hopf`, is left-invariant and right-invariant under `A` and `N`.
(It is a Haar measure of `SL(2, ℝ)`, but we never need this.)
-/

open MeasureTheory Matrix Matrix.SpecialLinearGroup Set Filter Real
open scoped MatrixGroups ENNReal

namespace OrbicurveCores.M2

/-- The Borel structure on `SL(2, ℝ)`. -/
instance instMeasurableSpaceSL : MeasurableSpace SL(2, ℝ) := borel _

/-- The upper unipotent `n_t`. -/
noncomputable def unip (t : ℝ) : SL(2, ℝ) :=
  ⟨!![1, t; 0, 1], by rw [det_fin_two_of]; ring⟩

/-- The diagonal element `a_σ = diag(e^σ, e^{-σ})`. -/
noncomputable def diagA (σ : ℝ) : SL(2, ℝ) :=
  ⟨!![exp σ, 0; 0, exp (-σ)], by rw [det_fin_two_of, ← exp_add]; simp⟩

lemma exp_mul_exp_neg (s : ℝ) : exp s * exp (-s) = 1 := by rw [← exp_add]; simp

/-- The Hopf chart. -/
noncomputable def hopf (p : ℝ × ℝ × ℝ) : SL(2, ℝ) :=
  ⟨!![p.1 * exp p.2.2, (p.1 * p.2.1 - 1) * exp (-p.2.2); exp p.2.2, p.2.1 * exp (-p.2.2)], by
    rw [det_fin_two_of]; linear_combination exp_mul_exp_neg p.2.2⟩

/-- The shear `(x, u, s) ↦ (x, u + e²ˢ t, s)`. -/
noncomputable def hopfN (t : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.1, p.2.1 + exp (2 * p.2.2) * t, p.2.2)

/-- The translation `(x, u, s) ↦ (x, u, s + σ)`. -/
def hopfA (σ : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (p.1, p.2.1, p.2.2 + σ)

lemma exp_two_mul' (s : ℝ) : exp (2 * s) = exp s * exp s := by rw [← exp_add]; ring_nf

/-! ### The left action -/

/-- The Möbius cocycle `α = c x + d`. -/
def cocy (γ : SL(2, ℝ)) (x : ℝ) : ℝ := γ 1 0 * x + γ 1 1

/-- The Möbius map `x ↦ (a x + b) / (c x + d)` on `ℝ` (junk value at the pole). -/
noncomputable def mob (γ : SL(2, ℝ)) (x : ℝ) : ℝ := (γ 0 0 * x + γ 0 1) / cocy γ x

/-- Left multiplication in Hopf coordinates. -/
noncomputable def hopfT (γ : SL(2, ℝ)) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (mob γ p.1, cocy γ p.1 ^ 2 * p.2.1 - γ 1 0 * cocy γ p.1, p.2.2 + log |cocy γ p.1|)

/-! ### Measurability -/

@[fun_prop]
lemma measurable_hopfN (t : ℝ) : Measurable (hopfN t) := by unfold hopfN; fun_prop

@[fun_prop]
lemma measurable_hopfA (σ : ℝ) : Measurable (hopfA σ) := by unfold hopfA; fun_prop

/-! ### Measure preservation in coordinates -/

lemma measurePreserving_shear (t : ℝ) :
    MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1 + exp (2 * q.2) * t, q.2)) volume volume := by
  have h1 : MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1, q.2 + exp (2 * q.1) * t))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.skew_product (f := id) (MeasurePreserving.id volume)
      (g := fun s u ↦ u + exp (2 * s) * t) (by fun_prop)
      (Eventually.of_forall fun s ↦ map_add_right_eq_self volume _)
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).comp (h1.comp Measure.measurePreserving_swap)
  exact h2

lemma measurePreserving_hopfN (t : ℝ) : MeasurePreserving (hopfN t) volume volume :=
  MeasurePreserving.skew_product (f := id) (MeasurePreserving.id volume)
    (g := fun (_ : ℝ) (q : ℝ × ℝ) ↦ (q.1 + exp (2 * q.2) * t, q.2)) (by fun_prop)
    (Eventually.of_forall fun _ ↦ (measurePreserving_shear t).map_eq)

lemma measurePreserving_hopfA (σ : ℝ) : MeasurePreserving (hopfA σ) volume volume :=
  (MeasurePreserving.id volume).prod
    ((MeasurePreserving.id volume).prod (measurePreserving_add_right volume σ))

/-- A nonzero affine function has at most one zero. -/
lemma subsingleton_affine {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) :
    {x : ℝ | c * x + d = 0}.Subsingleton := by
  intro x hx y hy
  simp only [Set.mem_ofPred_eq] at hx hy
  by_cases hc : c = 0
  · simp only [hc, zero_mul, zero_add] at hx
    exact absurd hx (h.resolve_left (not_not.mpr hc))
  · exact mul_left_cancel₀ hc (by linarith)

/-- Affine change of variables on `ℝ`. -/
lemma lintegral_comp_mul_add {a : ℝ} (ha : a ≠ 0) (b : ℝ) (J : ℝ → ℝ≥0∞) :
    ∫⁻ u, J (a * u + b) = ENNReal.ofReal |a⁻¹| * ∫⁻ u, J u := by
  set e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv
  have he : Measure.map e volume = ENNReal.ofReal |a⁻¹| • volume :=
    Real.map_volume_mul_left ha
  have h1 := lintegral_map_equiv (μ := volume) (fun v ↦ J (v + b)) e
  rw [he, lintegral_smul_measure, lintegral_add_right_eq_self, smul_eq_mul] at h1
  exact h1.symm

/-! ### The measure on `SL(2, ℝ)` -/

/-- The push-forward of Lebesgue measure under `± hopf` (a Haar measure on `SL(2, ℝ)`). -/
noncomputable def hopfMeasure : Measure SL(2, ℝ) :=
  volume.map hopf + volume.map fun p ↦ -hopf p

end OrbicurveCores.M2
