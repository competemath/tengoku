/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.PiecewiseContourIntegral
import Tengoku

/-!
# Cauchy Principal Value Integrals along Piecewise C¹ Paths

This file defines the Cauchy principal value (CPV) of a contour integral along a
piecewise C¹ path, both for a single singularity and for a finite set of singularities.

## Main definitions

### Single-point CPV

* `cpvIntegrand f γ z₀ ε t` — the ε-cutoff integrand: equals `f(γ(t)) · γ'(t)` when
  `‖γ(t) - z₀‖ > ε`, and `0` otherwise.

* `HasCauchyPV f γ z₀ L` — the **primary API predicate**: the limit of the cutoff integral
  as `ε → 0⁺` exists and equals `L`. Defined via `Tendsto`.

* `cauchyPV f γ z₀` — the CPV value, defined via `limUnder`. Returns junk when the limit
  does not exist.

* `HasCauchyPV.cauchyPV_eq` — bridge: `HasCauchyPV f γ z₀ L → cauchyPV f γ z₀ = L`.

### Multi-point CPV

* `cpvIntegrandOn S f γ ε t` — zero near any `s ∈ S`, otherwise `f(γ(t)) · γ'(t)`.

* `HasCauchyPVOn S f γ L` — multi-point Tendsto predicate.

* `cauchyPVOn S f γ` — multi-point CPV value via `limUnder`.

* `HasCauchyPVOn.cauchyPVOn_eq` — bridge for the multi-point case.

### Basic API

* `HasCauchyPV.neg` — `HasCauchyPV f γ z₀ L → HasCauchyPV (-f) γ z₀ (-L)`
* `HasCauchyPV.smul` — scalar multiplication
* `hasCauchyPV_of_avoids` — if `γ` avoids `z₀`, CPV equals the ordinary contour integral

## Design notes

The `HasCauchyPV` predicate (Tendsto-based) is the **primary API**. All downstream
theorems should be stated using it. The `cauchyPV` value (limUnder-based) is secondary —
only used when extracting a concrete value is needed.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology MeasureTheory Complex
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-- The ε-cutoff integrand for the Cauchy principal value at a single point `z₀`.
Returns `f(γ(t)) · γ'(t)` when `‖γ(t) - z₀‖ > ε`, and `0` otherwise. -/
def cpvIntegrand (f : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

/--
@isnad1 id=eq.1h5v.s6.a2a2da78e14f from=translated src=- shape=c0cd3bac vocab=6f868bf5
-/
@[simp]
theorem cpvIntegrand_of_gt {f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {ε : ℝ} {t : ℝ}
    (h : ε < ‖γ t - z₀‖) :
    cpvIntegrand f γ z₀ ε t = f (γ t) * deriv γ t :=
  ite_eq_left h

/-- The Cauchy principal value of `∮_γ f(z) dz` exists and equals `L`, where the integral
is computed by excluding ε-neighborhoods of `z₀` and taking the limit as `ε → 0⁺`.

This is the **primary API predicate** for CPV integrals. -/
def HasCauchyPV (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (z₀ : ℂ) (L : ℂ) : Prop :=
  Tendsto (fun ε => ∫ t in (0 : ℝ)..1, cpvIntegrand f γ.toPath.extend z₀ ε t)
    (𝓝[>] 0) (𝓝 L)

/-- The Cauchy principal value of `∮_γ f(z) dz`, excluding ε-neighborhoods of `z₀`.
Returns junk when the limit does not exist. -/
def cauchyPV (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    ∫ t in (0 : ℝ)..1, cpvIntegrand f γ.toPath.extend z₀ ε t

/-- Bridge theorem: if `HasCauchyPV f γ z₀ L`, then `cauchyPV f γ z₀ = L`.
@isnad1 id=eq.1h6v.s5.ac673838c9a2 from=translated src=- shape=4b1f0969 vocab=1600cef1
-/
theorem HasCauchyPV.cauchyPV_eq {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV f γ z₀ L) : cauchyPV f γ z₀ = L :=
  h.limUnder_eq

/-- Scalar multiplication: `HasCauchyPV f γ z₀ L → HasCauchyPV (c • f) γ z₀ (c * L)`.
@isnad1 id=hascauch.1h7v.s5.a7e3717f260b from=translated src=- shape=f428820a vocab=836d924f
-/
theorem HasCauchyPV.smul {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ : ℂ} {L : ℂ}
    (c : ℂ) (h : HasCauchyPV f γ z₀ L) :
    HasCauchyPV (fun z => c * f z) γ z₀ (c * L) := by
  simp only [HasCauchyPV] at h ⊢
  refine (h.const_mul c).congr fun ε => ?_
  refine (intervalIntegral.integral_const_mul c _).symm.trans
    (intervalIntegral.integral_congr fun t _ => ?_)
  simp only [cpvIntegrand]
  split_ifs <;> ring

/-- If `γ` avoids `z₀` (minimum distance `δ > 0`), then the CPV equals the ordinary
contour integral, since the cutoff integrand equals the full integrand for small `ε`.
@isnad1 id=hascauch.1h5v.s6.b206eb0ce46d from=translated src=- shape=0378c657 vocab=aa88358c
-/
theorem hasCauchyPV_of_avoids {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ : ℂ}
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - z₀‖) :
    HasCauchyPV f γ z₀ (γ.contourIntegral f) := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hδ
  simp only [HasCauchyPV, PiecewiseC1Path.contourIntegral]
  refine tendsto_const_nhds.congr' <| (Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨Ioo 0 δ, Ioo_mem_nhdsGT hδ_pos, fun ε hε => ?_⟩)
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  exact (cpvIntegrand_of_gt (hε.2.trans_le (hδ_bound t ht))).symm

/-- Multi-point CPV integrand: zero near any `s ∈ S`, else `f(γ(t)) · γ'(t)`. -/
def cpvIntegrandOn (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0
  else f (γ t) * deriv γ t

/--
@isnad1 id=eq.1h5v.s6.9e5d73247775 from=translated src=- shape=8e33d239 vocab=57a1a414
-/
@[simp]
theorem cpvIntegrandOn_of_forall_gt {S : Finset ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ} {ε : ℝ} {t : ℝ}
    (h : ∀ s ∈ S, ε < ‖γ t - s‖) :
    cpvIntegrandOn S f γ ε t = f (γ t) * deriv γ t :=
  ite_eq_right fun ⟨s, hs, hle⟩ => (h s hs).not_ge hle

/--
@isnad1 id=eq.1h5v.s6.a593aadd5d30 from=translated src=- shape=f873189e vocab=6e46bd81
-/
@[simp]
theorem cpvIntegrandOn_of_exists_le {S : Finset ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ} {ε : ℝ} {t : ℝ}
    (h : ∃ s ∈ S, ‖γ t - s‖ ≤ ε) :
    cpvIntegrandOn S f γ ε t = 0 :=
  ite_eq_left h

/-- Single-point CPV integrand agrees with multi-point CPV integrand for a singleton.
@isnad1 id=eq.0h5v.s5.5514930144f1 from=translated src=- shape=729dff23 vocab=d4a27c3f
-/
theorem cpvIntegrand_eq_cpvIntegrandOn_singleton {f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ}
    {ε : ℝ} {t : ℝ} :
    cpvIntegrand f γ z₀ ε t = cpvIntegrandOn {z₀} f γ ε t := by
  simp only [cpvIntegrand, cpvIntegrandOn, Finset.mem_singleton, exists_eq_left]
  split_ifs with h1 h2 <;> first | rfl | linarith

/-- The multi-point Cauchy principal value of `∮_γ f(z) dz` exists and equals `L`,
where the integral is computed by excluding ε-neighborhoods of all points in `S`
and taking the limit as `ε → 0⁺`. -/
def HasCauchyPVOn (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (L : ℂ) : Prop :=
  Tendsto (fun ε => ∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t)
    (𝓝[>] 0) (𝓝 L)

/-- If `γ` avoids all points in `S`, the multi-point CPV equals the ordinary
contour integral.
@isnad1 id=hascauch.1h5v.s6.e7a1875e7a9f from=translated src=- shape=681354bc vocab=40d2d924
-/
theorem hasCauchyPVOn_of_avoids {S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x y}
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖) :
    HasCauchyPVOn S f γ (γ.contourIntegral f) := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hδ
  simp only [HasCauchyPVOn, PiecewiseC1Path.contourIntegral]
  refine tendsto_const_nhds.congr' <| (Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨Ioo 0 δ, Ioo_mem_nhdsGT hδ_pos, fun ε hε => ?_⟩)
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  exact (cpvIntegrandOn_of_forall_gt fun s hs => hε.2.trans_le (hδ_bound s hs t ht)).symm

/-- The limit in `HasCauchyPV` is unique.
@isnad1 id=eq.2h7v.s5.7092bb5d5f65 from=translated src=- shape=54a3549a vocab=6c47fac3
-/
theorem HasCauchyPV.unique {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ : ℂ}
    {L₁ L₂ : ℂ} (h₁ : HasCauchyPV f γ z₀ L₁) (h₂ : HasCauchyPV f γ z₀ L₂) :
    L₁ = L₂ :=
  tendsto_nhds_unique h₁ h₂

end
