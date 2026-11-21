import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Birkhoff's theorem in the areal-radius static spherically symmetric gauge (uniqueness half)

Work in the static, spherically symmetric chart written with an areal radial coordinate,

`ds² = −f(r) dt² + f(r)⁻¹ dr² + r² dΩ²`.

For this metric the `θθ` component of the Ricci tensor is

`R_θθ = 1 − f(r) − r f′(r)`

(this is established elsewhere in `GRLab`; nothing here depends on it beyond motivation).
Consequently the single vacuum equation `R_θθ = 0` is the first-order linear ODE

`r f′(r) + f(r) − 1 = 0`,  equivalently  `d/dr [ r f(r) − r ] = 0`.

So `r ↦ r f(r) − r` is constant, i.e. `f(r) = 1 + C/r`, and writing `C = −2M` gives exactly
the Schwarzschild lapse `f(r) = 1 − 2M/r`.

This file formalises precisely that ODE step, as one-variable real calculus:

* `GRLab.areal_invariant_const` — the conserved quantity `r f(r) − r`;
* `GRLab.exists_mass_of_areal_vacuum` — on an interval avoiding `r = 0`, every solution is a
  member of the Schwarzschild family;
* `GRLab.areal_vacuum_of_mass` — the converse, that each Schwarzschild lapse solves `R_θθ = 0`.

## Scope

This is the **uniqueness direction of Birkhoff's theorem restricted to the areal-radius static
spherically symmetric gauge**, and *not* the full theorem. In particular staticity is assumed
here, whereas the genuine Birkhoff theorem *derives* it: there one starts from a general
spherically symmetric (possibly time-dependent) metric and the vacuum equations force both the
existence of a timelike Killing vector and the Schwarzschild form. The chart assumptions
(areal radius, and a lapse/inverse-radial-metric pair that are reciprocal) are likewise taken
as given rather than derived. What is proved below is the calculus core of the classical
argument once that gauge has been fixed.
-/

namespace GRLab

/-- If `r f′ + f − 1 = 0` on a convex set `s ⊆ ℝ`, the quantity `r f(r) − r` is constant on `s`.

No openness or connectedness hypothesis on `s` is needed: convexity alone suffices, via the
mean value inequality with Lipschitz constant `0`.
@isnad1 id=eq.5h5v.s7.dc5a370eb040 from=translated src=- shape=a6ed9c09 vocab=8f25c94b
-/
theorem areal_invariant_const {f f₁ : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (hd : ∀ r ∈ s, HasDerivAt f (f₁ r) r)
    (hz : ∀ r ∈ s, 1 - f r - r * f₁ r = 0) :
    ∀ r ∈ s, ∀ r' ∈ s, r * f r - r = r' * f r' - r' := by
  -- The invariant `G r = r * f r - r` has vanishing derivative at every point of `s`.
  have hGd : ∀ r ∈ s, HasDerivAt (fun x : ℝ => x * f x - x) 0 r := by
    intro r hr
    have h1 : HasDerivAt (fun x : ℝ => x * f x) (1 * f r + r * f₁ r) r :=
      (hasDerivAt_id' r).fun_mul (hd r hr)
    have h2 := h1.fun_sub (hasDerivAt_id' r)
    refine h2.congr_deriv ?_
    have := hz r hr
    linarith
  intro r hr r' hr'
  -- A function with derivative `0` on a convex set is `0`-Lipschitz there, hence constant.
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x : ℝ => x * f x - x) (f' := fun _ => (0 : ℝ)) (C := 0)
    (fun x hx => (hGd x hx).hasDerivWithinAt) (fun _ _ => by simp) hs hr hr'
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h.symm

/-- **Birkhoff (areal static gauge), uniqueness.**  On an interval avoiding `r = 0`, the only
lapses solving `R_θθ = 0` are the Schwarzschild family `f = 1 − 2M/r`.
@isnad1 id=ex.4h4v.s7.96ceabab620e from=translated src=- shape=608e0ac0 vocab=06a4992e
-/
theorem exists_mass_of_areal_vacuum {f f₁ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ r ∈ Set.Ioo a b, HasDerivAt f (f₁ r) r)
    (hz : ∀ r ∈ Set.Ioo a b, 1 - f r - r * f₁ r = 0)
    (h0 : ∀ r ∈ Set.Ioo a b, r ≠ 0) :
    ∃ M : ℝ, ∀ r ∈ Set.Ioo a b, f r = 1 - 2 * M / r := by
  obtain ⟨r₀, hr₀⟩ := Set.nonempty_Ioo.mpr hab
  have key := areal_invariant_const (convex_Ioo a b) hd hz
  refine ⟨-(r₀ * f r₀ - r₀) / 2, fun r hr => ?_⟩
  have hC : r * f r - r = r₀ * f r₀ - r₀ := key r hr r₀ hr₀
  have hrne : r ≠ 0 := h0 r hr
  field_simp
  linarith

/-- Converse: every Schwarzschild lapse does solve `R_θθ = 0`.
@isnad1 id=eq.1h2v.s7.18ff89fa8fff from=translated src=- shape=16127339 vocab=533ed9c4
-/
theorem areal_vacuum_of_mass (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    1 - (1 - 2 * M / r) - r * (2 * M / r ^ 2) = 0 := by
  field_simp
  ring

end GRLab
