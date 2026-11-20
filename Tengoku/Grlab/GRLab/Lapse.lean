import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lapse functions for static spherically symmetric metrics

One-variable calculus and algebra for the lapse `f(r)` in

  `ds² = −f(r) dt² + f(r)⁻¹ dr² + r² dΩ²`.

The companion curvature module proves that this metric has Ricci components

  `R_tt = f · (f″/2 + f′/r)`,   `R_rr = −(f″/2 + f′/r)/f`,
  `R_θθ = 1 − f − r f′`,        `R_φφ = sin²θ · (1 − f − r f′)`,

so everything reduces to the two scalars

  `A(r) := 1 − f − r f′`   (areal / angular block)
  `B(r) := f″/2 + f′/r`    (radial block)

and the lapse is Ricci-flat exactly when both vanish.  Contracting gives the
Ricci scalar `R = 2A/r² − 2B`.  This file supplies `HasDerivAt` facts for the
three standard lapses and evaluates `A` and `B` on each.

| solution                | `f`                  | `A = 1 − f − r f′` | `B = f″/2 + f′/r` | `R`  |
| ----------------------- | -------------------- | ------------------ | ----------------- | ---- |
| Schwarzschild           | `1 − 2M/r`           | `0`                | `0`               | `0`  |
| Reissner–Nordström      | `1 − 2M/r + Q²/r²`   | `Q²/r²`            | `Q²/r⁴`           | `0`  |
| Schwarzschild–de Sitter | `1 − 2M/r − Λr²/3`   | `Λr²`              | `−Λ`              | `4Λ` |

Only Schwarzschild is Ricci-flat.  Reissner–Nordström is electrovac: `A` and `B`
are nonzero — they are the Maxwell stress of the Coulomb field — but the Ricci
scalar `R = 2A/r² − 2B = 2Q²/r⁴ − 2Q²/r⁴` vanishes, which is exactly the
tracelessness of the electromagnetic stress tensor.  Schwarzschild–de Sitter
instead satisfies `R_μν = Λ g_μν`: `A = Λr²` gives `R_θθ = Λ r² = Λ g_θθ`, and
`B = −Λ` gives `R_tt = f · B = −Λ f = Λ g_tt`, whence `R = 4Λ`.

All values in this file were cross-checked against sympy 1.14, including an
independent Christoffel/Riemann computation of `R_μν` and `R` for each metric.
-/

namespace GRLab

open Real

/-! ### Reusable inverse-power derivatives -/

/-- `d/ds (a / s²) = −2a/s³`.-/
private theorem hasDerivAt_const_div_sq (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => a / s ^ 2) (-(2 * a / r ^ 3)) r :=
  ((hasDerivAt_const r a).fun_div (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr)).congr_deriv (by
    norm_num
    field_simp)

/-- `d/ds (a / s³) = −3a/s⁴`.-/
private theorem hasDerivAt_const_div_cube (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => a / s ^ 3) (-(3 * a / r ^ 4)) r :=
  ((hasDerivAt_const r a).fun_div (hasDerivAt_pow 3 r) (pow_ne_zero 3 hr)).congr_deriv (by
    norm_num
    field_simp)

/-! ### Schwarzschild -/

/-- The Schwarzschild lapse `f(r) = 1 − 2M/r` has `f′(r) = 2M/r²`.-/
theorem hasDerivAt_schwLapse (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => 1 - 2 * M / s) (2 * M / r ^ 2) r :=
  (((hasDerivAt_const r (2 * M)).fun_div (hasDerivAt_id' r) hr).const_sub 1).congr_deriv (by
    field_simp
    ring)

/-- The Schwarzschild lapse has `f″(r) = −4M/r³`, i.e. `d/ds (2M/s²) = −4M/s³`.-/
theorem hasDerivAt_schwLapse' (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => 2 * M / s ^ 2) (-(4 * M / r ^ 3)) r :=
  (hasDerivAt_const_div_sq (2 * M) hr).congr_deriv (by ring)

/-- The Schwarzschild lapse kills the `θθ` Ricci component: `1 − f − r f′ = 0`.-/
theorem schwLapse_areal (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    1 - (1 - 2 * M / r) - r * (2 * M / r ^ 2) = 0 := by
  field_simp
  ring

/-- The Schwarzschild lapse kills the `tt`/`rr` Ricci components: `f″/2 + f′/r = 0`.-/
theorem schwLapse_radial (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    -(4 * M / r ^ 3) / 2 + (2 * M / r ^ 2) / r = 0 := by
  field_simp
  ring

/-! ### Nonvanishing of the Schwarzschild lapse outside the horizon -/

/-- Outside the horizon (`0 < r`, `2M < r`) the Schwarzschild lapse is positive.-/
theorem schwLapse_pos {M r : ℝ} (hr : 0 < r) (h : 2 * M < r) : 0 < 1 - 2 * M / r := by
  have hlt : 2 * M / r < 1 := (div_lt_one hr).mpr h
  linarith

/-- Outside the horizon the Schwarzschild lapse is nonzero, so `f⁻¹` and the
Christoffel symbols built from it are defined.-/
theorem schwLapse_ne_zero {M r : ℝ} (hr : 0 < r) (h : 2 * M < r) : 1 - 2 * M / r ≠ 0 :=
  (schwLapse_pos hr h).ne'

/-- The exterior region is open: if `r` lies outside the horizon then so does every
nearby point.  Needed to differentiate a Christoffel symbol containing `f⁻¹`, which
requires `f ≠ 0` on a whole neighbourhood rather than at a single point.-/
theorem eventually_schwLapse_ne_zero {M r : ℝ} (hr : 0 < r) (h : 2 * M < r) :
    ∀ᶠ s in nhds r, (0 < s ∧ 2 * M < s) :=
  (eventually_gt_nhds hr).and (eventually_gt_nhds h)

/-! ### Reissner–Nordström -/

/-- Reissner–Nordström: `f = 1 − 2M/r + Q²/r²` has `f′ = 2M/r² − 2Q²/r³`.-/
theorem hasDerivAt_rnLapse (M Q : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => 1 - 2 * M / s + Q ^ 2 / s ^ 2)
      (2 * M / r ^ 2 - 2 * Q ^ 2 / r ^ 3) r :=
  ((hasDerivAt_schwLapse M hr).fun_add (hasDerivAt_const_div_sq (Q ^ 2) hr)).congr_deriv (by ring)

/-- Reissner–Nordström: `f″ = −4M/r³ + 6Q²/r⁴`.-/
theorem hasDerivAt_rnLapse' (M Q : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => 2 * M / s ^ 2 - 2 * Q ^ 2 / s ^ 3)
      (-(4 * M / r ^ 3) + 6 * Q ^ 2 / r ^ 4) r :=
  ((hasDerivAt_schwLapse' M hr).fun_sub (hasDerivAt_const_div_cube (2 * Q ^ 2) hr)).congr_deriv (by
    ring)

/-- Reissner–Nordström is **not** Ricci-flat: the `θθ` block leaves `Q²/r²`.-/
theorem rnLapse_areal (M Q : ℝ) {r : ℝ} (hr : r ≠ 0) :
    1 - (1 - 2 * M / r + Q ^ 2 / r ^ 2) - r * (2 * M / r ^ 2 - 2 * Q ^ 2 / r ^ 3)
      = Q ^ 2 / r ^ 2 := by
  field_simp
  ring

/-- Reissner–Nordström is **not** Ricci-flat: the radial block leaves `Q²/r⁴`.-/
theorem rnLapse_radial (M Q : ℝ) {r : ℝ} (hr : r ≠ 0) :
    (-(4 * M / r ^ 3) + 6 * Q ^ 2 / r ^ 4) / 2 + (2 * M / r ^ 2 - 2 * Q ^ 2 / r ^ 3) / r
      = Q ^ 2 / r ^ 4 := by
  field_simp
  ring

/-! ### Schwarzschild–de Sitter -/

/-- Schwarzschild–de Sitter: `f = 1 − 2M/r − Λr²/3` has `f′ = 2M/r² − 2Λr/3`.-/
theorem hasDerivAt_sdsLapse (M Λ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => 1 - 2 * M / s - Λ * s ^ 2 / 3)
      (2 * M / r ^ 2 - 2 * Λ * r / 3) r :=
  ((hasDerivAt_schwLapse M hr).fun_sub
      (((hasDerivAt_pow 2 r).const_mul Λ).div_const 3)).congr_deriv (by
    norm_num
    ring)

/-- Schwarzschild–de Sitter: `f″ = −4M/r³ − 2Λ/3`.-/
theorem hasDerivAt_sdsLapse' (M Λ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => 2 * M / s ^ 2 - 2 * Λ * s / 3)
      (-(4 * M / r ^ 3) - 2 * Λ / 3) r :=
  ((hasDerivAt_schwLapse' M hr).fun_sub
      (((hasDerivAt_id' r).const_mul (2 * Λ)).div_const 3)).congr_deriv (by ring)

/-- Schwarzschild–de Sitter is **not** Ricci-flat: the `θθ` block leaves `Λr²`.-/
theorem sdsLapse_areal (M Λ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    1 - (1 - 2 * M / r - Λ * r ^ 2 / 3) - r * (2 * M / r ^ 2 - 2 * Λ * r / 3)
      = Λ * r ^ 2 := by
  field_simp
  ring

/-- Schwarzschild–de Sitter is **not** Ricci-flat: the radial block leaves `−Λ`.-/
theorem sdsLapse_radial (M Λ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    (-(4 * M / r ^ 3) - 2 * Λ / 3) / 2 + (2 * M / r ^ 2 - 2 * Λ * r / 3) / r
      = -Λ := by
  field_simp
  ring

end GRLab
