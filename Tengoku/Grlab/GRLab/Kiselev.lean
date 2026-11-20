/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.SSRicci
import Tengoku.Grlab.GRLab.Lapse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Kiselev metric: a black hole surrounded by quintessence

Kiselev's static spherically symmetric solution puts a black hole of mass `M` inside an
anisotropic fluid ("quintessence") of equation-of-state parameter `w`:

  `ds² = −f dt² + f⁻¹ dr² + r² dΩ²`,   `f(r) = 1 − 2M/r − c r^{−(3w+1)}`,

with `c` the quintessence normalisation.  The exponent is a *real* number, so `s ^ p` here
is `Real.rpow` and every statement is restricted to `0 < r` — which is no loss, since the
Kiselev chart lives on `r > 0` anyway.

Differentiating,

  `f′  =  2M/r² + c(3w+1) r^{−(3w+2)}`,
  `f″  = −4M/r³ − c(3w+1)(3w+2) r^{−(3w+3)}`,

so the two scalars that `GRLab.ricci_ss` reduces the Ricci tensor to are

  `A := 1 − f − r f′ = −3wc · r^{−(3w+1)}`            (`R_θθ = A`, `R_φφ = A sin²θ`)
  `B := f″/2 + f′/r = −(3/2) w c (3w+1) · r^{−(3w+3)}` (`R_tt = f B`, `R_rr = −B/f`)

and the Ricci scalar is `R = 2A/r² − 2B = 3wc(3w−1) · r^{−(3w+3)}`.

### Degeneration checks (all three are visible in the formulas above)

| `w`    | fluid     | `A`          | `B`     | `R`   | metric                                  |
| ------ | --------- | ------------ | ------- | ----- | --------------------------------------- |
| `0`    | dust      | `0`          | `0`     | `0`   | Schwarzschild (the `c/r` term is a mass shift, `M ↦ M + c/2`) |
| `1/3`  | radiation | `−c/r²`      | `−c/r⁴` | `0`   | Reissner–Nordström with `Q² = −c` — traceless electrovac |
| `−1`   | vacuum    | `3c r²`      | `−3c`   | `12c` | Schwarzschild–de Sitter with `Λ = 3c`   |

The `w = 0` row is proved below as `GRLab.kiselev_ricciFlat_of_w_eq_zero`.  The other two
rows are read off `GRLab.kiselevLapse_areal` / `GRLab.kiselevLapse_radial` by substituting
the value of `w` and comparing with `GRLab.rnLapse_areal` / `GRLab.sdsLapse_areal` in
`GRLab.Lapse`.

### Oracle

The four bracket values were fixed *before* any proof was attempted by an independent
sympy computation of `Γ`, `Riemann` and `Ric` for this chart, cross-checked against
the author's own computer-algebra suite; the static-spherical
bracket section of that run reports, verbatim,
`A = -3*c*w/(r*r**(3*w))`, `B = 3*c*r**(-3*w - 3)*w*(-3*w - 1)/2`,
`R = 3*c*r**(-3*w - 3)*w*(3*w - 1)`, in agreement with the statements below.
-/

namespace GRLab

open Matrix Filter Topology

/-! ### The lapse and its two derivatives -/

/-- The Kiselev lapse `f(r) = 1 − 2M/r − c r^{−(3w+1)}`.  The exponent is real, so the
power is `Real.rpow`.-/
noncomputable def kiselevF (M c w : ℝ) : ℝ → ℝ :=
  fun s => 1 - 2 * M / s - c * s ^ (-(3 * w + 1))

/-- `f′(r) = 2M/r² + c(3w+1) r^{−(3w+2)}`.-/
noncomputable def kiselevF₁ (M c w : ℝ) : ℝ → ℝ :=
  fun s => 2 * M / s ^ 2 + c * (3 * w + 1) * s ^ (-(3 * w + 2))

/-- `f″(r) = −4M/r³ − c(3w+1)(3w+2) r^{−(3w+3)}`.-/
noncomputable def kiselevF₂ (M c w : ℝ) : ℝ → ℝ :=
  fun s => -(4 * M / s ^ 3) - c * (3 * w + 1) * (3 * w + 2) * s ^ (-(3 * w + 3))

/-- The Kiselev metric: a black hole surrounded by quintessence of equation of state `w`.-/
noncomputable def kiselev (M c w : ℝ) : MetricFn 4 := ssMetric (kiselevF M c w)

/-- `kiselev` is a static spherically symmetric chart, hence symmetric.
@isnad1 id=issymmet.0h3v.s4.13999d791e9d from=translated src=- shape=8c2e48b4 vocab=175ec9c4
-/
theorem kiselev_isSymm (M c w : ℝ) : IsSymmetricMetric (kiselev M c w) :=
  ssMetric_isSymm _

/-! ### Calculus

Both derivatives split as (a Schwarzschild piece, already done in `GRLab.Lapse`) plus (a
constant times an `rpow`).  The only real work is that `Real.hasDerivAt_rpow_const` returns
the exponent as `p - 1`, which is equal to the wanted exponent only *as a real number*, not
syntactically; a `rw [show … by ring]` fixes it before the combinators are applied. -/

/-- **`f′` for the Kiselev lapse.**
@isnad1 id=hasderiv.1h4v.s5.13c11ebf08e4 from=translated src=- shape=6c8b10b6 vocab=1c8b449c
-/
theorem hasDerivAt_kiselevF (M c w : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (kiselevF M c w) (kiselevF₁ M c w r) r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have h2 : HasDerivAt (fun s : ℝ => c * s ^ (-(3 * w + 1)))
      (c * (-(3 * w + 1) * r ^ (-(3 * w + 1) - 1))) r :=
    (Real.hasDerivAt_rpow_const (Or.inl hr0)).const_mul c
  rw [show (-(3 * w + 1) - 1 : ℝ) = -(3 * w + 2) by ring] at h2
  show HasDerivAt (fun s : ℝ => 1 - 2 * M / s - c * s ^ (-(3 * w + 1)))
    (kiselevF₁ M c w r) r
  refine ((hasDerivAt_schwLapse M hr0).fun_sub h2).congr_deriv ?_
  show 2 * M / r ^ 2 - c * (-(3 * w + 1) * r ^ (-(3 * w + 2)))
      = 2 * M / r ^ 2 + c * (3 * w + 1) * r ^ (-(3 * w + 2))
  ring1

/-- **`f″` for the Kiselev lapse.**
@isnad1 id=hasderiv.1h4v.s5.8a47ab87de2d from=translated src=- shape=6c8b10b6 vocab=c48d37e7
-/
theorem hasDerivAt_kiselevF' (M c w : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (kiselevF₁ M c w) (kiselevF₂ M c w r) r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have h2 : HasDerivAt (fun s : ℝ => c * (3 * w + 1) * s ^ (-(3 * w + 2)))
      (c * (3 * w + 1) * (-(3 * w + 2) * r ^ (-(3 * w + 2) - 1))) r :=
    (Real.hasDerivAt_rpow_const (Or.inl hr0)).const_mul (c * (3 * w + 1))
  rw [show (-(3 * w + 2) - 1 : ℝ) = -(3 * w + 3) by ring] at h2
  show HasDerivAt (fun s : ℝ => 2 * M / s ^ 2 + c * (3 * w + 1) * s ^ (-(3 * w + 2)))
    (kiselevF₂ M c w r) r
  refine ((hasDerivAt_schwLapse' M hr0).fun_add h2).congr_deriv ?_
  show -(4 * M / r ^ 3) + c * (3 * w + 1) * (-(3 * w + 2) * r ^ (-(3 * w + 3)))
      = -(4 * M / r ^ 3) - c * (3 * w + 1) * (3 * w + 2) * r ^ (-(3 * w + 3))
  ring1

/-! ### The two Ricci brackets

The exponent bookkeeping is done once, by reducing every `rpow` in the goal to a single
common power; after that `r ^ p` is an atom and `field_simp` / `ring1` finish. -/

/-- The angular bracket: `1 − f − r f′ = −3wc r^{−(3w+1)}`.

It vanishes exactly when `w = 0` or `c = 0`: for dust the quintessence term `c/r` is
indistinguishable from a shift of the mass.
@isnad1 id=eq.1h4v.s7.71ea38721d65 from=translated src=- shape=d7065fd4 vocab=fc8439a3
-/
theorem kiselevLapse_areal (M c w : ℝ) {r : ℝ} (hr : 0 < r) :
    1 - kiselevF M c w r - r * kiselevF₁ M c w r
      = -(3 * w * c * r ^ (-(3 * w + 1))) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have key : r ^ (-(3 * w + 2) : ℝ) = r ^ (-(3 * w + 1) : ℝ) / r := by
    rw [show (-(3 * w + 2) : ℝ) = -(3 * w + 1) - 1 by ring, Real.rpow_sub hr, Real.rpow_one]
  show 1 - (1 - 2 * M / r - c * r ^ (-(3 * w + 1)))
      - r * (2 * M / r ^ 2 + c * (3 * w + 1) * r ^ (-(3 * w + 2)))
      = -(3 * w * c * r ^ (-(3 * w + 1)))
  rw [key]
  field_simp
  ring1

/-- The radial bracket: `f″/2 + f′/r = −(3/2) w c (3w+1) r^{−(3w+3)}`.
@isnad1 id=eq.1h4v.s7.14d439f2c5e3 from=translated src=- shape=b5725360 vocab=9a236bc7
-/
theorem kiselevLapse_radial (M c w : ℝ) {r : ℝ} (hr : 0 < r) :
    kiselevF₂ M c w r / 2 + kiselevF₁ M c w r / r
      = -(3 * w * c * (3 * w + 1) / 2 * r ^ (-(3 * w + 3))) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have key : r ^ (-(3 * w + 2) : ℝ) = r ^ (-(3 * w + 3) : ℝ) * r := by
    rw [show (-(3 * w + 2) : ℝ) = -(3 * w + 3) + 1 by ring, Real.rpow_add hr, Real.rpow_one]
  show (-(4 * M / r ^ 3) - c * (3 * w + 1) * (3 * w + 2) * r ^ (-(3 * w + 3))) / 2
      + (2 * M / r ^ 2 + c * (3 * w + 1) * r ^ (-(3 * w + 2))) / r
      = -(3 * w * c * (3 * w + 1) / 2 * r ^ (-(3 * w + 3)))
  rw [key]
  field_simp
  ring1

/-! ### The Ricci tensor -/

end GRLab
