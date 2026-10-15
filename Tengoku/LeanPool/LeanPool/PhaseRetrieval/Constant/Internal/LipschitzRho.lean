/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # LipschitzRho.lean
  Lipschitz property of the function `rho`.
  Scaffolding notes: ElementaryLemmas/lipschitz_rho.md

  Dependencies: Definitions

  Public API:
  - `rho_lipschitz`       (Theorem 2.3: rho is 1-Lipschitz)
  - `rho_pointwise_upper` (Corollary 2.4a)
  - `rho_pointwise_lower` (Corollary 2.4b)
  - `rho_le_norm`         (Corollary 2.5)
-/
module

public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.Constant.Internal.Definitions
public import Tengoku

/-! # LipschitzRho -/

@[expose] public section

open Complex Real

namespace FockSPR

/-! ## Theorem 2.3: `rho` is 1-Lipschitz

`|rho(w) − rho(z)| ≤ ‖w − z‖` for all `w, z : ℂ`.

**Proof**:
```
|rho(w) − rho(z)|
  = | |‖1+w‖ − 1| − |‖1+z‖ − 1| |
  ≤ | ‖1+w‖ − ‖1+z‖ |              (reverse triangle ineq for |· − 1|)
  ≤ ‖(1+w) − (1+z)‖                (reverse triangle ineq for norm)
  = ‖w − z‖
```

**Lean notes**:
- `abs_abs_sub_abs_le_abs_sub` from Mathlib for `|t − 1|` Lipschitz.
- `norm_sub_norm_le` for the reverse triangle inequality on ℂ.
- `LipschitzWith.comp` from Mathlib can compose Lipschitz functions.
-/
/--
@isnad1 id=lipschit.0h0v.s4.45cd35ed6973 from=translated src=- shape=c80f5d6d vocab=8c412f4f
-/
theorem rho_lipschitz : LipschitzWith 1 rho := by
  apply LipschitzWith.mk_one
  intro w z
  simp only [rho, dist_eq_norm]
  calc |( |‖(1 : ℂ) + w‖ - 1| ) - ( |‖(1 : ℂ) + z‖ - 1| )|
      ≤ |(‖(1 : ℂ) + w‖ - 1) - (‖(1 : ℂ) + z‖ - 1)| :=
        abs_abs_sub_abs_le_abs_sub _ _
    _ = |‖(1 : ℂ) + w‖ - ‖(1 : ℂ) + z‖| := by ring_nf
    _ ≤ ‖(1 : ℂ) + w - ((1 : ℂ) + z)‖ := abs_norm_sub_norm_le _ _
    _ = ‖w - z‖ := by ring_nf

/-! ## Corollary 2.4: Pointwise comparison via Lipschitz -/

/-- `rho(w) ≤ rho(z) + ‖w − z‖`
@isnad1 id=le.0h2v.s4.e08cfcc53d1c from=translated src=- shape=fbde28d2 vocab=837c7f12
-/
theorem rho_pointwise_upper (w z : ℂ) : rho w ≤ rho z + ‖w - z‖ := by
  have h := rho_lipschitz.dist_le_mul w z
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm] at h
  linarith [le_abs_self (rho w - rho z)]

/-- `rho(w) ≥ rho(z) − ‖w − z‖`
@isnad1 id=le.0h2v.s4.32a57ed3a0f5 from=translated src=- shape=fd91b49d vocab=39390d1c
-/
theorem rho_pointwise_lower (w z : ℂ) : rho w ≥ rho z - ‖w - z‖ := by
  have h := rho_lipschitz.dist_le_mul w z
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm] at h
  linarith [neg_abs_le (rho w - rho z)]

/-! ## Corollary 2.5: `rho(w) ≤ ‖w‖`

**Proof**: Apply 2.4 with `z = 0`: `rho(w) ≤ rho(0) + ‖w‖ = 0 + ‖w‖`.
-/
/--
@isnad1 id=le.0h1v.s3.15209c78f5ec from=translated src=- shape=1b9c6b2b vocab=8d1c2d29
-/
theorem rho_le_norm (w : ℂ) : rho w ≤ ‖w‖ := by
  simpa only [rho, add_zero, norm_one, sub_self, abs_zero, zero_add, sub_zero] using
    rho_pointwise_upper w 0

end FockSPR
