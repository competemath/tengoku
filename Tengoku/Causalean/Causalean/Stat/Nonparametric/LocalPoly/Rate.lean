/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Stat.Concentration.Matrix.DesignInverse
public import Tengoku.Causalean.Causalean.Stat.Nonparametric.LocalPoly.Rate.Conjugation
public import Tengoku

/-!
# Explicit `O(1/(Nh))` upper bound for the local-polynomial leverage `(M⁻¹)₀₀`

One-sided leverage upper bounds for the local-polynomial design inverse, derived from deterministic
entrywise perturbation and population scaling hypotheses.

This module converts the entrywise design-matrix concentration of
`Concentration.DesignInverse` into the **explicit interior local-polynomial leverage rate**:

* `localPoly_inv00_rate` — on the good design event (empirical moment matrix `M` entrywise within
  `η` of the population matrix `S`), the leverage `(M⁻¹)₀₀ ≤ 2·cInv/(Nh)`, i.e. the variance
  scale has the upper bound `O(1/(Nh))`.
* `localPoly_leverage_bound` — the leverage product `√(M₀₀·(M⁻¹)₀₀) ≤ √(2·cInv·(cTop+1))`, a
  bandwidth-free constant, controlling the `ℓ¹` bias leverage.

The population matrix is supplied with one-sided `Nh`-scale bounds via the diagonal-conjugation
factorization `S = (Nh)·D·T·D` (`D = diagonal (h^j)`): `population_scaling_of_conj` turns a
bandwidth-free shape matrix `T` (invertible with bounded `(T⁻¹)₀₀` and `T₀₀`, supplied by the
integral-moment positive-definiteness of `LocalPoly.Rate.IntegralMoment`) into the leverage scaling
hypotheses `(S⁻¹)₀₀ ≤ cInv/(Nh)` and `S₀₀ ≤ cTop·(Nh)`. The entrywise-closeness condition is a
deterministic hypothesis here; this module does not instantiate it from a concentration event.
-/

public section

namespace Causalean.Stat.Nonparametric

open Causalean.Stat.Concentration
open scoped BigOperators
open Matrix

variable {p : ℕ}

/-- **One-sided population leverage bounds from the change-of-variables factorization.** If the
population
moment matrix factors as `S = (Nh)·D·T·D` with `D = diagonal (fun j => h^j)` (so `D₀₀ = 1`) and a
bandwidth-free shape matrix `T` that is invertible with `(T⁻¹)₀₀ ≤ cInv` and `T₀₀ ≤ cTop`, then `S`
is invertible and its intercept leverage scales as `(S⁻¹)₀₀ ≤ cInv/(Nh)` while its top weight
scales as `S₀₀ ≤ cTop·(Nh)`. This discharges the leverage-scaling hypotheses of the rate
capstones from the bandwidth-free shape matrix `T`.
@isnad1 id=and.6h7v.s10.fadbba5f00fd from=translated src=- shape=1a3c2909 vocab=c1048af1
-/
theorem population_scaling_of_conj {N : ℕ} {h cInv cTop : ℝ}
    (hh : 0 < h) (hN : 0 < (N : ℝ))
    {T S : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ} (hT : IsUnit T.det)
    (hTinv00 : T⁻¹ 0 0 ≤ cInv) (hT00 : T 0 0 ≤ cTop)
    (hS : S = ((N : ℝ) * h) •
      (Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)) * T *
        Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)))) :
    IsUnit S.det ∧ S⁻¹ 0 0 ≤ cInv / ((N : ℝ) * h) ∧ S 0 0 ≤ cTop * ((N : ℝ) * h) := by
  let κ : ℝ := (N : ℝ) * h
  have hκ : κ ≠ 0 := (mul_pos hN hh).ne'
  have hd : ∀ i : Fin (p + 1), h ^ (i : ℕ) ≠ 0 := fun i => pow_ne_zero _ hh.ne'
  have hd0 : (fun j : Fin (p + 1) => h ^ (j : ℕ)) 0 = 1 := by
    simp
  obtain ⟨hdet, hinv00⟩ :=
    inv00_diag_conj (κ := κ) hκ hd hd0 hT hS
  have htop := top00_diag_conj (κ := κ) hd0 hS
  refine ⟨hdet, ?_, ?_⟩
  · rw [hinv00]
    have hκnonneg : 0 ≤ κ⁻¹ := inv_nonneg.mpr (mul_pos hN hh).le
    calc
      κ⁻¹ * T⁻¹ 0 0 ≤ κ⁻¹ * cInv := mul_le_mul_of_nonneg_left hTinv00 hκnonneg
      _ = cInv / ((N : ℝ) * h) := by
        simp [κ, div_eq_mul_inv, mul_comm]
  · rw [htop]
    have hκnonneg : 0 ≤ κ := (mul_pos hN hh).le
    calc
      κ * T 0 0 ≤ κ * cTop := mul_le_mul_of_nonneg_left hT00 hκnonneg
      _ = cTop * ((N : ℝ) * h) := by
        simp [κ, mul_comm]

end Causalean.Stat.Nonparametric
