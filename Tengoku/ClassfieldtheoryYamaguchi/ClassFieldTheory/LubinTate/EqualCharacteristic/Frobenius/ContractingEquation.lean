/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.PowerSeries.Basic
import Tengoku.Seed.Algebra.BigOperators.NatAntidiagonal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# LubinTate the contracting Frobenius equation: the contracting Frobenius equation

The coefficient recursion in the proof of the contracting Frobenius equation repeatedly solves

`α - γ φ(α) = β`

in a complete discrete valuation ring, where `γ` has positive valuation.
For an equal-characteristic power-series ring, positive valuation is exactly
the vanishing of the constant coefficient.  The equation can therefore be
solved algebraically, coefficient by coefficient: the coefficient of degree
`n` on the right only involves coefficients of `α` of degree strictly less
than `n`.

This file records that source-producing recursion directly.  No completeness
or external existence assumption is needed.
-/

noncomputable section

open scoped PowerSeries

namespace LubinTate
namespace EqualCharacteristic

variable {R : Type*} [CommRing R]

/-- The recursively determined coefficients of the solution of
`α = β + γ * φ(α)` when `γ(0)=0`.-/
noncomputable def contractingFrobeniusEquationCoeff
    (φ : R →+* R) (γ β : R⟦X⟧) : ℕ → R :=
  Nat.strongRec fun n previous ↦
    PowerSeries.coeff n β +
      ∑ k : Fin n,
        PowerSeries.coeff (k.1 + 1) γ *
          φ (previous (n - 1 - k.1) (by omega))

/-- States the theorem `contractingFrobeniusEquationCoeff_eq`.
@isnad1 id=eq.0h5v.s8.2ca21f1fc591 from=translated src=- shape=5b60a167 vocab=4e820956
-/
theorem contractingFrobeniusEquationCoeff_eq
    (φ : R →+* R) (γ β : R⟦X⟧) (n : ℕ) :
    contractingFrobeniusEquationCoeff φ γ β n =
      PowerSeries.coeff n β +
        ∑ k : Fin n,
          PowerSeries.coeff (k.1 + 1) γ *
            φ (contractingFrobeniusEquationCoeff φ γ β (n - 1 - k.1)) := by
  rw [contractingFrobeniusEquationCoeff, Nat.strongRec_eq]
  rfl

/-- The power series obtained from the contracting coefficient recursion.-/
noncomputable def contractingFrobeniusEquationSolution
    (φ : R →+* R) (γ β : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (contractingFrobeniusEquationCoeff φ γ β)

/-- States the theorem `contractingFrobeniusEquationSolution_coeff`.
@isnad1 id=eq.0h5v.s7.80dd7a319d1e from=translated src=- shape=b562498f vocab=8add7703
-/
@[simp]
theorem contractingFrobeniusEquationSolution_coeff
    (φ : R →+* R) (γ β : R⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n
        (contractingFrobeniusEquationSolution φ γ β) =
      contractingFrobeniusEquationCoeff φ γ β n := by
  simp [contractingFrobeniusEquationSolution]

private theorem sum_range_succ_convolution_of_constantCoeff_eq_zero
    (φ : R →+* R) (γ α : R⟦X⟧)
    (hγ : PowerSeries.coeff 0 γ = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff k γ * φ (PowerSeries.coeff (n - k) α) =
      ∑ k ∈ Finset.range n,
        PowerSeries.coeff (k + 1) γ *
          φ (PowerSeries.coeff (n - 1 - k) α) := by
  rw [Finset.sum_range_succ']
  simp only [hγ, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  rw [Nat.sub_sub, Nat.add_comm]

/-- The recursively constructed series solves the contracting Frobenius
equation from the contracting Frobenius equation.
@isnad1 id=eq.1h4v.s8.160329ee9f07 from=translated src=- shape=fcb858f6 vocab=a395de4e
-/
theorem contractingFrobeniusEquationSolution_spec
    (φ : R →+* R) (γ β : R⟦X⟧)
    (hγ : PowerSeries.coeff 0 γ = 0) :
    contractingFrobeniusEquationSolution φ γ β =
      β + γ * PowerSeries.map φ
        (contractingFrobeniusEquationSolution φ γ β) := by
  apply PowerSeries.ext
  intro n
  rw [map_add, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_map]
  rw [sum_range_succ_convolution_of_constantCoeff_eq_zero φ γ _ hγ n,
    ← Fin.sum_univ_eq_sum_range,
    contractingFrobeniusEquationSolution_coeff,
    contractingFrobeniusEquationCoeff_eq]
  simp only [contractingFrobeniusEquationSolution_coeff]

/-- Uniqueness of the contracting Frobenius equation.  This is the
coefficientwise replacement for a global valuation argument.
@isnad1 id=eq.2h5v.s8.1f1c7f5b6196 from=translated src=- shape=8dbcb33f vocab=a395de4e
-/
theorem contractingFrobeniusEquationSolution_unique
    (φ : R →+* R) (γ β α : R⟦X⟧)
    (hγ : PowerSeries.coeff 0 γ = 0)
    (hα : α = β + γ * PowerSeries.map φ α) :
    α = contractingFrobeniusEquationSolution φ γ β := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have hcoeff := congrArg (PowerSeries.coeff n) hα
      rw [map_add, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
      simp only [PowerSeries.coeff_map] at hcoeff
      rw [sum_range_succ_convolution_of_constantCoeff_eq_zero
        φ γ α hγ n, ← Fin.sum_univ_eq_sum_range] at hcoeff
      rw [contractingFrobeniusEquationSolution_coeff,
        contractingFrobeniusEquationCoeff_eq, hcoeff]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      rw [← contractingFrobeniusEquationSolution_coeff]
      apply ih
      omega

/-- traditional notation form: the unique solution of `α - γ φ(α) = β`.
@isnad1 id=existsun.1h4v.s8.5c0a2b6209f7 from=translated src=- shape=1bf4b4ec vocab=1c3bcef4
-/
theorem existsUnique_contractingFrobeniusEquation
    (φ : R →+* R) (γ β : R⟦X⟧)
    (hγ : PowerSeries.coeff 0 γ = 0) :
    ∃! α : R⟦X⟧, α - γ * PowerSeries.map φ α = β := by
  refine ⟨contractingFrobeniusEquationSolution φ γ β, ?_, ?_⟩
  · apply (sub_eq_iff_eq_add).2
    exact contractingFrobeniusEquationSolution_spec φ γ β hγ
  · intro α hα
    apply contractingFrobeniusEquationSolution_unique φ γ β α hγ
    rw [sub_eq_iff_eq_add] at hα
    exact hα

end EqualCharacteristic
end LubinTate
