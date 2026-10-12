/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.NumberTheory.ArithmeticFunction.TwistedDivisorSum
public import Tengoku.Tauceti.TauCeti.NumberTheory.ModularForms.EisensteinSeries.Character
public import Tengoku.Tauceti.TauCeti.NumberTheory.TsumDivisorsAntidiagonal
import Tengoku.Tauceti.TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The `q`-expansion of Eisenstein series with character

For Dirichlet characters `ψ` modulo `u` and `φ` modulo `v` and a weight `k ≥ 3` with
`ψ(-1) φ(-1) = (-1)^k`, we compute the `q`-expansion of the Eisenstein series with character
`G_k^{ψ,φ}(z) = ∑_{(c, d) ∈ ℤ²} ψ(c) φ⁻¹(d) (c v z + d)^(-k)`
(`TauCeti.EisensteinSeries.charEisensteinSeriesMF`). Its constant coefficient is
`ψ(0) ∑_{d ∈ ℤ} φ⁻¹(d) d^(-k)`, and for `n ≥ 1` its `n`-th coefficient is
`2 (-2πi)^k / ((k-1)! v^k) ∑_{c m = n} ψ(c) φ̂(m) m^(k-1)`, where
`φ̂(m) = ∑_{r mod v} φ⁻¹(r) e^(2πi r m / v)`. When `φ` is primitive, `φ̂(m) = g(φ⁻¹) φ(m)` with
`g(φ⁻¹)` the Gauss sum, so the `n`-th coefficient is a constant multiple of the twisted divisor
sum `σ_{k-1}^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n/d) φ(d) d^(k-1)`.

The analytic input is a Lipschitz formula along residue classes: for any `f : ZMod v → ℂ`,
`∑_{n ∈ ℤ} f(n) (z + n)^(-k) = (-2πi)^k / ((k-1)! v^k) ∑_{m ≥ 1} 𝓕f(-m) m^(k-1) e^(2πi m z / v)`,
obtained by applying Mathlib's `EisensteinSeries.qExpansion_identity_pnat` to each residue class
of `n` modulo `v`. The rows `c` and `-c` of `G_k^{ψ,φ}` contribute equally by the parity
condition, the row `c = 0` gives the constant term, and the remaining double series is regrouped
by `n = c m` (`HasSum.sum_divisorsAntidiagonal`).

The coefficient-identification argument follows Mathlib's
`EisensteinSeries.E_qExpansion_coeff`.

## Main results

* `TauCeti.EisensteinSeries.qExpansion_identity_zmod`: the Lipschitz formula for a function of
  residues modulo `v`.
* `TauCeti.EisensteinSeries.qExpansion_charEisensteinSeriesMF_coeff`: the coefficients of
  `G_k^{ψ,φ}`.
* `TauCeti.EisensteinSeries.qExpansion_charEisensteinSeriesMF_coeff_of_isPrimitive`: for
  primitive `φ`, the nonconstant coefficients are `2 (-2πi)^k g(φ⁻¹) / ((k-1)! v^k)` times the
  twisted divisor sums.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.5,
  Theorem 4.5.1.
* [T. Miyake, *Modular forms*][miyake1989], §7.1.
-/

public section

noncomputable section

open Complex ZMod EisensteinSeries ModularForm CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

namespace TauCeti.EisensteinSeries

/-! ### The Lipschitz formula along residue classes -/

variable {v : ℕ} [NeZero v]

/-- The point `(z + r) / v` of the upper half-plane. -/
private def residuePoint (v : ℕ) [NeZero v] (z : ℍ) (r : ℕ) : ℍ :=
  ⟨((z : ℂ) + r) / v, by
    simpa [Complex.div_natCast_im] using div_pos z.2 (Nat.cast_pos.mpr (NeZero.pos v))⟩

private lemma coe_residuePoint (z : ℍ) (r : ℕ) :
    (residuePoint v z r : ℂ) = ((z : ℂ) + r) / v :=
  rfl

/-- The Lipschitz formula along one residue class modulo `v`. -/
private lemma tsum_residue (z : ℍ) {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    ∑' q : ℤ, ((z : ℂ) + (q * v + r : ℤ)) ^ (-(k : ℤ)) =
      (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) * ∑' m : ℕ+,
        (m : ℂ) ^ (k - 1) * cexp (2 * π * I * residuePoint v z r) ^ (m : ℕ) := by
  have hv : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
  have H := qExpansion_identity_pnat (k := k - 1) (by omega) (residuePoint v z r)
  have hk' : k - 1 + 1 = k := by omega
  rw [hk'] at H
  have hterm (q : ℤ) : ((z : ℂ) + (q * v + r : ℤ)) ^ (-(k : ℤ)) =
      ((v : ℂ) ^ k)⁻¹ * (1 / ((residuePoint v z r : ℂ) + q) ^ k) := by
    have : (z : ℂ) + (q * v + r : ℤ) = v * ((residuePoint v z r : ℂ) + q) := by
      rw [coe_residuePoint]
      push_cast
      field_simp
      ring
    rw [this, zpow_neg, zpow_natCast, mul_pow, mul_inv, one_div]
  simp_rw [hterm, tsum_mul_left, H]
  field_simp

/-- **The Lipschitz formula along residue classes.** For a function `f` of residues modulo `v`,
a weight `k ≥ 2` and `z` in the upper half-plane,
`∑_{n ∈ ℤ} f(n) (z + n)^(-k) = (-2πi)^k / ((k-1)! v^k) ∑_{m ≥ 1} 𝓕f(-m) m^(k-1) e^(2πi m z / v)`,
where `𝓕f(-m) = ∑_{r mod v} f(r) e^(2πi r m / v)` is the discrete Fourier transform of `f`.
For `v = 1` this is `f 0` times Mathlib's `EisensteinSeries.qExpansion_identity_pnat`. -/
theorem qExpansion_identity_zmod (f : ZMod v → ℂ) {k : ℕ} (hk : 2 ≤ k) (z : ℍ) :
    ∑' n : ℤ, f n * ((z : ℂ) + n) ^ (-(k : ℤ)) =
      (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) * ∑' m : ℕ+,
        𝓕 f (-(m : ZMod v)) * (m : ℂ) ^ (k - 1) * cexp (2 * π * I * z / v) ^ (m : ℕ) := by
  -- the series converges absolutely, as `f` is bounded
  have hS : Summable fun n : ℤ ↦ f n * ((z : ℂ) + n) ^ (-(k : ℤ)) := by
    have h0 : Summable fun n : ℤ ↦ ‖((z : ℂ) + n) ^ (-(k : ℤ))‖ :=
      summable_norm_iff.mpr <| (linear_right_summable (z : ℂ) 1 (k := k) (by omega)).congr
        fun n ↦ by simp [zpow_neg]
    refine (h0.mul_left (∑ x, ‖f x‖)).of_norm_bounded fun n ↦ ?_
    rw [norm_mul]
    gcongr
    exact Finset.single_le_sum (f := fun x ↦ ‖f x‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ _)
  -- split `n = q v + r` according to the residue `r` of `n` modulo `v`
  let e : Fin v × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv v).symm
  have he (p : Fin v × ℤ) : e p = p.2 * v + (p.1 : ℕ) := by
    simp [e]
  have hprod := (e.summable_iff.mpr hS).tsum_prod
  simp only [Function.comp_def] at hprod
  rw [← e.tsum_eq, hprod, tsum_fintype]
  simp_rw [he]
  have hf (r : Fin v) (q : ℤ) : f ((q * v + (r : ℕ) : ℤ) : ZMod v) = f ((r : ℕ) : ZMod v) := by
    push_cast
    simp
  simp_rw [hf, tsum_mul_left, tsum_residue z hk]
  have hsum (r : Fin v) : Summable fun m : ℕ+ ↦
      (m : ℂ) ^ (k - 1) * cexp (2 * π * I * residuePoint v z (r : ℕ)) ^ (m : ℕ) := by
    have := (summable_pow_mul_cexp (k - 1) 1 (residuePoint v z r)).comp_injective
      PNat.coe_injective
    simpa [Function.comp_def] using this
  simp_rw [mul_left_comm (f _), ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun r _ ↦ ((hsum r).mul_left (f r)).mul_left _]
  refine tsum_congr fun m ↦ ?_
  rw [← Finset.mul_sum]
  congr 1
  -- the residue `r` contributes the additive character `r m / v` to the exponential
  have hexp (r : Fin v) : cexp (2 * π * I * residuePoint v z (r : ℕ)) ^ (m : ℕ) =
      stdAddChar (-(((r : ℕ) : ZMod v) * -(m : ZMod v))) * cexp (2 * π * I * z / v) ^ (m : ℕ) := by
    have hrm : -(((r : ℕ) : ZMod v) * -(m : ZMod v)) = (((r : ℕ) * m : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hrm, stdAddChar_coe, coe_residuePoint, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hbij : Function.Bijective fun r : Fin v ↦ ((r : ℕ) : ZMod v) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨fun j ↦ ⟨⟨j.val, j.val_lt⟩, by simp⟩, by simp [ZMod.card]⟩
  rw [dft_apply, Finset.sum_mul, Finset.sum_mul,
    ← Fintype.sum_bijective _ hbij (fun r : Fin v ↦ _) _ fun _ ↦ rfl]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [hexp, smul_eq_mul]
  ring

/-! ### The Eisenstein series with character -/

section Character

variable {u v N : ℕ} [NeZero v] [NeZero N] (ψ : DirichletCharacter ℂ u)
  (φ : DirichletCharacter ℂ v) {k : ℕ}

end Character

end TauCeti.EisensteinSeries
