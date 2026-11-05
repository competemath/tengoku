/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.RingTheory.Nullstellensatz
import Tengoku.Seed.RingTheory.KrullDimension.NonZeroDivisors
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinates on the two-dimensional torus

The torus `Gₘ² = kˣ × kˣ` is the closed subvariety `X₀X₂ = 1 = X₁X₃` of `A⁴` through the
embedding `torusEmb : (u, v) ↦ (u, v, u⁻¹, v⁻¹)`; its coordinate rings are quotients of
`k[X₀, …, X₃]`.  This module provides the coordinate bookkeeping for blueprint Lemma
`subgroup-classification` (b):

* `torusEmb` is an injective multiplicative embedding with nonzero coordinates;
* every character `(u, v) ↦ u^a v^b` is a polynomial `charMono a b` on the torus;
* polynomials in the torus coordinates become plane polynomials after clearing denominators
  (`exists_plane_clear`), and one-variable polynomials along a monomial curve
  (`exists_curve_clear`);
* in a prime ideal over an algebraically closed field, `M ^ n - 1` forces some `M - ζ`
  (`exists_sub_C_mem_of_pow_sub_one_mem`);
* a strict chain of two primes above a prime gives Krull dimension at least two
  (`two_le_ringKrullDim_quotient`).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C5 support).
-/

namespace AclGeom

open MvPolynomial

variable {k : Type*} [Field k]

/-- The standard closed embedding of the torus into `A⁴`: `(u, v) ↦ (u, v, u⁻¹, v⁻¹)`.-/
def torusEmb (g : kˣ × kˣ) : Fin 4 → k :=
  ![(g.1 : k), (g.2 : k), ((g.1⁻¹ : kˣ) : k), ((g.2⁻¹ : kˣ) : k)]

@[simp] theorem torusEmb_apply_zero (g : kˣ × kˣ) : torusEmb g 0 = g.1 := rfl

@[simp] theorem torusEmb_apply_one (g : kˣ × kˣ) : torusEmb g 1 = g.2 := rfl

@[simp] theorem torusEmb_apply_two (g : kˣ × kˣ) : torusEmb g 2 = ((g.1 : k))⁻¹ := by
  simp [torusEmb]

@[simp] theorem torusEmb_apply_three (g : kˣ × kˣ) : torusEmb g 3 = ((g.2 : k))⁻¹ := by
  simp [torusEmb]

theorem torusEmb_injective : Function.Injective (torusEmb (k := k)) := fun _ _ hgh ↦
  Prod.ext (Units.ext (congrFun hgh 0)) (Units.ext (congrFun hgh 1))

theorem torusEmb_mul (g h : kˣ × kˣ) : torusEmb (g * h) = torusEmb g * torusEmb h := by
  funext j
  fin_cases j <;> simp [mul_comm]

theorem torusEmb_inv (g : kˣ × kˣ) : torusEmb g⁻¹ = (torusEmb g)⁻¹ := by
  funext j
  fin_cases j <;> simp

theorem torusEmb_ne_zero (g : kˣ × kˣ) (j : Fin 4) : torusEmb g j ≠ 0 := by
  fin_cases j <;> simp

/-- An integer power through its positive and negative parts.-/
theorem zpow_eq_pow_toNat_mul_inv_pow {G : Type*} [DivisionMonoid G] (a : G) (z : ℤ) :
    a ^ z = a ^ z.toNat * a⁻¹ ^ (-z).toNat := by
  cases z with
  | ofNat n => simp
  | negSucc n => simp [zpow_negSucc, inv_pow]

/-- The torus monomial representing the character `(u, v) ↦ u ^ a * v ^ b`.-/
noncomputable def charMono (a b : ℤ) : MvPolynomial (Fin 4) k :=
  X 0 ^ a.toNat * X 2 ^ (-a).toNat * X 1 ^ b.toNat * X 3 ^ (-b).toNat

theorem aeval_charMono (a b : ℤ) (g : kˣ × kˣ) :
    aeval (torusEmb g) (charMono (k := k) a b) = ((g.1 ^ a * g.2 ^ b : kˣ) : k) := by
  simp only [charMono, map_mul, map_pow, aeval_X, torusEmb_apply_zero, torusEmb_apply_one,
    torusEmb_apply_two, torusEmb_apply_three, Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [zpow_eq_pow_toNat_mul_inv_pow, zpow_eq_pow_toNat_mul_inv_pow]
  ring

/-- **Clearing denominators on the torus**: a polynomial in the torus coordinates agrees on the
torus, up to a power of `u v`, with a polynomial in `u, v`.-/
theorem exists_plane_clear (f : MvPolynomial (Fin 4) k) :
    ∃ (N : ℕ) (q : MvPolynomial (Fin 2) k), ∀ g : kˣ × kˣ,
      aeval ![(g.1 : k), (g.2 : k)] q = ((g.1 : k) * g.2) ^ N * aeval (torusEmb g) f := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, fun g ↦ by simp⟩
  | add p q hp hq =>
    obtain ⟨N, P, hP⟩ := hp
    obtain ⟨M, Q, hQ⟩ := hq
    refine ⟨N + M, P * (X 0 * X 1) ^ M + Q * (X 0 * X 1) ^ N, fun g ↦ ?_⟩
    simp only [map_add, map_mul, map_pow, aeval_X, hP, hQ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  | mul_X p n hp =>
    obtain ⟨N, P, hP⟩ := hp
    fin_cases n
    · refine ⟨N, P * X 0, fun g ↦ ?_⟩
      simp only [map_mul, aeval_X, hP]
      simp
      ring
    · refine ⟨N, P * X 1, fun g ↦ ?_⟩
      simp only [map_mul, aeval_X, hP]
      simp
      ring
    · refine ⟨N + 1, P * X 1, fun g ↦ ?_⟩
      have h1 : (g.1 : k) ≠ 0 := g.1.ne_zero
      simp only [map_mul, aeval_X, hP]
      simp
      field_simp
      ring
    · refine ⟨N + 1, P * X 0, fun g ↦ ?_⟩
      have h2 : (g.2 : k) ≠ 0 := g.2.ne_zero
      simp only [map_mul, aeval_X, hP]
      simp
      field_simp
      ring

/-- **Clearing denominators along a monomial curve**: a polynomial evaluated along
`t ↦ (t ^ e j)ⱼ` agrees, up to a power of `t`, with a one-variable polynomial.-/
theorem exists_curve_clear (e : Fin 4 → ℤ) (f : MvPolynomial (Fin 4) k) :
    ∃ (N : ℕ) (φ : Polynomial k), ∀ t : kˣ,
      φ.eval (t : k) = (t : k) ^ N * aeval (fun j ↦ ((t ^ e j : kˣ) : k)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, Polynomial.C a, fun t ↦ by simp⟩
  | add p q hp hq =>
    obtain ⟨N, φ, hφ⟩ := hp
    obtain ⟨M, ψ, hψ⟩ := hq
    refine ⟨N + M, φ * Polynomial.X ^ M + ψ * Polynomial.X ^ N, fun t ↦ ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, hφ, hψ, map_add]
    ring
  | mul_X p j hp =>
    obtain ⟨N, φ, hφ⟩ := hp
    refine ⟨N + (-(e j)).toNat, φ * Polynomial.X ^ (e j).toNat, fun t ↦ ?_⟩
    have hz : ((t ^ e j : kˣ) : k) * (t : k) ^ (-(e j)).toNat = (t : k) ^ (e j).toNat := by
      rw [Units.val_zpow_eq_zpow_val, zpow_eq_pow_toNat_mul_inv_pow, mul_assoc, ← mul_pow,
        inv_mul_cancel₀ t.ne_zero, one_pow, mul_one]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hφ, map_mul,
      aeval_X]
    rw [← hz]
    ring

/-- In a prime ideal over an algebraically closed field, `M ^ n - 1` forces some `M - ζ`.-/
theorem exists_sub_C_mem_of_pow_sub_one_mem [IsAlgClosed k] {σ : Type*}
    {J : Ideal (MvPolynomial σ k)} (hJ : J.IsPrime) (M : MvPolynomial σ k) {n : ℕ}
    (hn : n ≠ 0) (hM : M ^ n - 1 ∈ J) : ∃ ζ : k, M - C ζ ∈ J := by
  classical
  set q : Polynomial k := Polynomial.X ^ n - Polynomial.C 1 with hqdef
  have hmonic : q.Monic := Polynomial.monic_X_pow_sub_C 1 hn
  have hq : q = (q.roots.map fun ζ ↦ Polynomial.X - Polynomial.C ζ).prod :=
    (IsAlgClosed.splits q).eq_prod_roots_of_monic hmonic
  have himg : Polynomial.aeval M q = M ^ n - 1 := by
    simp [q]
  rw [← himg, hq, map_multiset_prod, Multiset.map_map] at hM
  obtain ⟨y, hy, hyJ⟩ := (hJ.multiset_prod_mem_iff_exists_mem _).1 hM
  obtain ⟨ζ, -, rfl⟩ := Multiset.mem_map.1 hy
  refine ⟨ζ, ?_⟩
  simpa [Function.comp, MvPolynomial.algebraMap_eq] using hyJ

/-- A strict chain of two primes above a prime ideal gives Krull dimension at least two.-/
theorem two_le_ringKrullDim_quotient {R : Type*} [CommRing R] {P p₁ p₂ : Ideal R}
    [P.IsPrime] [p₁.IsPrime] [p₂.IsPrime] (h₁ : P < p₁) (h₂ : p₁ < p₂) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P) := by
  rw [ringKrullDim_quotient]
  let a : PrimeSpectrum.zeroLocus (R := R) (P : Set R) := ⟨⟨P, inferInstance⟩, fun _ h ↦ h⟩
  let b : PrimeSpectrum.zeroLocus (R := R) (P : Set R) :=
    ⟨⟨p₁, inferInstance⟩, fun _ h ↦ h₁.le h⟩
  let c : PrimeSpectrum.zeroLocus (R := R) (P : Set R) :=
    ⟨⟨p₂, inferInstance⟩, fun _ h ↦ (h₁.trans h₂).le h⟩
  have hab : a < b := h₁
  have hbc : b < c := h₂
  let s : LTSeries (PrimeSpectrum.zeroLocus (R := R) (P : Set R)) :=
    ⟨2, ![a, b, c], fun i ↦ by fin_cases i <;> simp [hab, hbc]⟩
  have := Order.LTSeries.length_le_krullDim s
  exact_mod_cast this

end AclGeom
