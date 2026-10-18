/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.RingTheory.LaurentSeries
import Tengoku.Seed.RingTheory.MvPowerSeries.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reading a pole-free (iterated) Laurent series as a (bivariate) power series

This is a *curve-agnostic* algebraic toolbox for the Weierstrass formal group law construction
(issue #265). The formal group law is built as an element of the iterated Laurent ring
`(R⸨X⸩)⸨X⸩ = HahnSeries ℤ (HahnSeries ℤ R)` (outer grading `z₂`, inner grading `z₁`); to recognise
it as a genuine bivariate power series one needs two bridges that Mathlib does not provide:

* an **order-`≥0` extraction** turning a Laurent series `x : R⸨X⸩` with no negative-index
  coefficients back into (the coercion of) an honest power series, and
* a **double-coefficient reader** `ofDoubleLaurent` sending an iterated Laurent series to
  `MvPowerSeries (Fin 2) R` by reading off its bigraded coefficients.

Both are stated over an arbitrary `CommRing R`; in particular the extraction lemma applies at the
inner level too (take the coefficient ring to be `R⸨X⸩`).

## Main results

* `HahnSeries.ofPowerSeries_mk_coeff_eq_self` : if `x : R⸨X⸩` has `x.coeff g = 0` for all `g < 0`,
  then `HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk fun n => x.coeff n) = x`.
* `HahnSeries.ofDoubleLaurent` : the reader `(R⸨X⸩)⸨X⸩ → MvPowerSeries (Fin 2) R`,
  `d ↦ (x.coeff (d 1)).coeff (d 0)`, with `coeff_ofDoubleLaurent`,
  `constantCoeff_ofDoubleLaurent`, and the linear-slice lemmas
  `coeff_ofDoubleLaurent_single_zero`, `coeff_ofDoubleLaurent_single_one`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1
  (context; this file itself is pure algebra).
-/

open scoped LaurentSeries

namespace HahnSeries

variable {R : Type*} [CommRing R]

/-! ### Order-`≥0` extraction: a pole-free Laurent series is a coerced power series -/

/-- A Laurent series `x : R⸨X⸩` with no negative-index coefficients is exactly the coercion of the
power series reading off its non-negative coefficients. This is the (missing in Mathlib) partial
inverse to `HahnSeries.ofPowerSeries` on order-`≥0` series. -/
theorem ofPowerSeries_mk_coeff_eq_self {x : R⸨X⸩} (h : ∀ g < 0, x.coeff g = 0) :
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk fun n => x.coeff (n : ℤ)) = x := by
  ext g
  rcases lt_or_ge g 0 with hg | hg
  · rw [h g hg, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
    rintro ⟨n, hn⟩
    simp only [Nat.castOrderEmbedding, OrderEmbedding.coe_ofStrictMono] at hn
    omega
  · lift g to ℕ using hg with n
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

/-! ### The double-coefficient reader `(R⸨X⸩)⸨X⸩ → MvPowerSeries (Fin 2) R` -/

/-- Read an iterated Laurent series `x ∈ (R⸨X⸩)⸨X⸩` as a bivariate power series: the coefficient of
`z₁^(d 0) z₂^(d 1)` is the inner `z₁`-coefficient `(x.coeff (d 1)).coeff (d 0)` of `x`. When `x` is
pole-free in both gradings this loses no information. -/
noncomputable def ofDoubleLaurent (x : (R⸨X⸩)⸨X⸩) : MvPowerSeries (Fin 2) R :=
  fun d => (x.coeff (d 1 : ℤ)).coeff (d 0 : ℤ)

@[simp]
theorem coeff_ofDoubleLaurent (x : (R⸨X⸩)⸨X⸩) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (ofDoubleLaurent x) = (x.coeff (d 1 : ℤ)).coeff (d 0 : ℤ) :=
  rfl

/-- The constant coefficient of `ofDoubleLaurent x` is the doubly-`0`-indexed coefficient of `x`. -/
theorem constantCoeff_ofDoubleLaurent (x : (R⸨X⸩)⸨X⸩) :
    MvPowerSeries.constantCoeff (ofDoubleLaurent x) = (x.coeff (0 : ℤ)).coeff (0 : ℤ) := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_ofDoubleLaurent]
  simp

/-- The `z₁`-linear (`z₂`-constant) coefficient of `ofDoubleLaurent x` reads the `z₁`-degree-`k`
part of the order-`0` slice `x.coeff 0`. -/
theorem coeff_ofDoubleLaurent_single_zero (x : (R⸨X⸩)⸨X⸩) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 k) (ofDoubleLaurent x)
      = (x.coeff (0 : ℤ)).coeff (k : ℤ) := by
  rw [coeff_ofDoubleLaurent]
  simp

/-- The `z₂`-linear (`z₁`-constant) coefficient of `ofDoubleLaurent x` reads the `z₁`-degree-`0`
part of the `z₂`-degree-`k` slice `x.coeff k`. -/
theorem coeff_ofDoubleLaurent_single_one (x : (R⸨X⸩)⸨X⸩) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 1 k) (ofDoubleLaurent x)
      = (x.coeff (k : ℤ)).coeff (0 : ℤ) := by
  rw [coeff_ofDoubleLaurent]
  simp

/-! ### Basic additive algebra of the reader `ofDoubleLaurent`

Reading a bigraded coefficient is `ℤ`-linear, so `ofDoubleLaurent` is an additive map (it is *not*
multiplicative on all of `(R⸨X⸩)⸨X⸩` — that holds only on the pole-free-in-both subring, cf. the
faithful embedding below). -/

@[simp]
theorem ofDoubleLaurent_add (x y : (R⸨X⸩)⸨X⸩) :
    ofDoubleLaurent (x + y) = ofDoubleLaurent x + ofDoubleLaurent y := by
  refine MvPowerSeries.ext fun d => ?_
  simp only [map_add, coeff_ofDoubleLaurent, HahnSeries.coeff_add]

@[simp]
theorem ofDoubleLaurent_zero : ofDoubleLaurent (0 : (R⸨X⸩)⸨X⸩) = 0 := by
  refine MvPowerSeries.ext fun d => ?_
  simp only [map_zero, coeff_ofDoubleLaurent, HahnSeries.coeff_zero]

@[simp]
theorem ofDoubleLaurent_neg (x : (R⸨X⸩)⸨X⸩) :
    ofDoubleLaurent (-x) = -ofDoubleLaurent x := by
  refine MvPowerSeries.ext fun d => ?_
  simp only [map_neg, coeff_ofDoubleLaurent, HahnSeries.coeff_neg]

/-- The double constant `HahnSeries.C (HahnSeries.C a) = C₂ a ∈ (R⸨X⸩)⸨X⸩` is read as the
`MvPowerSeries` constant `MvPowerSeries.C a`. -/
theorem ofDoubleLaurent_C₂ (a : R) :
    ofDoubleLaurent (HahnSeries.C (HahnSeries.C a)) = MvPowerSeries.C a := by
  classical
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_ofDoubleLaurent, MvPowerSeries.coeff_C, HahnSeries.C_apply, HahnSeries.coeff_single]
  by_cases h1 : ((d 1 : ℕ) : ℤ) = 0
  · rw [ite_eq_left h1, HahnSeries.C_apply, HahnSeries.coeff_single]
    by_cases h0 : ((d 0 : ℕ) : ℤ) = 0
    · have hd : d = 0 := by
        ext i; fin_cases i
        · exact_mod_cast h0
        · exact_mod_cast h1
      rw [ite_eq_left h0, ite_eq_left hd]
    · have hd : d ≠ 0 := fun h => h0 (by rw [h]; simp)
      rw [ite_eq_right h0, ite_eq_right hd]
  · rw [ite_eq_right h1, HahnSeries.coeff_zero]
    have hd : d ≠ 0 := fun h => h1 (by rw [h]; simp)
    rw [ite_eq_right hd]

theorem ofDoubleLaurent_one : ofDoubleLaurent (1 : (R⸨X⸩)⸨X⸩) = 1 := by
  have h : (1 : (R⸨X⸩)⸨X⸩) = HahnSeries.C (HahnSeries.C (1 : R)) := by
    rw [map_one, map_one]
  rw [h, ofDoubleLaurent_C₂, map_one]

/-! ### The faithful writer `MvPowerSeries (Fin 2) R → (R⸨X⸩)⸨X⸩` and the round-trip identities

The partial inverse of `ofDoubleLaurent`: write a bivariate power series into the iterated Laurent
ring by two applications of `HahnSeries.ofPowerSeries`. It is a *right* inverse always
(`ofDoubleLaurent_embedDoubleLaurent`) and a *left* inverse on iterated Laurent series that are
pole-free in **both** gradings (`embedDoubleLaurent_ofDoubleLaurent`) — the faithfulness that makes
`ofDoubleLaurent` lossless on such series. -/

/-- Write a bivariate power series `φ` as an iterated Laurent series: the `z₁^m z₂^n` coefficient is
`MvPowerSeries.coeff (single 0 m + single 1 n) φ`, packaged through two `HahnSeries.ofPowerSeries`
casts (inner grading `z₁` = `Fin 2` index `0`, outer grading `z₂` = index `1`). -/
noncomputable def embedDoubleLaurent (φ : MvPowerSeries (Fin 2) R) : (R⸨X⸩)⸨X⸩ :=
  ofPowerSeries ℤ (R⸨X⸩)
    (PowerSeries.mk fun n => ofPowerSeries ℤ R
      (PowerSeries.mk fun m => MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 n) φ))

private lemma finTwo_single_apply_one (m n : ℕ) :
    (Finsupp.single (0 : Fin 2) m + Finsupp.single (1 : Fin 2) n) (1 : Fin 2) = n := by
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by decide), Finsupp.single_eq_same, zero_add]

private lemma finTwo_single_apply_zero (m n : ℕ) :
    (Finsupp.single (0 : Fin 2) m + Finsupp.single (1 : Fin 2) n) (0 : Fin 2) = m := by
  rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide), add_zero]

private lemma finTwo_single_add (d : Fin 2 →₀ ℕ) :
    Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) = d := by
  ext i; fin_cases i <;> simp

/-- **Right inverse.** Reading back a written bivariate power series recovers it:
`ofDoubleLaurent (embedDoubleLaurent φ) = φ`. -/
theorem ofDoubleLaurent_embedDoubleLaurent (φ : MvPowerSeries (Fin 2) R) :
    ofDoubleLaurent (embedDoubleLaurent φ) = φ := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_ofDoubleLaurent, embedDoubleLaurent, ofPowerSeries_apply_coeff, PowerSeries.coeff_mk,
    ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, finTwo_single_add]

/-- **Left inverse on the pole-free-in-both subring.** If `x ∈ (R⸨X⸩)⸨X⸩` has no negative outer
coefficients (`hout`) and each of its outer slices has no negative inner coefficients (`hin`), then
writing back the read bivariate power series recovers `x`:
`embedDoubleLaurent (ofDoubleLaurent x) = x`. This is the faithful embedding property: on series
pole-free in both gradings, `ofDoubleLaurent` loses no information. -/
theorem embedDoubleLaurent_ofDoubleLaurent {x : (R⸨X⸩)⸨X⸩}
    (hout : ∀ n < 0, x.coeff n = 0) (hin : ∀ (n : ℤ), ∀ g < 0, (x.coeff n).coeff g = 0) :
    embedDoubleLaurent (ofDoubleLaurent x) = x := by
  rw [embedDoubleLaurent]
  -- Each outer slice collapses to `x.coeff n` by the (inner) order-`≥0` extraction lemma.
  have hinner : (PowerSeries.mk fun n => ofPowerSeries ℤ R
      (PowerSeries.mk fun m =>
        MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 n) (ofDoubleLaurent x)))
      = PowerSeries.mk fun n => x.coeff (n : ℤ) := by
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    have hmk : (PowerSeries.mk fun m =>
        MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 n) (ofDoubleLaurent x))
        = PowerSeries.mk fun m => (x.coeff (n : ℤ)).coeff (m : ℤ) := by
      refine PowerSeries.ext fun m => ?_
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, coeff_ofDoubleLaurent,
        finTwo_single_apply_one, finTwo_single_apply_zero]
    rw [hmk]
    exact ofPowerSeries_mk_coeff_eq_self (hin (n : ℤ))
  rw [hinner]
  exact ofPowerSeries_mk_coeff_eq_self hout

end HahnSeries
