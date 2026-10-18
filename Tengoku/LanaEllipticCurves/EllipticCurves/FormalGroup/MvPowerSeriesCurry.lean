/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.PowerSeriesBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Currying `MvPowerSeries (Fin 2) R` as `PowerSeries (PowerSeries R)` and multiplicative transport

The double-coefficient reader `HahnSeries.ofDoubleLaurent : (R⸨X⸩)⸨X⸩ → MvPowerSeries (Fin 2) R`
of `PowerSeriesBridge.lean` is only *additive* in general; it becomes multiplicative once restricted
to iterated Laurent series that are pole-free in **both** gradings.  This file supplies the algebra
that upgrades the faithful embedding `embedDoubleLaurent` to a **ring homomorphism**, so that
multiplicative identities in `(R⸨X⸩)⸨X⸩` transport to `MvPowerSeries (Fin 2) R` on the pole-free
subring.  This is the transport tool the downstream commutativity (#283) and associativity /
`FormalGroup` packaging (#263) consume.

## Main definitions and results

* `mvPowerSeriesFinTwoCurry : MvPowerSeries (Fin 2) R ≃+* PowerSeries (PowerSeries R)` — the
  currying ring isomorphism (Mathlib provides `MvPowerSeries.rename` but no `finSuccEquiv` / `curry`
  for `MvPowerSeries`), sending `φ` to `mk n => mk m => coeff (single 0 m + single 1 n) φ`
  (inner grading `z₁` = `Fin 2` index `0`, outer `z₂` = index `1`, matching the `ofDoubleLaurent`
  convention `(x.coeff (d 1)).coeff (d 0)`).  The genuine content is multiplicativity: the
  `MvPowerSeries.coeff_mul` bivariate convolution reindexed as an iterated univariate convolution.
* `HahnSeries.embedDoubleLaurentRingHom : MvPowerSeries (Fin 2) R →+* (R⸨X⸩)⸨X⸩` — the sibling
  writer `embedDoubleLaurent` packaged as a ring hom, `= ofPowerSeries ∘ map ofPowerSeries ∘ curry`.
* `HahnSeries.ofDoubleLaurent_mul_of_poleFree` — the transport corollary: on series pole-free in
  both gradings, `ofDoubleLaurent (x * y) = ofDoubleLaurent x * ofDoubleLaurent y`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1
  (context; this file is pure algebra).
-/

open scoped LaurentSeries

variable {R : Type*} [CommRing R]

namespace MvPowerSeries

/-! ### Coordinate arithmetic for `Fin 2 →₀ ℕ` -/

private lemma single_add_apply_zero (m n : ℕ) :
    (Finsupp.single (0 : Fin 2) m + Finsupp.single (1 : Fin 2) n) (0 : Fin 2) = m := by
  rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide), add_zero]

private lemma single_add_apply_one (m n : ℕ) :
    (Finsupp.single (0 : Fin 2) m + Finsupp.single (1 : Fin 2) n) (1 : Fin 2) = n := by
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by decide), Finsupp.single_eq_same, zero_add]

private lemma finTwo_single_decomp (d : Fin 2 →₀ ℕ) :
    Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) = d := by
  ext i; fin_cases i <;> simp

private lemma single_add_eq_zero_iff (m n : ℕ) :
    (Finsupp.single (0 : Fin 2) m + Finsupp.single (1 : Fin 2) n = 0) ↔ (m = 0 ∧ n = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := congrArg (fun f => f (0 : Fin 2)) h
      rwa [single_add_apply_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    · have := congrArg (fun f => f (1 : Fin 2)) h
      rwa [single_add_apply_one, Finsupp.coe_zero, Pi.zero_apply] at this
  · rintro ⟨rfl, rfl⟩; simp

/-! ### The currying function and its bigraded coefficient -/

/-- The underlying function of the currying isomorphism: read `φ : MvPowerSeries (Fin 2) R` as an
iterated power series whose `z₂^n z₁^m` coefficient is `coeff (single 0 m + single 1 n) φ`. -/
noncomputable def curryFinTwoFun (φ : MvPowerSeries (Fin 2) R) : PowerSeries (PowerSeries R) :=
  PowerSeries.mk fun n => PowerSeries.mk fun m =>
    MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 n) φ

@[simp]
theorem coeff_coeff_curryFinTwoFun (φ : MvPowerSeries (Fin 2) R) (n m : ℕ) :
    PowerSeries.coeff m (PowerSeries.coeff n (curryFinTwoFun φ))
      = MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 n) φ := by
  simp only [curryFinTwoFun, PowerSeries.coeff_mk]

theorem curryFinTwoFun_add (φ ψ : MvPowerSeries (Fin 2) R) :
    curryFinTwoFun (φ + ψ) = curryFinTwoFun φ + curryFinTwoFun ψ := by
  refine PowerSeries.ext fun n => PowerSeries.ext fun m => ?_
  simp [map_add]

theorem curryFinTwoFun_zero : curryFinTwoFun (0 : MvPowerSeries (Fin 2) R) = 0 := by
  refine PowerSeries.ext fun n => PowerSeries.ext fun m => ?_
  simp

theorem curryFinTwoFun_one : curryFinTwoFun (1 : MvPowerSeries (Fin 2) R) = 1 := by
  classical
  refine PowerSeries.ext fun n => PowerSeries.ext fun m => ?_
  rw [coeff_coeff_curryFinTwoFun, MvPowerSeries.coeff_one, PowerSeries.coeff_one]
  by_cases hn : n = 0
  · subst hn
    rw [ite_eq_left rfl, PowerSeries.coeff_one]
    by_cases hm : m = 0
    · subst hm; rw [ite_eq_left rfl, ite_eq_left ((single_add_eq_zero_iff 0 0).2 ⟨rfl, rfl⟩)]
    · rw [ite_eq_right hm, ite_eq_right (fun h => hm ((single_add_eq_zero_iff m 0).1 h).1)]
  · rw [ite_eq_right hn, map_zero, ite_eq_right (fun h => hn ((single_add_eq_zero_iff m n).1 h).2)]

/-- **Multiplicativity** (the genuine content): the bivariate convolution `MvPowerSeries.coeff_mul`
reindexed as an iterated univariate convolution. -/
theorem curryFinTwoFun_mul (φ ψ : MvPowerSeries (Fin 2) R) :
    curryFinTwoFun (φ * ψ) = curryFinTwoFun φ * curryFinTwoFun ψ := by
  classical
  refine PowerSeries.ext fun n => PowerSeries.ext fun m => ?_
  -- LHS: a single sum over `antidiagonal (single 0 m + single 1 n)`.
  -- RHS: nest `PowerSeries.coeff_mul` twice into a double sum, then merge to a product sum.
  rw [coeff_coeff_curryFinTwoFun, MvPowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  simp_rw [PowerSeries.coeff_mul, coeff_coeff_curryFinTwoFun]
  -- Merge the nested double sum into one sum over the product antidiagonal.
  have hprod :
      (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n ×ˢ Finset.HasAntidiagonal.antidiagonal m,
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) x.2.1 + Finsupp.single 1 x.1.1) φ
            * MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) x.2.2 + Finsupp.single 1 x.1.2) ψ)
        = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            ∑ q ∈ Finset.HasAntidiagonal.antidiagonal m,
              MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.1 + Finsupp.single 1 p.1) φ
                * MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.2 + Finsupp.single 1 p.2) ψ :=
    Finset.sum_product _ _ _
  rw [← hprod]
  -- Reindex the finsupp antidiagonal onto the product of the two Nat antidiagonals.
  refine Finset.sum_nbij'
    (i := fun a => ((a.1 1, a.2 1), (a.1 0, a.2 0)))
    (j := fun q => (Finsupp.single 0 q.2.1 + Finsupp.single 1 q.1.1,
                    Finsupp.single 0 q.2.2 + Finsupp.single 1 q.1.2))
    ?_ ?_ ?_ ?_ ?_
  · -- `i` maps the finsupp antidiagonal into the product of Nat antidiagonals
    rintro ⟨a, b⟩ ha
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha
    rw [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal,
      Finset.HasAntidiagonal.mem_antidiagonal]
    refine ⟨?_, ?_⟩
    · have := congrArg (fun f => f (1 : Fin 2)) ha
      simpa [single_add_apply_one] using this
    · have := congrArg (fun f => f (0 : Fin 2)) ha
      simpa [single_add_apply_zero] using this
  · -- `j` maps the product back into the finsupp antidiagonal
    rintro ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ hpq
    rw [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal,
      Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    obtain ⟨hp, hq⟩ := hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    ext i; fin_cases i <;> simp [Finsupp.add_apply] <;> omega
  · -- left inverse `j ∘ i = id` on the finsupp antidiagonal
    rintro ⟨a, b⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨finTwo_single_decomp a, finTwo_single_decomp b⟩
  · -- right inverse `i ∘ j = id` on the product
    rintro ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ _
    simp [single_add_apply_zero, single_add_apply_one]
  · -- the summands agree under the reindexing
    rintro ⟨a, b⟩ _
    rw [finTwo_single_decomp a, finTwo_single_decomp b]

/-- The currying map bundled as a `RingHom`. -/
noncomputable def curryFinTwoRingHom :
    MvPowerSeries (Fin 2) R →+* PowerSeries (PowerSeries R) where
  toFun := curryFinTwoFun
  map_one' := curryFinTwoFun_one
  map_mul' := curryFinTwoFun_mul
  map_zero' := curryFinTwoFun_zero
  map_add' := curryFinTwoFun_add

@[simp]
theorem curryFinTwoRingHom_apply (φ : MvPowerSeries (Fin 2) R) :
    curryFinTwoRingHom φ = curryFinTwoFun φ := rfl

end MvPowerSeries

namespace HahnSeries

/-! ### The faithful writer as a ring hom, and the multiplicative transport corollary -/

/-- The faithful writer `embedDoubleLaurent` packaged as a **ring homomorphism**, factored as
`ofPowerSeries ∘ map ofPowerSeries ∘ curry`.  Its underlying function is `embedDoubleLaurent`
(`embedDoubleLaurentRingHom_apply`). -/
noncomputable def embedDoubleLaurentRingHom :
    MvPowerSeries (Fin 2) R →+* (R⸨X⸩)⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ (R⸨X⸩)).comp
    ((PowerSeries.map (HahnSeries.ofPowerSeries ℤ R)).comp
      MvPowerSeries.curryFinTwoRingHom)

theorem embedDoubleLaurentRingHom_apply (φ : MvPowerSeries (Fin 2) R) :
    embedDoubleLaurentRingHom φ = embedDoubleLaurent φ := by
  rw [embedDoubleLaurentRingHom, RingHom.comp_apply, RingHom.comp_apply, embedDoubleLaurent]
  refine congrArg (HahnSeries.ofPowerSeries ℤ (R⸨X⸩)) (PowerSeries.ext fun n => ?_)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  refine congrArg (HahnSeries.ofPowerSeries ℤ R) (PowerSeries.ext fun m => ?_)
  rw [PowerSeries.coeff_mk, MvPowerSeries.curryFinTwoRingHom_apply]
  exact MvPowerSeries.coeff_coeff_curryFinTwoFun φ n m

/-- **Multiplicative transport.** On iterated Laurent series pole-free in both gradings, the reader
`ofDoubleLaurent` is multiplicative:
`ofDoubleLaurent (x * y) = ofDoubleLaurent x * ofDoubleLaurent y` (with both `x`, `y` pole-free in
both gradings).  This is the tool #283 / #263 consume. -/
theorem ofDoubleLaurent_mul_of_poleFree {x y : (R⸨X⸩)⸨X⸩}
    (hxout : ∀ n < 0, x.coeff n = 0) (hxin : ∀ (n : ℤ), ∀ g < 0, (x.coeff n).coeff g = 0)
    (hyout : ∀ n < 0, y.coeff n = 0) (hyin : ∀ (n : ℤ), ∀ g < 0, (y.coeff n).coeff g = 0) :
    ofDoubleLaurent (x * y) = ofDoubleLaurent x * ofDoubleLaurent y := by
  have hx : embedDoubleLaurent (ofDoubleLaurent x) = x :=
    embedDoubleLaurent_ofDoubleLaurent hxout hxin
  have hy : embedDoubleLaurent (ofDoubleLaurent y) = y :=
    embedDoubleLaurent_ofDoubleLaurent hyout hyin
  calc ofDoubleLaurent (x * y)
      = ofDoubleLaurent
          (embedDoubleLaurent (ofDoubleLaurent x) * embedDoubleLaurent (ofDoubleLaurent y)) := by
        rw [hx, hy]
    _ = ofDoubleLaurent
          (embedDoubleLaurentRingHom (ofDoubleLaurent x)
            * embedDoubleLaurentRingHom (ofDoubleLaurent y)) := by
        rw [embedDoubleLaurentRingHom_apply, embedDoubleLaurentRingHom_apply]
    _ = ofDoubleLaurent (embedDoubleLaurentRingHom (ofDoubleLaurent x * ofDoubleLaurent y)) := by
        rw [← map_mul]
    _ = ofDoubleLaurent (embedDoubleLaurent (ofDoubleLaurent x * ofDoubleLaurent y)) := by
        rw [embedDoubleLaurentRingHom_apply]
    _ = ofDoubleLaurent x * ofDoubleLaurent y := ofDoubleLaurent_embedDoubleLaurent _

end HahnSeries
