/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
module

public import Tengoku.LeanPool.LeanPool.LehmerE10.Main
public import Tengoku
import Tengoku.LeanPool.LeanPool.LehmerE10.Kronecker

/-!
# the Mahler measure of Lehmer's polynomial, in Mathlib's own API.
Mathlib now has the Mahler measure (`Polynomial.mahlerMeasure`, Jensen-formula definition,
with `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`), Kronecker's theorem in Mahler form,
and Northcott's theorem.  This file connects the repository to that API:
* `lehmer_mahlerMeasure` : `M(L) = μ` — the Mahler measure of Lehmer's polynomial is
  exactly the Salem root, computed (not estimated) from the root classification: eight
  roots on the unit circle contribute `1`, `ν = 1/μ` lies inside, and `μ` alone lies
  outside.
* `one_lt_lehmer_mahlerMeasure`, `lehmer_mahlerMeasure_lt` : `1 < M(L) < 7/5`, from the
  interval `y₅ ∈ (2, 21/10)` already isolated by the trace-quintic sign changes.
* `LehmerConjecture`, `LehmerMinimal` : Lehmer's 1933 question, *stated* in Mathlib's
  vocabulary (a hypothesis `Prop`, not claimed, not assumed): Mahler measures of integer
  polynomials do not accumulate at `1`; strongly, `L` attains the minimum.
  `lehmerConjecture_of_minimal` : the strong form implies the gap form, with the gap
  witnessed by `M(L)` itself — which is `> 1` by this file.
* `coxeterE10_infinite_order` : the E₁₀ Coxeter element has infinite order in
  `GL(10, ℤ)`.  If `Cox^n = 1` then, since its characteristic polynomial `L` is
  irreducible, `L` would be the minimal polynomial and would divide `Xⁿ − 1`; but `μ` is
  a root of `L` with `μ > 1`, and every root of `Xⁿ − 1` has norm `1`.
Together with `coxeterE8_*` facts (finite case) this locates E₁₀ precisely: the Coxeter
series crosses from torsion (spectrum on the unit circle) to a Salem element exactly at
rank 10, and the crossing value is Lehmer's number.
-/

@[expose] public section

open Polynomial

namespace LehmerE10

/-! ### The Mahler measure of `L` is the Salem root `μ`. -/

/-- The classified product with `max 1 ‖·‖` weights: unit-circle roots contribute `1`,
`ν < 1` contributes `1`, and each occurrence of `μ` contributes `μ`.
@isnad1 id=eq.1h1v.s6.5ce2c47830aa from=translated src=- shape=1e80d324 vocab=d507df48
-/
lemma classified_prod_max (S : Multiset ℂ)
    (hS : ∀ z ∈ S, ‖z‖ = 1 ∨ z = (mu : ℂ) ∨ z = (nu : ℂ)) :
    (S.map fun z => max 1 ‖z‖).prod = mu ^ S.count (mu : ℂ) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have hs' : ∀ z ∈ s, ‖z‖ = 1 ∨ z = (mu : ℂ) ∨ z = (nu : ℂ) :=
      fun z hz => hS z (Multiset.mem_cons_of_mem hz)
    have ihs := ih hs'
    rcases hS a (Multiset.mem_cons_self a s) with h1 | rfl | rfl
    · have hamu : (mu : ℂ) ≠ a := by
        intro h; rw [← h, norm_muC] at h1; linarith [mu_gt_one]
      rw [Multiset.map_cons, Multiset.prod_cons, h1, max_self, one_mul, ihs,
        Multiset.count_cons_of_ne hamu]
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_muC,
        max_eq_right (le_of_lt mu_gt_one), ihs, Multiset.count_cons_self, pow_succ]
      ring
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_nuC,
        max_eq_left (le_of_lt nu_lt_one), one_mul, ihs,
        Multiset.count_cons_of_ne muC_ne_nuC]

/-- **The Mahler measure of Lehmer's polynomial is the Salem root**: `M(L) = μ`.
Computed exactly from `mahlerMeasure_eq_leadingCoeff_mul_prod_roots` and the root
classification — this is the number `≈ 1.17628`, the smallest known Mahler measure `> 1`
of an integer polynomial.
@isnad1 id=eq.0h0v.s2.99a91f148b40 from=translated src=- shape=4b736592 vocab=cc055256
-/
theorem lehmer_mahlerMeasure : LC.mahlerMeasure = mu := by
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, LC_monic.leadingCoeff, norm_one, one_mul,
    classified_prod_max LC.roots (fun z hz => root_classification hz), count_muC, pow_one]

/-- `M(L) > 1`: Lehmer's polynomial is not a product of cyclotomics, quantitatively.
@isnad1 id=lt.0h0v.s3.9e8b35177f30 from=translated src=- shape=a1bca669 vocab=bcbcf9bf
-/
theorem one_lt_lehmer_mahlerMeasure : 1 < LC.mahlerMeasure :=
  lehmer_mahlerMeasure ▸ mu_gt_one

/-- The Salem square root is below `7/10`: `s₅² = y₅² − 4 < (21/10)² − 4 < (7/10)²`.
@isnad1 id=lt.0h0v.s4.5d5ab7279e97 from=translated src=- shape=0efb1284 vocab=54152fa5
-/
lemma s5_lt : s5 < 7 / 10 := by
  have h5 := Set.mem_Ioo.mp y5_mem
  have hs := s5_sq
  have hpos := s5_pos
  nlinarith [hs, h5.1, h5.2, hpos]

/-- `M(L) < 7/5`: an unconditional upper bound from the trace-root interval.  (The true
value is `1.17628…`; sharper bounds need only a tighter sign-change interval for `y₅`.)
@isnad1 id=lt.0h0v.s4.3b51a5a588b2 from=translated src=- shape=c29dca45 vocab=b8d949e2
-/
theorem lehmer_mahlerMeasure_lt : LC.mahlerMeasure < 7 / 5 := by
  rw [lehmer_mahlerMeasure]
  have h5 := Set.mem_Ioo.mp y5_mem
  have hs := s5_lt
  unfold mu
  linarith

/-! ### Lehmer's question, stated in Mathlib's vocabulary.

Both are hypothesis `Prop`s: *stated*, never claimed, never assumed. -/

/-- **Lehmer's conjecture** (Lehmer 1933, gap form): Mahler measures of integer polynomials
do not accumulate at `1` — there is a uniform gap `c > 1` below which the only Mahler
measure is `1` itself. -/
def LehmerConjecture : Prop :=
  ∃ c : ℝ, 1 < c ∧ ∀ p : Polynomial ℤ,
    1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure →
    c ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure

/-- The strong form: Lehmer's polynomial attains the minimal Mahler measure `> 1`. -/
def LehmerMinimal : Prop :=
  ∀ p : Polynomial ℤ, 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure →
    LC.mahlerMeasure ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure

/-- The strong form implies the gap form, with the gap witnessed by `M(L)` itself —
legitimate because `M(L) > 1` is proven above.
@isnad1 id=lehmerco.1h0v.s1.515c98f9fb87 from=translated src=- shape=1d48f1ac vocab=d8ef671b
-/
theorem lehmerConjecture_of_minimal (h : LehmerMinimal) : LehmerConjecture :=
  ⟨LC.mahlerMeasure, one_lt_lehmer_mahlerMeasure, fun p hp => h p hp⟩

/-! ### The Coxeter element has infinite order. -/

/-- **The E₁₀ Coxeter element has infinite order.**  If `Cox^n = 1`, then since its
characteristic polynomial is the irreducible `L`, the minimal polynomial is `L` and
divides `Xⁿ − 1`; evaluating at the Salem root `μ > 1` gives `μⁿ = 1`, impossible.

Contrast: the Coxeter element of a *finite* Weyl group has order `h` (the Coxeter number
— `30` for E₈); at E₁₀ the spectrum has left the unit circle and no power returns.
@isnad1 id=ne.1h1v.s7.8e281af0a921 from=translated src=- shape=4c148e2d vocab=3123f698
-/
theorem coxeterE10_infinite_order {n : ℕ} (hn : 0 < n) : coxeterE10 ^ n ≠ 1 := by
  intro hpow
  -- move to ℚ
  have hpowq : (coxeterE10.map (Int.castRingHom ℚ)) ^ n = 1 := by
    have h := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℤ =>
      (Int.castRingHom ℚ).mapMatrix M) hpow
    simpa [map_pow, RingHom.mapMatrix_apply] using h
  set Cq : Matrix (Fin 10) (Fin 10) ℚ := coxeterE10.map (Int.castRingHom ℚ) with hCq
  -- the minimal polynomial of Cq is L (irreducible, monic, annihilating)
  set Lq : Polynomial ℚ := lehmerPolynomial.map (Int.castRingHom ℚ) with hLq
  have hLq_monic : Lq.Monic := lehmerPolynomial_monic.map _
  have haev : aeval Cq Lq = 0 := by
    have := Matrix.aeval_self_charpoly Cq
    rwa [coxeter_charpoly_rat] at this
  have hmin : minpoly ℚ Cq = Lq :=
    (minpoly.eq_of_irreducible_of_monic lehmer_irreducible_rat haev hLq_monic).symm
  -- L divides Xⁿ − 1
  have hannX : aeval Cq ((X : Polynomial ℚ) ^ n - 1) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, hpowq, sub_self]
  have hdvdQ : Lq ∣ (X : Polynomial ℚ) ^ n - 1 := hmin ▸ minpoly.dvd ℚ Cq hannX
  -- transport to ℂ and evaluate at μ
  have hdvdC : LC ∣ (X : Polynomial ℂ) ^ n - 1 := by
    have h := Polynomial.map_dvd (algebraMap ℚ ℂ) hdvdQ
    have hmapL : Lq.map (algebraMap ℚ ℂ) = LC := by
      rw [hLq, Polynomial.map_map]
      exact congrArg lehmerPolynomial.map (Subsingleton.elim _ _)
    have hmapX : ((X : Polynomial ℚ) ^ n - 1).map (algebraMap ℚ ℂ)
        = (X : Polynomial ℂ) ^ n - 1 := by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    rwa [hmapL, hmapX] at h
  obtain ⟨q, hq⟩ := hdvdC
  have hmu_root : LC.eval (mu : ℂ) = 0 := by
    have h := (mem_roots LC_ne_zero).mp muC_mem
    rwa [IsRoot.def] at h
  have hμn : ((mu : ℂ)) ^ n = 1 := by
    have h := congrArg (Polynomial.eval ((mu : ℝ) : ℂ)) hq
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, hmu_root, zero_mul] at h
    linear_combination h
  have hμnR : mu ^ n = 1 := by exact_mod_cast hμn
  have : (1 : ℝ) < mu ^ n := one_lt_pow₀ mu_gt_one hn.ne'
  linarith [hμnR ▸ this]

end LehmerE10
