/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Step

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# recursive Hensel iterates

This file records the recursive polynomial iterates used in the proof
of Hensel's lemma and the coefficientwise adic estimates needed for the later
completion argument.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- the recursive polynomial sequence
`F_{n+1}=F_n+π^(n+1)c_{n+1}` used for either factor in Hensel's iteration.-/
def henselFactorization_henselIterate {R : Type*} [CommRing R]
    (π : R) (F0 : R[X]) (corr : ℕ → R[X]) : ℕ → R[X]
  | 0 => F0
  | n + 1 =>
      henselFactorization_henselIterate π F0 corr n +
        Polynomial.C (π ^ (n + 1)) * corr (n + 1)

/--
@isnad1 id=eq.0h4v.s5.623bfc434902 from=translated src=- shape=9f86e5b5 vocab=bc3c8a07
-/
@[simp]
theorem henselFactorization_henselIterate_zero
    {R : Type*} [CommRing R] (π : R) (F0 : R[X]) (corr : ℕ → R[X]) :
    henselFactorization_henselIterate π F0 corr 0 = F0 :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.c43236639156 from=translated src=- shape=51f7656f vocab=466bb027
-/
@[simp]
theorem henselFactorization_henselIterate_succ
    {R : Type*} [CommRing R] (π : R) (F0 : R[X]) (corr : ℕ → R[X])
    (n : ℕ) :
    henselFactorization_henselIterate π F0 corr (n + 1) =
      henselFactorization_henselIterate π F0 corr n +
        Polynomial.C (π ^ (n + 1)) * corr (n + 1) :=
  rfl

/-- every recursive iterate is congruent to its initial lift
modulo `(π)`.  This is built into the update formula and does not require
`(π)` to be the maximal ideal.
@isnad1 id=mem.0h6v.s7.3575743790cd from=translated src=- shape=5c0e50a7 vocab=9dc4bd22
-/
theorem henselFactorization_henselIterate_span_singleton
    {R : Type*} [CommRing R] {π : R}
    (F0 : R[X]) (corr : ℕ → R[X]) :
    ∀ n i : ℕ,
      (henselFactorization_henselIterate π F0 corr n - F0).coeff i ∈
        Ideal.span ({π} : Set R) := by
  intro n
  induction n with
  | zero =>
      intro i
      rw [henselFactorization_henselIterate_zero, sub_self, Polynomial.coeff_zero]
      exact (Ideal.span ({π} : Set R)).zero_mem
  | succ n ih =>
      intro i
      simpa [henselFactorization_henselIterate_succ] using
        (henselFactorization_update_preserves_span_singleton
          (π := π) (n := n + 1)
          (g := henselFactorization_henselIterate π F0 corr n)
          (g0 := F0) (p := corr (n + 1))
          (Nat.succ_pos n) ih i)

/-- changing a correction coefficient at a later index does
not change an earlier Hensel iterate.
@isnad1 id=eq.1h7v.s6.76054f43f46b from=translated src=- shape=951542ce vocab=ba7cb632
-/
theorem henselFactorization_henselIterate_update_of_lt
    {R : Type*} [CommRing R] (π : R) (F0 : R[X])
    (corr : ℕ → R[X]) {n k : ℕ} (c : R[X]) (h : n < k) :
    henselFactorization_henselIterate π F0 (Function.update corr k c) n =
      henselFactorization_henselIterate π F0 corr n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [henselFactorization_henselIterate_succ,
        henselFactorization_henselIterate_succ]
      have hnlt : n < k := lt_trans (Nat.lt_succ_self n) h
      rw [ih hnlt]
      have hne : n + 1 ≠ k := ne_of_lt h
      rw [Function.update_of_ne hne]

/-- extending the correction sequence at the next index gives
the expected next Hensel iterate.
@isnad1 id=eq.0h6v.s8.bf1b4bea15b4 from=translated src=- shape=cb3bbfae vocab=07cf34f0
-/
theorem henselFactorization_henselIterate_update_next
    {R : Type*} [CommRing R] (π : R) (F0 : R[X])
    (corr : ℕ → R[X]) (n : ℕ) (c : R[X]) :
    henselFactorization_henselIterate π F0
        (Function.update corr (n + 1) c) (n + 1) =
      henselFactorization_henselIterate π F0 corr n +
        Polynomial.C (π ^ (n + 1)) * c := by
  rw [henselFactorization_henselIterate_succ]
  rw [henselFactorization_henselIterate_update_of_lt
    (π := π) (F0 := F0) (corr := corr) (c := c) (Nat.lt_succ_self n)]
  rw [Function.update_self]

/-- updating the correction functions at `n+1` preserves all
factorization invariants already established up to stage `n`.
@isnad1 id=eq.2h12v.s9.63ad5c8fbc79 from=translated src=- shape=8e3435d0 vocab=e61028f3
-/
theorem henselFactorization_henselIterate_update_preserves_factor_of_le
    {R : Type*} [CommRing R] {π : R}
    {f g0 h0 : R[X]} (pCorr qCorr : ℕ → R[X])
    {n r : ℕ} (hr : r ≤ n) (p q fn : R[X])
    (hfactor :
      f - henselFactorization_henselIterate π g0 pCorr r *
          henselFactorization_henselIterate π h0 qCorr r =
        Polynomial.C (π ^ (r + 1)) * fn) :
    f - henselFactorization_henselIterate π g0
          (Function.update pCorr (n + 1) p) r *
        henselFactorization_henselIterate π h0
          (Function.update qCorr (n + 1) q) r =
      Polynomial.C (π ^ (r + 1)) * fn := by
  have hrlt : r < n + 1 := Nat.lt_succ_of_le hr
  rw [henselFactorization_henselIterate_update_of_lt
      (π := π) (F0 := g0) (corr := pCorr) (c := p) hrlt,
    henselFactorization_henselIterate_update_of_lt
      (π := π) (F0 := h0) (corr := qCorr) (c := q) hrlt]
  exact hfactor

/-- the one-step factorization statement rewritten in terms
of the updated Hensel iterates.
@isnad1 id=eq.1h11v.s9.e431ff3a9b17 from=translated src=- shape=4053a813 vocab=2d22c2d3
-/
theorem henselFactorization_henselIterate_update_next_factor
    {R : Type*} [CommRing R] {π : R}
    {f g0 h0 : R[X]} (pCorr qCorr : ℕ → R[X])
    (n : ℕ) (p q fnNext : R[X])
    (hfactorNext :
      f - (henselFactorization_henselIterate π g0 pCorr n +
            Polynomial.C (π ^ (n + 1)) * p) *
          (henselFactorization_henselIterate π h0 qCorr n +
            Polynomial.C (π ^ (n + 1)) * q) =
        Polynomial.C (π ^ (n + 2)) * fnNext) :
    f - henselFactorization_henselIterate π g0
          (Function.update pCorr (n + 1) p) (n + 1) *
        henselFactorization_henselIterate π h0
          (Function.update qCorr (n + 1) q) (n + 1) =
      Polynomial.C (π ^ (n + 2)) * fnNext := by
  rw [henselFactorization_henselIterate_update_next
      (π := π) (F0 := g0) (corr := pCorr) (c := p),
    henselFactorization_henselIterate_update_next
      (π := π) (F0 := h0) (corr := qCorr) (c := q)]
  exact hfactorNext

/-- a global correction-degree bound is preserved when one
correction coefficient is replaced by another coefficient satisfying the same
bound.
@isnad1 id=le.2h6v.s6.8e62e21aaa29 from=translated src=- shape=d63021b9 vocab=71575454
-/
theorem henselFactorization_update_corr_natDegree_le
    {R : Type*} [CommRing R] {corr : ℕ → R[X]} {k M : ℕ} {c : R[X]}
    (hcorr : ∀ r : ℕ, (corr r).natDegree ≤ M)
    (hc : c.natDegree ≤ M) :
    ∀ r : ℕ, ((Function.update corr k c) r).natDegree ≤ M := by
  intro r
  by_cases h : r = k
  · subst r
    simpa [Function.update_self] using hc
  · rw [Function.update_of_ne h]
    exact hcorr r

end Valuations
end AlgebraicNumberTheory

end
