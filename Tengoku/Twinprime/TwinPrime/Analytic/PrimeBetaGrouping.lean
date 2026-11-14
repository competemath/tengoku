import Tengoku.Twinprime.TwinPrime.Analytic.BilinearPrimeBeta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Grouping the prime-beta factor sum by its product

The finite reindexing preserves both strict factor cutoffs and the interval
`X < d*r ≤ 2X`. It connects the factorwise prime-beta replacement to its
actual Dirichlet-convolution coefficient, for all natural cutoffs.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/--
@isnad1 id=eq.1h2v.s5.a4fe87b71482 from=translated src=- shape=d3903c8c vocab=ec95c1e4
-/
theorem primeVaughanBeta_eq_zero_of_le (V r : ℕ) (hr : r ≤ V) :
    primeVaughanBeta V r = 0 :=
  le_antisymm ((primeVaughanBeta_le V r).trans_eq (vaughanBeta_eq_zero_of_le V r hr))
    (primeVaughanBeta_nonneg V r)

/-- Generic exact grouping of the complete positive-factor domain.
@isnad1 id=eq.0h5v.s7.a1fd5345642a from=translated src=- shape=156fac61 vocab=465aa1d6
-/
theorem sum_bilinearPairs_eq_sum_divisorsAntidiagonal {A : Type*} [AddCommMonoid A]
    (U V X : ℕ) (f : ℕ × ℕ → A) :
    (∑ dr ∈ bilinearPairs U V X, f dr) =
      ∑ n ∈ Ioc X (2 * X),
        ∑ dr ∈ n.divisorsAntidiagonal with U < dr.1 ∧ V < dr.2, f dr := by
  classical
  symm
  rw [sum_sigma']
  apply sum_bij (fun nr _ => nr.2)
  · rintro ⟨n, dr⟩ hnr
    obtain ⟨hnI, hdr⟩ := mem_sigma.mp hnr
    obtain ⟨hanti, hU, hV⟩ := mem_filter.mp hdr
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hanti).1
    change dr.1 * dr.2 = n at hprod
    have hdpos : 0 < dr.1 := Nat.pos_of_ne_zero
      (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hanti)
    have hrpos : 0 < dr.2 := Nat.pos_of_ne_zero
      (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hanti)
    have hdle : dr.1 ≤ n := hprod ▸ Nat.le_mul_of_pos_right dr.1 hrpos
    have hrle : dr.2 ≤ n := hprod ▸ Nat.le_mul_of_pos_left dr.2 hdpos
    have hn := mem_Ioc.mp hnI
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hdpos, hdle.trans hn.2⟩,
      mem_Icc.mpr ⟨hrpos, hrle.trans hn.2⟩⟩, hU, hV, ?_⟩
    simpa only [hprod] using hn
  · rintro ⟨n, dr⟩ hnr ⟨m, er⟩ hmr h
    dsimp only at h
    subst er
    have hnprod := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hnr).2).1).1
    have hmprod := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hmr).2).1).1
    have hnm : n = m := hnprod.symm.trans hmprod
    subst m
    rfl
  · intro dr hdr
    obtain ⟨_, hU, hV, hlow, hupp⟩ := mem_filter.mp hdr
    refine ⟨⟨dr.1 * dr.2, dr⟩, ?_, rfl⟩
    apply mem_sigma.mpr
    refine ⟨mem_Ioc.mpr ⟨hlow, hupp⟩, mem_filter.mpr ⟨?_, hU, hV⟩⟩
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨rfl, Nat.ne_of_gt ((Nat.zero_le X).trans_lt hlow)⟩
  · intro nr _
    rfl

/-- The prime-beta factor sum is exactly its grouped convolution sum.
No positivity hypothesis on either cutoff or the interval endpoint is needed.
@isnad1 id=eq.0h3v.s6.38d059776f97 from=translated src=- shape=4b327de0 vocab=33183f92
-/
theorem bilinearPrimeBeta_eq_grouped (U V X : ℕ) :
    bilinearPrimeBeta U V X = ∑ n ∈ Ioc X (2 * X),
      vonMangoldt (n + 2) * (moebiusHigh U * primeVaughanBeta V) n := by
  rw [bilinearPrimeBeta, sum_bilinearPairs_eq_sum_divisorsAntidiagonal]
  apply sum_congr rfl
  intro n _
  rw [ArithmeticFunction.mul_apply, mul_sum, sum_filter]
  apply sum_congr rfl
  intro dr hdr
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hdr).1
  change dr.1 * dr.2 = n at hprod
  by_cases hU : U < dr.1
  · by_cases hV : V < dr.2
    · simp only [hU, hV, and_self, ite_true, moebiusHigh, cutoffHigh_apply, intCoe_apply]
      rw [hprod]
      ring
    · have hz := primeVaughanBeta_eq_zero_of_le V dr.2 (Nat.le_of_not_gt hV)
      simp [hU, hV, hz, moebiusHigh, cutoffHigh_apply]
  · simp [hU, moebiusHigh, cutoffHigh_apply]

end TwinPrime.Analytic
