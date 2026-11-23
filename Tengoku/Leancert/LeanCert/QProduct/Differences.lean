/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.QProduct.Stability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Difference calculus for finite q-product integrals

Removing an exponent from `F S = ∫₀¹ ∏_{n∈S}(1-uⁿ) du` changes the value by
exactly a moment of the remaining product, and mixed second differences are
moments at the *sum* of the removed exponents:

* `F_erase_sub_eq_moment` :
  `F (S.erase c) - F S = moment (S.erase c) c`
* `F_second_difference_eq_moment` :
  `F S - F (S.erase c) - F (S.erase d) + F ((S.erase c).erase d)
     = moment ((S.erase c).erase d) (c + d)`

Both right-hand sides are nonnegative, so single-exponent removals only
increase the integral (`F_erase_sub_nonneg`), removals of smaller exponents
increase it more (`moment_antitone_exponent`), and the family of differences
is discretely convex (`F_second_difference_nonneg`). The second difference
depends on the removed pair only through `c + d`, which is the analytic
source of the subset-sum expansion of `F`.

These identities support self-bounding tail estimates for directed-limit
certificates: consecutive truncation increments are moments, and moment
monotonicity converts observed increments into certified tail majorants.
-/

namespace LeanCert.QProduct

open MeasureTheory intervalIntegral

/-- `qProd` is continuous (duplicated here to keep this file independent of
the infinite-product development). -/
private theorem qProd_continuous' (S : Finset Nat) :
    Continuous fun u : ℝ => qProd S u := by
  unfold qProd
  exact continuous_finsetProd S fun n _ => continuous_const.sub (continuous_pow n)

private theorem qProd_intervalIntegrable (S : Finset Nat) :
    IntervalIntegrable (fun u => qProd S u) volume (0:ℝ) 1 :=
  (qProd_continuous' S).intervalIntegrable 0 1

private theorem qProd_mul_pow_intervalIntegrable (S : Finset Nat) (k : Nat) :
    IntervalIntegrable (fun u => qProd S u * u ^ k) volume (0:ℝ) 1 :=
  ((qProd_continuous' S).mul (continuous_pow k)).intervalIntegrable 0 1

/-- Moments of q-products are nonnegative.
@isnad1 id=le.0h2v.s4.61fd8406f7ed from=translated src=- shape=90e882b6 vocab=e06af58e
-/
theorem moment_nonneg (S : Finset Nat) (k : Nat) : 0 ≤ moment S k := by
  unfold moment
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  exact mul_nonneg (qProd_nonneg S hu) (pow_nonneg hu.1 k)

/-- Moments are antitone in the exponent.
@isnad1 id=le.1h3v.s4.9f38ffc01b21 from=translated src=- shape=89c46ed3 vocab=e06af58e
-/
theorem moment_antitone_exponent (S : Finset Nat) {k l : Nat} (hkl : k ≤ l) :
    moment S l ≤ moment S k := by
  unfold moment
  apply intervalIntegral.integral_mono_on (by norm_num)
    (qProd_mul_pow_intervalIntegrable S l) (qProd_mul_pow_intervalIntegrable S k)
  intro u hu
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hu.1 hu.2 hkl) (qProd_nonneg S hu)

/-- Removing the factor of an exponent `c ∈ S` splits the product.
@isnad1 id=eq.1h3v.s6.e0da97017eea from=translated src=- shape=eeb9ed70 vocab=02cbc856
-/
theorem qProd_erase_mul {S : Finset Nat} {c : Nat} (hc : c ∈ S) (u : ℝ) :
    qProd S u = (1 - u ^ c) * qProd (S.erase c) u := by
  unfold qProd
  exact (Finset.mul_prod_erase S _ hc).symm

/-- **First difference = moment.** Removing one exponent raises the integral
by exactly the corresponding moment of the remaining product.
@isnad1 id=eq.1h2v.s5.6a26f257f212 from=translated src=- shape=849edd67 vocab=7dee889e
-/
theorem F_erase_sub_eq_moment {S : Finset Nat} {c : Nat} (hc : c ∈ S) :
    F (S.erase c) - F S = moment (S.erase c) c := by
  unfold F moment
  rw [← intervalIntegral.integral_sub (qProd_intervalIntegrable (S.erase c))
    (qProd_intervalIntegrable S)]
  apply intervalIntegral.integral_congr
  intro u _
  show qProd (S.erase c) u - qProd S u = qProd (S.erase c) u * u ^ c
  rw [qProd_erase_mul hc]
  ring

/-- Single-exponent removal never decreases the integral.
@isnad1 id=le.1h2v.s5.e993f8cc920b from=translated src=- shape=b4159c56 vocab=dbfcc6c8
-/
theorem F_erase_sub_nonneg {S : Finset Nat} {c : Nat} (hc : c ∈ S) :
    0 ≤ F (S.erase c) - F S := by
  rw [F_erase_sub_eq_moment hc]
  exact moment_nonneg _ _

/-- **Second difference = moment at the sum.** The mixed second difference of
removals depends on the removed pair `{c, d}` only through `c + d`.
@isnad1 id=eq.3h3v.s6.ab94931e701c from=translated src=- shape=f23bbb18 vocab=a53c11fa
-/
theorem F_second_difference_eq_moment {S : Finset Nat} {c d : Nat}
    (hc : c ∈ S) (hd : d ∈ S) (hcd : c ≠ d) :
    F S - F (S.erase c) - F (S.erase d) + F ((S.erase c).erase d) =
      moment ((S.erase c).erase d) (c + d) := by
  have hd' : d ∈ S.erase c := Finset.mem_erase.mpr ⟨(Ne.symm hcd), hd⟩
  have hc' : c ∈ S.erase d := Finset.mem_erase.mpr ⟨hcd, hc⟩
  have hcomm : (S.erase d).erase c = (S.erase c).erase d := by
    ext x
    simp only [Finset.mem_erase]
    tauto
  unfold F moment
  rw [← intervalIntegral.integral_sub (qProd_intervalIntegrable S)
        (qProd_intervalIntegrable (S.erase c)),
      ← intervalIntegral.integral_sub
        ((qProd_intervalIntegrable S).sub (qProd_intervalIntegrable (S.erase c)))
        (qProd_intervalIntegrable (S.erase d)),
      ← intervalIntegral.integral_add
        (((qProd_intervalIntegrable S).sub
            (qProd_intervalIntegrable (S.erase c))).sub
          (qProd_intervalIntegrable (S.erase d)))
        (qProd_intervalIntegrable ((S.erase c).erase d))]
  apply intervalIntegral.integral_congr
  intro u _
  show qProd S u - qProd (S.erase c) u - qProd (S.erase d) u +
      qProd ((S.erase c).erase d) u =
    qProd ((S.erase c).erase d) u * u ^ (c + d)
  have h1 : qProd S u = (1 - u ^ c) * ((1 - u ^ d) * qProd ((S.erase c).erase d) u) := by
    rw [qProd_erase_mul hc, qProd_erase_mul hd']
  have h2 : qProd (S.erase c) u = (1 - u ^ d) * qProd ((S.erase c).erase d) u :=
    qProd_erase_mul hd' u
  have h3 : qProd (S.erase d) u = (1 - u ^ c) * qProd ((S.erase c).erase d) u := by
    rw [qProd_erase_mul hc', hcomm]
  simp only [h1, h2, h3, pow_add]
  ring

/-- Discrete convexity: mixed second differences are nonnegative.
@isnad1 id=le.3h3v.s6.07d77ba3c9db from=translated src=- shape=4f2c38b9 vocab=da91a493
-/
theorem F_second_difference_nonneg {S : Finset Nat} {c d : Nat}
    (hc : c ∈ S) (hd : d ∈ S) (hcd : c ≠ d) :
    0 ≤ F S - F (S.erase c) - F (S.erase d) + F ((S.erase c).erase d) := by
  rw [F_second_difference_eq_moment hc hd hcd]
  exact moment_nonneg _ _

/-- The second difference factors through the sum of the removed exponents:
two removal pairs over the same base with equal sums produce identical second
differences.
@isnad1 id=eq.8h5v.s7.7003e451b417 from=translated src=- shape=f0b40d01 vocab=08b7814e
-/
theorem F_second_difference_factors_through_sum {S : Finset Nat}
    {c d c' d' : Nat} (hc : c ∈ S) (hd : d ∈ S) (hcd : c ≠ d)
    (hc' : c' ∈ S) (hd' : d' ∈ S) (hcd' : c' ≠ d')
    (hbase : (S.erase c).erase d = (S.erase c').erase d')
    (hsum : c + d = c' + d') :
    F S - F (S.erase c) - F (S.erase d) + F ((S.erase c).erase d) =
      F S - F (S.erase c') - F (S.erase d') + F ((S.erase c').erase d') := by
  rw [F_second_difference_eq_moment hc hd hcd,
    F_second_difference_eq_moment hc' hd' hcd', hbase, hsum]

/-! ### Geometric tail collapse

A retained factor `(1 - u)` (respectively `(1 - u²)`) damps the geometric sum
of all missing exponents at once: the gap between a truncation and any finer
truncation collapses to a single moment of the truncation with the damping
exponent removed. This is the engine for computable tail majorants in
directed-limit certificates over arbitrary exponent systems. -/

private theorem one_sub_mul_geom_sum_Ico {u : ℝ} (m : Nat) :
    ∀ {n : Nat}, m ≤ n →
      (1 - u) * ∑ q ∈ Finset.Ico m n, u ^ q = u ^ m - u ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn]
      ring_nf
      ring_nf at ih
      linarith [ih]

/-- A damped geometric sum over distinct exponents at least `m` is at most
`u ^ m` on `[0, 1]`.
@isnad1 id=le.2h3v.s6.714e752a4415 from=translated src=- shape=a4909080 vocab=06c78062
-/
theorem one_sub_mul_sum_pow_le {A : Finset Nat} {m : Nat}
    (hm : ∀ q ∈ A, m ≤ q) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 - u) * ∑ q ∈ A, u ^ q ≤ u ^ m := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simpa using pow_nonneg hu.1 m
  · set M := A.max' hA with hM
    have hsub : A ⊆ Finset.Ico m (M + 1) := by
      intro q hq
      exact Finset.mem_Ico.mpr ⟨hm q hq, Nat.lt_succ_of_le (A.le_max' q hq)⟩
    have hmono : ∑ q ∈ A, u ^ q ≤ ∑ q ∈ Finset.Ico m (M + 1), u ^ q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun q _ _ => pow_nonneg hu.1 q)
    have hmM : m ≤ M + 1 :=
      le_trans (hm _ (A.max'_mem hA)) (Nat.le_succ M)
    calc (1 - u) * ∑ q ∈ A, u ^ q
        ≤ (1 - u) * ∑ q ∈ Finset.Ico m (M + 1), u ^ q :=
          mul_le_mul_of_nonneg_left hmono (by linarith [hu.2])
      _ = u ^ m - u ^ (M + 1) := one_sub_mul_geom_sum_Ico m hmM
      _ ≤ u ^ m := by linarith [pow_nonneg hu.1 (M + 1)]

end LeanCert.QProduct
