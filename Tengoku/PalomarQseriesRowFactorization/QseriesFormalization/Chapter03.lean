import Tengoku.Seed.Analysis.Normed.Group.Tannery
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Basic
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Chapter02

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chapter 3 — Part I: Second proof (Gaussian polynomials and the q-binomial theorem)

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 3, pp. 11–20.)

Gaussian (q-binomial) coefficients are defined in `Basic.lean`. This file
states and proves the finite q-binomial theorem
`∏_{k=0}^{n-1} (1 + x q^k) = ∑_{k=0}^n [n choose k]_q q^{k(k-1)/2} x^k`.

The main theorem is proved by induction from the defining q-Pascal recursion
for Gaussian binomial coefficients.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch03

section CommRing

variable {R : Type*} [CommRing R]

end CommRing

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Left side of the finite q-binomial theorem.-/
def qBinomialLHS (q x : R) : Nat → R
  | 0 => 1
  | Nat.succ n => qBinomialLHS q x n * (1 + x * q ^ n)

/-- A single term on the right side of the finite q-binomial theorem.-/
def qBinomialTerm (q x : R) (n k : Nat) : R :=
  gaussianBinom q n k * q ^ (k * (k - 1) / 2) * x ^ k

/-- Right side of the finite q-binomial theorem (closed-form finite sum).-/
def qBinomialRHS (q x : R) (n : Nat) : R :=
  natSum (fun k => qBinomialTerm q x n k) n

/--
@isnad1 id=eq.0h3v.s5.820364ae8d90 from=translated src=- shape=9c02e61a vocab=71e5aaaa
-/
@[simp] theorem qBinomialLHS_zero (q x : R) : qBinomialLHS q x 0 = 1 := rfl

/--
@isnad1 id=eq.0h3v.s5.0d8f45163242 from=translated src=- shape=9c02e61a vocab=3be53d9e
-/
@[simp] theorem qBinomialRHS_zero (q x : R) : qBinomialRHS q x 0 = 1 := by
  simp [qBinomialRHS, qBinomialTerm]

/--
@isnad1 id=eq.0h3v.s5.e01bad894bb7 from=translated src=- shape=9706cd55 vocab=9648096b
-/
@[simp] theorem qBinomialLHS_one (q x : R) : qBinomialLHS q x 1 = 1 + x := by
  simp [qBinomialLHS]

/--
@isnad1 id=eq.0h3v.s5.7e8da56ad573 from=translated src=- shape=9706cd55 vocab=f0fd6dda
-/
@[simp] theorem qBinomialRHS_one (q x : R) : qBinomialRHS q x 1 = 1 + x := by
  simp [qBinomialRHS, qBinomialTerm, gaussianBinom, natSum]

/-- The `n = 1` case is fully proved and serves as a first Lean exercise.
@isnad1 id=eq.0h3v.s4.cace13be88e1 from=translated src=- shape=70f6db3a vocab=3264bc55
-/
theorem qBinomial_one (q x : R) : qBinomialLHS q x 1 = qBinomialRHS q x 1 := by
  exact Eq.trans (qBinomialLHS_one q x) (Eq.symm (qBinomialRHS_one q x))

/--
@isnad1 id=eq.1h4v.s5.f937677cc3d0 from=translated src=- shape=d1d652df vocab=7a2634c4
-/
lemma natSum_congr_le {f g : Nat → R} :
    ∀ n, (∀ k, k ≤ n → f k = g k) → natSum f n = natSum g n
  | 0, h => by simp [h 0 (by omega)]
  | Nat.succ n, h => by
      rw [natSum_succ, natSum_succ]
      rw [natSum_congr_le n (fun k hk => h k (by omega))]
      rw [h (Nat.succ n) (by omega)]

/--
@isnad1 id=eq.0h4v.s6.0f843b86aaa6 from=translated src=- shape=76731732 vocab=f728d10e
-/
lemma natSum_add (f g : Nat → R) :
    ∀ n, natSum (fun k => f k + g k) n = natSum f n + natSum g n
  | 0 => by simp
  | Nat.succ n => by
      rw [natSum_succ, natSum_succ, natSum_succ, natSum_add f g n]
      ring

/--
@isnad1 id=eq.0h4v.s5.b4642867b785 from=translated src=- shape=1eae7d7b vocab=065c60bb
-/
lemma natSum_mul_right (f : Nat → R) (a : R) :
    ∀ n, natSum (fun k => f k * a) n = natSum f n * a
  | 0 => by simp
  | Nat.succ n => by
      rw [natSum_succ, natSum_succ, natSum_mul_right f a n]
      ring

/--
@isnad1 id=eq.0h4v.s5.6afe964c2f07 from=translated src=- shape=c30b0914 vocab=065c60bb
-/
lemma natSum_mul_left (a : R) (f : Nat → R) :
    ∀ n, natSum (fun k => a * f k) n = a * natSum f n
  | 0 => by simp
  | Nat.succ n => by
      rw [natSum_succ, natSum_succ, natSum_mul_left a f n]
      ring

/-- The repository's inclusive `natSum` agrees with the usual Finset range sum.
@isnad1 id=eq.0h3v.s5.cd66b7e5d359 from=translated src=- shape=4a95f298 vocab=2fd182e0
-/
theorem natSum_eq_sum_range (f : ℕ → R) (N : ℕ) :
    natSum f N = ∑ n ∈ Finset.range (N + 1), f n := by
  induction N with
  | zero =>
      simp [natSum]
  | succ N ih =>
      rw [natSum_succ, ih]
      simp [Finset.sum_range_succ, Nat.add_assoc]

/--
@isnad1 id=eq.0h3v.s5.12efcee88e70 from=translated src=- shape=518fdf96 vocab=ca6825aa
-/
lemma natSum_succ_shift (f : Nat → R) :
    ∀ n, natSum f (Nat.succ n) = f 0 + natSum (fun k => f (Nat.succ k)) n
  | 0 => by simp
  | Nat.succ n => by
      rw [natSum_succ, natSum_succ_shift f n, natSum_succ]
      ring

/--
@isnad1 id=eq.1h4v.s5.5c7214ebd9dc from=translated src=- shape=add6247f vocab=50196843
-/
@[simp] lemma gaussianBinom_eq_zero_of_lt (q : R) :
    ∀ {n k : Nat}, n < k → gaussianBinom q n k = 0
  | 0, 0, h => by omega
  | 0, Nat.succ k, _ => by rfl
  | Nat.succ n, 0, h => by omega
  | Nat.succ n, Nat.succ k, h => by
      simp [gaussianBinom, gaussianBinom_eq_zero_of_lt q (n := n) (k := Nat.succ k) (by omega),
        gaussianBinom_eq_zero_of_lt q (n := n) (k := k) (by omega)]

/--
@isnad1 id=eq.0h3v.s5.16a998d6a818 from=translated src=- shape=82da11a8 vocab=2f82dd73
-/
@[simp] lemma gaussianBinom_self (q : R) :
    ∀ n : Nat, gaussianBinom q n n = 1
  | 0 => by simp
  | Nat.succ n => by
      simp [gaussianBinom, gaussianBinom_self q n]

/--
@isnad1 id=eq.1h4v.s6.db6dec66d21b from=translated src=- shape=c6a68a64 vocab=60f6a682
-/
lemma gaussianBinom_pascal_alt (q : R) :
    ∀ (n k : Nat), k ≤ n →
      gaussianBinom q (Nat.succ n) (Nat.succ k) =
        q ^ Nat.succ k * gaussianBinom q n (Nat.succ k) +
        gaussianBinom q n k
  | 0, 0, _ => by simp [gaussianBinom]
  | 0, Nat.succ k, hk => by omega
  | Nat.succ n, k, hk => by
      rcases Nat.eq_or_lt_of_le hk with rfl | hklt
      · simp [gaussianBinom]
      · have hkn : k ≤ n := by omega
        cases k with
        | zero =>
            calc
              gaussianBinom q (Nat.succ (Nat.succ n)) 1 =
                  gaussianBinom q (Nat.succ n) 1 + q ^ Nat.succ n := by
                simp [gaussianBinom]
              _ = (q * gaussianBinom q n 1 + 1) + q ^ Nat.succ n := by
                rw [gaussianBinom_pascal_alt q n 0 (by omega)]
                simp
              _ = q * (gaussianBinom q n 1 + q ^ n) + 1 := by
                rw [pow_succ]
                ring
              _ = q ^ 1 * gaussianBinom q (Nat.succ n) 1 +
                  gaussianBinom q (Nat.succ n) 0 := by
                simp [gaussianBinom]
        | succ j =>
            have hjn : j ≤ n := by omega
            have hsjn : Nat.succ j ≤ n := by omega
            have hpow_left :
                q ^ (n - j) * q ^ Nat.succ j = q ^ Nat.succ n := by
              rw [← pow_add]
              congr 1
              omega
            have hpow_right :
                q ^ Nat.succ (Nat.succ j) * q ^ (n - Nat.succ j) =
                  q ^ Nat.succ n := by
              rw [mul_comm, ← pow_add]
              congr 1
              omega
            calc
              gaussianBinom q (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ j)) =
                  gaussianBinom q (Nat.succ n) (Nat.succ (Nat.succ j)) +
                    q ^ (n - j) * gaussianBinom q (Nat.succ n) (Nat.succ j) := by
                simp [gaussianBinom, Nat.succ_sub_succ_eq_sub]
              _ =
                  (q ^ Nat.succ (Nat.succ j) *
                      gaussianBinom q n (Nat.succ (Nat.succ j)) +
                    gaussianBinom q n (Nat.succ j)) +
                    q ^ (n - j) *
                      (q ^ Nat.succ j * gaussianBinom q n (Nat.succ j) +
                        gaussianBinom q n j) := by
                rw [gaussianBinom_pascal_alt q n (Nat.succ j) hsjn]
                rw [gaussianBinom_pascal_alt q n j hjn]
              _ =
                  q ^ Nat.succ (Nat.succ j) *
                    (gaussianBinom q n (Nat.succ (Nat.succ j)) +
                      q ^ (n - Nat.succ j) * gaussianBinom q n (Nat.succ j)) +
                    (gaussianBinom q n (Nat.succ j) +
                  q ^ (n - j) * gaussianBinom q n j) := by
                repeat rw [mul_add]
                repeat rw [← mul_assoc]
                rw [hpow_left, hpow_right]
                ring
              _ =
                  q ^ Nat.succ (Nat.succ j) *
                      gaussianBinom q (Nat.succ n) (Nat.succ (Nat.succ j)) +
                    gaussianBinom q (Nat.succ n) (Nat.succ j) := by
                simp [gaussianBinom]

/--
@isnad1 id=eq.1h4v.s5.c1584c746c0b from=translated src=- shape=b347f4f1 vocab=57666bf1
-/
lemma gaussianBinom_symm (q : R) :
    ∀ n k, k ≤ n → gaussianBinom q n k = gaussianBinom q n (n - k)
  | 0, 0, _ => by simp
  | 0, Nat.succ k, hk => by omega
  | Nat.succ n, 0, _ => by simp
  | Nat.succ n, Nat.succ k, hk => by
      rcases Nat.eq_or_lt_of_le hk with hk_eq | hklt
      · have : k = n := by omega
        subst k
        simp
      · have hkn : k ≤ n := by omega
        rw [gaussianBinom]
        rw [show Nat.succ n - Nat.succ k = n - k by omega]
        cases hdiff : n - k with
        | zero =>
            omega
        | succ d =>
            rw [gaussianBinom_pascal_alt q n d (by omega)]
            have hsym_k : gaussianBinom q n k = gaussianBinom q n (n - k) :=
              gaussianBinom_symm q n k hkn
            have hsym_succ :
                gaussianBinom q n (Nat.succ k) = gaussianBinom q n d := by
              rw [gaussianBinom_symm q n (Nat.succ k) (by omega)]
              rw [show n - Nat.succ k = d by omega]
            have hsym_k' :
                gaussianBinom q n k = gaussianBinom q n (Nat.succ d) := by
              simpa [hdiff] using hsym_k
            rw [hsym_succ, hsym_k']
            rw [pow_succ]
            ring

/--
@isnad1 id=eq.0h4v.s5.1afe309a0571 from=translated src=- shape=6d85ee18 vocab=f713d64d
-/
lemma qBinomialTerm_zero (q x : R) (n : Nat) :
    qBinomialTerm q x n 0 = 1 := by
  simp [qBinomialTerm]

/--
@isnad1 id=eq.0h5v.s8.998c3f3cb3ad from=translated src=- shape=b97ca02b vocab=a8077fbc
-/
lemma qBinomialTerm_succ_row_succ (q x : R) (n k : Nat) :
    qBinomialTerm q x (Nat.succ n) (Nat.succ k) =
      gaussianBinom q n (Nat.succ k) * q ^ ((Nat.succ k) * k / 2) * x ^ Nat.succ k +
        (q ^ (n - k) * gaussianBinom q n k) * q ^ ((Nat.succ k) * k / 2) *
          x ^ Nat.succ k := by
  simp [qBinomialTerm, gaussianBinom, Nat.succ_eq_add_one]
  ring

/--
@isnad1 id=eq.0h5v.s6.65640af3cbc5 from=translated src=- shape=469c63d3 vocab=8156531e
-/
lemma qBinomialTerm_succ_eq_shift_part (q x : R) (n k : Nat) :
    gaussianBinom q n (Nat.succ k) * q ^ ((Nat.succ k) * k / 2) * x ^ Nat.succ k =
      qBinomialTerm q x n (Nat.succ k) := by
  simp [qBinomialTerm]

/--
@isnad1 id=eq.1h5v.s7.891e686cc2a7 from=translated src=- shape=8cf3824b vocab=49e9452c
-/
lemma qBinomialTerm_mul_part (q x : R) (n k : Nat) (hk : k ≤ n) :
    (q ^ (n - k) * gaussianBinom q n k) * q ^ ((Nat.succ k) * k / 2) * x ^ Nat.succ k =
      qBinomialTerm q x n k * (x * q ^ n) := by
  have htri : (Nat.succ k) * k / 2 = k * (k - 1) / 2 + k := by
    simpa [Nat.succ_eq_add_one] using Nat.triangle_succ k
  simp [qBinomialTerm, pow_succ, htri]
  rw [pow_add]
  have hn : n - k + k = n := Nat.sub_add_cancel hk
  calc
    q ^ (n - k) * gaussianBinom q n k * (q ^ (k * (k - 1) / 2) * q ^ k) *
          (x ^ k * x) =
        gaussianBinom q n k * q ^ (k * (k - 1) / 2) * x ^ k *
          (x * (q ^ (n - k) * q ^ k)) := by
      ring
    _ = gaussianBinom q n k * q ^ (k * (k - 1) / 2) * x ^ k * (x * q ^ n) := by
      rw [← pow_add, hn]

/--
@isnad1 id=eq.0h4v.s5.695b99bf1dea from=translated src=- shape=a692ead2 vocab=e95d341b
-/
lemma qBinomialRHS_eq_one_add_shift (q x : R) :
    ∀ n : Nat,
      qBinomialRHS q x n =
        1 + natSum (fun k => qBinomialTerm q x n (Nat.succ k)) n
  | 0 => by
      simp [qBinomialRHS, qBinomialTerm]
  | Nat.succ n => by
      rw [qBinomialRHS, natSum_succ_shift]
      simp [qBinomialTerm]

/--
@isnad1 id=eq.0h4v.s6.bac4a5566a30 from=translated src=- shape=86dd315a vocab=e95d341b
-/
lemma qBinomialRHS_succ_eq_one_add_shift (q x : R) (n : Nat) :
    qBinomialRHS q x (Nat.succ n) =
      1 + natSum (fun k => qBinomialTerm q x (Nat.succ n) (Nat.succ k)) n := by
  rw [qBinomialRHS, natSum_succ_shift]
  simp [qBinomialTerm_zero]

/--
@isnad1 id=eq.0h4v.s6.d18190407032 from=translated src=- shape=007d4e83 vocab=9d6c66a3
-/
lemma natSum_shift_qBinomialTerm_eq_tail (q x : R) (n : Nat) :
    natSum (fun k => qBinomialTerm q x n (Nat.succ k)) n =
      natSum (fun k =>
        gaussianBinom q n (Nat.succ k) * q ^ ((Nat.succ k) * k / 2) * x ^ Nat.succ k) n := by
  exact natSum_congr_le n (fun k _ => by rw [qBinomialTerm_succ_eq_shift_part])

/--
@isnad1 id=eq.0h4v.s6.2c993fe820e2 from=translated src=- shape=da7ab3fd vocab=7915bb83
-/
lemma qBinomialRHS_succ (q x : R) (n : Nat) :
    qBinomialRHS q x (Nat.succ n) = qBinomialRHS q x n * (1 + x * q ^ n) := by
  rw [qBinomialRHS_succ_eq_one_add_shift q x n]
  rw [natSum_congr_le n (fun k _ => qBinomialTerm_succ_row_succ q x n k)]
  rw [natSum_add]
  rw [← natSum_shift_qBinomialTerm_eq_tail q x n]
  rw [natSum_congr_le n (fun k hk => qBinomialTerm_mul_part q x n k hk)]
  rw [natSum_mul_right]
  change
    1 + (natSum (fun k => qBinomialTerm q x n (Nat.succ k)) n +
      qBinomialRHS q x n * (x * q ^ n)) =
        qBinomialRHS q x n * (1 + x * q ^ n)
  rw [qBinomialRHS_eq_one_add_shift q x n]
  ring

/--
The finite q-binomial theorem:
`∏_{k=0}^{n-1} (1 + x q^k) = ∑_{k=0}^n [n choose k]_q q^{k(k-1)/2} x^k`.
@isnad1 id=eq.0h4v.s4.c6eea3b05afb from=translated src=- shape=b2942a79 vocab=3264bc55
-/
theorem finiteQBinomialTheorem (q x : R) (n : Nat) :
    qBinomialLHS q x n = qBinomialRHS q x n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [qBinomialLHS, qBinomialRHS_succ, ih]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/--
@isnad1 id=eq.1h3v.s6.365bcaf2e1e3 from=translated src=- shape=5245ca65 vocab=484680f7
-/
lemma qPochhammer_eq_pred_mul (q : R) {n : Nat} (hn : 0 < n) :
    qPochhammer q n = qPochhammer q (n - 1) * (1 - q ^ n) := by
  cases n with
  | zero => omega
  | succ n =>
      simp

/-- Gaussian binomial closed form in product form:
`[n,m]_q (q;q)_m (q;q)_{n-m} = (q;q)_n`.
@isnad1 id=eq.1h4v.s6.604e13b565b8 from=translated src=- shape=149859df vocab=6a81a553
-/
theorem gaussianBinom_mul_qPochhammer_eq (q : R) :
    ∀ n m, m ≤ n →
      gaussianBinom q n m * qPochhammer q m * qPochhammer q (n - m) =
        qPochhammer q n
  | 0, m, hm => by
      have : m = 0 := by omega
      subst m
      simp
  | Nat.succ n, 0, _ => by
      simp
  | Nat.succ n, Nat.succ k, hkm => by
      rcases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ hkm) with hk_eq | hk_lt
      · subst k
        simp [gaussianBinom_self]
      · have hskn : Nat.succ k ≤ n := by omega
        have hkn : k ≤ n := by omega
        have hleft := gaussianBinom_mul_qPochhammer_eq q n (Nat.succ k) hskn
        have hright := gaussianBinom_mul_qPochhammer_eq q n k hkn
        have hsub_succ : Nat.succ n - Nat.succ k = n - k := by omega
        have hsub_pred : n - Nat.succ k = n - k - 1 := by omega
        have hpoch_tail :
            qPochhammer q (n - k) =
              qPochhammer q (n - Nat.succ k) * (1 - q ^ (n - k)) := by
          rw [qPochhammer_eq_pred_mul q (n := n - k) (by omega)]
          rw [hsub_pred]
        have hpow :
            q ^ (n - k) * q ^ Nat.succ k = q ^ Nat.succ n := by
          rw [← pow_add]
          congr 1
          omega
        simp only [gaussianBinom, hsub_succ, qPochhammer_succ]
        rw [hpoch_tail]
        calc
          (gaussianBinom q n (Nat.succ k) + q ^ (n - k) * gaussianBinom q n k) *
                (qPochhammer q k * (1 - q ^ Nat.succ k)) *
                (qPochhammer q (n - Nat.succ k) * (1 - q ^ (n - k))) =
              (gaussianBinom q n (Nat.succ k) * qPochhammer q (Nat.succ k) *
                    qPochhammer q (n - Nat.succ k)) * (1 - q ^ (n - k)) +
                q ^ (n - k) *
                  (gaussianBinom q n k * qPochhammer q k * qPochhammer q (n - k)) *
                  (1 - q ^ Nat.succ k) := by
            rw [qPochhammer_succ, hpoch_tail]
            ring
          _ = qPochhammer q n * (1 - q ^ (n - k)) +
                q ^ (n - k) * qPochhammer q n * (1 - q ^ Nat.succ k) := by
            rw [hleft, hright]
          _ = qPochhammer q n * (1 - q ^ Nat.succ n) := by
            calc
              qPochhammer q n * (1 - q ^ (n - k)) +
                    q ^ (n - k) * qPochhammer q n * (1 - q ^ Nat.succ k) =
                  qPochhammer q n * (1 - q ^ (n - k) * q ^ Nat.succ k) := by
                ring
              _ = qPochhammer q n * (1 - q ^ Nat.succ n) := by
                rw [hpow]
          _ = qPochhammer q (Nat.succ n) := by
            rw [qPochhammer_succ]

/-- Centered product form for the Gaussian coefficient `[2n, n+r]_q`.
@isnad1 id=eq.1h4v.s6.3af8f2008d67 from=translated src=- shape=12665f68 vocab=90967aad
-/
theorem gaussianBinom_center_add_mul_qPochhammer_eq (q : R) (n r : Nat) (hr : r ≤ n) :
    gaussianBinom q (2 * n) (n + r) * qPochhammer q (n + r) *
        qPochhammer q (n - r) =
      qPochhammer q (2 * n) := by
  have h := gaussianBinom_mul_qPochhammer_eq q (2 * n) (n + r) (by omega)
  simpa [show 2 * n - (n + r) = n - r by omega] using h

/-- Centered product form for the Gaussian coefficient `[2n, n-r]_q`.
@isnad1 id=eq.1h4v.s6.02f1110cd131 from=translated src=- shape=12665f68 vocab=90967aad
-/
theorem gaussianBinom_center_sub_mul_qPochhammer_eq (q : R) (n r : Nat) (hr : r ≤ n) :
    gaussianBinom q (2 * n) (n - r) * qPochhammer q (n - r) *
        qPochhammer q (n + r) =
      qPochhammer q (2 * n) := by
  have h := gaussianBinom_mul_qPochhammer_eq q (2 * n) (n - r) (by omega)
  simpa [show 2 * n - (n - r) = n + r by omega] using h

/-- Multiplicative splitting of the finite q-Pochhammer symbol:
`(a; q)_{m+n} = (a; q)_m (a q^m; q)_n`.
@isnad1 id=eq.0h5v.s6.e7dc7676669c from=translated src=- shape=4c42f306 vocab=0fcc0ab7
-/
theorem qPoch_add (q a : R) (m n : Nat) :
    qPoch a q (m + n) = qPoch a q m * qPoch (a * q ^ m) q n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.add_succ, qPoch_succ, ih, qPoch_succ]
      rw [pow_add]
      ring

/-- Split `(a; q)_n` at an intermediate index `k ≤ n`.
@isnad1 id=eq.1h5v.s6.c28041d1bd52 from=translated src=- shape=bb463bda vocab=8dcf878c
-/
theorem qPoch_split (q a : R) (n k : Nat) (hk : k ≤ n) :
    qPoch a q n = qPoch a q k * qPoch (a * q ^ k) q (n - k) := by
  have hsum : k + (n - k) = n := by omega
  simpa [hsum] using qPoch_add q a k (n - k)

/-- Split `(q; q)_n`, stated for `qPochhammer`.
@isnad1 id=eq.1h4v.s6.b71b8ecbbad0 from=translated src=- shape=872570ab vocab=f96e13f2
-/
theorem qPochhammer_split (q : R) (n k : Nat) (hk : k ≤ n) :
    qPochhammer q n = qPochhammer q k * qPoch (q * q ^ k) q (n - k) := by
  simpa using qPoch_split q q n k hk

/--
@isnad1 id=eq.0h4v.s5.aa1b74691755 from=translated src=- shape=261c89ae vocab=e50f3efc
-/
lemma qBinomialLHS_neg_eq_qPoch (q z : R) :
    ∀ n : Nat, qBinomialLHS q (-z) n = qPoch z q n
  | 0 => by
      simp [qBinomialLHS]
  | Nat.succ n => by
      rw [qBinomialLHS, qPoch_succ, qBinomialLHS_neg_eq_qPoch q z n]
      ring

/-- Chan's q-binomial theorem (Theorem 3.2):
`(z; q)_n = ∑ [n,k]_q (-1)^k q^{k(k-1)/2} z^k`.
@isnad1 id=eq.0h4v.s7.00603b3a4be1 from=translated src=- shape=5142e68c vocab=5e52a589
-/
theorem qBinomialTheorem_chanForm (q z : R) (n : Nat) :
    qPoch z q n =
      natSum (fun k => gaussianBinom q n k * q ^ (k * (k - 1) / 2) * (-1 : R) ^ k * z ^ k) n := by
  have h := finiteQBinomialTheorem q (-z) n
  rw [qBinomialLHS_neg_eq_qPoch q z n] at h
  calc
    qPoch z q n = qBinomialRHS q (-z) n := h
    _ = natSum
        (fun k => gaussianBinom q n k * q ^ (k * (k - 1) / 2) * (-1 : R) ^ k * z ^ k) n := by
      unfold qBinomialRHS qBinomialTerm
      exact natSum_congr_le n (fun k _ => by
        rw [show (-z) ^ k = (-1 : R) ^ k * z ^ k by
          rw [show -z = (-1 : R) * z by ring]
          rw [mul_pow]]
        ring)

end CommRing

section ComplexLimits

open Filter
open scoped Topology

/-- Finite `(q²;q²)_N` factors are nonzero for `‖q‖ < 1`.
@isnad1 id=ne.1h2v.s5.995d9c0a13f3 from=translated src=- shape=93edda09 vocab=68d27171
-/
theorem qPochhammer_qsq_ne_zero (q : ℂ) (hq : ‖q‖ < 1) (N : ℕ) :
    qPochhammer (q ^ 2) N ≠ 0 := by
  rw [Ch02.qPochhammer_qsq_eq_jacobiProductEvenPartial]
  exact Finset.prod_ne_zero_iff.mpr fun n _ => Ch02.jacobiProductEvenFactor_ne_zero q hq n

/--
Ratio form for the centered coefficient `[2N, N+r]_{q²}`, after multiplying by
the finite even q-Pochhammer factor.
@isnad1 id=eq.2h3v.s8.f560c173f8b5 from=translated src=- shape=1830f0f5 vocab=05be3eb5
-/
theorem qPoch_mul_gaussian_center_add_eq_ratio (q : ℂ) (hq : ‖q‖ < 1)
    (N r : ℕ) (hr : r ≤ N) :
    qPoch (q ^ 2) (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N + r) =
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (q ^ 2) (q ^ 2) (2 * N)) /
        (qPoch (q ^ 2) (q ^ 2) (N + r) * qPoch (q ^ 2) (q ^ 2) (N - r)) := by
  have hcenter := gaussianBinom_center_add_mul_qPochhammer_eq (q ^ 2) N r hr
  have hden :
      qPochhammer (q ^ 2) (N + r) * qPochhammer (q ^ 2) (N - r) ≠ 0 := by
    exact mul_ne_zero (qPochhammer_qsq_ne_zero q hq (N + r))
      (qPochhammer_qsq_ne_zero q hq (N - r))
  simp only [qPoch_q_eq_qPochhammer]
  rw [eq_div_iff hden]
  rw [show qPochhammer (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N + r) *
      (qPochhammer (q ^ 2) (N + r) * qPochhammer (q ^ 2) (N - r)) =
      qPochhammer (q ^ 2) N *
        (gaussianBinom (q ^ 2) (2 * N) (N + r) * qPochhammer (q ^ 2) (N + r) *
          qPochhammer (q ^ 2) (N - r)) by ring]
  rw [hcenter]

/--
Ratio form for the centered coefficient `[2N, N-r]_{q²}`, after multiplying by
the finite even q-Pochhammer factor.
@isnad1 id=eq.2h3v.s8.890d8999d8a5 from=translated src=- shape=1830f0f5 vocab=05be3eb5
-/
theorem qPoch_mul_gaussian_center_sub_eq_ratio (q : ℂ) (hq : ‖q‖ < 1)
    (N r : ℕ) (hr : r ≤ N) :
    qPoch (q ^ 2) (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N - r) =
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (q ^ 2) (q ^ 2) (2 * N)) /
        (qPoch (q ^ 2) (q ^ 2) (N - r) * qPoch (q ^ 2) (q ^ 2) (N + r)) := by
  have hcenter := gaussianBinom_center_sub_mul_qPochhammer_eq (q ^ 2) N r hr
  have hden :
      qPochhammer (q ^ 2) (N - r) * qPochhammer (q ^ 2) (N + r) ≠ 0 := by
    exact mul_ne_zero (qPochhammer_qsq_ne_zero q hq (N - r))
      (qPochhammer_qsq_ne_zero q hq (N + r))
  simp only [qPoch_q_eq_qPochhammer]
  rw [eq_div_iff hden]
  rw [show qPochhammer (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N - r) *
      (qPochhammer (q ^ 2) (N - r) * qPochhammer (q ^ 2) (N + r)) =
      qPochhammer (q ^ 2) N *
        (gaussianBinom (q ^ 2) (2 * N) (N - r) * qPochhammer (q ^ 2) (N - r) *
          qPochhammer (q ^ 2) (N + r)) by ring]
  rw [hcenter]

/-- The finite even q-Pochhammer factors have uniformly bounded norms.-/
private theorem exists_qPoch_qsq_norm_bound (q : ℂ) (hq : ‖q‖ < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ‖qPoch (q ^ 2) (q ^ 2) n‖ ≤ B := by
  have hlim := (Ch02.tendsto_qPoch_qsq q hq).norm
  have hbdd : BddAbove (Set.range fun n : ℕ => ‖qPoch (q ^ 2) (q ^ 2) n‖) :=
    hlim.bddAbove_range
  rcases hbdd with ⟨B, hB⟩
  refine ⟨max B 0, le_max_right _ _, fun n => ?_⟩
  exact (hB (Set.mem_range_self n)).trans (le_max_left _ _)

/-- The inverses of the finite even q-Pochhammer factors have uniformly bounded norms.-/
private theorem exists_qPoch_qsq_inv_norm_bound (q : ℂ) (hq : ‖q‖ < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, ‖(qPoch (q ^ 2) (q ^ 2) n)⁻¹‖ ≤ D := by
  let A : ℂ := ∏' n : ℕ, Ch02.jacobiProductEvenFactor q n
  have hA_ne : A ≠ 0 := Ch02.tprod_jacobiProductEvenFactor_ne_zero q hq
  have hlim : Tendsto (fun n : ℕ => qPoch (q ^ 2) (q ^ 2) n) atTop (𝓝 A) := by
    simpa [A] using Ch02.tendsto_qPoch_qsq q hq
  have hinv := (hlim.inv₀ hA_ne).norm
  have hbdd : BddAbove (Set.range fun n : ℕ => ‖(qPoch (q ^ 2) (q ^ 2) n)⁻¹‖) :=
    hinv.bddAbove_range
  rcases hbdd with ⟨D, hD⟩
  refine ⟨max D 0, le_max_right _ _, fun n => ?_⟩
  exact (hD (Set.mem_range_self n)).trans (le_max_left _ _)

/--
The centered Gaussian coefficients, after multiplication by `(q²;q²)_N`, are
uniformly bounded in both `N` and the centered offset `r`.
@isnad1 id=ex.1h1v.s7.e508db0bb4aa from=translated src=- shape=21e69577 vocab=5adbb9d7
-/
theorem exists_qPoch_mul_gaussian_center_norm_bound (q : ℂ) (hq : ‖q‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N r : ℕ, r ≤ N →
      ‖qPoch (q ^ 2) (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N + r)‖ ≤ C ∧
      ‖qPoch (q ^ 2) (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N - r)‖ ≤ C := by
  rcases exists_qPoch_qsq_norm_bound q hq with ⟨B, hB_nonneg, hB⟩
  rcases exists_qPoch_qsq_inv_norm_bound q hq with ⟨D, hD_nonneg, hD⟩
  refine ⟨B * B * D * D, by positivity, fun N r hr => ?_⟩
  have hnum : ‖qPoch (q ^ 2) (q ^ 2) N * qPoch (q ^ 2) (q ^ 2) (2 * N)‖ ≤ B * B := by
    rw [norm_mul]
    exact mul_le_mul (hB N) (hB (2 * N)) (norm_nonneg _) hB_nonneg
  have hnum_nonneg : 0 ≤ B * B := mul_nonneg hB_nonneg hB_nonneg
  have hden_add :
      ‖(qPoch (q ^ 2) (q ^ 2) (N + r) * qPoch (q ^ 2) (q ^ 2) (N - r))⁻¹‖ ≤
        D * D := by
    rw [mul_inv_rev, norm_mul]
    exact mul_le_mul (hD (N - r)) (hD (N + r)) (norm_nonneg _) hD_nonneg
  have hden_sub :
      ‖(qPoch (q ^ 2) (q ^ 2) (N - r) * qPoch (q ^ 2) (q ^ 2) (N + r))⁻¹‖ ≤
        D * D := by
    rw [mul_inv_rev, norm_mul]
    exact mul_le_mul (hD (N + r)) (hD (N - r)) (norm_nonneg _) hD_nonneg
  constructor
  · rw [qPoch_mul_gaussian_center_add_eq_ratio q hq N r hr]
    rw [div_eq_mul_inv, norm_mul]
    calc
      ‖qPoch (q ^ 2) (q ^ 2) N * qPoch (q ^ 2) (q ^ 2) (2 * N)‖ *
          ‖(qPoch (q ^ 2) (q ^ 2) (N + r) * qPoch (q ^ 2) (q ^ 2) (N - r))⁻¹‖
          ≤ (B * B) * (D * D) :=
        mul_le_mul hnum hden_add (norm_nonneg _) hnum_nonneg
      _ = B * B * D * D := by ring
  · rw [qPoch_mul_gaussian_center_sub_eq_ratio q hq N r hr]
    rw [div_eq_mul_inv, norm_mul]
    calc
      ‖qPoch (q ^ 2) (q ^ 2) N * qPoch (q ^ 2) (q ^ 2) (2 * N)‖ *
          ‖(qPoch (q ^ 2) (q ^ 2) (N - r) * qPoch (q ^ 2) (q ^ 2) (N + r))⁻¹‖
          ≤ (B * B) * (D * D) :=
        mul_le_mul hnum hden_sub (norm_nonneg _) hnum_nonneg
      _ = B * B * D * D := by ring

/-- The subsequence `(q²;q²)_{2N}` tends to the even infinite product.
@isnad1 id=tendsto.1h1v.s6.98aaba9999a8 from=translated src=- shape=4f9e95e4 vocab=8eef6c4d
-/
theorem tendsto_qPoch_qsq_two_mul (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => qPoch (q ^ 2) (q ^ 2) (2 * N)) atTop
      (𝓝 (∏' n : ℕ, Ch02.jacobiProductEvenFactor q n)) := by
  have h2idx : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
    exact tendsto_atTop_mono (f := fun N : ℕ => N) (g := fun N => 2 * N)
      (fun N => Nat.le_mul_of_pos_left N (by norm_num : 0 < 2)) tendsto_id
  exact (Ch02.tendsto_qPoch_qsq q hq).comp h2idx

/--
For fixed `r`, the centered positive coefficient in the finite JTP limit has
coefficient limit `1`.
@isnad1 id=tendsto.1h2v.s7.cdc45b29bb66 from=translated src=- shape=96d88b71 vocab=000cec04
-/
theorem tendsto_qPoch_mul_gaussian_center_add (q : ℂ) (hq : ‖q‖ < 1) (r : ℕ) :
    Tendsto (fun N : ℕ =>
      qPoch (q ^ 2) (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N + r)) atTop
      (𝓝 1) := by
  let A : ℂ := ∏' n : ℕ, Ch02.jacobiProductEvenFactor q n
  have hA_ne : A ≠ 0 := Ch02.tprod_jacobiProductEvenFactor_ne_zero q hq
  have hN : Tendsto (fun N : ℕ => qPoch (q ^ 2) (q ^ 2) N) atTop (𝓝 A) := by
    simpa [A] using Ch02.tendsto_qPoch_qsq q hq
  have h2N : Tendsto (fun N : ℕ => qPoch (q ^ 2) (q ^ 2) (2 * N)) atTop
      (𝓝 A) := by
    simpa [A] using tendsto_qPoch_qsq_two_mul q hq
  have hadd : Tendsto (fun N : ℕ => qPoch (q ^ 2) (q ^ 2) (N + r)) atTop
      (𝓝 A) := by
    exact hN.comp (tendsto_add_atTop_nat r)
  have hsub : Tendsto (fun N : ℕ => qPoch (q ^ 2) (q ^ 2) (N - r)) atTop
      (𝓝 A) := by
    exact hN.comp (tendsto_sub_atTop_nat r)
  have hratio : Tendsto (fun N : ℕ =>
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (q ^ 2) (q ^ 2) (2 * N)) /
        (qPoch (q ^ 2) (q ^ 2) (N + r) * qPoch (q ^ 2) (q ^ 2) (N - r))) atTop
      (𝓝 ((A * A) / (A * A))) := by
    exact (hN.mul h2N).div (hadd.mul hsub) (mul_ne_zero hA_ne hA_ne)
  have heq : (fun N : ℕ =>
      qPoch (q ^ 2) (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N + r)) =ᶠ[atTop]
      (fun N : ℕ =>
        (qPoch (q ^ 2) (q ^ 2) N * qPoch (q ^ 2) (q ^ 2) (2 * N)) /
          (qPoch (q ^ 2) (q ^ 2) (N + r) * qPoch (q ^ 2) (q ^ 2) (N - r))) := by
    filter_upwards [eventually_ge_atTop r] with N hNge
    exact qPoch_mul_gaussian_center_add_eq_ratio q hq N r hNge
  have hlim : Tendsto (fun N : ℕ =>
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (q ^ 2) (q ^ 2) (2 * N)) /
        (qPoch (q ^ 2) (q ^ 2) (N + r) * qPoch (q ^ 2) (q ^ 2) (N - r))) atTop
      (𝓝 1) := by
    simpa [hA_ne] using hratio
  exact hlim.congr' heq.symm

/--
For fixed `r`, the centered negative coefficient in the finite JTP limit has
coefficient limit `1`.
@isnad1 id=tendsto.1h2v.s7.271a10c25cbe from=translated src=- shape=96d88b71 vocab=357bf765
-/
theorem tendsto_qPoch_mul_gaussian_center_sub (q : ℂ) (hq : ‖q‖ < 1) (r : ℕ) :
    Tendsto (fun N : ℕ =>
      qPoch (q ^ 2) (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N - r)) atTop
      (𝓝 1) := by
  let A : ℂ := ∏' n : ℕ, Ch02.jacobiProductEvenFactor q n
  have hA_ne : A ≠ 0 := Ch02.tprod_jacobiProductEvenFactor_ne_zero q hq
  have hN : Tendsto (fun N : ℕ => qPoch (q ^ 2) (q ^ 2) N) atTop (𝓝 A) := by
    simpa [A] using Ch02.tendsto_qPoch_qsq q hq
  have h2N : Tendsto (fun N : ℕ => qPoch (q ^ 2) (q ^ 2) (2 * N)) atTop
      (𝓝 A) := by
    simpa [A] using tendsto_qPoch_qsq_two_mul q hq
  have hadd : Tendsto (fun N : ℕ => qPoch (q ^ 2) (q ^ 2) (N + r)) atTop
      (𝓝 A) := by
    exact hN.comp (tendsto_add_atTop_nat r)
  have hsub : Tendsto (fun N : ℕ => qPoch (q ^ 2) (q ^ 2) (N - r)) atTop
      (𝓝 A) := by
    exact hN.comp (tendsto_sub_atTop_nat r)
  have hratio : Tendsto (fun N : ℕ =>
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (q ^ 2) (q ^ 2) (2 * N)) /
        (qPoch (q ^ 2) (q ^ 2) (N - r) * qPoch (q ^ 2) (q ^ 2) (N + r))) atTop
      (𝓝 ((A * A) / (A * A))) := by
    exact (hN.mul h2N).div (hsub.mul hadd) (mul_ne_zero hA_ne hA_ne)
  have heq : (fun N : ℕ =>
      qPoch (q ^ 2) (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N - r)) =ᶠ[atTop]
      (fun N : ℕ =>
        (qPoch (q ^ 2) (q ^ 2) N * qPoch (q ^ 2) (q ^ 2) (2 * N)) /
          (qPoch (q ^ 2) (q ^ 2) (N - r) * qPoch (q ^ 2) (q ^ 2) (N + r))) := by
    filter_upwards [eventually_ge_atTop r] with N hNge
    exact qPoch_mul_gaussian_center_sub_eq_ratio q hq N r hNge
  have hlim : Tendsto (fun N : ℕ =>
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (q ^ 2) (q ^ 2) (2 * N)) /
        (qPoch (q ^ 2) (q ^ 2) (N - r) * qPoch (q ^ 2) (q ^ 2) (N + r))) atTop
      (𝓝 1) := by
    simpa [hA_ne] using hratio
  exact hlim.congr' heq.symm

/--
For a fixed nonzero symmetric pair height `r + 1`, the Gaussian-weighted finite
JTP pair converges to Chapter 2's symmetric series pair term.
@isnad1 id=tendsto.1h3v.s8.266a391641be from=translated src=- shape=97446746 vocab=5c4976dd
-/
theorem tendsto_qPoch_mul_gaussian_center_pair (q z : ℂ) (hq : ‖q‖ < 1) (r : ℕ) :
    Tendsto (fun N : ℕ =>
      qPoch (q ^ 2) (q ^ 2) N *
        (gaussianBinom (q ^ 2) (2 * N) (N - (r + 1)) *
            z ^ (-(((r + 1 : ℕ) : ℤ))) * q ^ ((-(((r + 1 : ℕ) : ℤ))) ^ 2) +
          gaussianBinom (q ^ 2) (2 * N) (N + (r + 1)) *
            z ^ (((r + 1 : ℕ) : ℤ)) * q ^ ((((r + 1 : ℕ) : ℤ)) ^ 2))) atTop
      (𝓝 (Ch02.jacobiSeriesSymmetricPairTerm q z r)) := by
  have hneg := (tendsto_qPoch_mul_gaussian_center_sub q hq (r + 1)).mul_const
    (z ^ (-(((r + 1 : ℕ) : ℤ))) * q ^ ((-(((r + 1 : ℕ) : ℤ))) ^ 2))
  have hpos := (tendsto_qPoch_mul_gaussian_center_add q hq (r + 1)).mul_const
    (z ^ (((r + 1 : ℕ) : ℤ)) * q ^ ((((r + 1 : ℕ) : ℤ)) ^ 2))
  convert hneg.add hpos using 1
  · ext N
    ring
  · simp [Ch02.jacobiSeriesSymmetricPairTerm]

/-- The first `M` Gaussian-weighted symmetric nonzero pairs from the finite JTP RHS.-/
noncomputable def gaussianWeightedPairTerm (q z : ℂ) (N r : ℕ) : ℂ :=
  gaussianBinom (q ^ 2) (2 * N) (N - (r + 1)) *
      z ^ (-(((r + 1 : ℕ) : ℤ))) * q ^ ((-(((r + 1 : ℕ) : ℤ))) ^ 2) +
    gaussianBinom (q ^ 2) (2 * N) (N + (r + 1)) *
      z ^ (((r + 1 : ℕ) : ℤ)) * q ^ ((((r + 1 : ℕ) : ℤ)) ^ 2)

/-- Wrapped form of the fixed Gaussian-weighted pair limit.
@isnad1 id=tendsto.1h3v.s6.ef24a4fade09 from=translated src=- shape=a78f8af9 vocab=f958cc16
-/
theorem tendsto_qPoch_mul_gaussianWeightedPairTerm (q z : ℂ) (hq : ‖q‖ < 1)
    (r : ℕ) :
    Tendsto (fun N : ℕ =>
      qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTerm q z N r) atTop
      (𝓝 (Ch02.jacobiSeriesSymmetricPairTerm q z r)) := by
  simpa [gaussianWeightedPairTerm] using tendsto_qPoch_mul_gaussian_center_pair q z hq r

/-- The first `M` Gaussian-weighted symmetric nonzero pairs from the finite JTP RHS.-/
noncomputable def gaussianWeightedPairPartial (q z : ℂ) (N M : ℕ) : ℂ :=
  ∑ r ∈ Finset.range M, gaussianWeightedPairTerm q z N r

/--
@isnad1 id=eq.0h3v.s4.8b07c89b76d4 from=translated src=- shape=b99ec26b vocab=99ba63fc
-/
@[simp] theorem gaussianWeightedPairPartial_zero (q z : ℂ) (N : ℕ) :
    gaussianWeightedPairPartial q z N 0 = 0 := by
  simp [gaussianWeightedPairPartial]

/-- The tail of Gaussian-weighted symmetric nonzero pairs from indices `M, ..., K - 1`.-/
noncomputable def gaussianWeightedPairTail (q z : ℂ) (N M K : ℕ) : ℂ :=
  ∑ r ∈ Finset.Ico M K, gaussianWeightedPairTerm q z N r

/--
The zero-extended shifted Gaussian tail summand. For fixed lower index `M`,
the moving finite tail `M ≤ r < N` is represented by the `k`-indexed summand
with `r = M + k`, extended by zero once `M + k ≥ N`.-/
noncomputable def gaussianWeightedTailSummand (q z : ℂ) (N M k : ℕ) : ℂ :=
  if M + k < N then
    qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTerm q z N (M + k)
  else
    0

/--
Uniform domination of the zero-extended Gaussian tail summands by Chapter 2's
two-term symmetric-pair norm majorant.
@isnad1 id=ex.1h3v.s6.9230b216cb83 from=translated src=- shape=ec2bb7c6 vocab=bdeaa0be
-/
theorem exists_gaussianWeightedTailSummand_pairMajorant_bound (q z : ℂ)
    (hq : ‖q‖ < 1) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N in atTop, ∀ k,
        ‖gaussianWeightedTailSummand q z N M k‖ ≤
          C * Ch02.jacobiSeriesSymmetricPairNormMajorant q z (k + M) := by
  rcases exists_qPoch_mul_gaussian_center_norm_bound q hq with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, Eventually.of_forall fun N k => ?_⟩
  by_cases hlt : M + k < N
  · have hMk : M + k = k + M := by omega
    have hoff : k + M + 1 ≤ N := by omega
    have hcoeff := hC N (k + M + 1) hoff
    let negTerm : ℂ :=
      z ^ (-(((k + M + 1 : ℕ) : ℤ))) * q ^ ((-(((k + M + 1 : ℕ) : ℤ))) ^ 2)
    let posTerm : ℂ :=
      z ^ (((k + M + 1 : ℕ) : ℤ)) * q ^ ((((k + M + 1 : ℕ) : ℤ)) ^ 2)
    let coeffNeg : ℂ :=
      qPoch (q ^ 2) (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N - (k + M + 1))
    let coeffPos : ℂ :=
      qPoch (q ^ 2) (q ^ 2) N * gaussianBinom (q ^ 2) (2 * N) (N + (k + M + 1))
    have hterm :
        qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTerm q z N (k + M) =
          coeffNeg * negTerm + coeffPos * posTerm := by
      dsimp [coeffNeg, coeffPos, negTerm, posTerm]
      simp [gaussianWeightedPairTerm]
      ring
    rw [gaussianWeightedTailSummand, ite_eq_left hlt, hMk, hterm]
    calc
      ‖coeffNeg * negTerm + coeffPos * posTerm‖
          ≤ ‖coeffNeg * negTerm‖ + ‖coeffPos * posTerm‖ :=
        norm_add_le _ _
      _ ≤ C * ‖negTerm‖ + C * ‖posTerm‖ := by
        have hneg : ‖coeffNeg * negTerm‖ ≤ C * ‖negTerm‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hcoeff.2 (norm_nonneg _)
        have hpos : ‖coeffPos * posTerm‖ ≤ C * ‖posTerm‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hcoeff.1 (norm_nonneg _)
        exact add_le_add
          hneg hpos
      _ = C * Ch02.jacobiSeriesSymmetricPairNormMajorant q z (k + M) := by
        dsimp [negTerm, posTerm]
        rw [Ch02.jacobiSeriesSymmetricPairNormMajorant]
        rw [mul_add]
        norm_num [Int.natCast_add]
  · rw [gaussianWeightedTailSummand, ite_eq_right hlt, norm_zero]
    exact mul_nonneg hC_nonneg (by
      rw [Ch02.jacobiSeriesSymmetricPairNormMajorant]
      positivity)

/-- Pointwise limit of each zero-extended shifted Gaussian tail summand.
@isnad1 id=tendsto.1h4v.s5.b6e1f91a2da4 from=translated src=- shape=dcb35644 vocab=f7f78368
-/
theorem tendsto_gaussianWeightedTailSummand (q z : ℂ) (hq : ‖q‖ < 1)
    (M k : ℕ) :
    Tendsto (fun N : ℕ => gaussianWeightedTailSummand q z N M k) atTop
      (𝓝 (Ch02.jacobiSeriesSymmetricPairTerm q z (M + k))) := by
  have hbase := tendsto_qPoch_mul_gaussianWeightedPairTerm q z hq (M + k)
  refine hbase.congr' ?_
  filter_upwards [eventually_gt_atTop (M + k)] with N hN
  simp [gaussianWeightedTailSummand, hN]

/-- The moving Gaussian tail as a shifted range sum.
@isnad1 id=eq.0h4v.s7.55396930e016 from=translated src=- shape=b6d923cd vocab=3443c3ae
-/
theorem qPoch_mul_gaussianWeightedPairTail_eq_shiftedRange_sum (q z : ℂ)
    (N M : ℕ) :
    qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTail q z N M N =
      ∑ k ∈ Finset.range (N - M),
        qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTerm q z N (M + k) := by
  simp only [gaussianWeightedPairTail, Finset.mul_sum]
  rw [Finset.sum_Ico_eq_sum_range]

/-- The moving Gaussian tail as a shifted range sum of zero-extended summands.
@isnad1 id=eq.0h4v.s6.63ac964e753e from=translated src=- shape=4b0b1c55 vocab=f70b0321
-/
theorem qPoch_mul_gaussianWeightedPairTail_eq_shiftedTailSummand_sum (q z : ℂ)
    (N M : ℕ) :
    qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTail q z N M N =
      ∑ k ∈ Finset.range (N - M), gaussianWeightedTailSummand q z N M k := by
  rw [qPoch_mul_gaussianWeightedPairTail_eq_shiftedRange_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hklt : k < N - M := by simpa using hk
  have hMN : M + k < N := by omega
  simp [gaussianWeightedTailSummand, hMN]

/-- Tsum form of the zero-extended shifted Gaussian tail summands.
@isnad1 id=eq.0h4v.s6.550b1c7ba354 from=translated src=- shape=0fb73869 vocab=101ddaf3
-/
theorem tsum_gaussianWeightedTailSummand (q z : ℂ) (N M : ℕ) :
    (∑' k : ℕ, gaussianWeightedTailSummand q z N M k) =
      qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTail q z N M N := by
  rw [tsum_eq_sum (s := Finset.range (N - M))]
  · rw [qPoch_mul_gaussianWeightedPairTail_eq_shiftedTailSummand_sum]
  · intro k hk
    have hkge : N - M ≤ k := by simpa using hk
    have hnot : ¬ M + k < N := by omega
    simp [gaussianWeightedTailSummand, hnot]

/--
Splitting the full `N`-pair Gaussian block into its first `M` pairs and the
remaining finite tail.
@isnad1 id=eq.1h4v.s5.6280a79e9af3 from=translated src=- shape=ffa05503 vocab=e20c3fc0
-/
theorem gaussianWeightedPairPartial_eq_add_tail (q z : ℂ) {N M : ℕ} (hMN : M ≤ N) :
    gaussianWeightedPairPartial q z N N =
      gaussianWeightedPairPartial q z N M + gaussianWeightedPairTail q z N M N := by
  simp only [gaussianWeightedPairPartial, gaussianWeightedPairTail]
  exact (Finset.sum_range_add_sum_Ico _ hMN).symm

/--
For fixed `M`, the first `M` Gaussian-weighted finite-JTP pairs converge to
Chapter 2's symmetric pair partial after multiplication by `(q²;q²)_N`.
@isnad1 id=tendsto.1h3v.s6.12cdfb0fc45d from=translated src=- shape=a78f8af9 vocab=27cadc72
-/
theorem tendsto_qPoch_mul_gaussianWeightedPairPartial (q z : ℂ) (hq : ‖q‖ < 1)
    (M : ℕ) :
    Tendsto (fun N : ℕ =>
      qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairPartial q z N M) atTop
      (𝓝 (Ch02.jacobiSeriesSymmetricPairPartial q z M)) := by
  simpa [gaussianWeightedPairPartial, gaussianWeightedPairTerm,
    Ch02.jacobiSeriesSymmetricPairPartial, Finset.mul_sum]
    using tendsto_finsetSum (Finset.range M)
      (fun r _ => tendsto_qPoch_mul_gaussian_center_pair q z hq r)

/-- The centered term plus the first `M` Gaussian-weighted symmetric nonzero pairs.-/
noncomputable def gaussianWeightedSymmetricPartial (q z : ℂ) (N M : ℕ) : ℂ :=
  gaussianBinom (q ^ 2) (2 * N) N + gaussianWeightedPairPartial q z N M

/--
Splitting the full centered Gaussian block into a fixed symmetric core and its
remaining finite nonzero-pair tail.
@isnad1 id=eq.1h4v.s5.3bb536f4ee13 from=translated src=- shape=ffa05503 vocab=25b61eb4
-/
theorem gaussianWeightedSymmetricPartial_eq_add_tail (q z : ℂ) {N M : ℕ} (hMN : M ≤ N) :
    gaussianWeightedSymmetricPartial q z N N =
      gaussianWeightedSymmetricPartial q z N M + gaussianWeightedPairTail q z N M N := by
  simp only [gaussianWeightedSymmetricPartial]
  rw [gaussianWeightedPairPartial_eq_add_tail q z hMN]
  ring

/--
For fixed `M`, the centered Gaussian-weighted finite-JTP block converges to
Chapter 2's symmetric series partial after multiplication by `(q²;q²)_N`.
@isnad1 id=tendsto.1h3v.s6.593bd8d03bfa from=translated src=- shape=a78f8af9 vocab=99dc9e9a
-/
theorem tendsto_qPoch_mul_gaussianWeightedSymmetricPartial (q z : ℂ)
    (hq : ‖q‖ < 1) (M : ℕ) :
    Tendsto (fun N : ℕ =>
      qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedSymmetricPartial q z N M) atTop
      (𝓝 (Ch02.jacobiSeriesSymmetricPartial q z M)) := by
  have hzero := tendsto_qPoch_mul_gaussian_center_add q hq 0
  have hpairs := tendsto_qPoch_mul_gaussianWeightedPairPartial q z hq M
  convert hzero.add hpairs using 1
  · ext N
    simp [gaussianWeightedSymmetricPartial]
    ring
  · rw [Ch02.jacobiSeriesSymmetricPartial_eq_one_add_pairPartial]

/-- A single Gaussian-weighted Laurent summand after the finite-JTP substitution.-/
noncomputable def gaussianWeightedLaurentSummand (q z : ℂ) (N k : ℕ) : ℂ :=
  gaussianBinom (q ^ 2) (2 * N) k * z ^ ((k : Int) - (N : Int)) *
    q ^ (((k : Int) - (N : Int)) ^ 2)

/--
The full centered symmetric Gaussian block is exactly the weighted Laurent
`natSum` over `k = 0, ..., 2N`, just reordered into symmetric pairs.
@isnad1 id=eq.0h3v.s5.21e633ab0f2b from=translated src=- shape=1215dfd9 vocab=a374b2ac
-/
theorem gaussianWeightedSymmetricPartial_eq_weightedLaurentNatSum (q z : ℂ) (N : ℕ) :
    gaussianWeightedSymmetricPartial q z N N =
      natSum (gaussianWeightedLaurentSummand q z N) (2 * N) := by
  rw [natSum_eq_sum_range]
  rw [show 2 * N + 1 = N + (N + 1) by omega]
  rw [Finset.sum_range_add]
  rw [Finset.sum_range_succ']
  rw [← Finset.sum_range_reflect (gaussianWeightedLaurentSummand q z N) N]
  simp only [gaussianWeightedSymmetricPartial, gaussianWeightedPairPartial,
    gaussianWeightedPairTerm, gaussianWeightedLaurentSummand]
  rw [Finset.sum_add_distrib]
  have hleft :
      (∑ j ∈ Finset.range N,
        gaussianBinom (q ^ 2) (2 * N) (N - 1 - j) *
          z ^ ((↑(N - 1 - j) : Int) - ↑N) * q ^ (((↑(N - 1 - j) : Int) - ↑N) ^ 2)) =
      ∑ r ∈ Finset.range N,
        gaussianBinom (q ^ 2) (2 * N) (N - (r + 1)) *
          z ^ (-(((r + 1 : ℕ) : ℤ))) * q ^ ((-(((r + 1 : ℕ) : ℤ))) ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hrlt : r < N := by simpa using hr
    have hidx : N - 1 - r = N - (r + 1) := by omega
    have hcast : ((N - (r + 1) : ℕ) : ℤ) - (N : ℤ) =
        -(((r + 1 : ℕ) : ℤ)) := by
      omega
    rw [hidx, hcast]
  have hright :
      (∑ k ∈ Finset.range N,
        gaussianBinom (q ^ 2) (2 * N) (N + (k + 1)) *
          z ^ ((↑(N + (k + 1)) : Int) - ↑N) * q ^ (((↑(N + (k + 1)) : Int) - ↑N) ^ 2)) =
      ∑ r ∈ Finset.range N,
        gaussianBinom (q ^ 2) (2 * N) (N + (r + 1)) *
          z ^ (((r + 1 : ℕ) : ℤ)) * q ^ ((((r + 1 : ℕ) : ℤ)) ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro r _
    have hcast : ((N + (r + 1) : ℕ) : ℤ) - (N : ℤ) = (((r + 1 : ℕ) : ℤ)) := by
      omega
    rw [hcast]
  rw [hleft, hright]
  simp
  ring

end ComplexLimits

section FiniteJTP

open Filter
open scoped Topology

variable {R : Type*} [Field R]

/--
The `k`-indexed summand for Chan's finite Jacobi triple product.

This encodes the bilateral index `l = k - n`, with `k = 0, ..., 2n`.
Using the integer power `(-z) ^ l` keeps the negative Laurent monomials
instead of truncating negative indices through `Int.toNat`.-/
def finiteJTPSummand (q z : R) (n k : Nat) : R :=
  let l : Int := (k : Int) - (n : Int)
  gaussianBinom q (2 * n) k *
    q ^ ((l * (l - 1) / 2).toNat) *
    (-z) ^ l

/--
The finite bilateral sum in Chan Eq (3.15), encoded as the ordinary finite
sum over `k = 0, ..., 2n` after the change of variables `l = k - n`.-/
def finiteJTPRHS (q z : R) (n : Nat) : R :=
  natSum (fun k => finiteJTPSummand q z n k) (2 * n)

/-- The `n = 0` finite Jacobi triple product check.
@isnad1 id=eq.0h3v.s6.518d7dfbdc22 from=translated src=- shape=c815c268 vocab=e309e9aa
-/
theorem finite_jacobi_triple_product_zero (q z : R) :
    qPoch z q 0 * qPoch (z⁻¹ * q) q 0 = finiteJTPRHS q z 0 := by
  simp [finiteJTPRHS, finiteJTPSummand]

/--
The `n = 1` finite Jacobi triple product check:
`(1 - z) (1 - z^{-1} q) = -q z^{-1} + (1 + q) - z`.
@isnad1 id=eq.1h3v.s6.65e2c7fb8038 from=translated src=- shape=48520e40 vocab=e309e9aa
-/
theorem finite_jacobi_triple_product_one (q z : R) (hz : z ≠ 0) :
    qPoch z q 1 * qPoch (z⁻¹ * q) q 1 = finiteJTPRHS q z 1 := by
  norm_num [finiteJTPRHS, finiteJTPSummand, qPoch, gaussianBinom, natSum]
  field_simp [hz]
  ring_nf

/-- The `n = 2` finite Jacobi triple product check.
@isnad1 id=eq.1h3v.s6.f7b1b0ed709e from=translated src=- shape=48520e40 vocab=e309e9aa
-/
theorem finite_jacobi_triple_product_two (q z : R) (hz : z ≠ 0) :
    qPoch z q 2 * qPoch (z⁻¹ * q) q 2 = finiteJTPRHS q z 2 := by
  norm_num [finiteJTPRHS, finiteJTPSummand, qPoch, gaussianBinom, natSum]
  field_simp [hz]
  rw [show Int.toNat (3 : Int) = 3 by rfl]
  ring_nf

/-- The `n = 3` finite Jacobi triple product check.
@isnad1 id=eq.1h3v.s6.73ab8c4ca6ea from=translated src=- shape=48520e40 vocab=e309e9aa
-/
theorem finite_jacobi_triple_product_three (q z : R) (hz : z ≠ 0) :
    qPoch z q 3 * qPoch (z⁻¹ * q) q 3 = finiteJTPRHS q z 3 := by
  norm_num [finiteJTPRHS, finiteJTPSummand, qPoch, gaussianBinom, natSum]
  field_simp [hz]
  rw [show Int.toNat (3 : Int) = 3 by rfl]
  rw [show Int.toNat (6 : Int) = 6 by rfl]
  ring_nf

/--
@isnad1 id=eq.0h1v.s4.1d6286d51462 from=translated src=- shape=a0ed7b26 vocab=58e96b90
-/
lemma triangular_succ_add (n : Nat) :
    triangular (Nat.succ n) = triangular n + Nat.succ n := by
  simpa [triangular, Nat.succ_eq_add_one, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using Nat.triangle_succ (Nat.succ n)

/--
@isnad1 id=eq.0h4v.s6.7b966f5f2522 from=translated src=- shape=64f3124d vocab=355782a3
-/
lemma qPoch_succ_front (a q : R) (n : Nat) :
    qPoch a q (Nat.succ n) = (1 - a) * qPoch (a * q) q n := by
  have h := qPoch_add q a 1 n
  simpa [qPoch, Nat.one_add, pow_one, mul_comm, mul_left_comm, mul_assoc] using h

/--
@isnad1 id=eq.2h4v.s8.a7d9744a1f9e from=translated src=- shape=704be3d4 vocab=c4aa4290
-/
lemma one_sub_div_qpow_succ (q z : R) (hz : z ≠ 0) (hq : q ≠ 0) (n : Nat) :
    1 - z / q ^ Nat.succ n =
      (-z) * (q ^ Nat.succ n)⁻¹ * (1 - z⁻¹ * q ^ Nat.succ n) := by
  have hqpow : q ^ Nat.succ n ≠ 0 := pow_ne_zero _ hq
  field_simp [hz, hqpow]
  ring

/--
@isnad1 id=eq.2h4v.s7.ddf34fbbcec3 from=translated src=- shape=812100a9 vocab=b39e3c35
-/
lemma qPoch_substitute_div_qpow (q z : R) (hz : z ≠ 0) (hq : q ≠ 0) :
    ∀ n : Nat,
      qPoch (z / q ^ n) q n =
        (-z) ^ n * (q ^ triangular n)⁻¹ * qPoch (z⁻¹ * q) q n
  | 0 => by
      simp [triangular]
  | Nat.succ n => by
      have hqpow : q ^ n ≠ 0 := pow_ne_zero _ hq
      have hqpow_succ : q ^ Nat.succ n ≠ 0 := pow_ne_zero _ hq
      calc
        qPoch (z / q ^ Nat.succ n) q (Nat.succ n)
            = (1 - z / q ^ Nat.succ n) *
                qPoch ((z / q ^ Nat.succ n) * q) q n := by
              rw [qPoch_succ_front]
        _ = (1 - z / q ^ Nat.succ n) * qPoch (z / q ^ n) q n := by
              have harg : (z / q ^ Nat.succ n) * q = z / q ^ n := by
                rw [pow_succ]
                field_simp [hq, hqpow]
              rw [harg]
        _ = ((-z) * (q ^ Nat.succ n)⁻¹ * (1 - z⁻¹ * q ^ Nat.succ n)) *
              qPoch (z / q ^ n) q n := by
              rw [one_sub_div_qpow_succ q z hz hq n]
        _ = ((-z) * (q ^ Nat.succ n)⁻¹ * (1 - z⁻¹ * q ^ Nat.succ n)) *
              ((-z) ^ n * (q ^ triangular n)⁻¹ * qPoch (z⁻¹ * q) q n) := by
              rw [qPoch_substitute_div_qpow q z hz hq n]
        _ = (-z) ^ Nat.succ n * (q ^ triangular (Nat.succ n))⁻¹ *
              qPoch (z⁻¹ * q) q (Nat.succ n) := by
              rw [qPoch_succ, triangular_succ_add]
              rw [pow_add]
              field_simp [hz, hq, hqpow, hqpow_succ]
              rw [pow_succ (-z) n, pow_succ q n]
              ring_nf

/--
@isnad1 id=eq.2h4v.s8.68220667ee13 from=translated src=- shape=38f56c09 vocab=b39e3c35
-/
lemma qPoch_substitute_div_qpow_two_mul (q z : R) (hz : z ≠ 0) (hq : q ≠ 0)
    (n : Nat) :
    qPoch (z / q ^ n) q (2 * n) =
      (-z) ^ n * (q ^ triangular n)⁻¹ *
        (qPoch (z⁻¹ * q) q n * qPoch z q n) := by
  have hsplit := qPoch_split q (z / q ^ n) (2 * n) n (by omega)
  have hqpow : q ^ n ≠ 0 := pow_ne_zero _ hq
  have harg : (z / q ^ n) * q ^ n = z := by
    field_simp [hqpow]
  calc
    qPoch (z / q ^ n) q (2 * n)
        = qPoch (z / q ^ n) q n * qPoch ((z / q ^ n) * q ^ n) q (2 * n - n) := hsplit
    _ = qPoch (z / q ^ n) q n * qPoch z q n := by
          rw [harg]
          congr 1
          congr 1
          omega
    _ = (-z) ^ n * (q ^ triangular n)⁻¹ *
          (qPoch (z⁻¹ * q) q n * qPoch z q n) := by
          rw [qPoch_substitute_div_qpow q z hz hq n]
          ring

/--
Rearranged finite reflection identity for the centered product
`(z / q^n; q)_{2n}`.  This is the division-free form of
`qPoch_substitute_div_qpow_two_mul`.
@isnad1 id=eq.2h4v.s8.c69b100887a1 from=translated src=- shape=670823b2 vocab=b39e3c35
-/
theorem qPoch_reflection_two_mul_shifted (q z : R) (hq : q ≠ 0) (hz : z ≠ 0)
    (n : Nat) :
    qPoch (z / q ^ n) q (2 * n) * q ^ triangular n =
      (-z) ^ n * qPoch (z⁻¹ * q) q n * qPoch z q n := by
  have hqtri : q ^ triangular n ≠ 0 := pow_ne_zero _ hq
  rw [qPoch_substitute_div_qpow_two_mul q z hz hq n]
  field_simp [hqtri]

/-! ### Summand and sum identities for the finite Jacobi triple product -/

/-- `(-z)^(n:Nat) * (-z)^((k:Int) - (n:Int)) = (-z)^(k:Nat)` when `z ≠ 0`.-/
private lemma neg_z_zpow_shift (z : R) (hz : z ≠ 0) (n k : Nat) :
    (-z) ^ (n : Nat) * (-z) ^ ((k : Int) - (n : Int)) = (-z) ^ (k : Nat) := by
  have hnz : (-z : R) ≠ 0 := neg_ne_zero.mpr hz
  rw [← zpow_natCast (-z) n, ← zpow_natCast (-z) k, ← zpow_add₀ hnz]
  congr 1
  ring

/-- The integer `l * (l - 1) / 2` is non-negative.-/
private lemma int_l_mul_l_sub_one_div_two_nonneg (l : Int) : 0 ≤ l * (l - 1) / 2 := by
  apply Int.ediv_nonneg _ (by omega)
  nlinarith [sq_nonneg (2 * l - 1)]

/-- Two divides any product of consecutive integers.-/
private lemma int_two_dvd_mul_pred (l : Int) : (2 : Int) ∣ l * (l - 1) := by
  rcases Int.even_or_odd l with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (l - 1), by rw [hm]; ring⟩
  · exact ⟨l * m, by rw [hm]; ring⟩

/-- Key Nat-level exponent identity for the finite JTP:
`(l*(l-1)/2).toNat + n*k = k*(k-1)/2 + triangular n` where `l = k - n`.-/
private lemma finiteJTP_exponent_shift (n k : Nat) :
    ((((k : Int) - (n : Int)) * (((k : Int) - (n : Int)) - 1) / 2).toNat) + n * k =
      k * (k - 1) / 2 + triangular n := by
  set l : Int := (k : Int) - (n : Int)
  have hl_nn : 0 ≤ l * (l - 1) / 2 := int_l_mul_l_sub_one_div_two_nonneg l
  apply Nat.cast_injective (R := Rat)
  have hE_cast :
      (((((l * (l - 1) / 2 : Int).toNat) : Nat) : Rat) =
        (l : Rat) * ((l : Rat) - 1) / 2) := by
    have hto_int : (((l * (l - 1) / 2 : Int).toNat : Int) = l * (l - 1) / 2) :=
      Int.toNat_of_nonneg hl_nn
    have hto_rat :
        (((((l * (l - 1) / 2 : Int).toNat) : Nat) : Rat) =
          ((l * (l - 1) / 2 : Int) : Rat)) := by
      exact_mod_cast hto_int
    rw [hto_rat]
    rw [Int.cast_div (int_two_dvd_mul_pred l)
      (by norm_num : ((2 : Int) : Rat) ≠ 0)]
    push_cast
    ring
  have hk_cast :
      (((k * (k - 1) / 2 : Nat) : Rat) =
        (k : Rat) * ((k : Rat) - 1) / 2) := by
    rw [← Nat.choose_two_right k]
    rw [Nat.cast_choose_two Rat k]
  have htri_cast :
      ((triangular n : Nat) : Rat) = (n : Rat) * ((n : Rat) + 1) / 2 := by
    rw [show triangular n = Nat.choose (n + 1) 2 by
      rw [Nat.choose_two_right]
      simp [triangular, Nat.mul_comm]]
    rw [Nat.cast_choose_two Rat (n + 1)]
    push_cast
    ring
  simp only [Nat.cast_add, Nat.cast_mul]
  rw [hE_cast, hk_cast, htri_cast]
  subst l
  push_cast
  ring

/-- Each summand of `finiteJTPRHS`, multiplied by `(-z)^n`, equals the
corresponding q-binomial theorem term (at `z/q^n`) times `q^{tri n}`.-/
private lemma summand_shift (q z : R) (hz : z ≠ 0) (hq : q ≠ 0) (n k : Nat) :
    (-z) ^ n * finiteJTPSummand q z n k =
      gaussianBinom q (2 * n) k * q ^ (k * (k - 1) / 2) * (-1) ^ k *
        (z / q ^ n) ^ k * q ^ (triangular n) := by
  simp only [finiteJTPSummand]
  set l : Int := (k : Int) - (n : Int)
  have hqn : q ^ n ≠ 0 := pow_ne_zero _ hq
  have hqnk : q ^ (n * k) ≠ 0 := pow_ne_zero _ hq
  have hqtri : q ^ (triangular n) ≠ 0 := pow_ne_zero _ hq
  -- Step 1: (-z)^n * (-z)^l = (-z)^k
  have hzpow : (-z) ^ n * (-z) ^ l = (-z) ^ k := neg_z_zpow_shift z hz n k
  -- Step 2: (-z)^k = (-1)^k * z^k
  have hneg_z_k : (-z : R) ^ k = (-1 : R) ^ k * z ^ k := by
    rw [show (-z : R) = (-1 : R) * z from by ring, mul_pow]
  -- Step 3: (z/q^n)^k = z^k / q^{nk}
  have hdiv_k : (z / q ^ n) ^ k = z ^ k / q ^ (n * k) := by
    rw [div_pow, ← pow_mul]
  -- Step 4: Exponent identity
  have hexp := finiteJTP_exponent_shift n k
  -- Combine: LHS = gauss * q^{toNat} * (-z)^n * (-z)^l = gauss * q^{toNat} * (-1)^k * z^k
  -- RHS = gauss * q^{k(k-1)/2} * (-1)^k * z^k / q^{nk} * q^{tri n}
  -- So need: q^{toNat} = q^{k(k-1)/2 + tri n - nk}
  -- which is: q^{toNat + nk} = q^{k(k-1)/2 + tri n}
  -- which is hexp
  rw [hdiv_k]
  field_simp [hqn, hqnk, hqtri]
  calc
    (-z) ^ n * gaussianBinom q (2 * n) k * q ^ (l * (l - 1) / 2).toNat *
          (-z) ^ l * q ^ (n * k)
        = gaussianBinom q (2 * n) k * ((-1 : R) ^ k * z ^ k) *
            (q ^ (l * (l - 1) / 2).toNat * q ^ (n * k)) := by
          rw [show (-z) ^ n * gaussianBinom q (2 * n) k *
              q ^ (l * (l - 1) / 2).toNat * (-z) ^ l * q ^ (n * k) =
              gaussianBinom q (2 * n) k * q ^ (l * (l - 1) / 2).toNat *
                ((-z) ^ n * (-z) ^ l) * q ^ (n * k) by ring]
          rw [hzpow, hneg_z_k]
          ring
    _ = gaussianBinom q (2 * n) k * ((-1 : R) ^ k * z ^ k) *
            q ^ ((l * (l - 1) / 2).toNat + n * k) := by
          rw [pow_add]
    _ = gaussianBinom q (2 * n) k * ((-1 : R) ^ k * z ^ k) *
            q ^ (k * (k - 1) / 2 + triangular n) := by
          rw [show (l * (l - 1) / 2).toNat + n * k =
            k * (k - 1) / 2 + triangular n from by simpa [l] using hexp]
    _ = gaussianBinom q (2 * n) k * q ^ (k * (k - 1) / 2) *
          (-1 : R) ^ k * z ^ k * q ^ triangular n := by
          rw [pow_add]
          ring

/--
After the substitution `q ↦ q²`, `z ↦ -zq`, a finite-JTP summand is exactly
the Laurent monomial `z^l q^{l²}` times the finite Gaussian factor, where
`l = k - n`.
@isnad1 id=eq.1h4v.s7.7f517a0e5a8e from=translated src=- shape=4e35153c vocab=831bb017
-/
theorem finiteJTPSummand_qsq_neg_zq (q z : ℂ) (hq : q ≠ 0) (n k : Nat) :
    finiteJTPSummand (q ^ 2) (-(z * q)) n k =
      gaussianBinom (q ^ 2) (2 * n) k * z ^ ((k : Int) - (n : Int)) *
        q ^ (((k : Int) - (n : Int)) ^ 2) := by
  simp only [finiteJTPSummand]
  set l : Int := (k : Int) - (n : Int)
  have hl_nonneg : 0 ≤ l * (l - 1) / 2 := int_l_mul_l_sub_one_div_two_nonneg l
  have htwo : (2 : Int) ∣ l * (l - 1) := int_two_dvd_mul_pred l
  have hpow : (q ^ 2) ^ (l * (l - 1) / 2).toNat = q ^ (l * (l - 1)) := by
    have hto : (((l * (l - 1) / 2).toNat : Int) = l * (l - 1) / 2) :=
      Int.toNat_of_nonneg hl_nonneg
    rw [← zpow_natCast (q ^ 2) (l * (l - 1) / 2).toNat]
    rw [hto]
    change (q ^ (2 : ℤ)) ^ (l * (l - 1) / 2) = q ^ (l * (l - 1))
    rw [← zpow_mul q (2 : ℤ) (l * (l - 1) / 2)]
    congr 1
    have hdiv := Int.ediv_mul_cancel htwo
    omega
  rw [hpow]
  rw [show -(-(z * q)) = z * q by ring]
  rw [mul_zpow]
  rw [show gaussianBinom (q ^ 2) (2 * n) k * q ^ (l * (l - 1)) * (z ^ l * q ^ l) =
      gaussianBinom (q ^ 2) (2 * n) k * z ^ l * (q ^ (l * (l - 1)) * q ^ l) by
    ring]
  rw [← zpow_add₀ hq]
  congr 2
  ring

/-- The finite-JTP RHS after `q ↦ q²`, `z ↦ -zq` as a weighted symmetric Laurent sum.
@isnad1 id=eq.1h3v.s7.3e309d040c4a from=translated src=- shape=e96ee33d vocab=d5b65e20
-/
theorem finiteJTPRHS_qsq_neg_zq (q z : ℂ) (hq : q ≠ 0) (n : Nat) :
    finiteJTPRHS (q ^ 2) (-(z * q)) n =
      natSum (fun k =>
        gaussianBinom (q ^ 2) (2 * n) k * z ^ ((k : Int) - (n : Int)) *
          q ^ (((k : Int) - (n : Int)) ^ 2)) (2 * n) := by
  unfold finiteJTPRHS
  exact natSum_congr_le (2 * n) fun k _ => finiteJTPSummand_qsq_neg_zq q z hq n k

/-- The core sum identity: `(-z)^n * finiteJTPRHS = qPoch(z/q^n, q, 2n) * q^{tri n}`.-/
private lemma finiteJTPRHS_mul_neg_z_pow (q z : R) (hz : z ≠ 0) (hq : q ≠ 0) (n : Nat) :
    (-z) ^ n * finiteJTPRHS q z n =
      qPoch (z / q ^ n) q (2 * n) * q ^ (triangular n) := by
  rw [qBinomialTheorem_chanForm q (z / q ^ n) (2 * n)]
  simp only [finiteJTPRHS]
  -- LHS = ∑ ((-z)^n * summand_k), RHS = (∑ chan_k) * q^{tri n} = ∑ (chan_k * q^{tri n})
  rw [← natSum_mul_left ((-z) ^ n)
    (fun k => finiteJTPSummand q z n k) (2 * n)]
  rw [← natSum_mul_right
    (fun k => gaussianBinom q (2 * n) k * q ^ (k * (k - 1) / 2) *
      (-1) ^ k * (z / q ^ n) ^ k) (q ^ triangular n) (2 * n)]
  exact natSum_congr_le (2 * n) fun k _ => summand_shift q z hz hq n k

/--
**The finite Jacobi triple product** (Chan, Theorem 3.3):
`(z; q)_n (z⁻¹ q; q)_n = ∑_{k=0}^{2n} [2n, k]_q  q^{(k−n)(k−n−1)/2} (−z)^{k−n}`.
@isnad1 id=eq.2h4v.s6.e00736c3935b from=translated src=- shape=0f2e617e vocab=e309e9aa
-/
theorem finite_jacobi_triple_product (q z : R) (hz : z ≠ 0) (hq : q ≠ 0) (n : Nat) :
    qPoch z q n * qPoch (z⁻¹ * q) q n = finiteJTPRHS q z n := by
  have hnz : (-z) ^ n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hz)
  have hrefl := qPoch_reflection_two_mul_shifted q z hq hz n
  have hsum := finiteJTPRHS_mul_neg_z_pow q z hz hq n
  -- hrefl : qPoch(z/q^n, q, 2n) * q^{tri n} = (-z)^n * (z⁻¹q;q)_n * (z;q)_n
  -- hsum  : (-z)^n * finiteJTPRHS = qPoch(z/q^n, q, 2n) * q^{tri n}
  -- Therefore: (-z)^n * finiteJTPRHS = (-z)^n * (z;q)_n * (z⁻¹q;q)_n
  have h : (-z) ^ n * finiteJTPRHS q z n =
      (-z) ^ n * (qPoch z q n * qPoch (z⁻¹ * q) q n) := by
    rw [hsum, hrefl]; ring
  exact (mul_left_cancel₀ hnz h).symm

/--
Chapter 2's zero-based finite product is the even q-Pochhammer factor times
Chapter 3's finite JTP RHS after the substitution `q ↦ q²`, `z ↦ -zq`.
@isnad1 id=eq.2h3v.s6.8bf6b4c1dd91 from=translated src=- shape=ebbc2622 vocab=76808742
-/
theorem jacobiProductPartial_eq_qPoch_mul_finiteJTPRHS (q z : ℂ)
    (hq : q ≠ 0) (hz : z ≠ 0) (n : Nat) :
    Ch02.jacobiProductPartial q z n =
      qPoch (q ^ 2) (q ^ 2) n * finiteJTPRHS (q ^ 2) (-(z * q)) n := by
  rw [Ch02.jacobiProductPartial_eq_qPoch]
  have hparam : (-(z * q))⁻¹ * q ^ 2 = -(z⁻¹ * q) := by
    field_simp [hq, hz]
  have hfinite := finite_jacobi_triple_product (q ^ 2) (-(z * q))
    (neg_ne_zero.mpr (mul_ne_zero hz hq)) (pow_ne_zero 2 hq) n
  rw [hparam] at hfinite
  rw [← hfinite]
  ring

/--
Chapter 2's finite product partial as the even q-Pochhammer factor times a
Gaussian-weighted symmetric Laurent sum. This is the finite-limit form needed
to pass from Chapter 3's finite JTP to Chapter 2's infinite JTP.
@isnad1 id=eq.2h3v.s7.bf44dd6479b7 from=translated src=- shape=8a9d0ee0 vocab=66dab43d
-/
theorem jacobiProductPartial_eq_qPoch_mul_weightedLaurentSum (q z : ℂ)
    (hq : q ≠ 0) (hz : z ≠ 0) (n : Nat) :
    Ch02.jacobiProductPartial q z n =
      qPoch (q ^ 2) (q ^ 2) n *
        natSum (fun k =>
          gaussianBinom (q ^ 2) (2 * n) k * z ^ ((k : Int) - (n : Int)) *
            q ^ (((k : Int) - (n : Int)) ^ 2)) (2 * n) := by
  rw [jacobiProductPartial_eq_qPoch_mul_finiteJTPRHS q z hq hz n]
  rw [finiteJTPRHS_qsq_neg_zq q z hq n]

/--
Chapter 2's finite product partial in the centered symmetric-block form that
matches the fixed symmetric partial convergence interface.
@isnad1 id=eq.2h3v.s6.a5739ff210ba from=translated src=- shape=c9afeace vocab=55a24d80
-/
theorem jacobiProductPartial_eq_qPoch_mul_gaussianWeightedSymmetricPartial (q z : ℂ)
    (hq : q ≠ 0) (hz : z ≠ 0) (N : Nat) :
    Ch02.jacobiProductPartial q z N =
      qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedSymmetricPartial q z N N := by
  rw [jacobiProductPartial_eq_qPoch_mul_weightedLaurentSum q z hq hz N]
  rw [gaussianWeightedSymmetricPartial_eq_weightedLaurentNatSum]
  congr 1

/--
Finite-JTP limit form split into a fixed centered symmetric block and the
remaining finite nonzero-pair tail.
@isnad1 id=eq.3h4v.s7.8cd539321c4d from=translated src=- shape=f99f6807 vocab=598ae361
-/
theorem jacobiProductPartial_eq_qPoch_mul_fixedSymmetricPartial_add_tail (q z : ℂ)
    (hq : q ≠ 0) (hz : z ≠ 0) {N M : Nat} (hMN : M ≤ N) :
    Ch02.jacobiProductPartial q z N =
      qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedSymmetricPartial q z N M +
        qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTail q z N M N := by
  rw [jacobiProductPartial_eq_qPoch_mul_gaussianWeightedSymmetricPartial q z hq hz N]
  rw [gaussianWeightedSymmetricPartial_eq_add_tail q z hMN]
  ring

/--
Reduction of the nonzero-`q` Jacobi triple product to the remaining Gaussian
tail limit from the finite-JTP approach.
@isnad1 id=eq.4h3v.s7.7afdad193d34 from=translated src=- shape=a85e7d44 vocab=5af4746d
-/
theorem jacobiTripleProduct_of_gaussianWeightedTail_tendsto (q z : ℂ)
    (hq_norm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (M : Nat)
    (htail :
      Tendsto (fun N : ℕ =>
        qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTail q z N M N) atTop
        (𝓝 (Ch02.jacobiInfiniteSeries q z - Ch02.jacobiSeriesSymmetricPartial q z M))) :
    Ch02.jacobiInfiniteProduct q z = Ch02.jacobiInfiniteSeries q z := by
  have hproduct := Ch02.tendsto_jacobiProductPartial q z hq_norm
  have hcore := tendsto_qPoch_mul_gaussianWeightedSymmetricPartial q z hq_norm M
  have hsum :
      Tendsto (fun N : ℕ =>
        qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedSymmetricPartial q z N M +
          qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTail q z N M N) atTop
        (𝓝 (Ch02.jacobiInfiniteSeries q z)) := by
    have h := hcore.add htail
    simpa using h
  have hdecomp :
      (fun N : ℕ => Ch02.jacobiProductPartial q z N) =ᶠ[atTop]
        (fun N : ℕ =>
          qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedSymmetricPartial q z N M +
            qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTail q z N M N) := by
    filter_upwards [eventually_ge_atTop M] with N hMN
    exact jacobiProductPartial_eq_qPoch_mul_fixedSymmetricPartial_add_tail q z hq hz hMN
  have hproduct_to_series : Tendsto (fun N : ℕ => Ch02.jacobiProductPartial q z N) atTop
      (𝓝 (Ch02.jacobiInfiniteSeries q z)) :=
    hsum.congr' hdecomp.symm
  exact tendsto_nhds_unique hproduct hproduct_to_series

/--
Equivalent finite-JTP reduction where the remaining Gaussian tail is required
to converge to the `tsum` of Chapter 2's symmetric pair tail.
@isnad1 id=eq.4h3v.s7.fcef5ac2e9f0 from=translated src=- shape=27b4f95e vocab=563d5ef8
-/
theorem jacobiTripleProduct_of_gaussianWeightedTail_tendsto_tsum (q z : ℂ)
    (hq_norm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (M : Nat)
    (htail :
      Tendsto (fun N : ℕ =>
        qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTail q z N M N) atTop
        (𝓝 (∑' n : ℕ, Ch02.jacobiSeriesSymmetricPairTerm q z (n + M)))) :
    Ch02.jacobiInfiniteProduct q z = Ch02.jacobiInfiniteSeries q z := by
  refine jacobiTripleProduct_of_gaussianWeightedTail_tendsto q z hq_norm hq hz M ?_
  simpa [Ch02.tsum_jacobiSeriesSymmetricPairTerm_tail q z hq_norm M] using htail

/--
Dominated-convergence reduction for the finite-JTP Gaussian tail. It remains
to provide a summable bound for the zero-extended shifted tail summands.
@isnad1 id=eq.5h4v.s6.7096e6338675 from=translated src=- shape=28ae71f4 vocab=88bc538b
-/
theorem jacobiTripleProduct_of_gaussianWeightedTail_dominated (q z : ℂ)
    (hq_norm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (M : Nat)
    (bound : ℕ → ℝ) (h_sum : Summable bound)
    (h_bound :
      ∀ᶠ N in atTop, ∀ k,
        ‖gaussianWeightedTailSummand q z N M k‖ ≤ bound k) :
    Ch02.jacobiInfiniteProduct q z = Ch02.jacobiInfiniteSeries q z := by
  have htail_tsum :
      Tendsto (fun N : ℕ => ∑' k : ℕ, gaussianWeightedTailSummand q z N M k) atTop
        (𝓝 (∑' k : ℕ, Ch02.jacobiSeriesSymmetricPairTerm q z (k + M))) := by
    exact tendsto_tsum_of_dominated_convergence h_sum
      (fun k => by
        simpa [Nat.add_comm] using tendsto_gaussianWeightedTailSummand q z hq_norm M k)
      h_bound
  have htail :
      Tendsto (fun N : ℕ =>
        qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTail q z N M N) atTop
        (𝓝 (∑' k : ℕ, Ch02.jacobiSeriesSymmetricPairTerm q z (k + M))) :=
    htail_tsum.congr' (Eventually.of_forall fun N =>
      tsum_gaussianWeightedTailSummand q z N M)
  refine jacobiTripleProduct_of_gaussianWeightedTail_tendsto_tsum q z hq_norm hq hz M ?_
  simpa [Nat.add_comm] using htail

/--
Cancellation-free domination reduction: it is enough to bound the zero-extended
Gaussian tail summand by a constant multiple of the sum of the two norms in
the corresponding Chapter 2 symmetric pair.
@isnad1 id=eq.4h4v.s6.52891805f085 from=translated src=- shape=14d2c11e vocab=9e8efd8d
-/
theorem jacobiTripleProduct_of_gaussianWeightedTail_norm_le_pairMajorant (q z : ℂ)
    (hq_norm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (M : Nat) (C : ℝ)
    (h_bound :
      ∀ᶠ N in atTop, ∀ k,
        ‖gaussianWeightedTailSummand q z N M k‖ ≤
          C * Ch02.jacobiSeriesSymmetricPairNormMajorant q z (k + M)) :
    Ch02.jacobiInfiniteProduct q z = Ch02.jacobiInfiniteSeries q z := by
  have hmajorant : Summable fun r : ℕ =>
      Ch02.jacobiSeriesSymmetricPairNormMajorant q z r :=
    Ch02.summable_jacobiSeriesSymmetricPairNormMajorant q z hq_norm
  have hshift : Summable fun k : ℕ =>
      Ch02.jacobiSeriesSymmetricPairNormMajorant q z (k + M) := by
    exact (summable_nat_add_iff M).mpr hmajorant
  exact jacobiTripleProduct_of_gaussianWeightedTail_dominated q z hq_norm hq hz M
    (fun k => C * Ch02.jacobiSeriesSymmetricPairNormMajorant q z (k + M))
    (hshift.mul_left C) h_bound

/--
Jacobi's triple product, proved in Chapter 3 from the finite JTP and the
uniform Gaussian-tail domination package.
@isnad1 id=eq.2h2v.s5.bd42f4873d7e from=translated src=- shape=80feee63 vocab=61280040
-/
theorem jacobiTripleProduct_via_finiteJTP (q z : ℂ) (hq_norm : ‖q‖ < 1) (hz : z ≠ 0) :
    Ch02.jacobiInfiniteProduct q z = Ch02.jacobiInfiniteSeries q z := by
  by_cases hq : q = 0
  · subst q
    exact Ch02.jacobiTripleProduct_q_zero z
  · rcases exists_gaussianWeightedTailSummand_pairMajorant_bound q z hq_norm 0 with
      ⟨C, _hC_nonneg, hbound⟩
    exact jacobiTripleProduct_of_gaussianWeightedTail_norm_le_pairMajorant q z hq_norm hq hz 0 C
      hbound

end FiniteJTP

end Ch03

namespace Ch02

/--
Jacobi's triple product identity (Chan Theorem 2.1, Eq. 2.1), proved via the
finite Jacobi triple product and Gaussian-tail domination from Chapter 3.
@isnad1 id=eq.2h2v.s5.bd42f4873d7e from=translated src=- shape=80feee63 vocab=61280040
-/
theorem jacobiTripleProduct (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    jacobiInfiniteProduct q z = jacobiInfiniteSeries q z :=
  Ch03.jacobiTripleProduct_via_finiteJTP q z hq hz

end Ch02

end PartI
end QseriesFormalization
