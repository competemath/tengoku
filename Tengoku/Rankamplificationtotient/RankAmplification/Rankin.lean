import Tengoku.Rankamplificationtotient.RankAmplification.Definitions
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.NumberTheory.ArithmeticFunction.Misc

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite Rankin bounds This file isolates the exact finite inequalities behind the Rankin arguments in Lemmas 2.5, 10.1, and 10.2. -/

namespace RankAmplification

open Finset

noncomputable section

/-- Positive `R`-smooth integers at most `X`, using the paper's weak cutoff `p ≤ R`.-/
def finiteSmoothSet (R X : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 X).filter (IsSmooth R)

/-- Positive `R`-smooth integers in the half-open tail `(H, X]`.-/
def finiteSmoothTailSet (R H X : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Ioc H X).filter (IsSmooth R)

/--
@isnad1 id=iff.0h3v.s5.9c68020e41f5 from=translated src=- shape=7a528b81 vocab=88a00d27
-/
@[simp]
theorem mem_finiteSmoothSet {R X m : ℕ} :
    m ∈ finiteSmoothSet R X ↔ 1 ≤ m ∧ m ≤ X ∧ IsSmooth R m := by
  classical
  simp [finiteSmoothSet, and_assoc]

/--
@isnad1 id=iff.0h4v.s5.d9488b55ae90 from=translated src=- shape=ebf9aa70 vocab=44c1f207
-/
@[simp]
theorem mem_finiteSmoothTailSet {R H X m : ℕ} :
    m ∈ finiteSmoothTailSet R H X ↔ H < m ∧ m ≤ X ∧ IsSmooth R m := by
  classical
  simp [finiteSmoothTailSet, and_assoc]

/--
@isnad1 id=le.0h3v.s4.fb4c132829f8 from=translated src=- shape=d905d597 vocab=5b9f27ef
-/
theorem finiteSmoothTailSet_subset (R H X : ℕ) :
    finiteSmoothTailSet R H X ⊆ finiteSmoothSet R X := by
  intro m hm
  rw [mem_finiteSmoothTailSet] at hm
  rw [mem_finiteSmoothSet]
  exact ⟨Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt hm.1), hm.2⟩

/-- The ordered `j`-fold divisor function `τ_j`, defined as the `j`th Dirichlet-convolution power of the zeta arithmetic function.-/
def orderedDivisorCount (j n : ℕ) : ℕ :=
  (ArithmeticFunction.zeta ^ j) n

/--
@isnad1 id=eq.0h1v.s5.c1db168dd7f4 from=translated src=- shape=51addf3c vocab=ae0a2a9c
-/
@[simp]
theorem orderedDivisorCount_zero (n : ℕ) :
    orderedDivisorCount 0 n = if n = 1 then 1 else 0 := by
  simp [orderedDivisorCount, ArithmeticFunction.one_apply]

/--
@isnad1 id=eq.1h1v.s4.e4e86121a3d2 from=translated src=- shape=eefba1c9 vocab=d41e759e
-/
@[simp]
theorem orderedDivisorCount_one {n : ℕ} (hn : n ≠ 0) :
    orderedDivisorCount 1 n = 1 := by
  simp [orderedDivisorCount, ArithmeticFunction.zeta_apply_ne hn]

/-- Adding one ordered divisor coordinate sums over the divisors.
@isnad1 id=eq.0h2v.s5.ad139a497433 from=translated src=- shape=2abc9aef vocab=cd3b5d74
-/
theorem orderedDivisorCount_succ (j n : ℕ) :
    orderedDivisorCount (j + 1) n =
      ∑ d ∈ n.divisors, orderedDivisorCount j d := by
  simp only [orderedDivisorCount, pow_succ']
  exact ArithmeticFunction.zeta_mul_apply

/-- `τ_2` is Mathlib's ordinary divisor-counting function.
@isnad1 id=eq.0h1v.s3.968e84835bb7 from=translated src=- shape=545766f1 vocab=9208d246
-/
theorem orderedDivisorCount_two (n : ℕ) :
    orderedDivisorCount 2 n = n.divisors.card := by
  rw [show 2 = 1 + 1 by omega, orderedDivisorCount_succ]
  calc
    (∑ d ∈ n.divisors, orderedDivisorCount 1 d) = ∑ _d ∈ n.divisors, 1 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply orderedDivisorCount_one
      obtain ⟨hdvd, hn⟩ := Nat.mem_divisors.mp hd
      exact ne_zero_of_dvd_ne_zero hn hdvd
    _ = n.divisors.card := by simp

/-- A finite weighted smooth sum with real-power kernel `m^exponent`.-/
def finiteSmoothRpowSum (w : ℕ → ℝ) (R X : ℕ) (exponent : ℝ) : ℝ :=
  ∑ m ∈ finiteSmoothSet R X, w m * (m : ℝ) ^ exponent

/-- The corresponding finite tail over `H < m ≤ X`.-/
def finiteSmoothTailRpowSum (w : ℕ → ℝ) (R H X : ℕ) (exponent : ℝ) : ℝ :=
  ∑ m ∈ finiteSmoothTailSet R H X, w m * (m : ℝ) ^ exponent

/-- The finite unweighted reciprocal friable tail from Lemma 10.1.-/
def finiteSmoothReciprocalTail (R H X : ℕ) : ℝ :=
  ∑ m ∈ finiteSmoothTailSet R H X, (m : ℝ)⁻¹

/-- The finite `τ_j`-weighted reciprocal friable tail from Lemma 10.2.-/
def finiteTauSmoothReciprocalTail (j R H X : ℕ) : ℝ :=
  ∑ m ∈ finiteSmoothTailSet R H X, (orderedDivisorCount j m : ℝ) / m

/-- The finite `τ_j`-weighted smooth census underlying Lemma 2.5.-/
def finiteTauSmoothCount (j R X : ℕ) : ℝ :=
  ∑ m ∈ finiteSmoothSet R X, orderedDivisorCount j m

/-- The divisor-weighted smooth census `Ψ_τ(X,R)` from Lemma 2.5, with a finite exact sum.-/
def finiteDivisorWeightedSmoothCount (R X : ℕ) : ℝ :=
  finiteTauSmoothCount 2 R X

/--
@isnad1 id=eq.0h2v.s4.33b299bda816 from=translated src=- shape=7b6fd613 vocab=16c3c01b
-/
theorem finiteDivisorWeightedSmoothCount_eq (R X : ℕ) :
    finiteDivisorWeightedSmoothCount R X =
      ∑ m ∈ finiteSmoothSet R X, (m.divisors.card : ℝ) := by
  rw [finiteDivisorWeightedSmoothCount, finiteTauSmoothCount]
  apply Finset.sum_congr rfl
  intro m _
  simp [orderedDivisorCount_two]

/--
@isnad1 id=eq.0h3v.s5.d59bb1cb2adf from=translated src=- shape=6caf5dec vocab=52c19223
-/
theorem finiteSmoothReciprocalTail_eq_rpow (R H X : ℕ) :
    finiteSmoothReciprocalTail R H X =
      finiteSmoothTailRpowSum (fun _ => 1) R H X (-1) := by
  simp [finiteSmoothReciprocalTail, finiteSmoothTailRpowSum, Real.rpow_neg_one]

/--
@isnad1 id=eq.0h4v.s5.fbd6fa1378bb from=translated src=- shape=d7076837 vocab=8ecee274
-/
theorem finiteTauSmoothReciprocalTail_eq_rpow (j R H X : ℕ) :
    finiteTauSmoothReciprocalTail j R H X =
      finiteSmoothTailRpowSum (fun m => orderedDivisorCount j m) R H X (-1) := by
  simp [finiteTauSmoothReciprocalTail, finiteSmoothTailRpowSum, Real.rpow_neg_one,
    div_eq_mul_inv]

/--
@isnad1 id=eq.0h3v.s4.a9842063142f from=translated src=- shape=2952108a vocab=9426847a
-/
theorem finiteTauSmoothCount_eq_rpow_zero (j R X : ℕ) :
    finiteTauSmoothCount j R X =
      finiteSmoothRpowSum (fun m => orderedDivisorCount j m) R X 0 := by
  simp [finiteTauSmoothCount, finiteSmoothRpowSum]

/--
@isnad1 id=le.1h4v.s5.39419f027294 from=translated src=- shape=c844c301 vocab=64fe9299
-/
theorem finiteSmoothRpowSum_nonneg {w : ℕ → ℝ} {R X : ℕ} {exponent : ℝ}
    (hw : ∀ m ∈ finiteSmoothSet R X, 0 ≤ w m) :
    0 ≤ finiteSmoothRpowSum w R X exponent := by
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (hw m hm) (Real.rpow_nonneg (Nat.cast_nonneg m) exponent)

/--
@isnad1 id=le.1h5v.s5.797270a190d3 from=translated src=- shape=39e01cd5 vocab=a1e97dd8
-/
theorem finiteSmoothTailRpowSum_nonneg {w : ℕ → ℝ} {R H X : ℕ} {exponent : ℝ}
    (hw : ∀ m ∈ finiteSmoothTailSet R H X, 0 ≤ w m) :
    0 ≤ finiteSmoothTailRpowSum w R H X exponent := by
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (hw m hm) (Real.rpow_nonneg (Nat.cast_nonneg m) exponent)

/-- Finite Rankin inequality for a smooth weighted census.
@isnad1 id=le.2h4v.s6.b001d6207645 from=translated src=- shape=6f517ed3 vocab=fc19620c
-/
theorem finiteSmoothWeightedCount_le_rankin {w : ℕ → ℝ} {R X : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (hw : ∀ m ∈ finiteSmoothSet R X, 0 ≤ w m) :
    (∑ m ∈ finiteSmoothSet R X, w m) ≤
      (X : ℝ) ^ s * finiteSmoothRpowSum w R X (-s) := by
  rw [finiteSmoothRpowSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hmData := mem_finiteSmoothSet.mp hm
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmData.1)
  have hmX : (m : ℝ) ≤ X := by exact_mod_cast hmData.2.1
  have hpow : (m : ℝ) ^ s ≤ (X : ℝ) ^ s :=
    Real.rpow_le_rpow hmpos.le hmX hs
  have hneg : 0 ≤ (m : ℝ) ^ (-s) := Real.rpow_nonneg hmpos.le _
  have hcancel : (m : ℝ) ^ s * (m : ℝ) ^ (-s) = 1 := by
    rw [← Real.rpow_add hmpos]
    simp
  calc
    w m = (m : ℝ) ^ s * (w m * (m : ℝ) ^ (-s)) := by
      calc
        w m = w m * ((m : ℝ) ^ s * (m : ℝ) ^ (-s)) := by rw [hcancel, mul_one]
        _ = (m : ℝ) ^ s * (w m * (m : ℝ) ^ (-s)) := by ring
    _ ≤ (X : ℝ) ^ s * (w m * (m : ℝ) ^ (-s)) :=
      mul_le_mul_of_nonneg_right hpow (mul_nonneg (hw m hm) hneg)

/-- Finite reciprocal-tail Rankin inequality with an arbitrary nonnegative weight.
@isnad1 id=le.3h5v.s6.76e07d282232 from=translated src=- shape=03601d1b vocab=82299104
-/
theorem finiteSmoothWeightedTail_le_rankin {w : ℕ → ℝ} {R H X : ℕ} {δ : ℝ}
    (hH : 0 < H) (hδ : 0 ≤ δ) (hw : ∀ m ∈ finiteSmoothSet R X, 0 ≤ w m) :
    finiteSmoothTailRpowSum w R H X (-1) ≤
      (H : ℝ) ^ (-δ) * finiteSmoothRpowSum w R X (δ - 1) := by
  rw [finiteSmoothTailRpowSum, finiteSmoothRpowSum, Finset.mul_sum]
  calc
    (∑ m ∈ finiteSmoothTailSet R H X, w m * (m : ℝ) ^ (-1 : ℝ)) ≤
        ∑ m ∈ finiteSmoothTailSet R H X,
          (H : ℝ) ^ (-δ) * (w m * (m : ℝ) ^ (δ - 1)) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmData := mem_finiteSmoothTailSet.mp hm
      have hHreal : 0 < (H : ℝ) := by exact_mod_cast hH
      have hHm : (H : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt hmData.1)
      have hmpos : 0 < (m : ℝ) := hHreal.trans_le hHm
      have hpow : (m : ℝ) ^ (-δ) ≤ (H : ℝ) ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos hHreal hHm (neg_nonpos.mpr hδ)
      have hrest : 0 ≤ w m * (m : ℝ) ^ (δ - 1) :=
        mul_nonneg (hw m (finiteSmoothTailSet_subset R H X hm))
          (Real.rpow_nonneg hmpos.le _)
      have hcombine :
          (m : ℝ) ^ (-δ) * (m : ℝ) ^ (δ - 1) = (m : ℝ) ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hmpos]
        congr 1
        ring
      calc
        w m * (m : ℝ) ^ (-1 : ℝ) =
            (m : ℝ) ^ (-δ) * (w m * (m : ℝ) ^ (δ - 1)) := by
          calc
            w m * (m : ℝ) ^ (-1 : ℝ) =
                w m * ((m : ℝ) ^ (-δ) * (m : ℝ) ^ (δ - 1)) := by rw [hcombine]
            _ = (m : ℝ) ^ (-δ) * (w m * (m : ℝ) ^ (δ - 1)) := by ring
        _ ≤ (H : ℝ) ^ (-δ) * (w m * (m : ℝ) ^ (δ - 1)) :=
          mul_le_mul_of_nonneg_right hpow hrest
    _ ≤ ∑ m ∈ finiteSmoothSet R X,
        (H : ℝ) ^ (-δ) * (w m * (m : ℝ) ^ (δ - 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (finiteSmoothTailSet_subset R H X)
      intro m hm _
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg H) _)
        (mul_nonneg (hw m hm) (Real.rpow_nonneg (Nat.cast_nonneg m) _))

/-- Lemma 10.1's finite Rankin step.
@isnad1 id=le.2h4v.s6.b9ee801008c4 from=translated src=- shape=56c574fa vocab=effb68ce
-/
theorem finiteSmoothReciprocalTail_le_rankin {R H X : ℕ} {δ : ℝ}
    (hH : 0 < H) (hδ : 0 ≤ δ) :
    finiteSmoothReciprocalTail R H X ≤
      (H : ℝ) ^ (-δ) * finiteSmoothRpowSum (fun _ => 1) R X (δ - 1) := by
  rw [finiteSmoothReciprocalTail_eq_rpow]
  exact finiteSmoothWeightedTail_le_rankin hH hδ (fun _ _ => zero_le_one)

/-- Lemma 10.2's finite `τ_j`-weighted Rankin step.
@isnad1 id=le.2h5v.s6.74299a4d7a8e from=translated src=- shape=1a568f44 vocab=726fb047
-/
theorem finiteTauSmoothReciprocalTail_le_rankin {j R H X : ℕ} {δ : ℝ}
    (hH : 0 < H) (hδ : 0 ≤ δ) :
    finiteTauSmoothReciprocalTail j R H X ≤
      (H : ℝ) ^ (-δ) *
        finiteSmoothRpowSum (fun m => orderedDivisorCount j m) R X (δ - 1) := by
  rw [finiteTauSmoothReciprocalTail_eq_rpow]
  exact finiteSmoothWeightedTail_le_rankin hH hδ (fun _ _ => Nat.cast_nonneg _)

/-- Lemma 2.5's finite `τ_j`-weighted census Rankin step.
@isnad1 id=le.1h4v.s5.74b5d551fa57 from=translated src=- shape=0c373f8e vocab=598a0cde
-/
theorem finiteTauSmoothCount_le_rankin {j R X : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    finiteTauSmoothCount j R X ≤
      (X : ℝ) ^ s *
        finiteSmoothRpowSum (fun m => orderedDivisorCount j m) R X (-s) := by
  rw [finiteTauSmoothCount]
  exact finiteSmoothWeightedCount_le_rankin hs (fun _ _ => Nat.cast_nonneg _)

/-! ## The paper's Rankin parameter choice -/

/-- `u = log H / log R`.-/
def rankinU (H R : ℕ) : ℝ := Real.log H / Real.log R

/-- `δ = log u / log R`, the exponent shift used in Lemmas 2.5, 10.1, and 10.2.-/
def rankinDelta (H R : ℕ) : ℝ := Real.log (rankinU H R) / Real.log R

/--
@isnad1 id=eq.1h2v.s5.cfab19aa6f48 from=translated src=- shape=eff653cc vocab=97b9893d
-/
theorem rankinU_mul_log {H R : ℕ} (hR : 1 < R) :
    rankinU H R * Real.log R = Real.log H := by
  rw [rankinU, div_mul_cancel₀]
  exact (Real.log_pos (by exact_mod_cast hR)).ne'

/--
@isnad1 id=eq.1h2v.s5.e7cae69ceb7b from=translated src=- shape=6c26f2f1 vocab=fed21172
-/
theorem rankinDelta_mul_log {H R : ℕ} (hR : 1 < R) :
    rankinDelta H R * Real.log H = rankinU H R * Real.log (rankinU H R) := by
  have hlogR : Real.log (R : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hR)).ne'
  rw [← rankinU_mul_log hR, rankinDelta]
  field_simp

/--
@isnad1 id=le.2h2v.s5.54b561d77ee3 from=translated src=- shape=1a33fe44 vocab=1a8c6850
-/
theorem rankinDelta_nonneg {H R : ℕ} (hR : 1 < R) (hu : 1 ≤ rankinU H R) :
    0 ≤ rankinDelta H R := by
  rw [rankinDelta]
  exact div_nonneg (Real.log_nonneg hu) (Real.log_pos (by exact_mod_cast hR)).le

/--
@isnad1 id=le.3h2v.s5.59da01d01fbb from=translated src=- shape=02077528 vocab=8f9a1c7a
-/
theorem rankinDelta_le_one {H R : ℕ} (hR : 1 < R)
    (huR : rankinU H R ≤ R) (hu : 0 < rankinU H R) :
    rankinDelta H R ≤ 1 := by
  rw [rankinDelta, div_le_one (Real.log_pos (by exact_mod_cast hR))]
  exact Real.log_le_log hu (by exact_mod_cast huR)

/-- The Rankin prefactor after the paper's exponent choice.
@isnad1 id=eq.2h2v.s5.691cdd4f68c1 from=translated src=- shape=2de08914 vocab=fb548275
-/
theorem rankin_cutoff_rpow {H R : ℕ} (hH : 0 < H) (hR : 1 < R) :
    (H : ℝ) ^ (-rankinDelta H R) =
      Real.exp (-rankinU H R * Real.log (rankinU H R)) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hH)]
  congr 1
  rw [mul_neg, mul_comm, rankinDelta_mul_log hR]
  ring

/-- Lemma 10.1's finite Rankin bound after substituting `δ = log u / log R`.
@isnad1 id=le.3h3v.s6.0c4d18f77cd6 from=translated src=- shape=97b9f1a2 vocab=b5ba45c5
-/
theorem finiteSmoothReciprocalTail_le_chosen_rankin {R H X : ℕ}
    (hH : 0 < H) (hR : 1 < R) (hu : 1 ≤ rankinU H R) :
    finiteSmoothReciprocalTail R H X ≤
      Real.exp (-rankinU H R * Real.log (rankinU H R)) *
        finiteSmoothRpowSum (fun _ => 1) R X (rankinDelta H R - 1) := by
  simpa only [rankin_cutoff_rpow hH hR] using
    finiteSmoothReciprocalTail_le_rankin (R := R) (X := X)
      hH (rankinDelta_nonneg hR hu)

/-- Lemma 10.2's finite weighted bound after the same exponent substitution.
@isnad1 id=le.3h4v.s6.4b0150e4ebab from=translated src=- shape=d19ed7b7 vocab=5af01fe1
-/
theorem finiteTauSmoothReciprocalTail_le_chosen_rankin {j R H X : ℕ}
    (hH : 0 < H) (hR : 1 < R) (hu : 1 ≤ rankinU H R) :
    finiteTauSmoothReciprocalTail j R H X ≤
      Real.exp (-rankinU H R * Real.log (rankinU H R)) *
        finiteSmoothRpowSum (fun m => orderedDivisorCount j m) R X
          (rankinDelta H R - 1) := by
  simpa only [rankin_cutoff_rpow hH hR] using
    finiteTauSmoothReciprocalTail_le_rankin (j := j) (R := R) (X := X)
      hH (rankinDelta_nonneg hR hu)

/-- Lemma 2.5's finite divisor-weighted Rankin step with `s = 1 - δ`.
@isnad1 id=le.3h2v.s6.34772d33efd7 from=translated src=- shape=ae417761 vocab=fff228ca
-/
theorem finiteDivisorWeightedSmoothCount_le_chosen_rankin {R X : ℕ}
    (hR : 1 < R) (hu : 1 ≤ rankinU X R) (huR : rankinU X R ≤ R) :
    finiteDivisorWeightedSmoothCount R X ≤
      (X : ℝ) ^ (1 - rankinDelta X R) *
        finiteSmoothRpowSum (fun m => orderedDivisorCount 2 m) R X
          (rankinDelta X R - 1) := by
  rw [finiteDivisorWeightedSmoothCount]
  simpa only [neg_sub] using
    finiteTauSmoothCount_le_rankin (j := 2) (R := R) (X := X)
      (sub_nonneg.mpr (rankinDelta_le_one hR huR (zero_lt_one.trans_le hu)))

/-! ## Exact finite Euler boxes -/

/-- Exponent vectors on a finite set of primes, with every exponent at most `K`.-/
def eulerExponentBox (P : Finset ℕ) (K : ℕ) : Finset (∀ p : ℕ, p ∈ P → ℕ) :=
  P.pi fun _ => Finset.range (K + 1)

/-- A general finite Euler-box sum, before factorization into local sums.-/
def eulerBoxSum (P : Finset ℕ) (K : ℕ) (localWeight : ℕ → ℕ → ℝ) : ℝ :=
  ∑ e ∈ eulerExponentBox P K,
    ∏ p ∈ P.attach, localWeight p.1 (e p.1 p.2)

/-- Finite Euler-product factorization, directly from distributivity.
@isnad1 id=eq.0h3v.s5.0fa3c779386c from=translated src=- shape=630ac476 vocab=cad4bdc3
-/
theorem eulerBoxSum_eq_prod_local (P : Finset ℕ) (K : ℕ)
    (localWeight : ℕ → ℕ → ℝ) :
    eulerBoxSum P K localWeight =
      ∏ p ∈ P, ∑ a ∈ Finset.range (K + 1), localWeight p a := by
  classical
  simpa only [eulerBoxSum, eulerExponentBox] using
    (Finset.prod_sum P (fun _ => Finset.range (K + 1)) localWeight).symm

/-- The local ratio `p^{-s}` in a Rankin Euler product.-/
def rankinEulerRatio (p : ℕ) (s : ℝ) : ℝ := (p : ℝ) ^ (-s)

/--
@isnad1 id=lt.1h2v.s4.7cc9c12b04bd from=translated src=- shape=406bdadd vocab=6b689754
-/
theorem rankinEulerRatio_pos {p : ℕ} (hp : 0 < p) (s : ℝ) :
    0 < rankinEulerRatio p s := by
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp) _

/--
@isnad1 id=lt.2h2v.s5.d68f2c5b4d1a from=translated src=- shape=0fa2f457 vocab=6b689754
-/
theorem rankinEulerRatio_lt_one {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    rankinEulerRatio p s < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (neg_lt_zero.mpr hs)

/-- Truncated local geometric factors, each raised to the ordered-divisor rank `j`.-/
def truncatedRankinEulerProduct (P : Finset ℕ) (K j : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ P, (∑ a ∈ Finset.range (K + 1), rankinEulerRatio p s ^ a) ^ j

/-- The finite product of full geometric-series majorants.-/
def rankinEulerMajorant (P : Finset ℕ) (j : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ P, ((1 - rankinEulerRatio p s)⁻¹) ^ j

/-- A finite geometric sum is bounded by its convergent full series.
@isnad1 id=le.2h2v.s6.5c09966b4447 from=translated src=- shape=aa440217 vocab=2c51e5d8
-/
theorem finite_geometric_sum_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) :
    (∑ a ∈ Finset.range (K + 1), q ^ a) ≤ (1 - q)⁻¹ := by
  have hsum := hasSum_geometric_of_lt_one hq0 hq1
  calc
    (∑ a ∈ Finset.range (K + 1), q ^ a) ≤ ∑' a : ℕ, q ^ a :=
      hsum.summable.sum_le_tsum _ (fun a _ => pow_nonneg hq0 a)
    _ = (1 - q)⁻¹ := hsum.tsum_eq

/-- Exact factorization of the rank-one geometric Euler box.
@isnad1 id=eq.0h3v.s5.0fdf2457df55 from=translated src=- shape=4a3004c7 vocab=2d37ecbf
-/
theorem geometricEulerBoxSum_eq_product (P : Finset ℕ) (K : ℕ) (s : ℝ) :
    eulerBoxSum P K (fun p a => rankinEulerRatio p s ^ a) =
      truncatedRankinEulerProduct P K 1 s := by
  rw [eulerBoxSum_eq_prod_local, truncatedRankinEulerProduct]
  simp

/-- Finite Euler-product bound used after the Rankin inequality.
@isnad1 id=le.2h4v.s5.f68e8b4807b6 from=translated src=- shape=fa7aa22e vocab=51719e34
-/
theorem truncatedRankinEulerProduct_le_majorant {P : Finset ℕ} {K j : ℕ} {s : ℝ}
    (hP : ∀ p ∈ P, 1 < p) (hs : 0 < s) :
    truncatedRankinEulerProduct P K j s ≤ rankinEulerMajorant P j s := by
  rw [truncatedRankinEulerProduct, rankinEulerMajorant]
  apply Finset.prod_le_prod
  · intro p hp
    apply pow_nonneg
    exact Finset.sum_nonneg fun _ _ => pow_nonneg
      (rankinEulerRatio_pos (Nat.zero_lt_of_lt (hP p hp)) s).le _
  · intro p hp
    have hqpos : 0 < rankinEulerRatio p s :=
      rankinEulerRatio_pos (Nat.zero_lt_of_lt (hP p hp)) s
    have hqlt : rankinEulerRatio p s < 1 := rankinEulerRatio_lt_one (hP p hp) hs
    have hlocalNonneg :
        0 ≤ ∑ a ∈ Finset.range (K + 1), rankinEulerRatio p s ^ a := by
      exact Finset.sum_nonneg fun _ _ => pow_nonneg hqpos.le _
    exact pow_le_pow_left₀ hlocalNonneg
      (finite_geometric_sum_le_inv_one_sub hqpos.le hqlt K) j

/-- The logarithm of the finite Euler majorant is exactly the corresponding finite prime sum.
@isnad1 id=eq.2h3v.s6.e1e1a158931d from=translated src=- shape=f2c31595 vocab=d03e4c22
-/
theorem log_rankinEulerMajorant {P : Finset ℕ} {j : ℕ} {s : ℝ}
    (hP : ∀ p ∈ P, 1 < p) (hs : 0 < s) :
    Real.log (rankinEulerMajorant P j s) =
      (j : ℝ) * ∑ p ∈ P, -Real.log (1 - rankinEulerRatio p s) := by
  rw [rankinEulerMajorant, Real.log_prod]
  · simp_rw [Real.log_pow, Real.log_inv]
    rw [Finset.mul_sum]
  · intro p hp
    have hq : rankinEulerRatio p s < 1 := rankinEulerRatio_lt_one (hP p hp) hs
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr hq.ne'))

/-- An exact elementary bound for a local logarithmic Euler factor.
@isnad1 id=le.1h1v.s5.ffcdbbe073c7 from=translated src=- shape=8223b29a vocab=3c5f5cf8
-/
theorem neg_log_one_sub_le_div {q : ℝ} (hq1 : q < 1) :
    -Real.log (1 - q) ≤ q / (1 - q) := by
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hlog := Real.one_sub_inv_le_log_of_pos hden
  have hid : 1 - (1 - q)⁻¹ = -(q / (1 - q)) := by
    field_simp [hden.ne']
    ring
  rw [hid] at hlog
  linarith

/-- The finite logarithmic Euler product is bounded by a finite sum of local rational terms.
@isnad1 id=le.2h3v.s6.3989cd31a85c from=translated src=- shape=5645ce77 vocab=8495537c
-/
theorem log_rankinEulerMajorant_le_sum {P : Finset ℕ} {j : ℕ} {s : ℝ}
    (hP : ∀ p ∈ P, 1 < p) (hs : 0 < s) :
    Real.log (rankinEulerMajorant P j s) ≤
      (j : ℝ) * ∑ p ∈ P,
        rankinEulerRatio p s / (1 - rankinEulerRatio p s) := by
  rw [log_rankinEulerMajorant hP hs]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg j)
  apply Finset.sum_le_sum
  intro p hp
  exact neg_log_one_sub_le_div (rankinEulerRatio_lt_one (hP p hp) hs)

end

end RankAmplification
