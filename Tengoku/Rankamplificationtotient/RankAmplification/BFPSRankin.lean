import Tengoku.Rankamplificationtotient.RankAmplification.LargeCofactor
import Tengoku.Rankamplificationtotient.RankAmplification.PSeriesEuler
import Tengoku.Rankamplificationtotient.RankAmplification.Counting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The Rankin--Euler reduction for smooth totients This module formalizes equation (2.2) of Banks--Friedlander--Pomerance--Shparlinski. -/

namespace RankAmplification

open scoped BigOperators Nat.Prime

noncomputable section

/-- Primes `p ≤ X` for which `p-1` is `Y`-smooth.-/
noncomputable def smoothPredecessorPrimeSet (X Y : ℕ) : Finset ℕ := by
  classical
  exact (Nat.primesLE X).filter fun p ↦ IsSmooth Y (p - 1)

@[simp]
theorem mem_smoothPredecessorPrimeSet {X Y p : ℕ} :
    p ∈ smoothPredecessorPrimeSet X Y ↔
      p.Prime ∧ p ≤ X ∧ IsSmooth Y (p - 1) := by
  classical
  rw [smoothPredecessorPrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  aesop

theorem smoothPredecessorPrimeSet_prime {X Y p : ℕ}
    (hp : p ∈ smoothPredecessorPrimeSet X Y) : p.Prime :=
  (mem_smoothPredecessorPrimeSet.mp hp).1

/-- A prime divisor contributes its predecessor to the totient.-/
theorem prime_pred_dvd_totient {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    p - 1 ∣ n.totient := by
  have htot := Nat.totient_dvd_of_dvd hpn
  rw [Nat.totient_prime hp] at htot
  exact htot

/-- Smoothness of a totient forces smoothness of every prime predecessor in its support.-/
theorem prime_pred_smooth_of_totient_smooth {Y p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hphi : IsSmooth Y n.totient) : IsSmooth Y (p - 1) := by
  apply hphi.of_dvd (prime_pred_dvd_totient hp hpn)
  exact Nat.ne_of_gt (Nat.sub_pos_of_lt hp.one_lt)

/-- Every integer counted by `Φ(X,Y)` is factored over the finite set of primes with smooth predecessor.-/
theorem smoothTotient_mem_factoredNumbers {X Y n : ℕ} (hn : n ∈ smoothTotientSet X Y) :
    n ∈ Nat.factoredNumbers (smoothPredecessorPrimeSet X Y) := by
  rw [Nat.mem_factoredNumbers']
  intro p hp hpn
  have hnData := mem_smoothTotientSet.mp hn
  apply mem_smoothPredecessorPrimeSet.mpr
  refine ⟨hp, ?_, prime_pred_smooth_of_totient_smooth hp hpn hnData.2.2⟩
  exact (Nat.le_of_dvd (by omega) hpn).trans hnData.2.1

/-- The finite Dirichlet sum over smooth totients at exponent `c`.-/
def smoothTotientRankinSum (X Y : ℕ) (c : ℝ) : ℝ :=
  ∑ n ∈ smoothTotientSet X Y, (n : ℝ) ^ (-c)

/-- Euler product over primes with `Y`-smooth predecessor.-/
def smoothPredecessorEulerProduct (X Y : ℕ) (c : ℝ) : ℝ :=
  rankinEulerMajorant (smoothPredecessorPrimeSet X Y) 1 c

/-- Exact Euler-product expansion over all integers factored by smooth-predecessor primes.-/
theorem hasSum_smoothPredecessor_factored (X Y : ℕ) {c : ℝ} (hc : 0 < c) :
    HasSum
      (fun n : Nat.factoredNumbers (smoothPredecessorPrimeSet X Y) ↦
        (n.1 : ℝ) ^ (-c))
      (smoothPredecessorEulerProduct X Y c) := by
  have heuler :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := reciprocalRpowMonoidHom c)
      (fun {_p} hp ↦ norm_reciprocalRpowMonoidHom_prime_lt_one hc hp)
      (smoothPredecessorPrimeSet X Y)
  have hfilter : (smoothPredecessorPrimeSet X Y).filter Nat.Prime =
      smoothPredecessorPrimeSet X Y := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact smoothPredecessorPrimeSet_prime hp
  simpa [smoothPredecessorEulerProduct, rankinEulerMajorant, rankinEulerRatio,
    hfilter, reciprocalRpowMonoidHom_apply] using heuler.2

/-- The finite Dirichlet sum in the Rankin reduction is bounded by the complete Euler product.-/
theorem smoothTotientRankinSum_le_eulerProduct (X Y : ℕ) {c : ℝ} (hc : 0 < c) :
    smoothTotientRankinSum X Y c ≤ smoothPredecessorEulerProduct X Y c := by
  let e : {n : ℕ // n ∈ smoothTotientSet X Y} ↪
      Nat.factoredNumbers (smoothPredecessorPrimeSet X Y) :=
    { toFun := fun n ↦ ⟨n.1, smoothTotient_mem_factoredNumbers n.2⟩
      inj' := fun a b hab ↦ Subtype.ext <|
        congrArg (fun z : Nat.factoredNumbers (smoothPredecessorPrimeSet X Y) ↦ z.1) hab }
  let A : Finset (Nat.factoredNumbers (smoothPredecessorPrimeSet X Y)) :=
    Finset.univ.map e
  have hs := hasSum_smoothPredecessor_factored X Y hc
  have hle : (∑ n ∈ A, (n.1 : ℝ) ^ (-c)) ≤ smoothPredecessorEulerProduct X Y c := by
    calc
      (∑ n ∈ A, (n.1 : ℝ) ^ (-c)) ≤
          ∑' n : Nat.factoredNumbers (smoothPredecessorPrimeSet X Y),
            (n.1 : ℝ) ^ (-c) :=
        hs.summable.sum_le_tsum A
          (fun n _ ↦ Real.rpow_nonneg (Nat.cast_nonneg n.1) _)
      _ = smoothPredecessorEulerProduct X Y c := hs.tsum_eq
  have hfinite : smoothTotientRankinSum X Y c =
      ∑ n : {n : ℕ // n ∈ smoothTotientSet X Y}, (n.1 : ℝ) ^ (-c) := by
    rw [smoothTotientRankinSum, ← Finset.sum_attach, Finset.attach_eq_univ]
  have hmap :
      (∑ n : {n : ℕ // n ∈ smoothTotientSet X Y}, (n.1 : ℝ) ^ (-c)) =
        ∑ n ∈ A, (n.1 : ℝ) ^ (-c) := by
    change (∑ n : {n : ℕ // n ∈ smoothTotientSet X Y}, (n.1 : ℝ) ^ (-c)) =
      ∑ n ∈ Finset.univ.map e, (n.1 : ℝ) ^ (-c)
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n _
    rfl
  rw [hfinite, hmap]
  exact hle

/-- The exact Rankin inequality for the smooth-totient census.-/
theorem smoothTotientCount_le_rankinEuler {X Y : ℕ} {c : ℝ} (hc : 0 < c) :
    (smoothTotientCount X Y : ℝ) ≤
      (X : ℝ) ^ c * smoothPredecessorEulerProduct X Y c := by
  rw [smoothTotientCount]
  calc
    ((smoothTotientSet X Y).card : ℝ) =
        ∑ n ∈ smoothTotientSet X Y, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ smoothTotientSet X Y, (X : ℝ) ^ c * (n : ℝ) ^ (-c) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnData := mem_smoothTotientSet.mp hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hnData.1)
      have hnX : (n : ℝ) ≤ X := by exact_mod_cast hnData.2.1
      have hpow : (n : ℝ) ^ c ≤ (X : ℝ) ^ c :=
        Real.rpow_le_rpow hnpos.le hnX hc.le
      have hcancel : (n : ℝ) ^ c * (n : ℝ) ^ (-c) = 1 := by
        rw [← Real.rpow_add hnpos]
        simp
      calc
        (1 : ℝ) = (n : ℝ) ^ c * (n : ℝ) ^ (-c) := hcancel.symm
        _ ≤ (X : ℝ) ^ c * (n : ℝ) ^ (-c) :=
          mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hnpos.le _)
    _ = (X : ℝ) ^ c * smoothTotientRankinSum X Y c := by
      rw [smoothTotientRankinSum, Finset.mul_sum]
    _ ≤ (X : ℝ) ^ c * smoothPredecessorEulerProduct X Y c :=
      mul_le_mul_of_nonneg_left (smoothTotientRankinSum_le_eulerProduct X Y hc)
        (Real.rpow_nonneg (Nat.cast_nonneg X) _)

/-- Exact logarithm of the BFPS Euler product.-/
theorem log_smoothPredecessorEulerProduct {X Y : ℕ} {c : ℝ} (hc : 0 < c) :
    Real.log (smoothPredecessorEulerProduct X Y c) =
      ∑ p ∈ smoothPredecessorPrimeSet X Y,
        -Real.log (1 - (p : ℝ) ^ (-c)) := by
  have hp : ∀ p ∈ smoothPredecessorPrimeSet X Y, 1 < p := by
    intro p hp
    exact (smoothPredecessorPrimeSet_prime hp).one_lt
  simpa [smoothPredecessorEulerProduct, rankinEulerRatio] using
    (log_rankinEulerMajorant (P := smoothPredecessorPrimeSet X Y) (j := 1) hp hc)

/-- Elementary rational majorant for the logarithm of the BFPS Euler product.-/
theorem log_smoothPredecessorEulerProduct_le {X Y : ℕ} {c : ℝ} (hc : 0 < c) :
    Real.log (smoothPredecessorEulerProduct X Y c) ≤
      ∑ p ∈ smoothPredecessorPrimeSet X Y,
        (p : ℝ) ^ (-c) / (1 - (p : ℝ) ^ (-c)) := by
  have hp : ∀ p ∈ smoothPredecessorPrimeSet X Y, 1 < p := by
    intro p hp
    exact (smoothPredecessorPrimeSet_prime hp).one_lt
  simpa [smoothPredecessorEulerProduct, rankinEulerRatio] using
    (log_rankinEulerMajorant_le_sum
      (P := smoothPredecessorPrimeSet X Y) (j := 1) hp hc)

end

end RankAmplification
