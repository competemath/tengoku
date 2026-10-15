/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Tengoku.LeanPool.LeanPool.PentagonalNumberTheoremAnalytic.QSeries.FPSEuler
public import Tengoku.LeanPool.LeanPool.PentagonalNumberTheoremAnalytic.QSeries.FiniteBinomial

/-!
# Algebraic identities for FPS q-series

Purely algebraic proofs of the **Euler second identity** and the **key identity**
`S_k = (qPochhammerInf X)⁻¹` in the formal power series ring `R⟦X⟧` over any
commutative ring with discrete topology. Combined with the product expansion
and Cauchy product, these identities yield the Jacobi triple product.

## Main results

* `QSeries.FormalPowerSeries.euler_second_identity` — FPS Euler second identity.
* `QSeries.FormalPowerSeries.keySum_eq_qPochhammerInfInv` — `S_k = (qPochhammerInf X)⁻¹`
  for all `k`.
* `QSeries.FormalPowerSeries.hasSum_pow_choose_two_nonneg` — Cauchy diagonal coefficient
  for `n ≥ 0`.
* `QSeries.FormalPowerSeries.hasSum_pow_choose_two_neg` — Cauchy diagonal coefficient for `n < 0`.
* `QSeries.FormalPowerSeries.jacobiTripleProduct` — FPS Jacobi Triple Product Identity.
-/

@[expose] public section

noncomputable section

open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset

namespace QSeries.FormalPowerSeries

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

/-- Inverse of `qPochhammer X k` in `R⟦X⟧`, defined via `invOfUnit` since the
constant coefficient is `1`. -/
def qPochhammerInv (k : ℕ) : R⟦X⟧ :=
  MvPowerSeries.invOfUnit (qPochhammer (X : R⟦X⟧) k) 1

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- `qPochhammer X k` times its formal power series inverse equals 1.
@isnad1 id=eq.0h2v.s5.418fa5d2920e from=translated src=- shape=ffc64272 vocab=23144c23
-/
@[simp]
theorem qPochhammer_X_mul_qPochhammerInv (k : ℕ) :
    qPochhammer (X : R⟦X⟧) k * qPochhammerInv (R := R) k = 1 :=
  PowerSeries.mul_invOfUnit _ 1 (by simpa using constantCoeff_qPochhammer_X (R := R) k)

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- The formal power series inverse of `qPochhammer X k` times `qPochhammer X k` equals 1.
@isnad1 id=eq.0h2v.s5.ae0e271d0cd1 from=translated src=- shape=228f4acf vocab=23144c23
-/
@[simp]
theorem qPochhammerInv_mul_qPochhammer_X (k : ℕ) :
    qPochhammerInv (R := R) k * qPochhammer (X : R⟦X⟧) k = 1 := by
  rw [mul_comm, qPochhammer_X_mul_qPochhammerInv]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- The recursion `(1 - X^{k+1}) * qPochhammerInv(k+1) = qPochhammerInv(k)` for the inverse
q-Pochhammer symbol.
@isnad1 id=eq.0h2v.s7.e50cde59cce8 from=translated src=- shape=659a4ceb vocab=f88176c9
-/
theorem one_sub_pow_mul_qPochhammerInv_succ (k : ℕ) :
    (1 - (X : R⟦X⟧) ^ (k + 1)) * qPochhammerInv (R := R) (k + 1) = qPochhammerInv k := by
  have h1 := qPochhammer_X_mul_qPochhammerInv (R := R) (k + 1)
  rw [qPochhammer_succ, ← pow_succ'] at h1
  refine (isUnit_qPochhammer_X (R := R) k).mul_left_cancel ?_
  rw [qPochhammer_X_mul_qPochhammerInv, ← mul_assoc, h1]

/-- `qPochhammerInf X` is a unit.
@isnad1 id=isunit.0h1v.s5.088835592840 from=translated src=- shape=e67f82c8 vocab=a0463096
-/
theorem isUnit_qPochhammerInf_X : IsUnit (qPochhammerInf (X : R⟦X⟧)) :=
  isUnit_qPochhammerInf X (by simp)

/-- Inverse of `qPochhammerInf X`. -/
def qPochhammerInfInv : R⟦X⟧ := ↑(isUnit_qPochhammerInf_X (R := R)).unit⁻¹

/-- `qPochhammerInf X` times its formal power series inverse equals 1.
@isnad1 id=eq.0h1v.s6.43c2b7bc2b13 from=translated src=- shape=c593a092 vocab=0911a23f
-/
@[simp]
theorem qPochhammerInf_X_mul_qPochhammerInfInv :
    qPochhammerInf (X : R⟦X⟧) * qPochhammerInfInv (R := R) = 1 :=
  isUnit_qPochhammerInf_X.mul_val_inv

/-- The formal power series inverse of `qPochhammerInf X` times `qPochhammerInf X` equals 1.
@isnad1 id=eq.0h1v.s6.bc6c4f326bdd from=translated src=- shape=754046e5 vocab=0911a23f
-/
@[simp]
theorem qPochhammerInfInv_mul_qPochhammerInf_X :
    qPochhammerInfInv (R := R) * qPochhammerInf (X : R⟦X⟧) = 1 :=
  isUnit_qPochhammerInf_X.val_inv_mul

/-- `qPochhammerInf X * qPochhammerInv n = qPochhammerInf (X * X^n)`: multiplying the infinite
product by the `n`-th inverse Pochhammer symbol shifts the argument.
@isnad1 id=eq.0h2v.s6.ac203a7ca6c3 from=translated src=- shape=3162119f vocab=545b47d3
-/
theorem qPochhammerInf_X_mul_qPochhammerInv (n : ℕ) :
    qPochhammerInf (X : R⟦X⟧) * qPochhammerInv (R := R) n = qPochhammerInf (X * X ^ n) := by
  rw [qPochhammerInf_X_eq_qPochhammer_mul n, mul_right_comm, qPochhammer_X_mul_qPochhammerInv,
    one_mul]

section Euler2

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Every finite q-Pochhammer product is `1` plus a multiple of its argument:
`(a; X)_k = 1 + a * g` for some `g`. -/
private theorem exists_qPochhammer_eq_one_add_mul (a : R⟦X⟧) (k : ℕ) :
    ∃ g : R⟦X⟧, qPochhammer a k = 1 + a * g := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨g - X ^ k - a * g * X ^ k, by rw [qPochhammer_succ, hg]; ring⟩

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- For `j ≤ m` the `j`-th coefficient of `(X·X^m; X)_k` agrees with that of `1`. -/
private theorem coeff_qPochhammer_X_mul_pow (m k : ℕ) {j : ℕ} (hj : j < m + 1) :
    PowerSeries.coeff j (qPochhammer ((X : R⟦X⟧) * X ^ m) k) = PowerSeries.coeff j 1 := by
  obtain ⟨g, hg⟩ := exists_qPochhammer_eq_one_add_mul ((X : R⟦X⟧) * X ^ m) k
  rw [hg, map_add, ← pow_succ', PowerSeries.coeff_X_pow_mul', ite_eq_right hj.not_ge, add_zero]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Telescoping split `(X; X)_n = (X; X)_{n-k} · (X·X^{n-k}; X)_k` for `k ≤ n`. -/
private theorem qPochhammer_X_eq_qPochhammer_mul {k n : ℕ} (hkn : k ≤ n) :
    qPochhammer (X : R⟦X⟧) n =
      qPochhammer (X : R⟦X⟧) (n - k) * qPochhammer ((X : R⟦X⟧) * X ^ (n - k)) k := by
  conv_lhs => rw [show n = n - k + k from (Nat.sub_add_cancel hkn).symm]
  rw [qPochhammer, qPochhammer, qPochhammer, Finset.prod_range_add]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => by ring)

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Two power series agreeing in all coefficients below `N` still agree there after
multiplication by a common factor. -/
private theorem coeff_mul_congr {f g b : R⟦X⟧} {N j : ℕ} (hj : j < N)
    (h : ∀ i < N, PowerSeries.coeff i f = PowerSeries.coeff i g) :
    PowerSeries.coeff j (f * b) = PowerSeries.coeff j (g * b) := by
  have hd : (X : R⟦X⟧) ^ N ∣ f - g :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi => by rw [map_sub, h i hi, sub_self]
  have hj0 := PowerSeries.X_pow_dvd_iff.mp (hd.mul_right b) j hj
  rwa [sub_mul, map_sub, sub_eq_zero] at hj0

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- For `j + k ≤ n`, the `j`-th coefficient of `qBinom n k X` equals that of `qPochhammerInv k`.
@isnad1 id=eq.1h4v.s8.73b6e0711fa3 from=translated src=- shape=ea3818fc vocab=bf8ea22d
-/
theorem coeff_qBinom_eq_coeff_qPochhammerInv {k j n : ℕ} (hjk : j + k ≤ n) :
    PowerSeries.coeff j (QSeries.qBinom n k (X : R⟦X⟧)) =
    PowerSeries.coeff j (qPochhammerInv (R := R) k) := by
  have hkn : k ≤ n := by omega
  have h_eq : QSeries.qBinom n k (X : R⟦X⟧) * qPochhammer (X : R⟦X⟧) k *
      qPochhammer (X : R⟦X⟧) (n - k) = qPochhammer (X : R⟦X⟧) n :=
    QSeries.qBinom_mul_qPochhammer_mul_qPochhammer (X : R⟦X⟧) hkn
  have hcancel : QSeries.qBinom n k (X : R⟦X⟧) * qPochhammer (X : R⟦X⟧) k
      = qPochhammer ((X : R⟦X⟧) * X ^ (n - k)) k := by
    refine (isUnit_qPochhammer_X (R := R) (n - k)).mul_right_cancel ?_
    rw [h_eq, qPochhammer_X_eq_qPochhammer_mul hkn]
    exact mul_comm _ _
  have hdvd : (X : R⟦X⟧) ^ (n - k + 1) ∣
      QSeries.qBinom n k (X : R⟦X⟧) - qPochhammerInv (R := R) k := by
    refine (IsUnit.dvd_mul_right (isUnit_qPochhammer_X (R := R) k)).mp ?_
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [sub_mul, hcancel, qPochhammerInv_mul_qPochhammer_X, map_sub,
      coeff_qPochhammer_X_mul_pow _ _ hm, sub_self]
  rw [← sub_eq_zero, ← map_sub]
  exact PowerSeries.X_pow_dvd_iff.mp hdvd j (by omega)

omit [TopologicalSpace R] [DiscreteTopology R] in
private theorem qPochhammer_neg_eq_sum (a : R⟦X⟧) (n : ℕ) :
    qPochhammer (-a) n = ∑ k ∈ Finset.range (n + 1),
      X ^ k.choose 2 * QSeries.qBinom n k (X : R⟦X⟧) * a ^ k := by
  rw [qPochhammer, ← QSeries.prod_one_add_mul_pow_eq_sum_qBinom (X : R⟦X⟧) a n]
  exact Finset.prod_congr rfl fun _ _ => by ring

omit [TopologicalSpace R] [DiscreteTopology R] in
private theorem coeff_eq_zero_of_lt_choose_two (a : R⟦X⟧) (d k : ℕ) (hk : d < k.choose 2) :
    PowerSeries.coeff d (X ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k) = 0 := by
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', ite_eq_right hk.not_ge]

omit [DiscreteTopology R] in
/-- The Euler-second summands `X^{C(k,2)} · a^k · (X; X)_k⁻¹` form a summable family. -/
private theorem summable_pow_choose_two_mul_pow_mul_qPochhammerInv (a : R⟦X⟧) :
    Summable fun k : ℕ => (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k := by
  refine (WithPiTopology.summable_iff_summable_coeff R).mpr fun d => ?_
  refine summable_of_ne_finset_zero (s := Finset.range (d + 2)) fun k hk => ?_
  exact coeff_eq_zero_of_lt_choose_two a d k (Nat.lt_choose_two_of_add_two_le (by simpa using hk))

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Termwise agreement, in degree `n`, between the finite q-binomial expansion of
`(-a; X)_{n+1}` and the Euler-second summands. -/
private theorem coeff_pow_choose_two_mul_qBinom_mul_pow (a : R⟦X⟧) (n k : ℕ) :
    PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * QSeries.qBinom (n + 1) k X * a ^ k) =
      PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k) := by
  rw [mul_assoc, show (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k
      = X ^ k.choose 2 * (qPochhammerInv (R := R) k * a ^ k) from by ring,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · refine coeff_mul_congr (N := n - k.choose 2 + 1) (by omega) fun i hi => ?_
    exact coeff_qBinom_eq_coeff_qPochhammerInv (by have := Nat.le_choose_two_add_one k; omega)
  · rfl

/-- FPS Euler second identity: `qPochhammerInf(-a) = Σ_{k≥0} X^{C(k,2)} · a^k · (qPochhammer X k)⁻¹`
in `R⟦X⟧`.
@isnad1 id=eq.0h2v.s7.c9f273935ba4 from=translated src=- shape=583c299e vocab=9c2ec3d9
-/
theorem euler_second_identity (a : R⟦X⟧) :
    qPochhammerInf (-a) = ∑' k : ℕ, X ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k := by
  ext n
  have hcoeff :
      ∑' k : ℕ, PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k)
        = PowerSeries.coeff n
            (∑' k : ℕ, (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k) :=
    ((summable_pow_choose_two_mul_pow_mul_qPochhammerInv a).hasSum.map
      (PowerSeries.coeff n).toAddMonoidHom (WithPiTopology.continuous_coeff R n)).tsum_eq
  rw [coeff_qPochhammerInf, qPochhammer_neg_eq_sum, ← hcoeff,
    tsum_eq_sum (s := Finset.range (n + 2)) fun k hk =>
      coeff_eq_zero_of_lt_choose_two a n k (Nat.lt_choose_two_of_add_two_le (by simpa using hk)),
    map_sum]
  exact Finset.sum_congr rfl fun k _ => coeff_pow_choose_two_mul_qBinom_mul_pow a n k

end Euler2

section KeyIdentity

omit [DiscreteTopology R] in
/-- A family `m ↦ X ^ e m * g m` in `R⟦X⟧` is summable as soon as the exponents `e m`
eventually exceed every fixed degree: only finitely many terms contribute to each
coefficient. -/
private theorem summable_X_pow_mul {e : ℕ → ℕ}
    (he : ∀ d : ℕ, ∃ N : ℕ, ∀ m ≥ N, d < e m) (g : ℕ → R⟦X⟧) :
    Summable fun m : ℕ => (X : R⟦X⟧) ^ e m * g m := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff R).mpr fun d => ?_
  obtain ⟨N, hN⟩ := he d
  refine summable_of_ne_finset_zero (s := Finset.range N) fun m hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (by have := hN m hm; omega)]

/-- The exponents `m * (m + k)` eventually exceed every fixed degree. -/
private theorem exists_forall_lt_mul (k d : ℕ) : ∃ N : ℕ, ∀ m ≥ N, d < m * (m + k) :=
  ⟨d + 1, fun m hm => lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right m (by omega))⟩

/-- The exponents `C(m, 2)` eventually exceed every fixed degree. -/
private theorem exists_forall_lt_choose_two (d : ℕ) :
    ∃ N : ℕ, ∀ m ≥ N, d < m.choose 2 := by
  refine ⟨d + 2, fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [Nat.choose_two_succ]
  omega

/-- The key sum `S_k = ∑_m X^{m(m+k)} / ((X;X)_m (X;X)_{m+k})`. -/
def keySum (k : ℕ) : R⟦X⟧ :=
  ∑' m : ℕ, X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k)

omit [DiscreteTopology R] in
/-- The defining series for `keySum k` is summable in `R⟦X⟧`.
@isnad1 id=summable.0h2v.s7.5a2f8aee65bf from=translated src=- shape=b992542b vocab=73817c40
-/
theorem summable_keySummand (k : ℕ) :
    Summable (fun m : ℕ =>
      X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k)) := by
  simpa [mul_assoc] using summable_X_pow_mul (R := R)
    (exists_forall_lt_mul k) fun m => qPochhammerInv m * qPochhammerInv (m + k)

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Key auxiliary: `qPochhammerInv(n-1) + X^n * qPochhammerInv(n) = qPochhammerInv(n)`.
    Equivalently,
    `(1 - X^{n+1}) * qPochhammerInv(n+1) + X^{n+1} * qPochhammerInv(n+1) = qPochhammerInv(n+1)`. -/
private theorem qPochhammerInv_add_pow_mul_qPochhammerInv_succ (n : ℕ) :
    qPochhammerInv (R := R) n + X ^ (n + 1) * qPochhammerInv (R := R) (n + 1) =
    qPochhammerInv (R := R) (n + 1) := by
  rw [← one_sub_pow_mul_qPochhammerInv_succ (R := R) n]; ring

/-- The intermediate sum `T_k = ∑ m, X^{m(m+k)} * qPochhammerInv(m) * qPochhammerInv(m+k+1)`. -/
private def keySumShift (k : ℕ) : R⟦X⟧ :=
  ∑' m : ℕ, X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k + 1)

private theorem keySumShift_eq_keySum_add (k : ℕ) :
    keySumShift (R := R) k = keySum k + X ^ (k + 1) * keySum (k + 1) := by
  unfold keySumShift keySum
  rw [← Summable.tsum_mul_left _ (summable_keySummand (R := R) (k + 1)),
    ← Summable.tsum_add (summable_keySummand (R := R) k)
      (Summable.mul_left _ (summable_keySummand (R := R) (k + 1)))]
  refine tsum_congr fun m => ?_
  simp only [← add_assoc]
  have hpow : (X : R⟦X⟧) ^ (k + 1) * X ^ (m * (m + k + 1)) =
      X ^ (m + k + 1) * X ^ (m * (m + k)) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [← one_sub_pow_mul_qPochhammerInv_succ (R := R) (m + k), ← mul_assoc ((X : R⟦X⟧) ^ (k + 1)),
    ← mul_assoc ((X : R⟦X⟧) ^ (k + 1)), hpow]
  generalize (X : R⟦X⟧) ^ (m * (m + k)) = A
  ring

/-- The shifted form of `X^{k+1} · S_{k+2}` as a `HasSum` statement. -/
private theorem hasSum_pow_mul_keySum (k : ℕ) :
    HasSum (fun n : ℕ =>
      X ^ ((n + 1) * (n + 1 + k)) * qPochhammerInv (R := R) n * qPochhammerInv (n + k + 2))
      (X ^ (k + 1) * keySum (R := R) (k + 2)) := by
  have hfun : (fun n : ℕ => (X : R⟦X⟧) ^ (k + 1) *
      (X ^ (n * (n + (k + 2))) * qPochhammerInv (R := R) n * qPochhammerInv (n + (k + 2)))) =
      fun n : ℕ => X ^ ((n + 1) * (n + 1 + k)) * qPochhammerInv (R := R) n *
        qPochhammerInv (n + k + 2) := by
    funext n
    rw [show n + (k + 2) = n + k + 2 from by omega,
      show (n + 1) * (n + 1 + k) = k + 1 + n * (n + k + 2) from by ring, pow_add]
    ring
  exact hfun ▸ (summable_keySummand (R := R) (k + 2)).hasSum.mul_left _

private theorem keySumShift_eq_keySum_succ_add (k : ℕ) :
    keySumShift (R := R) k = keySum (k + 1) + X ^ (k + 1) * keySum (k + 2) := by
  have hA := (hasSum_nat_add_iff' (f := fun m : ℕ =>
    X ^ (m * (m + (k + 1))) * qPochhammerInv (R := R) m * qPochhammerInv (m + (k + 1))) 1).mpr
      (summable_keySummand (R := R) (k + 1)).hasSum
  refine HasSum.tsum_eq ((hasSum_nat_add_iff' 1).mp ?_)
  convert hA.add (hasSum_pow_mul_keySum (R := R) k) using 1
  · funext n
    rw [show n + 1 + k + 1 = n + k + 2 from by omega,
      show n + 1 + (k + 1) = n + k + 2 from by omega,
      show (n + 1) * (n + k + 2) = (n + 1) * (n + 1 + k) + (n + 1) from by ring, pow_add]
    conv_lhs => rw [← qPochhammerInv_add_pow_mul_qPochhammerInv_succ (R := R) n]
    ring
  · simp only [keySum, Finset.sum_range_one, Nat.zero_mul, Nat.zero_add, pow_zero, one_mul]
    ring

/-- The recurrence: `S_k − S_{k+1} = X^{k+1} (S_{k+2} − S_{k+1})`.
@isnad1 id=eq.0h2v.s7.c036add89a06 from=translated src=- shape=bf6da468 vocab=3ca702f5
-/
theorem keySum_sub_keySum_succ (k : ℕ) :
    keySum (R := R) k - keySum (k + 1) =
    X ^ (k + 1) * (keySum (R := R) (k + 2) - keySum (k + 1)) := by
  have h := (keySumShift_eq_keySum_add (R := R) k).symm.trans (keySumShift_eq_keySum_succ_add k)
  rw [mul_sub, sub_eq_sub_iff_add_eq_add]
  exact h.trans (add_comm _ _)

/-- `keySum k` is independent of `k`: all values are equal to `keySum 0`.
@isnad1 id=eq.0h2v.s4.428770950339 from=translated src=- shape=3bc33c16 vocab=133148bf
-/
theorem keySum_eq_keySum_zero (k : ℕ) : keySum (R := R) k = keySum 0 := by
  -- `S_j - S_{j+1}` is divisible by `X ^ N` for every `N`, hence zero.
  have key : ∀ N j : ℕ, ∃ g : R⟦X⟧, keySum (R := R) j - keySum (j + 1) = X ^ N * g := by
    intro N
    induction N with
    | zero => exact fun j => ⟨_, (one_mul _).symm⟩
    | succ N ih =>
      intro j
      obtain ⟨g, hg⟩ := ih (j + 1)
      refine ⟨-(X ^ j * g), ?_⟩
      rw [keySum_sub_keySum_succ j, ← neg_sub (keySum (R := R) (j + 1)), hg]
      ring
  have hzero : ∀ j : ℕ, keySum (R := R) j = keySum (j + 1) := by
    intro j
    rw [← sub_eq_zero]
    ext d
    obtain ⟨g, hg⟩ := key (d + 1) j
    rw [hg, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega), map_zero]
  induction k with
  | zero => rfl
  | succ k ih => rw [← hzero k, ih]

end KeyIdentity

section Cauchy

/-- `qPochhammerInf X * qPochhammerInf(-a) = Σ_n X^{C(n,2)} a^n qPochhammerInf(X · X^n)`
in `R⟦X⟧`.
@isnad1 id=eq.0h2v.s8.0dd3db187133 from=translated src=- shape=e768876c vocab=91c37693
-/
theorem qPochhammerInf_X_mul_qPochhammerInf_neg (a : R⟦X⟧) :
    qPochhammerInf (X : R⟦X⟧) * qPochhammerInf (-a) =
    ∑' n : ℕ, X ^ n.choose 2 * a ^ n * qPochhammerInf (X * X ^ n) := by
  have hs : Summable fun n : ℕ => X ^ n.choose 2 * a ^ n * qPochhammerInv (R := R) n := by
    simpa [mul_assoc] using summable_X_pow_mul (R := R)
      exists_forall_lt_choose_two fun n => a ^ n * qPochhammerInv n
  rw [euler_second_identity a, ← Summable.tsum_mul_left _ hs]
  exact tsum_congr fun n => by rw [← qPochhammerInf_X_mul_qPochhammerInv n]; ring

end Cauchy

section JTP

/-- The equivalence ℕ × ℕ ≃ (ℕ × ℕ) ⊕ (ℕ × ℕ) splitting along the diagonal:
  (n, m) ↦ if m ≤ n then inl (n - m, m) else inr (m - n - 1, n). -/
private def diagonalEquiv : ℕ × ℕ ≃ (ℕ × ℕ) ⊕ (ℕ × ℕ) where
  toFun p := if p.2 ≤ p.1 then Sum.inl (p.1 - p.2, p.2) else Sum.inr (p.2 - p.1 - 1, p.1)
  invFun s := match s with
    | Sum.inl (k, m) => (m + k, m)
    | Sum.inr (l, n) => (n, n + l + 1)
  left_inv := by intro ⟨n, m⟩; simp only; split_ifs with h <;> simp <;> omega
  right_inv := by
    intro s
    rcases s with ⟨k, m⟩ | ⟨l, n⟩ <;> simp
    omega

open LaurentPolynomial in
private abbrev leftSummand (n : ℕ) : (LaurentPolynomial ℂ)⟦X⟧ :=
  X ^ n.choose 2 * laurentZ ^ n * qPochhammerInf (X * X ^ n)

open LaurentPolynomial in
private abbrev rightSummand (m : ℕ) : (LaurentPolynomial ℂ)⟦X⟧ :=
  X ^ (m.choose 2 + m) * laurentZInv ^ m * qPochhammerInv m

end JTP

end QSeries.FormalPowerSeries

end
