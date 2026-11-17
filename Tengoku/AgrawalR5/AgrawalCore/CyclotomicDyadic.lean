/-
Exact two-primary depth of the canonical cyclotomic order.

For an odd inert prime `p`, put `u = zeta_5 - 1`.  The Frobenius identity
`u^(p^2 - 1) = -zeta_5^4` has right-hand side of exact order ten.  This
module turns it into

  v_2(orderOf u) = v_2(p^2 - 1) + 1.

No density statement or finite census enters the proof.
-/
import Tengoku.AgrawalR5.AgrawalCore.QuarticRigidity
import Tengoku.AgrawalR5.AgrawalCore.ScalarCompleteness
import Tengoku.AgrawalR5.AgrawalCore.TwoAdicJaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

/-- If the `d`-th power of a group element has exact order ten, then the
two-primary depth of the original order is exactly one larger than that of
`d`.  No finiteness assumption on the ambient group is needed.
@isnad1 id=eq.2h3v.s6.35abbab51255 from=translated src=- shape=8d83f6e6 vocab=19d537e7
-/
theorem orderOf_factorization_two_of_orderOf_pow_eq_ten
    {G : Type*} [Group G] (u : G) {d : ℕ} (hd : d ≠ 0)
    (hord : orderOf (u ^ d) = 10) :
    (orderOf u).factorization 2 = d.factorization 2 + 1 := by
  have hu10 : u ^ (10 * d) = 1 := by
    rw [mul_comm, pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hord]
  have hdvd : orderOf u ∣ 10 * d := orderOf_dvd_of_pow_eq_one hu10
  have hnot : ¬ orderOf u ∣ 5 * d := by
    intro hdiv
    have hu5 : u ^ (5 * d) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
    have hpow5 : (u ^ d) ^ 5 = 1 := by
      simpa [pow_mul, mul_comm] using hu5
    have h10dvd5 : 10 ∣ 5 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hpow5
    norm_num at h10dvd5
  have hu0 : orderOf u ≠ 0 := by
    intro hu
    rw [hu] at hdvd
    exact (Nat.mul_ne_zero (by norm_num) hd)
      (Nat.eq_zero_of_zero_dvd hdvd)
  set a := d.factorization 2 with ha
  set v := d / 2 ^ a with hv
  have hsplit : 2 ^ a * v = d :=
    Nat.ordProj_mul_ordCompl_eq_self d 2
  have hdvd' : orderOf u ∣ 2 ^ (a + 1) * (5 * v) := by
    have heq : 2 ^ (a + 1) * (5 * v) = 10 * d := by
      rw [pow_succ, ← hsplit]
      ring
    rwa [heq]
  have hnot' : ¬ orderOf u ∣ 2 ^ a * (5 * v) := by
    have heq : 2 ^ a * (5 * v) = 5 * d := by
      rw [← hsplit]
      ring
    rwa [heq]
  have hlowerDvd : 2 ^ (a + 1) ∣ orderOf u :=
    pow_two_dvd_of_not_dvd_half hu0 hdvd' hnot'
  have hlower : a + 1 ≤ (orderOf u).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hu0).mp
      hlowerDvd
  have htenD0 : 10 * d ≠ 0 := Nat.mul_ne_zero (by norm_num) hd
  have hfac : (orderOf u).factorization ≤ (10 * d).factorization :=
    (Nat.factorization_le_iff_dvd hu0 htenD0).mpr hdvd
  have hupper := hfac 2
  rw [Nat.factorization_mul (by norm_num) hd] at hupper
  have h10fac : ((10 : ℕ).factorization 2) = 1 := by
    have h2 : (2 : ℕ).Prime := by norm_num
    rw [show (10 : ℕ) = 2 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    rw [h2.factorization]
    simp [Nat.factorization_eq_zero_of_not_dvd
      (by norm_num : ¬ (2 : ℕ) ∣ 5)]
  change (orderOf u).factorization 2 ≤
    (10 : ℕ).factorization 2 + d.factorization 2 at hupper
  rw [h10fac] at hupper
  omega

variable {p : ℕ} [Fact p.Prime]

noncomputable def zetaFiveUnit : (Phi5Ring p)ˣ :=
  (zeta5_isUnit (p := p)).unit

/--
@isnad1 id=eq.0h1v.s5.e32df9873941 from=translated src=- shape=c1619118 vocab=28d6decb
-/
@[simp] lemma zetaFiveUnit_val :
    ((zetaFiveUnit (p := p) : (Phi5Ring p)ˣ) : Phi5Ring p) = zeta5 :=
  (zeta5_isUnit (p := p)).unit_spec

/-- The exact Frobenius quotient `-zeta_5^4`, as a unit.-/
noncomputable def inertTwistUnit : (Phi5Ring p)ˣ :=
  -(zetaFiveUnit (p := p) ^ 4)

/--
@isnad1 id=eq.0h1v.s6.eb02fbf9505c from=translated src=- shape=7aee9484 vocab=2c4c3bdc
-/
@[simp] lemma inertTwistUnit_val :
    ((inertTwistUnit (p := p) : (Phi5Ring p)ˣ) : Phi5Ring p) =
      -(zeta5 ^ 4) := by
  simp [inertTwistUnit]

/--
@isnad1 id=eq.0h1v.s7.4fcb171b2cf3 from=translated src=- shape=2fc5a411 vocab=8711c99a
-/
lemma inertTwistUnit_pow_ten :
    (inertTwistUnit (p := p)) ^ 10 = 1 := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, inertTwistUnit_val, Units.val_one]
  calc
    (-(zeta5 ^ 4 : Phi5Ring p)) ^ 10 = (zeta5 ^ 5) ^ 8 := by ring
    _ = 1 := by rw [zeta5_pow_five, one_pow]

/--
@isnad1 id=ne.1h1v.s7.3bc8c46c529f from=translated src=- shape=9397c474 vocab=8711c99a
-/
lemma inertTwistUnit_pow_five (hp2 : p ≠ 2) :
    (inertTwistUnit (p := p)) ^ 5 ≠ 1 := by
  intro h
  have hv := congrArg (fun x : (Phi5Ring p)ˣ => (x : Phi5Ring p)) h
  simp only [Units.val_pow_eq_pow_val, inertTwistUnit_val, Units.val_one] at hv
  have hneg : (-(zeta5 ^ 4 : Phi5Ring p)) ^ 5 = -1 := by
    calc
      (-(zeta5 ^ 4 : Phi5Ring p)) ^ 5 = -((zeta5 ^ 5) ^ 4) := by ring
      _ = -1 := by rw [zeta5_pow_five, one_pow]
  rw [hneg] at hv
  have hchar : (2 : Phi5Ring p) = 0 := by
    calc
      (2 : Phi5Ring p) = 1 + 1 := by norm_num
      _ = (-1) + 1 := by rw [hv]
      _ = 0 := by ring
  have hcast : p ∣ 2 :=
    (CharP.cast_eq_zero_iff (Phi5Ring p) p 2).mp hchar
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hcast)

/--
@isnad1 id=ne.1h1v.s7.e6ad44f7e5c8 from=translated src=- shape=9397c474 vocab=8711c99a
-/
lemma inertTwistUnit_pow_two (hp5 : p ≠ 5) :
    (inertTwistUnit (p := p)) ^ 2 ≠ 1 := by
  intro h
  have hv := congrArg (fun x : (Phi5Ring p)ˣ => (x : Phi5Ring p)) h
  simp only [Units.val_pow_eq_pow_val, inertTwistUnit_val, Units.val_one] at hv
  have hsq : (-(zeta5 ^ 4 : Phi5Ring p)) ^ 2 = zeta5 ^ 3 := by
    calc
      (-(zeta5 ^ 4 : Phi5Ring p)) ^ 2 = zeta5 ^ 8 := by ring
      _ = zeta5 ^ 3 := by
        rw [show (8 : ℕ) = 5 + 3 by norm_num, pow_add,
          zeta5_pow_five, one_mul]
  rw [hsq] at hv
  exact (u3_isUnit (p := p) hp5).ne_zero (sub_eq_zero.mpr hv)

/-- The Frobenius quotient has exact order ten for every odd good prime.
@isnad1 id=eq.2h1v.s6.80f4e47ef63c from=translated src=- shape=010aa7b2 vocab=f54b861b
-/
lemma orderOf_inertTwistUnit (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    orderOf (inertTwistUnit (p := p)) = 10 := by
  apply orderOf_eq_of_pow_and_pow_div_prime
    (by norm_num) inertTwistUnit_pow_ten
  intro ell hell helldvd
  have hdvd : ell ∣ 2 * 5 := by simpa using helldvd
  rcases hell.dvd_mul.mp hdvd with h2 | h5
  · rcases (Nat.dvd_prime Nat.prime_two).mp h2 with heq | heq
    · exact (hell.ne_one heq).elim
    subst ell
    norm_num
    exact inertTwistUnit_pow_five hp2
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h5 with heq | heq
    · exact (hell.ne_one heq).elim
    subst ell
    norm_num
    exact inertTwistUnit_pow_two hp5

/-- The cancelled Frobenius identity in the unit group.
@isnad1 id=eq.3h1v.s8.3d1f4a750477 from=translated src=- shape=0a044abc vocab=31d07fc7
-/
lemma localCyclotomicUnit_pow_sq_sub_one
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5) (hp1 : 1 ≤ p) :
    (localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ)) ^ (p * p - 1) =
      inertTwistUnit (p := p) := by
  apply mul_right_cancel (b := localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ))
  have hppos : 1 ≤ p * p := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  have hsub : p * p - 1 + 1 = p * p := by omega
  rw [← pow_succ, hsub]
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val,
    localCyclotomicUnit_val, zmodFiveUnitOne_val, pow_one,
    inertTwistUnit_val]
  exact order_bound_relation (p := p) hp

/--
@isnad1 id=eq.4h1v.s8.9d467d398acf from=translated src=- shape=3c09e7e9 vocab=a3c8a55e
-/
lemma orderOf_localCyclotomicUnit_pow_sq_sub_one
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp2 : p ≠ 2)
    (hp5 : p ≠ 5) (hp1 : 1 ≤ p) :
    orderOf
      ((localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ)) ^ (p * p - 1)) = 10 := by
  rw [localCyclotomicUnit_pow_sq_sub_one hp hp5 hp1]
  exact orderOf_inertTwistUnit hp2 hp5

/-- **Exact binary law for the cyclotomic order.**
@isnad1 id=eq.3h1v.s8.b3f7fa6ca88f from=translated src=- shape=ec283426 vocab=2d509a1c
-/
theorem localCyclotomicUnit_order_factorization_two
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (orderOf (localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ))).factorization 2 =
      (p * p - 1).factorization 2 + 1 := by
  have hpge : 3 ≤ p := by
    have hpge2 := (Fact.out : p.Prime).two_le
    omega
  exact orderOf_factorization_two_of_orderOf_pow_eq_ten
    (localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ))
    (by
      have hpp : 9 ≤ p * p := Nat.mul_le_mul hpge hpge
      omega : p * p - 1 ≠ 0)
    (orderOf_localCyclotomicUnit_pow_sq_sub_one
      hp hp2 hp5 (by omega))

/-- Adding the modulus `5` does not change the two-primary depth.
@isnad1 id=eq.3h1v.s7.007b8893e4b4 from=translated src=- shape=3d5093ed vocab=ec66283f
-/
theorem quarticOrderModulus_factorization_two
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (quarticOrderModulus p hp5).factorization 2 =
      (p * p - 1).factorization 2 + 1 := by
  unfold quarticOrderModulus
  have hfac := localCyclotomicUnit_order_factorization_two hp hp2 hp5
  have ho0 : orderOf
      (localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hfac
    simp at hfac
  rw [Nat.factorization_lcm ho0 (by norm_num)]
  change max
    ((orderOf (localCyclotomicUnit hp5
      (1 : (ZMod 5)ˣ))).factorization 2)
    ((5 : ℕ).factorization 2) = _
  rw [localCyclotomicUnit_order_factorization_two hp hp2 hp5]
  have h5fac : ((5 : ℕ).factorization 2) = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [h5fac, max_eq_left]
  omega

/-- Divisibility form of the exact binary law.
@isnad1 id=dvd.3h1v.s7.622f5063ac64 from=translated src=- shape=9d8cb335 vocab=9f2b4ce1
-/
theorem twoPow_dvd_quarticOrderModulus
    (hp : p % 5 = 2 ∨ p % 5 = 3) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    2 ^ ((p * p - 1).factorization 2 + 1) ∣
      quarticOrderModulus p hp5 := by
  have hfac := localCyclotomicUnit_order_factorization_two hp hp2 hp5
  have ho0 : orderOf
      (localCyclotomicUnit hp5 (1 : (ZMod 5)ˣ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hfac
    simp at hfac
  have hmod0 : quarticOrderModulus p hp5 ≠ 0 := by
    unfold quarticOrderModulus
    exact Nat.lcm_ne_zero ho0 (by norm_num)
  apply (Nat.Prime.pow_dvd_iff_le_factorization
    Nat.prime_two hmod0).mpr
  rw [quarticOrderModulus_factorization_two hp hp2 hp5]

end AgrawalCore
