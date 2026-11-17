/-
Esclusione delle prime quattro profondità della famiglia strutturale H4
con un solo supporto dispari:
`p-1 = 2^b*q^e`, per `b ∈ {3,4,5,6}`.

Il lemma combinatorio sugli ordini è in `PrimitiveSupport`. Qui vengono
formalizzati i due certificati algebrico-aritmetici che eliminano il caso
in cui uno degli ordini completi divide la potenza di due fissata.
-/
import Tengoku.AgrawalR5.AgrawalCore.PrimitiveScalarBridge
import Tengoku.AgrawalR5.AgrawalCore.Reciprocity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/--
@isnad1 id=eq.0h0v.s6.1423edd9fe73 from=translated src=- shape=fb3a899a vocab=4ffbedeb
-/
theorem five_pow_eight_sub_one_factorization :
    5 ^ 8 - 1 = 2 ^ 5 * 3 * 13 * 313 := by
  norm_num

/--
@isnad1 id=eq.0h0v.s6.4701f49839f3 from=translated src=- shape=0dd3ede8 vocab=de4a4c74
-/
theorem golden_square_norm_eight_factorization :
    2205 = 3 ^ 2 * 5 * 7 ^ 2 := by
  norm_num

/--
@isnad1 id=eq.0h0v.s6.eed622a9cce5 from=translated src=- shape=5ebd626d vocab=4ffbedeb
-/
theorem five_pow_sixteen_sub_one_factorization :
    5 ^ 16 - 1 = 2 ^ 6 * 3 * 13 * 17 * 313 * 11489 := by
  norm_num

/--
@isnad1 id=eq.0h0v.s6.86ae489c7d6f from=translated src=- shape=ede41a53 vocab=de4a4c74
-/
theorem golden_square_norm_sixteen_factorization :
    4870845 = 3 ^ 2 * 5 * 7 ^ 2 * 47 ^ 2 := by
  norm_num

/--
@isnad1 id=eq.0h0v.s7.b03a0b191e54 from=translated src=- shape=bbac3466 vocab=4ffbedeb
-/
theorem five_pow_thirtytwo_sub_one_factorization :
    5 ^ 32 - 1 =
      2 ^ 7 * 3 * 13 * 17 * 313 * 2593 * 11489 * 29423041 := by
  norm_num

/--
@isnad1 id=eq.0h0v.s7.c8373e5ac41b from=translated src=- shape=dd90aef5 vocab=de4a4c74
-/
theorem golden_square_norm_thirtytwo_factorization :
    23725150497405 = 3 ^ 2 * 5 * 7 ^ 2 * 47 ^ 2 * 2207 ^ 2 := by
  norm_num

/--
@isnad1 id=or.2h1v.s6.548e469e3cd8 from=translated src=- shape=2a23f20c vocab=d5acfd5f
-/
theorem prime_dvd_five_pow_eight_sub_one_cases {p : ℕ} (hp : p.Prime)
    (h : p ∣ 5 ^ 8 - 1) :
    p = 2 ∨ p = 3 ∨ p = 13 ∨ p = 313 := by
  have h' : p ∣ 2 ^ 5 * 3 * 13 * 313 := by
    rwa [five_pow_eight_sub_one_factorization] at h
  rcases hp.dvd_mul.mp h' with hleft | h313
  · rcases hp.dvd_mul.mp hleft with hleft | h13
    · rcases hp.dvd_mul.mp hleft with h2pow | h3
      · left
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
          (hp.dvd_of_dvd_pow h2pow)
      · right; left
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3
    · right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h13
  · right; right; right
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h313

/--
@isnad1 id=or.2h1v.s5.d798da612325 from=translated src=- shape=587e5538 vocab=806915f4
-/
theorem prime_dvd_2205_cases {p : ℕ} (hp : p.Prime) (h : p ∣ 2205) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have h' : p ∣ 3 ^ 2 * 5 * 7 ^ 2 := by
    rwa [golden_square_norm_eight_factorization] at h
  rcases hp.dvd_mul.mp h' with hleft | h7pow
  · rcases hp.dvd_mul.mp hleft with h3pow | h5
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
        (hp.dvd_of_dvd_pow h3pow)
    · right; left
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
  · right; right
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
      (hp.dvd_of_dvd_pow h7pow)

/--
@isnad1 id=or.2h1v.s6.dbc07d369b00 from=translated src=- shape=38a6b82d vocab=d5acfd5f
-/
theorem prime_dvd_five_pow_sixteen_sub_one_cases {p : ℕ}
    (hp : p.Prime) (h : p ∣ 5 ^ 16 - 1) :
    p = 2 ∨ p = 3 ∨ p = 13 ∨ p = 17 ∨ p = 313 ∨ p = 11489 := by
  have h' : p ∣ 2 ^ 6 * 3 * 13 * 17 * 313 * 11489 := by
    rwa [five_pow_sixteen_sub_one_factorization] at h
  rcases hp.dvd_mul.mp h' with hleft | h11489
  · rcases hp.dvd_mul.mp hleft with hleft | h313
    · rcases hp.dvd_mul.mp hleft with hleft | h17
      · rcases hp.dvd_mul.mp hleft with hleft | h13
        · rcases hp.dvd_mul.mp hleft with h2pow | h3
          · left
            exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
              (hp.dvd_of_dvd_pow h2pow)
          · right; left
            exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3
        · right; right; left
          exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h13
      · right; right; right; left
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h17
    · right; right; right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h313
  · right; right; right; right; right
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h11489

/--
@isnad1 id=or.2h1v.s5.d40a38963441 from=translated src=- shape=d15e27ad vocab=806915f4
-/
theorem prime_dvd_4870845_cases {p : ℕ} (hp : p.Prime)
    (h : p ∣ 4870845) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 47 := by
  have h' : p ∣ 3 ^ 2 * 5 * 7 ^ 2 * 47 ^ 2 := by
    rwa [golden_square_norm_sixteen_factorization] at h
  rcases hp.dvd_mul.mp h' with hleft | h47pow
  · rcases hp.dvd_mul.mp hleft with hleft | h7pow
    · rcases hp.dvd_mul.mp hleft with h3pow | h5
      · left
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
          (hp.dvd_of_dvd_pow h3pow)
      · right; left
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
    · right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
        (hp.dvd_of_dvd_pow h7pow)
  · right; right; right
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
      (hp.dvd_of_dvd_pow h47pow)

/--
@isnad1 id=or.2h1v.s6.a6cfa380e75f from=translated src=- shape=2047b2c6 vocab=d5acfd5f
-/
theorem prime_dvd_five_pow_thirtytwo_sub_one_cases {p : ℕ}
    (hp : p.Prime) (h : p ∣ 5 ^ 32 - 1) :
    p = 2 ∨ p = 3 ∨ p = 13 ∨ p = 17 ∨ p = 313 ∨ p = 2593 ∨
      p = 11489 ∨ p = 29423041 := by
  have h' :
      p ∣ 2 ^ 7 * 3 * 13 * 17 * 313 * 2593 * 11489 * 29423041 := by
    rwa [five_pow_thirtytwo_sub_one_factorization] at h
  rcases hp.dvd_mul.mp h' with hleft | h29423041
  · rcases hp.dvd_mul.mp hleft with hleft | h11489
    · rcases hp.dvd_mul.mp hleft with hleft | h2593
      · rcases hp.dvd_mul.mp hleft with hleft | h313
        · rcases hp.dvd_mul.mp hleft with hleft | h17
          · rcases hp.dvd_mul.mp hleft with hleft | h13
            · rcases hp.dvd_mul.mp hleft with h2pow | h3
              · left
                exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
                  (hp.dvd_of_dvd_pow h2pow)
              · right; left
                exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3
            · right; right; left
              exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h13
          · right; right; right; left
            exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h17
        · right; right; right; right; left
          exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h313
      · right; right; right; right; right; left
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2593
    · right; right; right; right; right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h11489
  · right; right; right; right; right; right; right
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h29423041

/--
@isnad1 id=or.2h1v.s5.6f753c87ac0e from=translated src=- shape=8dbf7813 vocab=806915f4
-/
theorem prime_dvd_23725150497405_cases {p : ℕ} (hp : p.Prime)
    (h : p ∣ 23725150497405) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 47 ∨ p = 2207 := by
  have h' : p ∣ 3 ^ 2 * 5 * 7 ^ 2 * 47 ^ 2 * 2207 ^ 2 := by
    rwa [golden_square_norm_thirtytwo_factorization] at h
  rcases hp.dvd_mul.mp h' with hleft | h2207pow
  · rcases hp.dvd_mul.mp hleft with hleft | h47pow
    · rcases hp.dvd_mul.mp hleft with hleft | h7pow
      · rcases hp.dvd_mul.mp hleft with h3pow | h5
        · left
          exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
            (hp.dvd_of_dvd_pow h3pow)
        · right; left
          exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
      · right; right; left
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
          (hp.dvd_of_dvd_pow h7pow)
    · right; right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
        (hp.dvd_of_dvd_pow h47pow)
  · right; right; right; right
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
      (hp.dvd_of_dvd_pow h2207pow)

variable {p : ℕ} [Fact p.Prime]

/-- Se `5^8=1` modulo un buon primo, quel primo è inerte.
@isnad1 id=or.3h1v.s7.dc5e49628999 from=translated src=- shape=c7ad1888 vocab=018cf423
-/
theorem inert_of_five_pow_eight_eq_one (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hpow : (5 : ZMod p) ^ 8 = 1) :
    p % 5 = 2 ∨ p % 5 = 3 := by
  have hzero : (390624 : ZMod p) = 0 := by
    norm_num at hpow ⊢
    linear_combination hpow
  have hdvd : p ∣ 5 ^ 8 - 1 := by
    norm_num
    exact (CharP.cast_eq_zero_iff (ZMod p) p 390624).mp hzero
  rcases prime_dvd_five_pow_eight_sub_one_cases Fact.out hdvd with
      rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · right; norm_num
  · right; norm_num
  · right; norm_num

/-- Riduzione di `x^8` per una radice di `X²-3X+1`.
@isnad1 id=eq.1h2v.s7.413e66ab4548 from=translated src=- shape=344b9e46 vocab=dc5e6440
-/
theorem golden_square_pow_eight {R : Type*} [CommRing R] (x : R)
    (hx : x ^ 2 = 3 * x - 1) :
    x ^ 8 = 987 * x - 377 := by
  have hx4 : x ^ 4 = 21 * x - 8 := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = (3 * x - 1) ^ 2 := by rw [hx]
      _ = 9 * x ^ 2 - 6 * x + 1 := by ring
      _ = 9 * (3 * x - 1) - 6 * x + 1 := by rw [hx]
      _ = 21 * x - 8 := by ring
  calc
    x ^ 8 = (x ^ 4) ^ 2 := by ring
    _ = (21 * x - 8) ^ 2 := by rw [hx4]
    _ = 441 * x ^ 2 - 336 * x + 64 := by ring
    _ = 441 * (3 * x - 1) - 336 * x + 64 := by rw [hx]
    _ = 987 * x - 377 := by ring

/-- Sixteenth-power reduction for a root of `X²-3X+1`.
@isnad1 id=eq.1h2v.s7.88ea929ec72d from=translated src=- shape=344b9e46 vocab=dc5e6440
-/
theorem golden_square_pow_sixteen {R : Type*} [CommRing R] (x : R)
    (hx : x ^ 2 = 3 * x - 1) :
    x ^ 16 = 2178309 * x - 832040 := by
  have h8 := golden_square_pow_eight x hx
  calc
    x ^ 16 = (x ^ 8) ^ 2 := by ring
    _ = (987 * x - 377) ^ 2 := by rw [h8]
    _ = 974169 * x ^ 2 - 744198 * x + 142129 := by ring
    _ = 974169 * (3 * x - 1) - 744198 * x + 142129 := by rw [hx]
    _ = 2178309 * x - 832040 := by ring

/-- Thirty-second-power reduction for a root of `X²-3X+1`.
@isnad1 id=eq.1h2v.s7.145dc7fa416c from=translated src=- shape=344b9e46 vocab=dc5e6440
-/
theorem golden_square_pow_thirtytwo {R : Type*} [CommRing R] (x : R)
    (hx : x ^ 2 = 3 * x - 1) :
    x ^ 32 = 10610209857723 * x - 4052739537881 := by
  have h16 := golden_square_pow_sixteen x hx
  calc
    x ^ 32 = (x ^ 16) ^ 2 := by ring
    _ = (2178309 * x - 832040) ^ 2 := by rw [h16]
    _ = 4745030099481 * x ^ 2 - 3624880440720 * x
          + 692290561600 := by ring
    _ = 4745030099481 * (3 * x - 1) - 3624880440720 * x
          + 692290561600 := by rw [hx]
    _ = 10610209857723 * x - 4052739537881 := by ring

/-- Se una radice aurea quadrata ha ottava potenza uno, la caratteristica
divide il risultante `2205`.
@isnad1 id=dvd.2h2v.s7.c9935ef54d5c from=translated src=- shape=a303c917 vocab=1254c8d0
-/
theorem dvd_2205_of_golden_square_pow_eight (x : ZMod p)
    (hx : x ^ 2 = 3 * x - 1) (hpow : x ^ 8 = 1) :
    p ∣ 2205 := by
  have h8 := golden_square_pow_eight x hx
  have hlin : 987 * x - 378 = 0 := by
    linear_combination hpow - h8
  have hzero : (2205 : ZMod p) = 0 := by
    linear_combination -974169 * hx + (987 * x - 2583) * hlin
  exact (CharP.cast_eq_zero_iff (ZMod p) p 2205).mp hzero

/-- If a golden-square root has sixteenth power one, the characteristic
divides the exact resultant `4870845`.
@isnad1 id=dvd.2h2v.s7.52be84d79500 from=translated src=- shape=a303c917 vocab=1254c8d0
-/
theorem dvd_4870845_of_golden_square_pow_sixteen (x : ZMod p)
    (hx : x ^ 2 = 3 * x - 1) (hpow : x ^ 16 = 1) :
    p ∣ 4870845 := by
  have h16 := golden_square_pow_sixteen x hx
  have hlin : 2178309 * x - 832041 = 0 := by
    linear_combination hpow - h16
  have hzero : (4870845 : ZMod p) = 0 := by
    linear_combination
      -4745030099481 * hx + (2178309 * x - 5702886) * hlin
  exact (CharP.cast_eq_zero_iff (ZMod p) p 4870845).mp hzero

/-- The complementary sign at depth sixteen has resultant
`4870849 = 2207²`.
@isnad1 id=dvd.2h2v.s8.8ed3e1caa0c7 from=translated src=- shape=6f436b1a vocab=e1aa3055
-/
theorem dvd_4870849_of_golden_square_pow_sixteen_eq_neg_one
    (x : ZMod p) (hx : x ^ 2 = 3 * x - 1) (hpow : x ^ 16 = -1) :
    p ∣ 4870849 := by
  have h16 := golden_square_pow_sixteen x hx
  have hlin : 2178309 * x - 832039 = 0 := by
    linear_combination hpow - h16
  have hzero : (4870849 : ZMod p) = 0 := by
    linear_combination
      4745030099481 * hx - (2178309 * x - 5702888) * hlin
  exact (CharP.cast_eq_zero_iff (ZMod p) p 4870849).mp hzero

/-- If a golden-square root has thirty-second power one, the
characteristic divides its exact norm resultant.
@isnad1 id=dvd.2h2v.s7.d78aa3f4f485 from=translated src=- shape=a303c917 vocab=1254c8d0
-/
theorem dvd_23725150497405_of_golden_square_pow_thirtytwo
    (x : ZMod p)
    (hx : x ^ 2 = 3 * x - 1) (hpow : x ^ 32 = 1) :
    p ∣ 23725150497405 := by
  have hsquare : (x ^ 16) * (x ^ 16) = 1 := by
    rw [← pow_add]
    norm_num at hpow ⊢
    exact hpow
  rcases mul_self_eq_one_iff.mp hsquare with hpos | hneg
  · have hdvd := dvd_4870845_of_golden_square_pow_sixteen x hx hpos
    exact hdvd.trans (by norm_num)
  · have hdvd :=
      dvd_4870849_of_golden_square_pow_sixteen_eq_neg_one x hx hneg
    exact hdvd.trans (by norm_num)

/-- The complementary sign at depth thirty-two has exact norm
`23725150497409 = 1087²·4481²`.
@isnad1 id=dvd.2h2v.s8.8b2c14cb0907 from=translated src=- shape=6f436b1a vocab=e1aa3055
-/
theorem dvd_23725150497409_of_golden_square_pow_thirtytwo_eq_neg_one
    (x : ZMod p)
    (hx : x ^ 2 = 3 * x - 1) (hpow : x ^ 32 = -1) :
    p ∣ 23725150497409 := by
  have h32 := golden_square_pow_thirtytwo x hx
  have hlin : 10610209857723 * x - 4052739537880 = 0 := by
    linear_combination hpow - h32
  have hxzero : x ^ 2 - 3 * x + 1 = 0 := by
    linear_combination hx
  have hzero : (23725150497409 : ZMod p) = 0 := by
    calc
      (23725150497409 : ZMod p) =
          10610209857723 ^ 2 * (x ^ 2 - 3 * x + 1)
          - (10610209857723 * x - 27777890035289)
            * (10610209857723 * x - 4052739537880) := by ring
      _ = 0 := by rw [hxzero, hlin]; ring
  exact (CharP.cast_eq_zero_iff (ZMod p) p 23725150497409).mp hzero

set_option maxRecDepth 100000 in
/-- Exact semiperiod of either golden-square root modulo the sole
split candidate `11489` arising at the next dyadic layer.
@isnad1 id=eq.1h1v.s8.53df7f3e06e5 from=translated src=- shape=24530754 vocab=5cf67005
-/
theorem golden_square_pow_718_eq_neg_one_mod_11489
    (x : ZMod 11489) (hx : x ^ 2 = 3 * x - 1) :
    x ^ 718 = -1 := by
  letI : Fact (Nat.Prime 11489) := ⟨by norm_num⟩
  have hsum : (357 + 11135 : ZMod 11489) = 3 := by decide
  have hprod : (357 * 11135 : ZMod 11489) = 1 := by decide
  have hfac : (x - 357) * (x - 11135) = 0 := by
    calc
      (x - 357) * (x - 11135) =
          x ^ 2 - (357 + 11135) * x + 357 * 11135 := by ring
      _ = x ^ 2 - 3 * x + 1 := by rw [hsum, hprod]
      _ = 0 := by linear_combination hx
  rcases mul_eq_zero.mp hfac with hroot | hroot
  · have hxv : x = 357 := by linear_combination hroot
    rw [hxv]
    decide
  · have hxv : x = 11135 := by linear_combination hroot
    rw [hxv]
    decide

private theorem five_pow_eight_eq_neg_one_mod_11489 :
    (5 : ZMod 11489) ^ 8 = -1 := by
  decide

private theorem five_pow_sixteen_eq_one_mod_11489 :
    (5 : ZMod 11489) ^ 16 = 1 := by
  decide

private theorem neg_one_ne_one_mod_11489 :
    (-1 : ZMod 11489) ≠ 1 := by
  decide

/--
@isnad1 id=ne.1h2v.s4.4a3c49cca45c from=translated src=- shape=db067907 vocab=7232c250
-/
theorem prime_power_ne_35 {q e : ℕ} (hq : q.Prime) :
    q ^ e ≠ 35 := by
  intro hqe
  have he : e ≠ 0 := by
    intro he0
    simp [he0] at hqe
  have hqdiv : q ∣ 35 := by
    rw [← hqe]
    exact dvd_pow_self q he
  have hqcase : q = 5 ∨ q = 7 := by
    have h' : q ∣ 5 * 7 := by norm_num at hqdiv ⊢; exact hqdiv
    rcases hq.dvd_mul.mp h' with h5 | h7
    · left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5
    · right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h7
  rcases hqcase with rfl | rfl
  · have h7div : 7 ∣ 5 ^ e := by rw [hqe]; norm_num
    have hcop := (by norm_num : Nat.Coprime 7 5).pow_right e
    have hone := hcop.eq_one_of_dvd h7div
    norm_num at hone
  · have h5div : 5 ∣ 7 ^ e := by rw [hqe]; norm_num
    have hcop := (by norm_num : Nat.Coprime 5 7).pow_right e
    have hone := hcop.eq_one_of_dvd h5div
    norm_num at hone

/-- Anche il ramo aureo `x^8=1` forza un buon primo a essere inerte.
@isnad1 id=or.4h2v.s8.ca01bdb55b3b from=translated src=- shape=fad62662 vocab=9de8b228
-/
theorem inert_of_golden_square_pow_eight (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (x : ZMod p) (hx : x ^ 2 = 3 * x - 1) (hpow : x ^ 8 = 1) :
    p % 5 = 2 ∨ p % 5 = 3 := by
  rcases prime_dvd_2205_cases Fact.out
      (dvd_2205_of_golden_square_pow_eight x hx hpow) with rfl | rfl | rfl
  · right; norm_num
  · exact absurd rfl hp5
  · left; norm_num

/-- **Esclusione universale del singolo supporto dispari.**

Se `p-1=8*q^e`, i due semiordini sono coprimi e sono davvero gli ordini
di `5` e di una radice di `X²-3X+1`, allora `p` non può essere split
modulo `5`.
@isnad1 id=or.8h6v.s8.bba99e8237a4 from=translated src=- shape=f288a7e3 vocab=d5c6fcf5
-/
theorem no_split_single_odd_support {q e r s : ℕ} (hq : q.Prime)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hrs : Nat.Coprime r s)
    (hpform : p - 1 = 8 * q ^ e)
    (hord5 : orderOf (5 : ZMod p) = 2 * r)
    (x : ZMod p) (hx : x ^ 2 = 3 * x - 1)
    (hordx : orderOf x = 2 * s) :
    p % 5 = 2 ∨ p % 5 = 3 := by
  have hR : 2 * r ∣ 8 * q ^ e := by
    rw [← hpform, ← hord5]
    exact ZMod.orderOf_dvd_card_sub_one (by
      intro h50
      have hpdiv : p ∣ 5 :=
        (CharP.cast_eq_zero_iff (ZMod p) p 5).mp h50
      exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hpdiv))
  have hE : 2 * s ∣ 8 * q ^ e := by
    rw [← hpform, ← hordx]
    exact ZMod.orderOf_dvd_card_sub_one (by
      intro hx0
      rw [hx0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hx
      norm_num at hx)
  rcases one_order_dvd_eight_of_single_odd_prime hq hrs hR hE with h8 | h8
  · apply inert_of_five_pow_eight_eq_one hp2 hp5
    apply orderOf_dvd_iff_pow_eq_one.mp
    rwa [hord5]
  · apply inert_of_golden_square_pow_eight hp2 hp5 x hx
    apply orderOf_dvd_iff_pow_eq_one.mp
    rwa [hordx]

/-- **The next dyadic single-support layer is also impossible.**

No good split H-profile can have `p - 1 = 16*q^e` with `q` odd prime.
The only split divisor introduced by the scalar-five resultant is
`11489`; its predecessor has one additional factor of two, so it cannot
occur in the stated layer.
@isnad1 id=false.10h6v.s8.13d1c48f28a0 from=translated src=- shape=169731b7 vocab=d5c6fcf5
-/
theorem no_split_single_odd_support_sixteen
    {q e r s : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hpSplit : p % 5 = 1 ∨ p % 5 = 4)
    (hrs : Nat.Coprime r s)
    (hpform : p - 1 = 16 * q ^ e)
    (hord5 : orderOf (5 : ZMod p) = 2 * r)
    (x : ZMod p) (hx : x ^ 2 = 3 * x - 1)
    (hordx : orderOf x = 2 * s) :
    False := by
  have h5zero : (5 : ZMod p) ≠ 0 := by
    intro h50
    have hpdiv : p ∣ 5 :=
      (CharP.cast_eq_zero_iff (ZMod p) p 5).mp h50
    exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hpdiv)
  have hx0 : x ≠ 0 := by
    intro hxzero
    rw [hxzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hx
    norm_num at hx
  have hR : 2 * r ∣ 16 * q ^ e := by
    rw [← hpform, ← hord5]
    exact ZMod.orderOf_dvd_card_sub_one h5zero
  have hE : 2 * s ∣ 16 * q ^ e := by
    rw [← hpform, ← hordx]
    exact ZMod.orderOf_dvd_card_sub_one hx0
  have hqOdd : Odd q := hq.odd_of_ne_two hq2
  have hqPowOdd : Odd (q ^ e) := hqOdd.pow
  rcases one_order_dvd_two_pow_succ_of_single_odd_prime
      (b := 3) hq hrs (by norm_num at hR ⊢; exact hR)
        (by norm_num at hE ⊢; exact hE) with h16 | h16
  · have hpow : (5 : ZMod p) ^ 16 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rwa [hord5])
    have hzero : (152587890624 : ZMod p) = 0 := by
      norm_num at hpow ⊢
      linear_combination hpow
    have hdvdNat : p ∣ 152587890624 :=
      (CharP.cast_eq_zero_iff (ZMod p) p 152587890624).mp hzero
    have hdvd : p ∣ 5 ^ 16 - 1 := by
      norm_num
      exact hdvdNat
    rcases prime_dvd_five_pow_sixteen_sub_one_cases Fact.out hdvd with
        rfl | rfl | rfl | rfl | rfl | hp11489
    · exact hp2 rfl
    · norm_num at hpSplit
    · norm_num at hpSplit
    · norm_num at hpSplit
    · norm_num at hpSplit
    · subst p
      obtain ⟨a, ha⟩ := hqPowOdd
      norm_num at hpform
      omega
  · have hpow : x ^ 16 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rwa [hordx])
    rcases prime_dvd_4870845_cases Fact.out
        (dvd_4870845_of_golden_square_pow_sixteen x hx hpow) with
        rfl | rfl | rfl | rfl
    · norm_num at hpSplit
    · exact hp5 rfl
    · norm_num at hpSplit
    · norm_num at hpSplit

/-- End-to-end four-coefficient form of the depth-four single-support
exclusion.
@isnad1 id=false.14h7v.s8.f6216a4050b8 from=translated src=- shape=119e8656 vocab=334340c5
-/
theorem no_split_single_odd_support_sixteen_primitive
    {q e r s k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hpSplit : p % 5 = 1 ∨ p % 5 = 4)
    (hr : 0 < r) (hs : 0 < s) (hrs : Nat.Coprime r s)
    (hkpos : 1 ≤ k) (hpm : ¬p ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    (hpform : p - 1 = 16 * q ^ e) :
    False := by
  obtain ⟨hord5, hordx⟩ :=
    dvd_D_exact_scalar_profile hp5 hr hs hkpos hpm hsig γ hγ hD
  exact no_split_single_odd_support_sixteen
    hq hq2 hp2 hp5 hpSplit hrs hpform hord5
      (goldenSquareFromGamma γ)
      (goldenSquareFromGamma_sq_eq_three_mul_sub_one hp5 γ hγ)
      hordx

/-- **The depth-five single-support layer is impossible.**

At this depth the scalar-five resultant has one arithmetically compatible
split factor, `11489`.  Its exact golden semiperiod is `718`, which forces
the two semiorders to share a factor and closes the exceptional case.
@isnad1 id=false.10h6v.s8.14fa0f78abf4 from=translated src=- shape=169731b7 vocab=d5c6fcf5
-/
theorem no_split_single_odd_support_thirtytwo
    {q e r s : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hpSplit : p % 5 = 1 ∨ p % 5 = 4)
    (hrs : Nat.Coprime r s)
    (hpform : p - 1 = 32 * q ^ e)
    (hord5 : orderOf (5 : ZMod p) = 2 * r)
    (x : ZMod p) (hx : x ^ 2 = 3 * x - 1)
    (hordx : orderOf x = 2 * s) :
    False := by
  have h5zero : (5 : ZMod p) ≠ 0 := by
    intro h50
    have hpdiv : p ∣ 5 :=
      (CharP.cast_eq_zero_iff (ZMod p) p 5).mp h50
    exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hpdiv)
  have hx0 : x ≠ 0 := by
    intro hxzero
    rw [hxzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hx
    norm_num at hx
  have hR : 2 * r ∣ 32 * q ^ e := by
    rw [← hpform, ← hord5]
    exact ZMod.orderOf_dvd_card_sub_one h5zero
  have hE : 2 * s ∣ 32 * q ^ e := by
    rw [← hpform, ← hordx]
    exact ZMod.orderOf_dvd_card_sub_one hx0
  have hqOdd : Odd q := hq.odd_of_ne_two hq2
  have hqPowOdd : Odd (q ^ e) := hqOdd.pow
  rcases one_order_dvd_two_pow_succ_of_single_odd_prime
      (b := 4) hq hrs (by norm_num at hR ⊢; exact hR)
        (by norm_num at hE ⊢; exact hE) with h32 | h32
  · have hpow : (5 : ZMod p) ^ 32 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rwa [hord5])
    have hzero : (23283064365386962890624 : ZMod p) = 0 := by
      norm_num at hpow ⊢
      linear_combination hpow
    have hdvdNat : p ∣ 23283064365386962890624 :=
      (CharP.cast_eq_zero_iff
        (ZMod p) p 23283064365386962890624).mp hzero
    have hdvd : p ∣ 5 ^ 32 - 1 := by
      norm_num
      exact hdvdNat
    rcases prime_dvd_five_pow_thirtytwo_sub_one_cases Fact.out hdvd with
        rfl | rfl | rfl | rfl | rfl | rfl | hp11489 | hp29423041
    · exact hp2 rfl
    · norm_num at hpSplit
    · norm_num at hpSplit
    · norm_num at hpSplit
    · norm_num at hpSplit
    · norm_num at hpSplit
    · subst p
      have h5eight : (5 : ZMod 11489) ^ 8 = -1 :=
        five_pow_eight_eq_neg_one_mod_11489
      have h5sixteen : (5 : ZMod 11489) ^ 16 = 1 :=
        five_pow_sixteen_eq_one_mod_11489
      have hordDiv16 : orderOf (5 : ZMod 11489) ∣ 16 :=
        orderOf_dvd_of_pow_eq_one h5sixteen
      have hordNotDiv8 : ¬orderOf (5 : ZMod 11489) ∣ 8 := by
        intro hdvd8
        have hone : (5 : ZMod 11489) ^ 8 = 1 :=
          orderOf_dvd_iff_pow_eq_one.mp hdvd8
        exact neg_one_ne_one_mod_11489 (h5eight.symm.trans hone)
      have hrDiv16 : 2 * r ∣ 16 := by
        simpa [hord5] using hordDiv16
      have hrNotDiv8 : ¬2 * r ∣ 8 := by
        simpa [hord5] using hordNotDiv8
      have hr8 : r = 8 := by
        have hrDivPow : 2 * r ∣ 2 ^ 4 := by
          norm_num
          exact hrDiv16
        obtain ⟨j, hjle, hj⟩ :=
          (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hrDivPow
        have hj4 : j = 4 := by
          by_contra hjne
          have hj3 : j ≤ 3 := by omega
          apply hrNotDiv8
          rw [hj, show 8 = 2 ^ 3 by norm_num]
          exact Nat.pow_dvd_pow 2 hj3
        rw [hj4] at hj
        norm_num at hj
        omega
      have hqEq : q ^ e = 359 := by
        obtain ⟨a, ha⟩ := hqPowOdd
        norm_num at hpform
        omega
      have hTwoS : Nat.Coprime 2 s := by
        apply hrs.coprime_dvd_left
        rw [hr8]
        norm_num
      have hsOdd : Odd s := Nat.coprime_two_left.mp hTwoS
      have hsDiv : s ∣ 16 * q ^ e := by
        obtain ⟨c, hc⟩ := hE
        refine ⟨c, ?_⟩
        have hc' : 2 * (16 * q ^ e) = 2 * (s * c) := by
          calc
            2 * (16 * q ^ e) = 32 * q ^ e := by ring
            _ = (2 * s) * c := hc
            _ = 2 * (s * c) := by ring
        exact Nat.mul_left_cancel (by norm_num) hc'
      have hsCoprime : Nat.Coprime s 16 := by
        simpa using (Nat.coprime_two_right.mpr hsOdd).pow_right 4
      have hsQ : s ∣ q ^ e :=
        hsCoprime.dvd_of_dvd_mul_left hsDiv
      have hs359 : s ∣ 359 := by rwa [hqEq] at hsQ
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 359)).mp hs359 with
          hsOne | hsEq
      · apply orderOf_golden_square_ne_two
          (p := 11489) (by norm_num) (by norm_num) x hx
        simpa [hsOne] using hordx
      · have honeOrder : x ^ (2 * s) = 1 := by
          rw [← hordx]
          exact pow_orderOf_eq_one x
        have hone : x ^ 718 = 1 := by
          simpa [hsEq] using honeOrder
        have hneg := golden_square_pow_718_eq_neg_one_mod_11489 x hx
        exact neg_one_ne_one_mod_11489 (hneg.symm.trans hone)
    · subst p
      obtain ⟨a, ha⟩ := hqPowOdd
      norm_num at hpform
      omega
  · have hpow : x ^ 32 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rwa [hordx])
    rcases prime_dvd_23725150497405_cases Fact.out
        (dvd_23725150497405_of_golden_square_pow_thirtytwo x hx hpow) with
        rfl | rfl | rfl | rfl | rfl
    · norm_num at hpSplit
    · exact hp5 rfl
    · norm_num at hpSplit
    · norm_num at hpSplit
    · norm_num at hpSplit

/-- End-to-end four-coefficient form of the depth-five exclusion.
@isnad1 id=false.14h7v.s8.0159fed45bb4 from=translated src=- shape=119e8656 vocab=334340c5
-/
theorem no_split_single_odd_support_thirtytwo_primitive
    {q e r s k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hpSplit : p % 5 = 1 ∨ p % 5 = 4)
    (hr : 0 < r) (hs : 0 < s) (hrs : Nat.Coprime r s)
    (hkpos : 1 ≤ k) (hpm : ¬p ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    (hpform : p - 1 = 32 * q ^ e) :
    False := by
  obtain ⟨hord5, hordx⟩ :=
    dvd_D_exact_scalar_profile hp5 hr hs hkpos hpm hsig γ hγ hD
  exact no_split_single_odd_support_thirtytwo
    hq hq2 hp2 hp5 hpSplit hrs hpform hord5
      (goldenSquareFromGamma γ)
      (goldenSquareFromGamma_sq_eq_three_mul_sub_one hp5 γ hγ)
      hordx

end AgrawalCore
