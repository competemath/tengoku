/-
  NiceNumbers.lean
  ================

  Ten theorems about nice / quasi-nice numbers, formalised in Lean 4, and one
  proposition about the shape of the candidate band.  They are numbered as in the
  article series *The middle digit wall*, which presents them in this order; the
  sections of this file follow the order they were proved in instead, so each
  entry below names its section.

  `n` is **(e1,e2)-nice in base b** when the base-`b` digits of `n^e1` and `n^e2`
  together are exactly {0,…,b-1}, each once.  `(2,3)` is the classical "nice
  number" problem, whose only known solution is 69 in base 10.

  Pandigitality has two immediate consequences, and both are formalised here as
  hypotheses so that Theorems 1 and 3 and the band's shape apply to *any* notion
  of solution satisfying them:

    * the digit-length identity   `numDigits b (n^e1) + numDigits b (n^e2) = b`
    * the digit-sum identity      `2 * (digitSum b (n^e1) + digitSum b (n^e2)) = b * (b-1)`

  Theorem 2 is about a digit *collision*, which neither consequence sees, so §5
  defines pandigitality outright (`Pandigital`, from a `digits` list built by
  repeated division) and proves it satisfiable at 69.

  **Theorem 1** (§1, §11; `no_nice_of_dvd`, `band_nonempty_iff`): if
  `(e1+e2) ∣ e1*(b-1)` — equivalently `b ≡ 1 mod (e1+e2)/gcd(e1,e2)` — the length
  identity is unsatisfiable.  Special cases: `b ≡ 1 mod 5` kills `(2,3)`,
  `b ≡ 1 mod 4` kills `(1,3)`, `b ≡ 1 mod 3` kills `(2,4)`.  Conversely, above an
  explicit threshold every other base has a candidate, so this is a classification
  rather than a filter.

  **The band's shape** (§3; `base_unique`, `bands_disjoint`, `band_convex`,
  `band_lengths_const`): the length identity holds for at most one base, so
  distinct bases' candidate bands are disjoint and each `n` is a candidate in at
  most one base; and within a base the band is one interval, with both digit
  lengths constant across it.  Proved for arbitrary values, hence for every
  exponent pair.  It rules nothing out, so it carries no number.

  **Theorem 2** (§5; `no_nice_of_universal_clash`, `clash_iff_dvd_clashMod`,
  `clash_prime_pow_iff`): if `x^e1 ≡ x^e2 (mod b)` for *every* `x` — a universal
  last-digit clash — then no `n` is pandigital in base `b`.  The bases where that
  happens are **exactly the divisors of one number** `N(e1,e2)`, computed here as
  a finite gcd (`N(1,3) = 6`, `N(2,4) = 12`, `N(3,7) = 120`, `N(2,3) = 2`); and
  `p^a ∣ N` iff `a ≤ e1` and every unit mod `p` has order dividing `e2-e1`, which
  is `λ(p^a) ∣ e2-e1` once the unit group's exponent is known.  Evaluating that
  exponent is the one step of Theorem 2 left unformalised.

  **Theorem 3** (§2; `no_nice_of_mod_four`): for *every* pair with `e1,e2 ≥ 1`, if
  `b ≡ 3 (mod 4)` the digit-sum identity is unsatisfiable.

  **Theorem 4** (§7; `residues_nonempty_iff`, `residues_empty_iff`,
  `residues_single_nonempty_iff`): the residue set `R_b = {ρ : ρ^e1+ρ^e2 ≡ T}` is
  **empty iff `a = 1`, or `a ≥ 3` with `e2-e1` even and `e1 ∤ a-1`**, where
  `a = v_2(b-1)`.  No odd prime divisor of `b-1` enters: modulo the odd part `T`
  vanishes and `ρ = 0` is a residue, so the whole classification is a valuation
  count at 2.  Theorem 3 is its `a = 1` case.  For a single exponent `n^e` the
  rule is `R_b ≠ ∅` iff `a = 0` or `e ∣ a-1`.

  **Theorem 5** (§6; `valOf_mod_wsum`, `sieve_sound`,
  `base_four_sieve_is_incomplete`, `sieve_complete`): how much a congruence sieve
  can know.  Modulo `b^j - 1` a
  pair of digit lists is worth only its `j` block totals, so no sieve sees more
  than those; the naive claim that the digit-sum congruence already captures
  everything is **false** (base 4 is a machine-checked counterexample); and under
  an explicit block-size hypothesis it is true, by an explicit construction of a
  pandigital pair for every permitted residue.

  **Theorem 6** (§9; `adm_of_pandigital`, `countP_pandigital_le_adm`,
  `countP_pandigital_le_window`, `admTop_of_pandigital`): the first
  *quantitative* result here — an upper bound on how many nice numbers a base can
  have, with no hypotheses beyond the base and a choice of depth `k`.  Every
  pandigital `n` lies in the crude band `b^(b-2) ≤ n^E < b^b` and passes a test
  `adm` depending on `n` only through `n mod (b-1)` and `n mod b^k`; `adm` has
  period `(b-1)·b^k`, so counting one window of that length bounds the whole band.
  Two witnesses: at base 10, `k = 4` leaves exactly one survivor and it is 69
  (`base_ten_nice_iff` — the set of `(2,3)`-nice numbers in base 10 is `{69}`), and
  at base 17 a 272-number window bounds a band 38 times longer (`≤ 585`).

  **Theorem 7** (§8; `greedy_distinct_slots`, `greedy_deficiency_le`): a
  *constructive* result rather than an impossibility.  With `gcd(e1e2, b) = 1`, a
  starting digit `ρ` and a unit `β` separating the two progressions, if
  `4(d-1) + 2 < b` then some `d`-digit `n` has `2d` pairwise-distinct low slots,
  hence combined digit deficiency at most `b - 2d`.  Since `d ≈ b/E` that is
  `b(1 - 2/E)`: the same `2/E` as the DFS prune, reached from the constructive side.

  **Theorems 8, 9 and 10** (§10; `infinitude_iff`, `model_diverges`,
  `conditional_infinitude`, `divergence_is_not_existence`): the infinitude
  question, cut into the half that is provable and the half that is not.
  Theorem 8: there are infinitely many nice numbers **iff** infinitely many bases
  host one, both directions from the crude band of §9.4.  Theorem 9: the
  *heuristic* count `|band|·b!/b^b` exceeds any `M` along an explicit infinite
  family of bases — band exhibited, not estimated, and no proved obstruction
  (Theorems 1-4) touches it.  Theorem 10: one named hypothesis, `ModelPositive`,
  closes the gap; nothing here proves it, and `divergence_is_not_existence` shows
  it cannot be weakened to "the heuristic is large" — the `(2,3)` bases `20s+7`
  have a divergent heuristic over a band Theorem 3 proves empty.

  Together these replace exhaustive machine checks over `e1 ≤ 8`, `e2 ≤ 9`,
  `b < 400` (Theorems 1, 3 and 4), `b < 500`, five pairs, ~2700 values of `n` (the
  band's shape), and `e1 ≤ 5`, `e2 ≤ 7`, `b < 200` (Theorem 2) with proofs valid
  for all bases, all exponent pairs and all `n`.

  Lean 4.16-4.33, core only.  No Mathlib, no `sorry`.  `#print axioms` at the end
  shows only the three standard foundational axioms.
-/


namespace Nice

/-! ## §0  Digits, from first principles

`numDigits` and `digitSum` are defined by the usual repeated division, so they
really are "how many digits does `x` print in base `b`" and "what do they add
up to".  Nothing else about digits is assumed anywhere below. -/

/-- Number of base-`b` digits of `x`; zero has none.-/
def numDigits (b x : Nat) : Nat :=
  if h : 1 < b ∧ 0 < x then numDigits b (x / b) + 1 else 0
decreasing_by exact Nat.div_lt_self h.2 h.1

/-- Sum of the base-`b` digits of `x`.-/
def digitSum (b x : Nat) : Nat :=
  if h : 1 < b ∧ 0 < x then x % b + digitSum b (x / b) else 0
decreasing_by exact Nat.div_lt_self h.2 h.1

/--
@isnad1 id=eq.0h1v.s4.152084e71979 from=translated src=- shape=1d838610 vocab=4aba56e8
-/
theorem numDigits_zero (b : Nat) : numDigits b 0 = 0 := by rw [numDigits]; simp

/--
@isnad1 id=eq.0h1v.s4.5a300d0216e8 from=translated src=- shape=1d838610 vocab=46644e62
-/
theorem digitSum_zero (b : Nat) : digitSum b 0 = 0 := by rw [digitSum]; simp

theorem eq_zero_of_numDigits_eq_zero {b x : Nat} (hb : 1 < b)
    (h : numDigits b x = 0) : x = 0 := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · exact h0
  · rw [numDigits, dite_eq_left ⟨hb, h0⟩] at h; omega

/--
@isnad1 id=lt.2h2v.s5.331ae7c31d1d from=translated src=- shape=6c67d60b vocab=6bce1123
-/
theorem numDigits_pos {b x : Nat} (hb : 1 < b) (hx : 0 < x) : 0 < numDigits b x := by
  rw [numDigits, dite_eq_left ⟨hb, hx⟩]; omega

/-- `numDigits b x = k+1` means exactly `b^k ≤ x < b^(k+1)`.
@isnad1 id=and.2h3v.s6.8b448fcb09f7 from=translated src=- shape=8cfc4530 vocab=850b17f7
-/
theorem bounds_of_numDigits {b : Nat} (hb : 1 < b) :
    ∀ x k, numDigits b x = k + 1 → b ^ k ≤ x ∧ x < b ^ (k + 1) := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro k hk
    have hx : 0 < x := by
      rcases Nat.eq_zero_or_pos x with rfl | h
      · rw [numDigits_zero] at hk; omega
      · exact h
    rw [numDigits, dite_eq_left ⟨hb, hx⟩] at hk
    have hkk : numDigits b (x / b) = k := by omega
    have hdm : b * (x / b) + x % b = x := Nat.div_add_mod x b
    have hmod : x % b < b := Nat.mod_lt _ (by omega)
    match k with
    | 0 =>
      have h0 : x / b = 0 := eq_zero_of_numDigits_eq_zero hb hkk
      rw [h0, Nat.mul_zero, Nat.zero_add] at hdm
      refine ⟨by rw [Nat.pow_zero]; omega, ?_⟩
      rw [Nat.pow_one]; omega
    | (j+1) =>
      have hlt : x / b < x := Nat.div_lt_self hx hb
      have hIH := ih (x / b) hlt j hkk
      refine ⟨?_, ?_⟩
      · calc b ^ (j+1) = b ^ j * b := rfl
          _ ≤ (x / b) * b := Nat.mul_le_mul_right b hIH.1
          _ ≤ x := Nat.div_mul_le_self x b
      · calc x < b * (x / b) + b := by omega
          _ = b * (x / b + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ b * b ^ (j+1) := Nat.mul_le_mul_left b (by omega)
          _ = b ^ (j+1+1) := (Nat.mul_comm b (b^(j+1))).trans (Nat.pow_succ b (j+1)).symm

/-- Casting out `b-1`s: the classical digit-sum congruence.
@isnad1 id=eq.1h2v.s5.33f2a557b19a from=translated src=- shape=7211bc27 vocab=cfaf6dba
-/
theorem digitSum_mod {b : Nat} (hb : 1 < b) : ∀ x, x % (b - 1) = digitSum b x % (b - 1) := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [digitSum_zero]
    · rw [digitSum, dite_eq_left ⟨hb, hx⟩]
      have hlt : x / b < x := Nat.div_lt_self hx hb
      have hIH : (x / b) % (b - 1) = digitSum b (x / b) % (b - 1) := ih (x / b) hlt
      have hdm : b * (x / b) + x % b = x := Nat.div_add_mod x b
      -- b * q = q + (b-1) * q, so b*q ≡ q  (mod b-1)
      have hsplit : b * (x / b) = (x / b) + (b - 1) * (x / b) := by
        have : b = 1 + (b - 1) := by omega
        calc b * (x / b) = (1 + (b - 1)) * (x / b) := by rw [← this]
          _ = (x / b) + (b - 1) * (x / b) := by rw [Nat.add_mul, Nat.one_mul]
      have key : ((x / b + x % b) + (b - 1) * (x / b)) % (b - 1) = (x / b + x % b) % (b - 1) :=
        Nat.add_mul_mod_self_left _ _ _
      have hxeq : (x / b + x % b) + (b - 1) * (x / b) = x := by omega
      rw [hxeq] at key
      rw [key, Nat.add_mod, hIH, ← Nat.add_mod, Nat.add_comm]

/-! ## §1  Theorem 1 — the length obstruction -/

/-- Core lacks the strict form of `pow_le_pow_left`.
@isnad1 id=lt.2h3v.s5.bfa8ac3175a9 from=translated src=- shape=c574f6f7 vocab=7ddce274
-/
theorem pow_lt_pow_left' {x y : Nat} (h : x < y) : ∀ k, k ≠ 0 → x ^ k < y ^ k := by
  intro k hk
  match k, hk with
  | (k+1), _ =>
    have hy : 0 < y ^ k := Nat.pow_pos (Nat.lt_of_le_of_lt (Nat.zero_le x) h)
    calc x ^ (k+1) = x ^ k * x := rfl
      _ < y ^ k * y := Nat.mul_lt_mul_of_le_of_lt (Nat.pow_le_pow_left (Nat.le_of_lt h) k) h hy
      _ = y ^ (k+1) := rfl

/-- Comparing `b^a ≤ n^e1` and `n^e2 < b^(c+1)` through the common value
`n^(e1e2)` pins `a·e2` strictly below `(c+1)·e1`.  Used both ways round, this
confines `(a,c)` to a window of width exactly `e1+e2` — the whole theorem.
@isnad1 id=lt.4h6v.s7.c4c308bdcaa6 from=translated src=- shape=4337d001 vocab=3f16b8dd
-/
theorem exp_lt {b e1 e2 n a c : Nat} (hb : 1 < b) (he1 : e1 ≠ 0)
    (ha : b ^ a ≤ n ^ e1) (hc' : n ^ e2 < b ^ (c + 1)) :
    a * e2 < (c + 1) * e1 := by
  have h1' : b ^ (a * e2) ≤ n ^ (e1 * e2) := by
    rw [Nat.pow_mul, Nat.pow_mul]; exact Nat.pow_le_pow_left ha e2
  have h2' : n ^ (e2 * e1) < b ^ ((c + 1) * e1) := by
    rw [Nat.pow_mul, Nat.pow_mul]; exact pow_lt_pow_left' hc' e1 he1
  rw [Nat.mul_comm e1 e2] at h1'
  exact (Nat.pow_lt_pow_iff_right hb).mp (Nat.lt_of_le_of_lt h1' h2')

/--
@isnad1 id=false.9h6v.s7.9e548b0b92cb from=translated src=- shape=9e0d493b vocab=2f6feaa2
-/
theorem no_candidate {b e1 e2 n a c : Nat}
    (hb : 1 < b) (he1 : e1 ≠ 0) (he2 : e2 ≠ 0)
    (ha : b ^ a ≤ n ^ e1) (ha' : n ^ e1 < b ^ (a + 1))
    (hc : b ^ c ≤ n ^ e2) (hc' : n ^ e2 < b ^ (c + 1))
    (hlen : (a + 1) + (c + 1) = b)
    (hdvd : (e1 + e2) ∣ e1 * (b - 1)) : False := by
  have h1 : a * e2 < (c + 1) * e1 := exp_lt hb he1 ha hc'
  have h2 : c * e1 < (a + 1) * e2 := exp_lt hb he2 hc ha'
  have h1' : a * e2 < c * e1 + e1 := by rw [Nat.succ_mul] at h1; exact h1
  have h2' : c * e1 < a * e2 + e2 := by rw [Nat.succ_mul] at h2; exact h2
  obtain ⟨k, hk⟩ := hdvd
  have hb1 : b - 1 = a + c + 1 := by omega
  rw [hb1] at hk
  have hA : e1 * (a + c + 1) = a * e1 + c * e1 + e1 := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm e1 a, Nat.mul_comm e1 c]
  have hB : (e1 + e2) * (a + 1) = a * e1 + a * e2 + (e1 + e2) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.mul_comm e1 a, Nat.mul_comm e2 a]
  have hC : (e1 + e2) * (k + 1) = (e1 + e2) * k + (e1 + e2) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hA] at hk
  have hlt1 : (e1 + e2) * k < (e1 + e2) * (a + 1) := by omega
  have hlt2 : (e1 + e2) * (a + 1) < (e1 + e2) * (k + 1) := by omega
  have hk1' : k < a + 1 := Nat.lt_of_mul_lt_mul_left hlt1
  have hk2' : a + 1 < k + 1 := Nat.lt_of_mul_lt_mul_left hlt2
  omega

/--
**Theorem 1.**  If `(e1+e2) ∣ e1*(b-1)` then no `n` has
`numDigits b (n^e1) + numDigits b (n^e2) = b`, so base `b` contains no
`(e1,e2)`-nice number.
@isnad1 id=ne.4h4v.s6.ef21b40f6b63 from=translated src=- shape=bbfca1ab vocab=6b751c31
-/
theorem no_nice_of_dvd {b e1 e2 n : Nat}
    (hb : 1 < b) (he1 : e1 ≠ 0) (he2 : e2 ≠ 0)
    (hdvd : (e1 + e2) ∣ e1 * (b - 1)) :
    numDigits b (n ^ e1) + numDigits b (n ^ e2) ≠ b := by
  intro hsum
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_pow (Nat.pos_of_ne_zero he1), Nat.zero_pow (Nat.pos_of_ne_zero he2),
        numDigits_zero] at hsum
    omega
  have hp1' : 0 < numDigits b (n ^ e1) := numDigits_pos hb (Nat.pow_pos hn)
  have hp2' : 0 < numDigits b (n ^ e2) := numDigits_pos hb (Nat.pow_pos hn)
  obtain ⟨a, hae⟩ : ∃ a, numDigits b (n ^ e1) = a + 1 := ⟨numDigits b (n ^ e1) - 1, by omega⟩
  obtain ⟨c, hce⟩ : ∃ c, numDigits b (n ^ e2) = c + 1 := ⟨numDigits b (n ^ e2) - 1, by omega⟩
  obtain ⟨ha, ha'⟩ := bounds_of_numDigits hb _ _ hae
  obtain ⟨hc, hc'⟩ := bounds_of_numDigits hb _ _ hce
  exact no_candidate hb he1 he2 ha ha' hc hc' (by omega) hdvd

/-! ### Named corollaries -/

/-- Square/cube ("nice") numbers: base `b ≡ 1 (mod 5)` is empty.
@isnad1 id=ne.2h2v.s6.30933c09cf5c from=translated src=- shape=ee2dc1a8 vocab=41efc7a8
-/
theorem nice_no_solution {b n : Nat} (hb : 1 < b) (hmod : b % 5 = 1) :
    numDigits b (n ^ 2) + numDigits b (n ^ 3) ≠ b := by
  refine no_nice_of_dvd (e1 := 2) (e2 := 3) hb (by decide) (by decide) ?_
  obtain ⟨t, ht⟩ : 5 ∣ (b - 1) := by omega
  exact ⟨2 * t, by omega⟩

/-- The `(1,3)` problem: base `b ≡ 1 (mod 4)` is empty.
@isnad1 id=ne.2h2v.s6.5392ab130c9c from=translated src=- shape=ee2dc1a8 vocab=41efc7a8
-/
theorem one_three_no_solution {b n : Nat} (hb : 1 < b) (hmod : b % 4 = 1) :
    numDigits b (n ^ 1) + numDigits b (n ^ 3) ≠ b := by
  refine no_nice_of_dvd (e1 := 1) (e2 := 3) hb (by decide) (by decide) ?_
  obtain ⟨t, ht⟩ : 4 ∣ (b - 1) := by omega
  exact ⟨t, by omega⟩

/-- The `(2,4)` problem: base `b ≡ 1 (mod 3)` is empty — a *third* of all bases.
    This is the `gcd(e1,e2) > 1` phenomenon, free from the divisibility form.
@isnad1 id=ne.2h2v.s6.a4af71ba4cc5 from=translated src=- shape=ee2dc1a8 vocab=41efc7a8
-/
theorem two_four_no_solution {b n : Nat} (hb : 1 < b) (hmod : b % 3 = 1) :
    numDigits b (n ^ 2) + numDigits b (n ^ 4) ≠ b := by
  refine no_nice_of_dvd (e1 := 2) (e2 := 4) hb (by decide) (by decide) ?_
  obtain ⟨t, ht⟩ : 3 ∣ (b - 1) := by omega
  exact ⟨t, by omega⟩

/-! ## §2  Theorem 3 — the parity obstruction, for every exponent pair -/

/--
@isnad1 id=eq.1h2v.s5.23b133671b10 from=translated src=- shape=00177818 vocab=df461349
-/
theorem pow_mod_two {n : Nat} : ∀ e, e ≠ 0 → n ^ e % 2 = n % 2 := by
  intro e he
  induction e with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [Nat.pow_one]
    · have hIH := ih (by omega)
      have : n ^ (j + 1) % 2 = (n ^ j % 2) * (n % 2) % 2 := by
        rw [Nat.pow_succ, Nat.mul_mod]
      rw [this, hIH]
      have h2' : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h2' with h | h <;> rw [h] <;> decide

/--
**Theorem 3.**  For every exponent pair with `e1, e2 ≥ 1`, base `b ≡ 3 (mod 4)`
contains no `(e1,e2)`-nice number: the digit-sum identity
`2·(digitSum(n^e1) + digitSum(n^e2)) = b(b-1)` is already unsatisfiable.
@isnad1 id=false.5h4v.s7.1dc56cafca25 from=translated src=- shape=e54f9c15 vocab=1a50f88f
-/
theorem no_nice_of_mod_four {b e1 e2 n : Nat}
    (hb : 1 < b) (he1 : e1 ≠ 0) (he2 : e2 ≠ 0) (hmod : b % 4 = 3)
    (hT : 2 * (digitSum b (n ^ e1) + digitSum b (n ^ e2)) = b * (b - 1)) : False := by
  have h2m : 2 ∣ (b - 1) := by omega
  -- the two powers are congruent to their digit sums mod b-1 ...
  have hd1' : n ^ e1 % (b-1) = digitSum b (n ^ e1) % (b-1) := digitSum_mod hb _
  have hd2' : n ^ e2 % (b-1) = digitSum b (n ^ e2) % (b-1) := digitSum_mod hb _
  -- ... hence mod 2, since 2 ∣ b-1
  have step : ∀ x y : Nat, x % (b-1) = y % (b-1) → x % 2 = y % 2 := by
    intro x y h
    rw [← Nat.mod_mod_of_dvd x h2m, ← Nat.mod_mod_of_dvd y h2m, h]
  have e1' : n ^ e1 % 2 = digitSum b (n ^ e1) % 2 := step _ _ hd1'
  have e2' : n ^ e2 % 2 = digitSum b (n ^ e2) % 2 := step _ _ hd2'
  -- left side: n^e ≡ n (mod 2) for any e ≥ 1, so the sum of the two is even
  rw [pow_mod_two e1 he1] at e1'
  rw [pow_mod_two e2 he2] at e2'
  have hsum_even : (digitSum b (n ^ e1) + digitSum b (n ^ e2)) % 2 = 0 := by
    have := Nat.add_mod (digitSum b (n ^ e1)) (digitSum b (n ^ e2)) 2
    rw [← e1', ← e2'] at this
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hn with h | h <;> rw [h] at this <;> omega
  -- right side: b odd and (b-1)/2 odd force the digit-sum total to be odd
  obtain ⟨S, hS⟩ : ∃ S, digitSum b (n ^ e1) + digitSum b (n ^ e2) = 2 * S := by
    exact ⟨(digitSum b (n ^ e1) + digitSum b (n ^ e2)) / 2, by omega⟩
  obtain ⟨u, hu⟩ : ∃ u, b - 1 = 2 * u := ⟨(b-1)/2, by omega⟩
  have hodd_u : u % 2 = 1 := by omega
  have hodd_b : b % 2 = 1 := by omega
  -- 4S = b*m = b*2*u  ⇒  2S = b*u, which is odd·odd = odd, contradicting 2 ∣ 2S
  have hmul : 2 * (2 * S) = b * (2 * u) := by rw [← hS, ← hu]; exact hT
  have hbu2 : b * (2 * u) = 2 * (b * u) := by
    rw [Nat.mul_comm b (2*u), Nat.mul_assoc, Nat.mul_comm u b]
  have h4 : 2 * S = b * u := by omega
  have hbu : (b * u) % 2 = 1 := by
    rw [Nat.mul_mod, hodd_b, hodd_u]
  omega

/--
**Theorem 3, residue-set form.**  The same parity obstruction stated the way the
sieve uses it: for `b ≡ 3 (mod 4)` the residue set
`R_b = {ρ : ρ^e1 + ρ^e2 ≡ T (mod b-1)}`, `2T = b(b-1)`, is **empty**.

`no_nice_of_mod_four` rules out an actual solution's digit sums; this rules out
the congruence class it would have to live in, which is the statement
an exhaustive check once covered over `e1 ≤ 8`, `e2 ≤ 9`, `b < 400`.
@isnad1 id=ne.5h5v.s7.e9b800fdd2e1 from=translated src=- shape=d8e223ca vocab=f572c56f
-/
theorem residues_empty_of_mod_four {b e1 e2 T ρ : Nat}
    (hb : 1 < b) (he1 : e1 ≠ 0) (he2 : e2 ≠ 0) (hmod : b % 4 = 3)
    (hT : 2 * T = b * (b - 1)) :
    (ρ ^ e1 + ρ ^ e2) % (b - 1) ≠ T % (b - 1) := by
  intro h
  have h2m : 2 ∣ (b - 1) := by omega
  have step : ∀ x y : Nat, x % (b-1) = y % (b-1) → x % 2 = y % 2 := by
    intro x y hxy
    rw [← Nat.mod_mod_of_dvd x h2m, ← Nat.mod_mod_of_dvd y h2m, hxy]
  have hpar : (ρ ^ e1 + ρ ^ e2) % 2 = T % 2 := step _ _ h
  -- ρ^e ≡ ρ (mod 2) for e ≥ 1, so the left side is ρ + ρ: even
  have hl : (ρ ^ e1 + ρ ^ e2) % 2 = 0 := by
    have h1' := pow_mod_two (n := ρ) e1 he1
    have h2' := pow_mod_two (n := ρ) e2 he2
    have hadd := Nat.add_mod (ρ ^ e1) (ρ ^ e2) 2
    rw [h1', h2'] at hadd
    have hn : ρ % 2 = 0 ∨ ρ % 2 = 1 := by omega
    rcases hn with hq | hq <;> rw [hq] at hadd <;> omega
  -- b odd and (b-1)/2 odd make T = b·(b-1)/2 odd
  obtain ⟨u, hu⟩ : ∃ u, b - 1 = 2 * u := ⟨(b-1)/2, by omega⟩
  have hodd_u : u % 2 = 1 := by omega
  have hodd_b : b % 2 = 1 := by omega
  have hbu2 : b * (2 * u) = 2 * (b * u) := by
    rw [Nat.mul_comm b (2*u), Nat.mul_assoc, Nat.mul_comm u b]
  rw [hu, hbu2] at hT
  have hTbu : T = b * u := by omega
  have hodd_T : (b * u) % 2 = 1 := by rw [Nat.mul_mod, hodd_b, hodd_u]
  omega

/-- Theorem 3's residue form firing: base 7 has no `(2,3)` residue at all
(`T = 21`, `2·21 = 7·6`).
@isnad1 id=ne.0h1v.s6.ad56dba82827 from=translated src=- shape=589029cd vocab=b2ffaa0b
-/
theorem base_seven_no_residue (ρ : Nat) : (ρ ^ 2 + ρ ^ 3) % 6 ≠ 21 % 6 :=
  residues_empty_of_mod_four (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-! ## §3  The band's shape — one base per `n`, and the bands are disjoint

The candidate band of base `b` is `{n : numDigits b (n^e1) + numDigits b (n^e2) = b}`.
Distinct bases have **disjoint** bands, so each `n` is a candidate in at most one
base and "search more bases" and "search more numbers" are the same axis.

The proof needs nothing about exponents at all: `numDigits b x` is *antitone* in
`b`, so `numDigits b x + numDigits b y - b` is strictly decreasing in `b` and can
vanish once.  What is formalised is therefore the general two-value statement,
with the exponent form as a corollary. -/

/-- `b^k ≤ x` forces `x` to have at least `k+1` digits — the converse direction
of `bounds_of_numDigits`, and all that antitonicity needs.
@isnad1 id=le.2h3v.s5.db49011a11ad from=translated src=- shape=a465ce2c vocab=850b17f7
-/
theorem le_numDigits_of_pow_le {b x k : Nat} (hb : 1 < b) (h : b ^ k ≤ x) :
    k + 1 ≤ numDigits b x := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.pow_pos (a := b) (n := k) (by omega)) h
  obtain ⟨j, hj⟩ : ∃ j, numDigits b x = j + 1 :=
    ⟨numDigits b x - 1, by have := numDigits_pos hb hx; omega⟩
  obtain ⟨-, g2⟩ := bounds_of_numDigits hb x j hj
  have hpow : b ^ k < b ^ (j + 1) := Nat.lt_of_le_of_lt h g2
  have := (Nat.pow_lt_pow_iff_right hb).mp hpow
  omega

/-- A bigger base never needs more digits.
@isnad1 id=le.2h3v.s4.1780265db26a from=translated src=- shape=e76e0b44 vocab=dab38113
-/
theorem numDigits_antitone {b b' : Nat} (hb : 1 < b) (hbb : b ≤ b') (x : Nat) :
    numDigits b' x ≤ numDigits b x := by
  rcases Nat.eq_zero_or_pos (numDigits b' x) with h | h
  · omega
  obtain ⟨k, hk⟩ : ∃ k, numDigits b' x = k + 1 := ⟨numDigits b' x - 1, by omega⟩
  have hb' : 1 < b' := by omega
  obtain ⟨g1, -⟩ := bounds_of_numDigits hb' x k hk
  have hle : b ^ k ≤ x := Nat.le_trans (Nat.pow_le_pow_left hbb k) g1
  rw [hk]
  exact le_numDigits_of_pow_le hb hle

/--
**One base per value.**  For any two values `x, y`, at most one base `b` satisfies the
length identity `numDigits b x + numDigits b y = b`.
@isnad1 id=eq.4h4v.s6.b43ec02f109e from=translated src=- shape=df564095 vocab=db2b533d
-/
theorem base_unique {b b' x y : Nat} (hb : 1 < b) (hb' : 1 < b')
    (h : numDigits b x + numDigits b y = b)
    (h' : numDigits b' x + numDigits b' y = b') : b = b' := by
  rcases Nat.lt_trichotomy b b' with hlt | heq | hgt
  · have h1' := numDigits_antitone hb (Nat.le_of_lt hlt) x
    have h2' := numDigits_antitone hb (Nat.le_of_lt hlt) y
    omega
  · exact heq
  · have h1' := numDigits_antitone hb' (Nat.le_of_lt hgt) x
    have h2' := numDigits_antitone hb' (Nat.le_of_lt hgt) y
    omega

/-- `n` lies in the base-`b` candidate band for the pair `(e1,e2)`.-/
def InBand (b e1 e2 n : Nat) : Prop :=
  numDigits b (n ^ e1) + numDigits b (n ^ e2) = b

/-- **The bands are disjoint.**  The bands of two distinct bases are disjoint: no `n`
is a candidate in both.  Holds for every exponent pair, `n` included `0`.
@isnad1 id=not.3h5v.s5.93766b777ad2 from=translated src=- shape=e4ca6fdb vocab=62854c8f
-/
theorem bands_disjoint {b b' e1 e2 n : Nat} (hb : 1 < b) (hb' : 1 < b')
    (hne : b ≠ b') : ¬(InBand b e1 e2 n ∧ InBand b' e1 e2 n) := by
  rintro ⟨h, h'⟩
  exact hne (base_unique hb hb' h h')

/-- A bigger number never has fewer digits — the same move as `numDigits_antitone`,
in the other variable.
@isnad1 id=le.2h3v.s4.98fab56b638b from=translated src=- shape=53b07e13 vocab=dab38113
-/
theorem numDigits_mono {b x y : Nat} (hb : 1 < b) (hxy : x ≤ y) :
    numDigits b x ≤ numDigits b y := by
  rcases Nat.eq_zero_or_pos (numDigits b x) with h | h
  · omega
  obtain ⟨k, hk⟩ : ∃ k, numDigits b x = k + 1 := ⟨numDigits b x - 1, by omega⟩
  obtain ⟨g1, -⟩ := bounds_of_numDigits hb x k hk
  rw [hk]
  exact le_numDigits_of_pow_le hb (Nat.le_trans g1 hxy)

/-- **The band's shape, part 1: one digit split.**  Across a base's band both
lengths are individually constant — two non-decreasing quantities with a fixed
sum cannot move — so a base has exactly one split `L1 + L2 = b`, or no band.
@isnad1 id=and.4h5v.s6.97cf22ea2045 from=translated src=- shape=8d5cefbd vocab=7338f5d2
-/
theorem band_lengths_const {b e1 e2 n n' : Nat} (hb : 1 < b) (hle : n ≤ n')
    (h : InBand b e1 e2 n) (h' : InBand b e1 e2 n') :
    numDigits b (n ^ e1) = numDigits b (n' ^ e1) ∧
    numDigits b (n ^ e2) = numDigits b (n' ^ e2) := by
  have m1 := numDigits_mono hb (Nat.pow_le_pow_left hle e1)
  have m2 := numDigits_mono hb (Nat.pow_le_pow_left hle e2)
  unfold InBand at h h'
  omega

/-- **The band's shape, part 2: no holes.**  Anything between two band members is
a band member, so the band is a single unbroken interval of `n`.
@isnad1 id=inband.5h6v.s5.b83ee476cf6d from=translated src=- shape=3ff5d232 vocab=6f3998eb
-/
theorem band_convex {b e1 e2 lo n hi : Nat} (hb : 1 < b) (h1 : lo ≤ n) (h2 : n ≤ hi)
    (hlo : InBand b e1 e2 lo) (hhi : InBand b e1 e2 hi) : InBand b e1 e2 n := by
  have a1 := numDigits_mono hb (Nat.pow_le_pow_left h1 e1)
  have a2 := numDigits_mono hb (Nat.pow_le_pow_left h1 e2)
  have c1 := numDigits_mono hb (Nat.pow_le_pow_left h2 e1)
  have c2 := numDigits_mono hb (Nat.pow_le_pow_left h2 e2)
  unfold InBand at hlo hhi ⊢
  omega

/-! ## §4  Non-vacuity

An impossibility theorem is worthless if its hypotheses are secretly
contradictory.  They are not: **69 in base 10** satisfies both of them, and it
is the only known (2,3)-nice number.  Everything below is kernel-checked. -/

/-- Converse of `bounds_of_numDigits`, so non-vacuity reduces to arithmetic on
numerals that `decide` can do.
@isnad1 id=eq.3h3v.s6.c71c4f58cc92 from=translated src=- shape=f4498c2f vocab=850b17f7
-/
theorem numDigits_eq_of_bounds {b x k : Nat} (hb : 1 < b)
    (h1' : b ^ k ≤ x) (h2' : x < b ^ (k + 1)) : numDigits b x = k + 1 := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.pow_pos (a := b) (n := k) (by omega)) h1'
  obtain ⟨j, hj⟩ : ∃ j, numDigits b x = j + 1 :=
    ⟨numDigits b x - 1, by have := numDigits_pos hb hx; omega⟩
  obtain ⟨g1, g2⟩ := bounds_of_numDigits hb x j hj
  have : j = k := by
    rcases Nat.lt_trichotomy j k with h | h | h
    · have : b ^ (j + 1) ≤ b ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · exact h
    · have : b ^ (k + 1) ≤ b ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      omega
  omega

/-- One unfolding of `digitSum`.
@isnad1 id=eq.2h2v.s5.ca7fb69e6393 from=translated src=- shape=41a6fdc7 vocab=13261a74
-/
theorem digitSum_step {b x : Nat} (hb : 1 < b) (hx : 0 < x) :
    digitSum b x = x % b + digitSum b (x / b) := by
  rw [digitSum, dite_eq_left ⟨hb, hx⟩]

/-- 69^2 = 4761 has 4 base-10 digits.
@isnad1 id=eq.0h0v.s5.f9e1903744f4 from=translated src=- shape=50862e3b vocab=8ef9df92
-/
theorem nd_sq : numDigits 10 (69 ^ 2) = 4 := numDigits_eq_of_bounds (by decide) (by decide) (by decide)

/-- 69^3 = 328509 has 6 base-10 digits.
@isnad1 id=eq.0h0v.s5.b0140fd90fb0 from=translated src=- shape=50862e3b vocab=8ef9df92
-/
theorem nd_cb : numDigits 10 (69 ^ 3) = 6 := numDigits_eq_of_bounds (by decide) (by decide) (by decide)

/-- The length identity really is satisfiable: 4 + 6 = 10.
@isnad1 id=eq.0h0v.s6.7b01568c0e5a from=translated src=- shape=a75ab5c9 vocab=a7b2f459
-/
theorem length_identity_holds : numDigits 10 (69 ^ 2) + numDigits 10 (69 ^ 3) = 10 := by
  rw [nd_sq, nd_cb]

/--
@isnad1 id=eq.0h0v.s5.9bcc9d8fa76f from=translated src=- shape=50862e3b vocab=70120bfa
-/
theorem ds_sq : digitSum 10 (69 ^ 2) = 18 := by
  show digitSum 10 4761 = 18
  rw [digitSum_step (by decide) (by decide), digitSum_step (by decide) (by decide),
      digitSum_step (by decide) (by decide), digitSum_step (by decide) (by decide),
      digitSum_zero]

/--
@isnad1 id=eq.0h0v.s5.0c2f5fdcbb68 from=translated src=- shape=50862e3b vocab=70120bfa
-/
theorem ds_cb : digitSum 10 (69 ^ 3) = 27 := by
  show digitSum 10 328509 = 27
  rw [digitSum_step (by decide) (by decide), digitSum_step (by decide) (by decide),
      digitSum_step (by decide) (by decide), digitSum_step (by decide) (by decide),
      digitSum_step (by decide) (by decide), digitSum_step (by decide) (by decide),
      digitSum_zero]

/-- The digit-sum identity really is satisfiable: 18 + 27 = 45 = 10·9/2.
@isnad1 id=eq.0h0v.s6.7954894b4db5 from=translated src=- shape=e9d0443f vocab=eb087b00
-/
theorem digitsum_identity_holds :
    2 * (digitSum 10 (69 ^ 2) + digitSum 10 (69 ^ 3)) = 10 * (10 - 1) := by
  rw [ds_sq, ds_cb]

/-- Theorem 1 firing: base 11 ≡ 1 (mod 5) admits no square/cube candidate.
@isnad1 id=ne.0h1v.s5.d878aba446c9 from=translated src=- shape=6f546437 vocab=a7b2f459
-/
theorem base_eleven_dead (n : Nat) : numDigits 11 (n ^ 2) + numDigits 11 (n ^ 3) ≠ 11 :=
  nice_no_solution (by decide) (by decide)

/-- Theorem 3 firing where Theorem 1 says nothing: 7 ≢ 1 (mod 5), but 7 ≡ 3
(mod 4), so the digit-sum identity is already impossible in base 7.
@isnad1 id=ne.0h1v.s6.df91d4a8217c from=translated src=- shape=be881c80 vocab=eb087b00
-/
theorem base_seven_dead (n : Nat) :
    2 * (digitSum 7 (n ^ 2) + digitSum 7 (n ^ 3)) ≠ 7 * (7 - 1) :=
  fun h => no_nice_of_mod_four (by decide) (by decide) (by decide) (by decide) h

/-- `base_unique` needs a witness too, or "at most one base" could mean "no base": 69 is
in the base-10 `(2,3)` band.
@isnad1 id=inband.0h0v.s4.2eb18d85b8cf from=translated src=- shape=147f988f vocab=7d977a64
-/
theorem sixtynine_in_band : InBand 10 2 3 69 := length_identity_holds

/-- `base_unique` firing on that witness: base 10 is the *only* base 69 is a candidate
in — no finite search, and no appeal to the exponents being `(2,3)`.
@isnad1 id=eq.2h1v.s5.24d18a973212 from=translated src=- shape=e4ee31a4 vocab=62854c8f
-/
theorem sixtynine_only_base_ten {b : Nat} (hb : 1 < b) (h : InBand b 2 3 69) : b = 10 :=
  base_unique hb (by decide) h sixtynine_in_band

/-- Theorem 3 is genuinely pair-independent: same base, exponents (3,8).
@isnad1 id=ne.0h1v.s6.2e1b6c9bd0ba from=translated src=- shape=be881c80 vocab=eb087b00
-/
theorem base_seven_dead' (n : Nat) :
    2 * (digitSum 7 (n ^ 3) + digitSum 7 (n ^ 8)) ≠ 7 * (7 - 1) :=
  fun h => no_nice_of_mod_four (by decide) (by decide) (by decide) (by decide) h

/-! ## §5  Theorem 2 — the universal last-digit clash

If `x^e1 ≡ x^e2 (mod b)` for *every* `x` then the last base-`b` digits of `n^e1`
and `n^e2` coincide for every `n`, one digit value is used twice, and base `b` is
dead for reasons that have nothing to do with the size of the band.  Theorem 2
classifies the bases where that happens.

Two halves, and only the first needs pandigitality:

* `no_nice_of_universal_clash` — a clashing base contains no pandigital `n`.
* `clash_iff_dvd_clashMod` — the clashing bases for a pair are **exactly the
  divisors of one number** `N(e1,e2)`, computed here as a finite gcd.
* `clash_prime_pow_iff` — and the prime powers dividing `N` are exactly those
  with `a ≤ e1` whose unit group has exponent dividing `e2-e1`.  Evaluating that
  exponent is the classical `λ(p^a)`, the one step left to Mathlib.

This is also the first section that needs pandigitality itself rather than one of
its consequences, so §5.0 defines it. -/

/-! ### §5.0  Pandigitality, from the digits up -/

/-- The base-`b` digits of `x`, least significant first.-/
def digits (b x : Nat) : List Nat :=
  if h : 1 < b ∧ 0 < x then x % b :: digits b (x / b) else []
decreasing_by exact Nat.div_lt_self h.2 h.1

/--
@isnad1 id=eq.0h1v.s3.0ca870f7fa2d from=translated src=- shape=45d350c2 vocab=54361ee8
-/
theorem digits_zero (b : Nat) : digits b 0 = [] := by rw [digits]; simp

/--
@isnad1 id=eq.2h2v.s5.36054351ddd9 from=translated src=- shape=f71e833b vocab=1e1797d9
-/
theorem digits_step {b x : Nat} (hb : 1 < b) (hx : 0 < x) :
    digits b x = x % b :: digits b (x / b) := by rw [digits, dite_eq_left ⟨hb, hx⟩]

/-- Occurrences of `v` in `l`.  Core's `List.count` would do; this keeps the
section self-contained and reduces in the kernel.-/
def occ (v : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => (if a = v then 1 else 0) + occ v l

/--
@isnad1 id=eq.0h2v.s4.0b8dce10fe40 from=translated src=- shape=fa06886e vocab=792f4c61
-/
theorem occ_cons_self (v : Nat) (l : List Nat) : occ v (v :: l) = 1 + occ v l := by
  show (if v = v then 1 else 0) + occ v l = 1 + occ v l
  rw [ite_eq_left rfl]

/--
@isnad1 id=eq.0h3v.s5.07494d958c46 from=translated src=- shape=d76f1390 vocab=6b950f29
-/
theorem occ_append (v : Nat) : ∀ l1 l2 : List Nat,
    occ v (l1 ++ l2) = occ v l1 + occ v l2 := by
  intro l1
  induction l1 with
  | nil => intro l2; show occ v l2 = 0 + occ v l2; omega
  | cons a t ih =>
    intro l2
    show (if a = v then 1 else 0) + occ v (t ++ l2)
        = ((if a = v then 1 else 0) + occ v t) + occ v l2
    rw [ih]
    omega

/-- `n` is **`(e1,e2)`-pandigital in base `b`**: the base-`b` digits of `n^e1`
and of `n^e2`, taken together, contain every value `< b` exactly once.  This is
the definition an exhaustive search tests for; §1-§3 above use only its two
numerical consequences.-/
def Pandigital (b e1 e2 n : Nat) : Prop :=
  ∀ v, v < b → occ v (digits b (n ^ e1) ++ digits b (n ^ e2)) = 1

/-! ### §5.1  A universal clash kills the base -/

/-- Base `b` has a **universal clash** for `(e1,e2)` when the last digits of
`x^e1` and `x^e2` agree for every `x`.-/
def UniversalClash (b e1 e2 : Nat) : Prop := ∀ x, x ^ e1 % b = x ^ e2 % b

/-- A pandigital `n` is positive: `0` supplies no digit `0` in any base.
@isnad1 id=lt.2h4v.s5.61c1575e51e7 from=translated src=- shape=ba2d70e5 vocab=71524155
-/
theorem pos_of_pandigital {b e1 e2 n : Nat} (hb : 1 < b)
    (hp : Pandigital b e1 e2 n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · exfalso
    have key : ∀ e : Nat, occ 0 (digits b ((0 : Nat) ^ e)) = 0 := by
      intro e
      rcases Nat.eq_zero_or_pos e with rfl | he
      · rw [Nat.pow_zero, digits_step hb Nat.one_pos, Nat.mod_eq_of_lt hb,
            Nat.div_eq_of_lt hb, digits_zero]
        decide
      · rw [Nat.zero_pow he, digits_zero]
        rfl
    have h0 := hp 0 (by omega)
    rw [occ_append, key, key] at h0
    omega
  · exact h

/--
**Theorem 2, the operative half.**  A base with a universal clash contains no
pandigital `n` at all — the last digits of `n^e1` and `n^e2` are the same value,
so that value is used twice.  Every exponent pair, every `n`, no search.
@isnad1 id=not.2h4v.s4.6f1e104253e0 from=translated src=- shape=96429708 vocab=17e448d0
-/
theorem no_nice_of_universal_clash {b e1 e2 n : Nat} (hb : 1 < b)
    (hclash : UniversalClash b e1 e2) : ¬ Pandigital b e1 e2 n := by
  intro hp
  have hn : 0 < n := pos_of_pandigital hb hp
  have h1' : digits b (n ^ e1) = n ^ e1 % b :: digits b (n ^ e1 / b) :=
    digits_step hb (Nat.pow_pos hn)
  have h2' : digits b (n ^ e2) = n ^ e2 % b :: digits b (n ^ e2 / b) :=
    digits_step hb (Nat.pow_pos hn)
  have hcount := hp (n ^ e1 % b) (Nat.mod_lt _ (by omega))
  rw [occ_append, h1', h2', ← hclash n, occ_cons_self, occ_cons_self] at hcount
  omega

/-! ### §5.2  The classification: the clashing bases are the divisors of one number -/

/-- `gcd_{x < m} (x^e2 - x^e1)`.-/
def clashGcd (e1 e2 : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => Nat.gcd (m ^ e2 - m ^ e1) (clashGcd e1 e2 m)

/--
@isnad1 id=eq.0h3v.s5.d5c8bf95ccfb from=translated src=- shape=1db7df50 vocab=72f51aa9
-/
theorem clashGcd_succ (e1 e2 m : Nat) :
    clashGcd e1 e2 (m + 1) = Nat.gcd (m ^ e2 - m ^ e1) (clashGcd e1 e2 m) := rfl

/-- `N(e1,e2)` — the modulus of Theorem 2.  The range stops at `2^e2 - 2^e1`
because the `x = 2` term already bounds every clashing base by it.-/
def clashMod (e1 e2 : Nat) : Nat := clashGcd e1 e2 (2 ^ e2 - 2 ^ e1 + 1)

/-- `x^e1 ≤ x^e2` for `1 ≤ e1 ≤ e2`, `x = 0` included.
@isnad1 id=le.2h3v.s5.87c73b86708e from=translated src=- shape=44559af5 vocab=74f5fafa
-/
theorem pow_le_pow_exp {x e1 e2 : Nat} (he1 : 1 ≤ e1) (he : e1 ≤ e2) :
    x ^ e1 ≤ x ^ e2 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · have h1' : (0 : Nat) ^ e1 = 0 := Nat.zero_pow (by omega)
    have h2' : (0 : Nat) ^ e2 = 0 := Nat.zero_pow (by omega)
    omega
  · exact Nat.pow_le_pow_right hx he

/-- Congruence as divisibility of the (truncated) difference.
@isnad1 id=iff.2h3v.s5.2114fbc1ea04 from=translated src=- shape=c88eaafe vocab=473cfa50
-/
theorem dvd_sub_iff_mod_eq {b x y : Nat} (hb : 0 < b) (hyx : y ≤ x) :
    b ∣ x - y ↔ x % b = y % b := by
  constructor
  · rintro ⟨k, hk⟩
    have hx : x = y + b * k := by omega
    rw [hx, Nat.add_mul_mod_self_left]
  · intro h
    have hdx : b * (x / b) + x % b = x := Nat.div_add_mod x b
    have hdy : b * (y / b) + y % b = y := Nat.div_add_mod y b
    have hq : y / b ≤ x / b := Nat.div_le_div_right hyx
    obtain ⟨t, ht⟩ : ∃ t, x / b = y / b + t := ⟨x / b - y / b, by omega⟩
    have hmul : b * (y / b + t) = b * (y / b) + b * t := Nat.mul_add b _ _
    rw [ht] at hdx
    exact ⟨t, by omega⟩

/--
@isnad1 id=iff.3h3v.s6.75f6928ad075 from=translated src=- shape=dac012e9 vocab=61d73516
-/
theorem clash_iff_dvd_sub {b e1 e2 : Nat} (hb : 0 < b) (he1 : 1 ≤ e1) (he : e1 ≤ e2) :
    UniversalClash b e1 e2 ↔ ∀ x, b ∣ x ^ e2 - x ^ e1 := by
  constructor
  · intro h x
    exact (dvd_sub_iff_mod_eq hb (pow_le_pow_exp he1 he)).mpr (h x).symm
  · intro h x
    exact ((dvd_sub_iff_mod_eq hb (pow_le_pow_exp he1 he)).mp (h x)).symm

/--
@isnad1 id=iff.0h4v.s5.b22419659761 from=translated src=- shape=ad347efa vocab=16da91eb
-/
theorem dvd_clashGcd_iff {b e1 e2 : Nat} :
    ∀ m, b ∣ clashGcd e1 e2 m ↔ ∀ x, x < m → b ∣ x ^ e2 - x ^ e1 := by
  intro m
  induction m with
  | zero =>
    exact ⟨fun _ x hx => absurd hx (Nat.not_lt_zero x), fun _ => Nat.dvd_zero b⟩
  | succ m ih =>
    rw [clashGcd_succ]
    constructor
    · intro h x hx
      rcases Nat.lt_or_ge x m with hlt | hge
      · exact (ih.mp (Nat.dvd_trans h (Nat.gcd_dvd_right _ _))) x hlt
      · have hxm : x = m := by omega
        subst hxm
        exact Nat.dvd_trans h (Nat.gcd_dvd_left _ _)
    · intro h
      exact Nat.dvd_gcd (h m (by omega)) (ih.mpr (fun x hx => h x (by omega)))

/--
**Theorem 2 (classification).**  For `1 ≤ e1 < e2` and any `b > 0`, base `b` has
a universal clash **iff** `b ∣ N(e1,e2)`.  So the clashing bases of a pair are
exactly the divisors of a single computable number — divisor-closed, closed under
lcm, and bounded, all at once.
@isnad1 id=iff.3h3v.s5.e083e9cd2f6f from=translated src=- shape=f12fbd84 vocab=2b5b6d8d
-/
theorem clash_iff_dvd_clashMod {b e1 e2 : Nat} (hb : 0 < b) (he1 : 1 ≤ e1) (he : e1 < e2) :
    UniversalClash b e1 e2 ↔ b ∣ clashMod e1 e2 := by
  -- the x = 2 term is at least 2, so it is inside the range and bounds b
  have hp1' : 2 ^ (e1 + 1) ≤ 2 ^ e2 := Nat.pow_le_pow_right (by omega) (by omega)
  have hp2' : 2 ^ 1 ≤ 2 ^ e1 := Nat.pow_le_pow_right (by omega) he1
  have hp3 : 2 ^ (e1 + 1) = 2 ^ e1 * 2 := Nat.pow_succ 2 e1
  have hp4 : (2 : Nat) ^ 1 = 2 := Nat.pow_one 2
  have hK : 2 ≤ 2 ^ e2 - 2 ^ e1 := by omega
  constructor
  · intro h
    exact (dvd_clashGcd_iff _).mpr
      (fun x _ => (clash_iff_dvd_sub hb he1 (Nat.le_of_lt he)).mp h x)
  · intro h x
    have hall := (dvd_clashGcd_iff _).mp h
    have hble : b ≤ 2 ^ e2 - 2 ^ e1 := Nat.le_of_dvd (by omega) (hall 2 (by omega))
    have hmod := (dvd_sub_iff_mod_eq hb (pow_le_pow_exp he1 (Nat.le_of_lt he))).mp
      (hall (x % b) (by have := Nat.mod_lt x hb; omega))
    rw [Nat.pow_mod x e1 b, Nat.pow_mod x e2 b]
    exact hmod.symm

/-- Divisor-closure, the half of the structure that is obvious.
@isnad1 id=universa.2h4v.s4.e2042f08445b from=translated src=- shape=f56d14f5 vocab=8a0d33f3
-/
theorem clash_of_dvd {b b' e1 e2 : Nat} (hbb : b ∣ b') (h : UniversalClash b' e1 e2) :
    UniversalClash b e1 e2 := by
  intro x
  have h1' : x ^ e1 % b' % b = x ^ e2 % b' % b := by rw [h x]
  rwa [Nat.mod_mod_of_dvd _ hbb, Nat.mod_mod_of_dvd _ hbb] at h1'

/-- Closure under lcm, which is what makes "divisors of one number" possible.
@isnad1 id=universa.6h4v.s5.2e488c1bdf4a from=translated src=- shape=11c6ab49 vocab=ceedea73
-/
theorem clash_lcm {b b' e1 e2 : Nat} (hb : 0 < b) (hb' : 0 < b') (he1 : 1 ≤ e1) (he : e1 < e2)
    (h : UniversalClash b e1 e2) (h' : UniversalClash b' e1 e2) :
    UniversalClash (Nat.lcm b b') e1 e2 := by
  have hd := (clash_iff_dvd_clashMod hb he1 he).mp h
  have hd' := (clash_iff_dvd_clashMod hb' he1 he).mp h'
  exact (clash_iff_dvd_clashMod (Nat.lcm_pos hb hb') he1 he).mpr (Nat.lcm_dvd hd hd')

/-! ### §5.3  Which prime powers divide `N`

The local criterion, stated without Carmichael's `λ`: the unit condition is
"every unit has order dividing `e2-e1`", which is what `λ(p^a) ∣ e2-e1` says
once the unit group's exponent is known.  That evaluation is the classical
structure theorem for `(ℤ/p^aℤ)ˣ` and is the only part of Theorem 2 left
unformalised. -/

/-- Core has no `Nat.Prime`, and only one consequence of primality is used.-/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ k, k ∣ p → k = 1 ∨ k = p

/--
@isnad1 id=coprime.2h2v.s4.e24627e6d68c from=translated src=- shape=8e5dcdd3 vocab=30a741b1
-/
theorem coprime_of_not_dvd {p u : Nat} (hp : IsPrime p) (h : ¬ p ∣ u) :
    Nat.Coprime p u := by
  rcases hp.2 (Nat.gcd p u) (Nat.gcd_dvd_left p u) with h1' | h1'
  · exact h1'
  · exact absurd (by rw [← h1']; exact Nat.gcd_dvd_right p u) h

/-- Primality of a numeral: a divisor of `p` is at most `p`, so the unbounded
quantifier in `IsPrime` becomes a bounded one that `decide` can do.
@isnad1 id=isprime.2h1v.s5.e45cfc696b1d from=translated src=- shape=d19a15bd vocab=a275a289
-/
theorem isPrime_of_bounded {p : Nat} (hp : 2 ≤ p)
    (h : ∀ k, k < p + 1 → k ∣ p → k = 1 ∨ k = p) : IsPrime p :=
  ⟨hp, fun k hk => h k (by have := Nat.le_of_dvd (show 0 < p by omega) hk; omega) hk⟩

/--
@isnad1 id=isprime.0h0v.s2.ec4d231a1ef1 from=translated src=- shape=e590c3e1 vocab=39fe27f3
-/
theorem isPrime_two : IsPrime 2 := isPrime_of_bounded (by decide) (by decide)

/--
@isnad1 id=isprime.0h0v.s2.be8761c2c6be from=translated src=- shape=e590c3e1 vocab=39fe27f3
-/
theorem isPrime_three : IsPrime 3 := isPrime_of_bounded (by decide) (by decide)

/--
@isnad1 id=dvd.1h3v.s5.9608029bb829 from=translated src=- shape=8e01055e vocab=059ded25
-/
theorem pow_dvd_pow_of_dvd {a b : Nat} (h : a ∣ b) (n : Nat) : a ^ n ∣ b ^ n := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k ^ n, Nat.mul_pow a k n⟩

/--
**Theorem 2 (local criterion).**  For a prime power `p^a` with `a ≥ 1` and
`1 ≤ e1 < e2`, the universal clash holds mod `p^a` **iff** `a ≤ e1` and every
unit mod `p` satisfies `u^(e2-e1) ≡ 1 (mod p^a)`.

The `x = p` half of the proof forces `a ≤ e1`; the unit half forces the exponent
condition; and the two together suffice, by the dichotomy `p ∣ x` or not.
@isnad1 id=iff.4h4v.s6.a5ad209d4367 from=translated src=- shape=7c4e0721 vocab=8d7df736
-/
theorem clash_prime_pow_iff {p a e1 e2 : Nat} (hp : IsPrime p) (ha : 1 ≤ a)
    (he1 : 1 ≤ e1) (he : e1 < e2) :
    UniversalClash (p ^ a) e1 e2 ↔
      (a ≤ e1 ∧ ∀ u, ¬ p ∣ u → u ^ (e2 - e1) % p ^ a = 1) := by
  have hp2' : 2 ≤ p := hp.1
  have hm1' : p ^ 1 ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha
  have hm : 1 < p ^ a := by rw [Nat.pow_one] at hm1'; omega
  have hmpos : 0 < p ^ a := by omega
  have hfac : ∀ x : Nat, x ^ e1 * (x ^ (e2 - e1) - 1) = x ^ e2 - x ^ e1 := by
    intro x
    have hsum : e1 + (e2 - e1) = e2 := by omega
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, hsum]
  constructor
  · intro hcl
    have hdvd : ∀ x, p ^ a ∣ x ^ e2 - x ^ e1 :=
      (clash_iff_dvd_sub hmpos he1 (Nat.le_of_lt he)).mp hcl
    refine ⟨?_, ?_⟩
    · -- x = p: p^a ∣ p^e1·(p^(e2-e1) - 1) and the second factor is prime to p
      rcases Nat.lt_or_ge e1 a with hlt | hge
      case inr => exact hge
      exfalso
      have h1' : p ^ (e1 + 1) ∣ p ^ a := Nat.pow_dvd_pow p (by omega)
      have h2' : p ^ a ∣ p ^ e1 * (p ^ (e2 - e1) - 1) := by rw [hfac]; exact hdvd p
      have h3 : p ^ e1 * p ∣ p ^ e1 * (p ^ (e2 - e1) - 1) := by
        rw [← Nat.pow_succ p e1]
        exact Nat.dvd_trans h1' h2'
      have h4 : p ∣ p ^ (e2 - e1) - 1 :=
        (Nat.mul_dvd_mul_iff_left (Nat.pow_pos (show 0 < p by omega))).mp h3
      have h5 : p ∣ p ^ (e2 - e1) := by
        have := Nat.pow_dvd_pow p (show 1 ≤ e2 - e1 by omega)
        rwa [Nat.pow_one] at this
      have h6 : p ∣ p ^ (e2 - e1) - (p ^ (e2 - e1) - 1) := Nat.dvd_sub h5 h4
      have h7 : 1 ≤ p ^ (e2 - e1) := Nat.pow_pos (show 0 < p by omega)
      have h8 : p ^ (e2 - e1) - (p ^ (e2 - e1) - 1) = 1 := by omega
      rw [h8] at h6
      have := Nat.le_of_dvd Nat.one_pos h6
      omega
    · -- x = u a unit: cancel u^e1, which is prime to p
      intro u hu
      have hu0 : 0 < u := by
        rcases Nat.eq_zero_or_pos u with rfl | h
        · exact absurd (Nat.dvd_zero p) hu
        · exact h
      have hco : Nat.Coprime (p ^ a) (u ^ e1) :=
        Nat.Coprime.pow a e1 (coprime_of_not_dvd hp hu)
      have h2' : p ^ a ∣ u ^ e1 * (u ^ (e2 - e1) - 1) := by rw [hfac]; exact hdvd u
      have h3 : p ^ a ∣ u ^ (e2 - e1) - 1 := hco.dvd_of_dvd_mul_left h2'
      have h5 := (dvd_sub_iff_mod_eq hmpos (Nat.pow_pos hu0)).mp h3
      rwa [Nat.mod_eq_of_lt hm] at h5
  · rintro ⟨hae, hunit⟩ x
    by_cases hpx : p ∣ x
    · -- p ∣ x: both powers are ≡ 0, since a ≤ e1 ≤ e2
      have h1' : p ^ a ∣ x ^ e1 :=
        Nat.dvd_trans (Nat.pow_dvd_pow p hae) (pow_dvd_pow_of_dvd hpx e1)
      have h2' : p ^ a ∣ x ^ e2 :=
        Nat.dvd_trans (Nat.pow_dvd_pow p (by omega)) (pow_dvd_pow_of_dvd hpx e2)
      rw [Nat.dvd_iff_mod_eq_zero.mp h1', Nat.dvd_iff_mod_eq_zero.mp h2']
    · -- x a unit: multiply the congruence u^(e2-e1) ≡ 1 by x^e1
      have hd : x ^ (e2 - e1) % p ^ a = 1 := hunit x hpx
      have hsplit : x ^ e2 = x ^ e1 * x ^ (e2 - e1) := by
        rw [← Nat.pow_add]
        have : e1 + (e2 - e1) = e2 := by omega
        rw [this]
      rw [hsplit, Nat.mul_mod, hd, Nat.mul_one, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]

/-- The valuation form of Theorem 2: `p^a ∣ N(e1,e2)` exactly when `a ≤ e1` and
every unit mod `p` has order dividing `e2-e1`.  Feed in `λ(p^a)` — the exponent
of `(ℤ/p^aℤ)ˣ` — and this is the textbook closed form
`N = ∏_p p^{a_p}`, `a_p = max{a ≤ e1 : λ(p^a) ∣ e2-e1}`.
@isnad1 id=iff.4h4v.s6.b121277b2b00 from=translated src=- shape=3c9910e8 vocab=fe208349
-/
theorem prime_pow_dvd_clashMod_iff {p a e1 e2 : Nat} (hp : IsPrime p) (ha : 1 ≤ a)
    (he1 : 1 ≤ e1) (he : e1 < e2) :
    p ^ a ∣ clashMod e1 e2 ↔ (a ≤ e1 ∧ ∀ u, ¬ p ∣ u → u ^ (e2 - e1) % p ^ a = 1) := by
  have hppos : 0 < p := by have := hp.1; omega
  exact (clash_iff_dvd_clashMod (Nat.pow_pos hppos) he1 he).symm.trans
    (clash_prime_pow_iff hp ha he1 he)

/-! ### §5.4  `N(e1,e2)`, computed, and the theorem firing

The values agree with the Carmichael product `∏ p^{a_p}` computed independently, which
is the form Theorem 2 is usually stated in.  These are kernel computations, not `native_decide`. -/

/--
@isnad1 id=eq.0h0v.s4.8c689cb7b1f4 from=translated src=- shape=7226d0ee vocab=ac90ef74
-/
theorem clashMod_one_two : clashMod 1 2 = 2 := by decide
/--
@isnad1 id=eq.0h0v.s4.dc3fd437e3a7 from=translated src=- shape=7226d0ee vocab=ac90ef74
-/
theorem clashMod_two_three : clashMod 2 3 = 2 := by decide
/--
@isnad1 id=eq.0h0v.s4.1ae1d39a4ff7 from=translated src=- shape=7226d0ee vocab=ac90ef74
-/
theorem clashMod_one_four : clashMod 1 4 = 2 := by decide
/--
@isnad1 id=eq.0h0v.s4.26344cdefd51 from=translated src=- shape=7226d0ee vocab=ac90ef74
-/
theorem clashMod_one_three : clashMod 1 3 = 6 := by decide
/--
@isnad1 id=eq.0h0v.s4.e968ade58c6c from=translated src=- shape=7226d0ee vocab=ac90ef74
-/
theorem clashMod_two_four : clashMod 2 4 = 12 := by decide
/--
@isnad1 id=eq.0h0v.s4.b9cab8b41b23 from=translated src=- shape=7226d0ee vocab=ac90ef74
-/
theorem clashMod_one_five : clashMod 1 5 = 30 := by decide
/--
@isnad1 id=eq.0h0v.s4.e5f1022fa1fc from=translated src=- shape=7226d0ee vocab=ac90ef74
-/
theorem clashMod_one_seven : clashMod 1 7 = 42 := by decide
/--
@isnad1 id=eq.0h0v.s4.e4e088e3e3b2 from=translated src=- shape=7226d0ee vocab=ac90ef74
-/
theorem clashMod_two_six : clashMod 2 6 = 60 := by decide
/--
@isnad1 id=eq.0h0v.s4.21999556001e from=translated src=- shape=7226d0ee vocab=ac90ef74
-/
theorem clashMod_three_seven : clashMod 3 7 = 120 := by decide

/-- Every divisor of `N(e1,e2)` is a dead base, for every `n`.
@isnad1 id=not.4h4v.s5.ad102d914730 from=translated src=- shape=956e73ec vocab=2ce8c48a
-/
theorem no_pandigital_of_dvd_clashMod {b e1 e2 n : Nat} (hb : 1 < b) (he1 : 1 ≤ e1)
    (he : e1 < e2) (hdvd : b ∣ clashMod e1 e2) : ¬ Pandigital b e1 e2 n :=
  no_nice_of_universal_clash hb ((clash_iff_dvd_clashMod (by omega) he1 he).mpr hdvd)

/-- Theorem 2 firing where Theorems 1 and 3 both say nothing: `6 % 4 = 2` so Theorem 1
misses it and `6` is even so Theorem 3 misses it, but `x ≡ x^3 (mod 6)` for every
`x` because `6 ∣ N(1,3) = 6`.  So base 6 has no `(1,3)` pandigital number.
@isnad1 id=not.0h1v.s4.55390026c5f6 from=translated src=- shape=2e95bcf2 vocab=f94668c8
-/
theorem one_three_base_six_dead (n : Nat) : ¬ Pandigital 6 1 3 n :=
  no_pandigital_of_dvd_clashMod (by decide) (by decide) (by decide) (by decide)

/-- The same at `(2,4)`, base 12: `12 ≡ 0 (mod 3)` so Theorem 1 misses it too,
and `12 ∣ N(2,4) = 12`.
@isnad1 id=not.0h1v.s4.e0ebc1b8ee29 from=translated src=- shape=2e95bcf2 vocab=f94668c8
-/
theorem two_four_base_twelve_dead (n : Nat) : ¬ Pandigital 12 2 4 n :=
  no_pandigital_of_dvd_clashMod (by decide) (by decide) (by decide) (by decide)

/-! ### §5.5  Non-vacuity

Two directions matter here.  `Pandigital` must be satisfiable, or §5.1 proves
nothing; and Theorem 2 must **not** kill base 10 at `(2,3)`, or it would
contradict 69. -/

/--
@isnad1 id=eq.0h0v.s5.6ff35e0dfeb3 from=translated src=- shape=82c8f877 vocab=c2c693df
-/
theorem digits_69sq : digits 10 (69 ^ 2) = [1, 6, 7, 4] := by
  show digits 10 4761 = [1, 6, 7, 4]
  rw [digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_zero]

/--
@isnad1 id=eq.0h0v.s6.1be8648cb6e5 from=translated src=- shape=70269627 vocab=c2c693df
-/
theorem digits_69cb : digits 10 (69 ^ 3) = [9, 0, 5, 8, 2, 3] := by
  show digits 10 328509 = [9, 0, 5, 8, 2, 3]
  rw [digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_zero]

/-- 69 in base 10 really is `(2,3)`-pandigital: `69^2 = 4761`, `69^3 = 328509`,
and the ten digits are `{0,…,9}` once each.
@isnad1 id=pandigit.0h0v.s4.8c67aca80e56 from=translated src=- shape=147f988f vocab=f94668c8
-/
theorem sixtynine_pandigital : Pandigital 10 2 3 69 := by
  have h : ∀ v, v < 10 → occ v ([1, 6, 7, 4] ++ [9, 0, 5, 8, 2, 3]) = 1 := by decide
  intro v hv
  rw [digits_69sq, digits_69cb]
  exact h v hv

/-- Theorem 2 does not kill base 10 at `(2,3)` — it had better not.
`N(2,3) = 2` and `10 ∤ 2`.
@isnad1 id=not.0h0v.s4.eef19b509056 from=translated src=- shape=7029dda5 vocab=cc77a806
-/
theorem base_ten_no_clash : ¬ UniversalClash 10 2 3 := by
  intro h
  have hd := (clash_iff_dvd_clashMod (by decide) (by decide) (by decide)).mp h
  rw [clashMod_two_three] at hd
  have := Nat.le_of_dvd (by decide) hd
  omega

/-- The local criterion running forwards: `3 = 3^1` clashes for `(1,3)` because
`1 ≤ e1` and every unit mod 3 squares to 1.
@isnad1 id=universa.0h0v.s4.9e81319133cb from=translated src=- shape=b850a97b vocab=cc77a806
-/
theorem clash_three_one_three : UniversalClash 3 1 3 := by
  refine (clash_prime_pow_iff (p := 3) (a := 1) isPrime_three (by decide) (by decide)
    (by decide)).mpr ⟨by decide, ?_⟩
  intro u hu
  have h0 : u % 3 ≠ 0 := fun h => hu (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hlt : u % 3 < 3 := Nat.mod_lt u (by decide)
  have hpm := Nat.pow_mod u 2 3
  have h3 : u % 3 = 1 ∨ u % 3 = 2 := by omega
  rcases h3 with h | h <;> rw [h] at hpm <;> omega

/-- And backwards: base 9 does *not* clash for `(1,3)`, because `a = 2` exceeds
`e1 = 1`.  No unit-group computation is needed to see it.
@isnad1 id=not.0h0v.s4.19f66578129a from=translated src=- shape=7029dda5 vocab=cc77a806
-/
theorem nine_no_clash_one_three : ¬ UniversalClash 9 1 3 := by
  intro h
  have hc := (clash_prime_pow_iff (p := 3) (a := 2) isPrime_three (by decide) (by decide)
    (by decide)).mp h
  omega

/-! ## §6  Theorem 5 — how complete the congruence sieve is

A *congruence sieve* at modulus `m` prunes a candidate `n` by testing
`(n^e1 + n^e2) mod m` for membership in the set of residues that a pandigital
pair can have.  The naive claim is that set is always exactly
the one the digit-sum congruence already gives — that **no** modulus adds
information.  This section formalises the two halves of that claim, and they
come out differently:

* **Soundness** (`sieve_sound_mod_pred`, `valOf_mod_pow_sub_one`) — the half that
  is true for every modulus.  Casting out `b-1`s pins `x + y` mod `b-1`, and
  more generally `x + y ≡ Σ_t b^t S_t (mod b^j - 1)` where `S_t` totals the
  digits in positions `≡ t (mod j)`.  This is the engine of the whole
  proposition: it is why only `j = ord_m(b)` matters, and why the block sizes
  `c_t` are the only combinatorial data.
* **Completeness** — the claim that nothing beyond that survives.  It is
  **false**, and `base_four_sieve_is_incomplete` is a machine-checked
  counterexample: in base 4 with digit lengths `(2,2)` — a genuine `(2,3)` band,
  `n = 2` lies in it — the digit-sum congruence permits all five residues mod 5,
  and only three occur.  So a modulus *can* buy density the digit sum does not.

What is true instead: completeness holds under
an explicit hypothesis on the block sizes, the deficiency elsewhere is tiny
(base 10 loses 2 residues in 11111), and the sharp threshold is conjectural. -/

/-! ### §6.0  Little-endian values, and folding the weights mod `b^j - 1` -/

/-- Value of a digit list, least significant digit first.-/
def valOf (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + b * valOf b ds

/-- `Σ_i b^(i mod j) · dᵢ` — the same sum with the weights folded to period `j`.
The accumulator `t` is the current position mod `j`.-/
def wsum (b j : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | t, d :: ds => b ^ t * d + wsum b j ((t + 1) % j) ds

/--
@isnad1 id=eq.0h3v.s4.cbc38f31f186 from=translated src=- shape=dca39eb1 vocab=490731e1
-/
theorem wsum_nil (b j t : Nat) : wsum b j t [] = 0 := rfl

/--
@isnad1 id=eq.0h5v.s6.56071898e1eb from=translated src=- shape=94489032 vocab=c969d204
-/
theorem wsum_cons (b j t d : Nat) (ds : List Nat) :
    wsum b j t (d :: ds) = b ^ t * d + wsum b j ((t + 1) % j) ds := rfl

/-- `x^q ≡ 1 (mod x-1)`, the reason weights are periodic at all.
@isnad1 id=eq.1h2v.s6.b2c6aa0356a9 from=translated src=- shape=cd6215c1 vocab=f9c26dd3
-/
theorem pow_mod_pred {x : Nat} (hx : 1 ≤ x) : ∀ q, x ^ q % (x - 1) = 1 % (x - 1) := by
  intro q
  induction q with
  | zero => rw [Nat.pow_zero]
  | succ k ih =>
    have hstep : x % (x - 1) = 1 % (x - 1) := by
      have h := Nat.add_mod_left (x - 1) 1
      rwa [show x - 1 + 1 = x from by omega] at h
    rw [Nat.pow_succ, Nat.mul_mod, ih, hstep, ← Nat.mul_mod, Nat.one_mul]

/-- Weights are periodic mod `b^j - 1`: only `u mod j` matters.
@isnad1 id=eq.2h3v.s6.29648e657ba5 from=translated src=- shape=0f64699e vocab=533ac268
-/
theorem pow_mod_cycle {b j : Nat} (hb : 1 < b) (hj : 0 < j) (u : Nat) :
    b ^ u % (b ^ j - 1) = b ^ (u % j) % (b ^ j - 1) := by
  have hbj : 1 ≤ b ^ j := Nat.pow_pos (by omega)
  have key : b ^ u = (b ^ j) ^ (u / j) * b ^ (u % j) := by
    rw [← Nat.pow_mul, ← Nat.pow_add, Nat.div_add_mod]
  rw [key, Nat.mul_mod, pow_mod_pred hbj (u / j), ← Nat.mul_mod, Nat.one_mul]

/--
**The block congruence.**  `b^t · valOf b ds ≡ wsum b j t ds (mod b^j - 1)`:
reducing mod `b^j - 1` collapses the digit positions into `j` residue classes,
and only the total of each class survives.  Everything §6 says about which
moduli can see what comes from this one identity.
@isnad1 id=eq.2h4v.s7.674b5476a5e7 from=translated src=- shape=37276312 vocab=53172ae8
-/
theorem valOf_mod_wsum {b j : Nat} (hb : 1 < b) (hj : 0 < j) :
    ∀ (ds : List Nat) (t : Nat),
      (b ^ t * valOf b ds) % (b ^ j - 1) = wsum b j (t % j) ds % (b ^ j - 1) := by
  intro ds
  induction ds with
  | nil => intro t; show (b ^ t * 0) % _ = 0 % _; rw [Nat.mul_zero]
  | cons d ds ih =>
    intro t
    have hsplit : b ^ t * valOf b (d :: ds) = b ^ t * d + b ^ (t + 1) * valOf b ds := by
      show b ^ t * (d + b * valOf b ds) = _
      rw [Nat.mul_add, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm b (valOf b ds)]
    have hidx : (t % j + 1) % j = (t + 1) % j := Nat.mod_add_mod t j 1
    rw [hsplit, wsum_cons, hidx, Nat.add_mod, Nat.add_mod (b ^ (t % j) * d),
        Nat.mul_mod (b ^ t) d, Nat.mul_mod (b ^ (t % j)) d,
        pow_mod_cycle hb hj t, ih (t + 1)]

/-- The block congruence at `t = 0`, which is the form actually used.
@isnad1 id=eq.2h3v.s6.745717f2e0c4 from=translated src=- shape=fe6bb3c2 vocab=1962d1cb
-/
theorem valOf_mod_pow_sub_one {b j : Nat} (hb : 1 < b) (hj : 0 < j) (ds : List Nat) :
    valOf b ds % (b ^ j - 1) = wsum b j 0 ds % (b ^ j - 1) := by
  have h := valOf_mod_wsum hb hj ds 0
  rwa [Nat.pow_zero, Nat.one_mul, Nat.zero_mod] at h

/--
**Only the block totals are visible.**  For any modulus dividing `b^j - 1`, the
pair `(x,y)` enters the sieve only through `wsum b j 0` of each digit list — the
`j` totals of the digits in positions `≡ t (mod j)`.  This is why the block
sizes are the sole combinatorial data in §6, and why `j = ord_m(b)` is the only
feature of `m` that matters.
@isnad1 id=eq.2h4v.s7.f64ec7ecf3ac from=translated src=- shape=cee94526 vocab=13daad14
-/
theorem pair_mod_pow_sub_one {b j : Nat} (hb : 1 < b) (hj : 0 < j) (d1 d2 : List Nat) :
    (valOf b d1 + valOf b d2) % (b ^ j - 1)
      = (wsum b j 0 d1 + wsum b j 0 d2) % (b ^ j - 1) := by
  rw [Nat.add_mod, valOf_mod_pow_sub_one hb hj, valOf_mod_pow_sub_one hb hj, ← Nat.add_mod]

/-- At `j = 1` the weights collapse to `1` and `wsum` is the plain digit sum.
@isnad1 id=eq.0h2v.s4.648531d758a3 from=translated src=- shape=e990e290 vocab=0093045a
-/
theorem wsum_one (b : Nat) : ∀ ds : List Nat, wsum b 1 0 ds = ds.sum := by
  intro ds
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [wsum_cons, ih]; simp

/-- **Casting out `b-1`s, for lists.**  The `j = 1` case of the block
congruence, and the only congruence the naive claim says is available.
@isnad1 id=eq.1h2v.s6.dd97463354e8 from=translated src=- shape=7aea0edb vocab=84cda3ab
-/
theorem valOf_mod_pred {b : Nat} (hb : 1 < b) (ds : List Nat) :
    valOf b ds % (b - 1) = ds.sum % (b - 1) := by
  have h := valOf_mod_pow_sub_one hb Nat.one_pos ds
  rwa [Nat.pow_one, wsum_one] at h

/-- **Soundness of the digit-sum sieve.**  A pandigital pair has
`x + y ≡ T (mod b-1)`, where `T` is the total of all `b` digits.  Stated on the
digit lists, so it holds for any notion of solution whose digits are those
lists — the same convention §1-§3 use.
@isnad1 id=eq.2h4v.s6.9e9274ff48c0 from=translated src=- shape=b0791472 vocab=02e41b9f
-/
theorem sieve_sound_mod_pred {b T : Nat} (hb : 1 < b) (d1 d2 : List Nat)
    (hT : d1.sum + d2.sum = T) :
    (valOf b d1 + valOf b d2) % (b - 1) = T % (b - 1) := by
  rw [Nat.add_mod, valOf_mod_pred hb, valOf_mod_pred hb, ← Nat.add_mod, hT]

/-- `valOf` inverts `digits`, so everything above is about actual numbers and
not merely about lists that resemble digits.
@isnad1 id=eq.1h2v.s4.c3c357dd31ee from=translated src=- shape=eb0f5b30 vocab=89d04391
-/
theorem valOf_digits {b : Nat} (hb : 1 < b) : ∀ x, valOf b (digits b x) = x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [digits_zero]; rfl
    · rw [digits_step hb hx]
      show x % b + b * valOf b (digits b (x / b)) = x
      rw [ih (x / b) (Nat.div_lt_self hx hb)]
      exact Nat.mod_add_div x b

/-- …and `digitSum` of §0 is the sum of that list, so §6 and §2 are talking
about the same quantity.
@isnad1 id=eq.1h2v.s4.8a28aad93a52 from=translated src=- shape=d864a40f vocab=8633980f
-/
theorem digitSum_eq_sum {b : Nat} (hb : 1 < b) : ∀ x, digitSum b x = (digits b x).sum := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [digitSum_zero, digits_zero]; rfl
    · rw [digitSum_step hb hx, digits_step hb hx, ih (x / b) (Nat.div_lt_self hx hb)]
      simp

/-- **Soundness, on numbers.**  Whatever else a sieve knows, it never learns
more than this about `x + y` from a modulus dividing `b-1`.
@isnad1 id=eq.2h4v.s6.337a19c45110 from=translated src=- shape=ef554868 vocab=34bdc0e3
-/
theorem sieve_sound {b x y T : Nat} (hb : 1 < b)
    (hT : digitSum b x + digitSum b y = T) :
    (x + y) % (b - 1) = T % (b - 1) := by
  have h := sieve_sound_mod_pred (b := b) (T := T) hb (digits b x) (digits b y)
    (by rw [← digitSum_eq_sum hb, ← digitSum_eq_sum hb]; exact hT)
  rwa [valOf_digits hb, valOf_digits hb] at h

/-! ### §6.1  Completeness fails — a machine-checked counterexample

Base 4 with digit lengths `(2,2)`.  That is a genuine `(2,3)` band: `n = 2` has
`2^2 = 4 = "10"` and `2^3 = 8 = "20"`, two base-4 digits each, and `2 + 2 = 4 = b`,
so Theorem 1's length identity holds and neither Theorem 1 (`4 % 5 ≠ 1`) nor Theorem 3
(`4 % 4 ≠ 3`) kills the base.

`gcd(5, b-1) = gcd(5,3) = 1`, so the digit-sum congruence mod 3 excludes **no**
residue mod 5 whatsoever — the naive claim therefore predicts all five occur.
Only three do.  The three attainable sums are `15, 18, 21`; all are `≡ 0 (mod 3)`
as casting out 3s demands, and mod 5 they are `0, 3, 1`. -/

/-- A number with exactly two base-`b` digits has the digit list you expect.
Same two-`digits_step` unfolding as `digits_69sq`, done once and generically.
@isnad1 id=eq.3h2v.s6.3363728f8cca from=translated src=- shape=8d6564f1 vocab=c890173d
-/
theorem digits_two {b x : Nat} (hb : 1 < b) (h1' : b ≤ x) (h2' : x < b * b) :
    digits b x = [x % b, x / b] := by
  have hx : 0 < x := by omega
  have hq : 0 < x / b := Nat.div_pos h1' (by omega)
  have hqb : x / b < b := Nat.div_lt_of_lt_mul h2'
  have hq2 : x / b / b = 0 := Nat.div_eq_of_lt hqb
  rw [digits_step hb hx, digits_step hb hq, hq2, digits_zero, Nat.mod_eq_of_lt hqb]

/-- The finite heart of the counterexample, and it pins the image exactly: over
every pair of two-digit base-4 numbers, a pandigital one sums to `0`, `1` or `3`
mod 5 — never `2`, never `4`.  256 cases, checked by the kernel.  (The
hypotheses are conjoined rather than curried purely so that
`Nat.decidableBallLT` instance search succeeds; curried, it gives up.)
@isnad1 id=or.3h2v.s7.82538005fe5a from=translated src=- shape=e6ea8e3f vocab=0076e7da
-/
theorem base_four_gap_core :
    ∀ x < 16, ∀ y < 16,
      (4 ≤ x ∧ 4 ≤ y ∧ ∀ v < 4, occ v [x % 4, x / 4, y % 4, y / 4] = 1) →
      ((x + y) % 5 = 0 ∨ (x + y) % 5 = 1 ∨ (x + y) % 5 = 3) := by decide

/-- Lifting the finite check off the digit lists and onto the numbers.
@isnad1 id=or.3h2v.s7.b5eb19a3b5c1 from=translated src=- shape=ab8eda96 vocab=dc464879
-/
theorem base_four_image {x y : Nat}
    (hx : numDigits 4 x = 2) (hy : numDigits 4 y = 2)
    (hpan : ∀ v, v < 4 → occ v (digits 4 x ++ digits 4 y) = 1) :
    (x + y) % 5 = 0 ∨ (x + y) % 5 = 1 ∨ (x + y) % 5 = 3 := by
  obtain ⟨hx1, hx2⟩ := bounds_of_numDigits (b := 4) (by decide) x 1 hx
  obtain ⟨hy1, hy2⟩ := bounds_of_numDigits (b := 4) (by decide) y 1 hy
  rw [Nat.pow_one] at hx1 hy1
  rw [show (4 : Nat) ^ (1 + 1) = 16 from by decide] at hx2 hy2
  have hdx : digits 4 x = [x % 4, x / 4] := digits_two (by decide) hx1 (by omega)
  have hdy : digits 4 y = [y % 4, y / 4] := digits_two (by decide) hy1 (by omega)
  rw [hdx, hdy] at hpan
  exact base_four_gap_core x hx2 y hy2 ⟨hx1, hy1, fun v hv => hpan v hv⟩

/--
**The naive completeness claim is false.**  In base 4 with digit lengths `(2,2)`, no pandigital
pair has `x + y ≡ 2 (mod 5)` — while the digit-sum congruence, the only thing
the naive claim allows a sieve to know, permits every residue mod 5 because
`gcd(5, 4-1) = 1`.  So the modulus 5 is strictly stronger than casting out 3s,
and "no modulus yields additional density" does not hold as stated.
@isnad1 id=ne.3h2v.s6.8d763a1abc9e from=translated src=- shape=cf2594fb vocab=dc464879
-/
theorem base_four_sieve_is_incomplete {x y : Nat}
    (hx : numDigits 4 x = 2) (hy : numDigits 4 y = 2)
    (hpan : ∀ v, v < 4 → occ v (digits 4 x ++ digits 4 y) = 1) :
    (x + y) % 5 ≠ 2 := by
  rcases base_four_image hx hy hpan with h | h | h <;> omega

/-- The same for `4`: two of the five residues are unreachable, so the sieve
mod 5 keeps `3/5` of the residues where casting out 3s keeps all of them.
@isnad1 id=ne.3h2v.s6.3ee471ef8e3a from=translated src=- shape=cf2594fb vocab=dc464879
-/
theorem base_four_sieve_is_incomplete' {x y : Nat}
    (hx : numDigits 4 x = 2) (hy : numDigits 4 y = 2)
    (hpan : ∀ v, v < 4 → occ v (digits 4 x ++ digits 4 y) = 1) :
    (x + y) % 5 ≠ 4 := by
  rcases base_four_image hx hy hpan with h | h | h <;> omega

/-- Non-vacuity *and* sharpness, which an impossibility statement about an empty
hypothesis set would have neither of.  The three pandigital base-4 pairs are
`(4,11)`, `(4,14)` and `(9,12)`, with sums `15, 18, 21` — every one `≡ 0 (mod 3)`
as casting out 3s demands, and mod 5 they are exactly `0, 3, 1`.  So `{0,1,3}` in
`base_four_gap_core` is attained, not merely permitted.
@isnad1 id=and.0h0v.s8.0b15c789bfe3 from=translated src=- shape=048d9f42 vocab=26becef1
-/
theorem base_four_attained :
    ((∀ v, v < 4 → occ v (digits 4 4 ++ digits 4 11) = 1) ∧ (4 + 11) % 5 = 0) ∧
    ((∀ v, v < 4 → occ v (digits 4 4 ++ digits 4 14) = 1) ∧ (4 + 14) % 5 = 3) ∧
    ((∀ v, v < 4 → occ v (digits 4 9 ++ digits 4 12) = 1) ∧ (9 + 12) % 5 = 1) := by
  have h4 : digits 4 4 = [0, 1] := digits_two (by decide) (by decide) (by decide)
  have h9 : digits 4 9 = [1, 2] := digits_two (by decide) (by decide) (by decide)
  have h11 : digits 4 11 = [3, 2] := digits_two (by decide) (by decide) (by decide)
  have h12 : digits 4 12 = [0, 3] := digits_two (by decide) (by decide) (by decide)
  have h14 : digits 4 14 = [2, 3] := digits_two (by decide) (by decide) (by decide)
  refine ⟨⟨?_, by decide⟩, ⟨?_, by decide⟩, ⟨?_, by decide⟩⟩
  · rw [h4, h11]; decide
  · rw [h4, h14]; decide
  · rw [h9, h12]; decide

/-- And the lengths are right, so this really is the `(2,2)` split: `4`, `9`,
`11`, `12` and `14` all have exactly two base-4 digits.
@isnad1 id=and.0h0v.s6.d25a51bda663 from=translated src=- shape=1190bf51 vocab=4aba56e8
-/
theorem base_four_lengths :
    numDigits 4 4 = 2 ∧ numDigits 4 9 = 2 ∧ numDigits 4 11 = 2 ∧
    numDigits 4 12 = 2 ∧ numDigits 4 14 = 2 :=
  ⟨numDigits_eq_of_bounds (by decide) (by decide) (by decide),
   numDigits_eq_of_bounds (by decide) (by decide) (by decide),
   numDigits_eq_of_bounds (by decide) (by decide) (by decide),
   numDigits_eq_of_bounds (by decide) (by decide) (by decide),
   numDigits_eq_of_bounds (by decide) (by decide) (by decide)⟩

/-- Base 4 is a genuine `(2,3)` band and not an artefact: `n = 2` has
`2^2 = "10"` and `2^3 = "20"`, two base-4 digits each, so the length identity
`2 + 2 = 4 = b` holds.  Neither Theorem 1 (`4 % 5 ≠ 1`) nor Theorem 3
(`4 % 4 ≠ 3`) kills the base, so the counterexample sits inside the very family
under study.
@isnad1 id=inband.0h0v.s4.f2d8d5a091b2 from=translated src=- shape=147f988f vocab=7d977a64
-/
theorem base_four_band_nonempty : InBand 4 2 3 2 := by
  show numDigits 4 (2 ^ 2) + numDigits 4 (2 ^ 3) = 4
  rw [numDigits_eq_of_bounds (b := 4) (x := 2 ^ 2) (k := 1) (by decide) (by decide) (by decide),
      numDigits_eq_of_bounds (b := 4) (x := 2 ^ 3) (k := 1) (by decide) (by decide) (by decide)]

/-! ### §6.2  Theorem 5 — completeness, under an explicit hypothesis

§6.1 refuted the unconditional claim.  This is what survives, and it is the
statement the informal proof gives on paper: **if** the class sizes
`c_t` admit a legal split `p` whose no-gap conditions hold, and the classes are
big enough, then the image is the whole coset — so no modulus of order `j` prunes
more than casting out `b-1`s does.

The proof is constructive, and it runs on two engines that are independent of
each other and of the digits:

* `pick_sum` — **subset-sum contiguity**.  The `p`-element sublists of a run of
  `p+q` consecutive integers realise every sum from the minimum to the minimum
  plus `p·q`, with no gaps.  `pick` is that sublist, built as a staircase.
* `cover_exists` — **mixed-radix covering**.  If each place `b^t` opens before
  the lower places run out, `{Σ_t ν_t b^t : ν_t ≤ N_t}` is a full interval.

Between them sits the arrangement.  Run `t` keeps `p_t` of its values for class
`t` and passes the other `q_t` up to class `t+1`; `blk_identity` is an exact
identity in `ℕ` — no congruence anywhere in it — saying that raising the
kept-sums by one lowers the block-sum value `X = Σ_t b^t S_t` by `b-1`, up to a
single explicit wrap of `b^j - 1`.  `deal` then reads the blocks out into the two
digit lists, and `ins0` places the digit `0` at an index of its block that is
neither number's leading slot.  That last step is the only use of the class-size
rider, and the only place the leading-digit rule enters at all — take it away and
the *block-sum* image can overstate the true image, as at base 4, where it says 5
residues and §6.1 counts 3.

`sieve_complete` is the headline.  `blocks_hit` is its block-level half, which
mentions no digit lengths and no leading digits; `blocks_to_pair` is the other
half, which mentions no arithmetic. -/

/-- Cancelling a common summand under `%`.
@isnad1 id=eq.2h4v.s6.7db38f87cbc1 from=translated src=- shape=283c3aee vocab=fd2b17b6
-/
theorem mod_add_cancel {b c u v : Nat} (hb : 0 < b) (h : (u + c) % b = (v + c) % b) :
    u % b = v % b := by
  rcases Nat.le_total u v with hle | hle
  · have h1' : u + c ≤ v + c := by omega
    have hd : b ∣ v + c - (u + c) := (dvd_sub_iff_mod_eq hb h1').mpr h.symm
    have he : v + c - (u + c) = v - u := by omega
    rw [he] at hd
    exact ((dvd_sub_iff_mod_eq hb hle).mp hd).symm
  · have h1' : v + c ≤ u + c := by omega
    have hd : b ∣ u + c - (v + c) := (dvd_sub_iff_mod_eq hb h1').mpr h
    have he : u + c - (v + c) = u - v := by omega
    rw [he] at hd
    exact (dvd_sub_iff_mod_eq hb hle).mp hd

/--
@isnad1 id=eq.0h1v.s3.86b5e4de4965 from=translated src=- shape=8686b4dd vocab=3d320731
-/
theorem occ_nil (v : Nat) : occ v [] = 0 := rfl

/-! ### Runs of consecutive naturals -/

/-- `[s, s+1, …, s+n-1]`.-/
def run (s : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => s :: run (s + 1) n

/-- `p(p-1)/2`, without the division.-/
def tri : Nat → Nat
  | 0 => 0
  | p + 1 => tri p + p

/--
@isnad1 id=eq.0h2v.s3.b232cc8e9139 from=translated src=- shape=9da2df65 vocab=1cca483f
-/
theorem run_length (s n : Nat) : (run s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => show (run (s+1) k).length + 1 = k + 1; rw [ih]

/--
@isnad1 id=eq.0h2v.s5.1bb7fe03e411 from=translated src=- shape=bc24ce81 vocab=0dc16578
-/
theorem run_sum (s : Nat) : ∀ n, (run s n).sum = n * s + tri n := by
  intro n
  induction n generalizing s with
  | zero => simp [run, tri]
  | succ k ih =>
    show s + (run (s+1) k).sum = _
    rw [ih (s+1)]
    show s + (k * (s+1) + tri k) = (k+1) * s + (tri k + k)
    rw [Nat.mul_succ, Nat.succ_mul]
    omega

/-- `run` splits at any point.
@isnad1 id=eq.0h3v.s5.1771a15abf23 from=translated src=- shape=7a8fe856 vocab=15b8dc28
-/
theorem run_add (s m : Nat) : ∀ n, run s (m + n) = run s m ++ run (s + m) n := by
  intro n
  induction m generalizing s with
  | zero => simp [run]
  | succ k ih =>
    show run s (k + 1 + n) = _
    have : k + 1 + n = (k + n) + 1 := by omega
    rw [this]
    show s :: run (s+1) (k + n) = (s :: run (s+1) k) ++ run (s + (k+1)) n
    rw [ih (s+1)]
    show s :: (run (s+1) k ++ run (s + 1 + k) n) = s :: (run (s+1) k ++ run (s + (k+1)) n)
    rw [show s + 1 + k = s + (k+1) from by omega]

/--
@isnad1 id=eq.0h2v.s5.ed49f895d900 from=translated src=- shape=1e155ae5 vocab=925d86d2
-/
theorem run_succ (s n : Nat) : run s (n + 1) = run s n ++ [s + n] := by
  have h := run_add s n 1
  simpa [run] using h

/-! ### The staircase split -/

/-- Split `run s (p+q)` into a `p`-element sublist and its `q`-element
complement, so that the first has sum `p·s + tri p + ν`.-/
def pick : Nat → Nat → Nat → Nat → List Nat × List Nat
  | s, 0,     q,     _ => ([], run s q)
  | s, p + 1, 0,     _ => (run s (p + 1), [])
  | s, p + 1, q + 1, ν =>
      if q + 1 ≤ ν then
        (((pick s p (q + 1) (ν - (q + 1))).1) ++ [s + p + q + 1],
         (pick s p (q + 1) (ν - (q + 1))).2)
      else
        ((pick s (p + 1) q ν).1,
         ((pick s (p + 1) q ν).2) ++ [s + p + q + 1])
termination_by _ p q _ => p + q

/--
@isnad1 id=eq.0h4v.s4.956fafdb9f03 from=translated src=- shape=f2fd1e52 vocab=569365e1
-/
theorem pick_len1 (s p q ν : Nat) : (pick s p q ν).1.length = p := by
  induction s, p, q, ν using pick.induct with
  | case1 s q ν => simp [pick]
  | case2 s p ν => simp [pick, run_length]
  | case3 s p q ν h ih => rw [pick]; simp [h, ih]
  | case4 s p q ν h ih => rw [pick]; simp [h, ih]

/--
@isnad1 id=eq.0h4v.s4.3a5b122ff3d4 from=translated src=- shape=9a0cc209 vocab=9baa3063
-/
theorem pick_len2 (s p q ν : Nat) : (pick s p q ν).2.length = q := by
  induction s, p, q, ν using pick.induct with
  | case1 s q ν => simp [pick, run_length]
  | case2 s p ν => simp [pick]
  | case3 s p q ν h ih => rw [pick]; simp [h, ih]
  | case4 s p q ν h ih => rw [pick]; simp [h, ih]

/--
@isnad1 id=eq.0h5v.s5.80be01a4b678 from=translated src=- shape=bd55b2c1 vocab=c90bb715
-/
theorem pick_occ (v : Nat) : ∀ s p q ν,
    occ v (pick s p q ν).1 + occ v (pick s p q ν).2 = occ v (run s (p + q)) := by
  intro s p q ν
  induction s, p, q, ν using pick.induct with
  | case1 s q ν => rw [pick]; simp [occ_nil]
  | case2 s p ν => rw [pick]; simp [occ_nil]
  | case3 s p q ν h ih =>
    rw [pick, ite_eq_left h]
    show occ v ((pick s p (q+1) (ν - (q+1))).1 ++ [s + p + q + 1])
        + occ v (pick s p (q+1) (ν - (q+1))).2 = _
    rw [occ_append, show p + 1 + (q + 1) = (p + (q+1)) + 1 from by omega, run_succ,
        occ_append, ← ih, show s + (p + (q+1)) = s + p + q + 1 from by omega]
    omega
  | case4 s p q ν h ih =>
    rw [pick, ite_eq_right h]
    show occ v (pick s (p+1) q ν).1
        + occ v ((pick s (p+1) q ν).2 ++ [s + p + q + 1]) = _
    rw [occ_append, show p + 1 + (q + 1) = ((p+1) + q) + 1 from by omega, run_succ,
        occ_append, ← ih, show s + ((p+1) + q) = s + p + q + 1 from by omega]
    omega

/--
@isnad1 id=eq.0h4v.s6.973efc596e6c from=translated src=- shape=396e9556 vocab=8e2b9cce
-/
theorem pick_sum_total : ∀ s p q ν,
    (pick s p q ν).1.sum + (pick s p q ν).2.sum = (run s (p + q)).sum := by
  intro s p q ν
  induction s, p, q, ν using pick.induct with
  | case1 s q ν => rw [pick]; simp
  | case2 s p ν => rw [pick]; simp
  | case3 s p q ν h ih =>
    rw [pick, ite_eq_left h]
    show ((pick s p (q+1) (ν - (q+1))).1 ++ [s + p + q + 1]).sum
        + (pick s p (q+1) (ν - (q+1))).2.sum = _
    rw [List.sum_append, show p + 1 + (q + 1) = (p + (q+1)) + 1 from by omega, run_succ,
        List.sum_append, ← ih, show s + (p + (q+1)) = s + p + q + 1 from by omega]
    simp; omega
  | case4 s p q ν h ih =>
    rw [pick, ite_eq_right h]
    show (pick s (p+1) q ν).1.sum
        + ((pick s (p+1) q ν).2 ++ [s + p + q + 1]).sum = _
    rw [List.sum_append, show p + 1 + (q + 1) = ((p+1) + q) + 1 from by omega, run_succ,
        List.sum_append, ← ih, show s + ((p+1) + q) = s + p + q + 1 from by omega]
    simp; omega

/-- **Subset-sum contiguity.**  The `p`-element sublists of a run of `p+q`
consecutive integers realise every sum from the minimum to the minimum plus
`p·q`, with no gaps — this is the one combinatorial fact Theorem 5 needs.
@isnad1 id=eq.1h4v.s6.8e43c9f6f188 from=translated src=- shape=95eeedad vocab=73941ef6
-/
theorem pick_sum : ∀ s p q ν, ν ≤ p * q →
    (pick s p q ν).1.sum = p * s + tri p + ν := by
  intro s p q ν
  induction s, p, q, ν using pick.induct with
  | case1 s q ν => intro h; rw [pick]; simp [tri]; omega
  | case2 s p ν =>
    intro h
    simp only [Nat.mul_zero, Nat.le_zero_eq] at h
    subst h
    rw [pick]
    show (run s (p+1)).sum = _
    rw [run_sum]
    simp only [Nat.succ_eq_add_one]
    omega
  | case3 s p q ν h ih =>
    intro hν
    simp only [Nat.succ_eq_add_one] at hν
    have hexp : (p + 1) * (q + 1) = p * (q + 1) + (q + 1) := Nat.succ_mul p (q+1)
    have hle : ν - (q + 1) ≤ p * (q + 1) := by omega
    rw [pick, ite_eq_left h]
    show ((pick s p (q+1) (ν - (q+1))).1 ++ [s + p + q + 1]).sum = _
    rw [List.sum_append, ih hle]
    show p * s + tri p + (ν - (q+1)) + (s + p + q + 1 + 0) = (p+1) * s + (tri p + p) + ν
    rw [Nat.succ_mul]
    omega
  | case4 s p q ν h ih =>
    intro _
    have hle : ν ≤ (p + 1) * q := by
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · omega
      · have : q ≤ (p+1) * q := Nat.le_mul_of_pos_left q (by omega)
        omega
    rw [pick, ite_eq_right h]
    exact ih hle

/-! ### Finite sums over an initial segment -/

/-- `Σ_{t<n} f t`.-/
def sumRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange f n + f n

/--
@isnad1 id=eq.1h3v.s5.28bc9597ae8a from=translated src=- shape=f6826cbd vocab=4902b010
-/
theorem sumRange_congr {f g : Nat → Nat} :
    ∀ n, (∀ t, t < n → f t = g t) → sumRange f n = sumRange g n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    show sumRange f k + f k = sumRange g k + g k
    rw [ih (fun t ht => h t (by omega)), h k (by omega)]

/-! ### The no-gap covering lemma -/

/-- **Mixed-radix covering.**  If each place `b^t` opens before the lower places
run out — `b^t ≤ 1 + Σ_{s<t} N_s b^s` — then `{Σ_{t<j} ν_t b^t : ν_t ≤ N_t}` is
the whole interval `[0, Σ_{t<j} N_t b^t]`, with no gaps.  This is the second of
Theorem 5's two engines, and the only place the no-gap hypothesis is used.
@isnad1 id=ex.3h4v.s7.d7f7b4ed3bc4 from=translated src=- shape=44a2c56a vocab=43250dbd
-/
theorem cover_exists {b : Nat} (hb : 0 < b) (N : Nat → Nat) :
    ∀ j, (∀ t, t < j → b ^ t ≤ sumRange (fun s => N s * b ^ s) t + 1) →
      ∀ V, V ≤ sumRange (fun s => N s * b ^ s) j →
      ∃ ν : Nat → Nat, (∀ t, ν t ≤ N t) ∧ sumRange (fun t => ν t * b ^ t) j = V := by
  intro j
  induction j with
  | zero =>
    intro _ V hV
    have hV0 : V = 0 := Nat.le_zero.mp hV
    exact ⟨fun _ => 0, fun _ => Nat.zero_le _, by rw [hV0]; rfl⟩
  | succ k ih =>
    intro hgap V hV
    have hbk : 0 < b ^ k := Nat.pow_pos hb
    have hVk : V ≤ sumRange (fun s => N s * b ^ s) k + N k * b ^ k := hV
    by_cases hc : V / b ^ k ≤ N k
    · -- the greedy digit is legal, and the remainder is a genuine remainder
      have hdm := Nat.div_add_mod V (b ^ k)
      have hlt : V % b ^ k < b ^ k := Nat.mod_lt _ hbk
      have hle : V % b ^ k ≤ sumRange (fun s => N s * b ^ s) k := by
        have := hgap k (by omega); omega
      obtain ⟨ν, hν, hsum⟩ := ih (fun t ht => hgap t (by omega)) (V % b ^ k) hle
      refine ⟨fun t => if t = k then V / b ^ k else ν t, ?_, ?_⟩
      · intro t
        by_cases h : t = k
        · subst h; simpa using hc
        · simpa [h] using hν t
      · show sumRange _ k + _ = V
        rw [sumRange_congr (f := fun t => (if t = k then V / b ^ k else ν t) * b ^ t)
              (g := fun t => ν t * b ^ t) k
              (by intro t ht; rw [ite_eq_right (Nat.ne_of_lt ht)]), hsum]
        show V % b ^ k + (if k = k then V / b ^ k else ν k) * b ^ k = V
        rw [ite_eq_left rfl, Nat.mul_comm]
        omega
    · -- the greedy digit overflows, so take all of `N k`
      have hcc : N k < V / b ^ k := Nat.lt_of_not_le hc
      have hbig : N k * b ^ k ≤ V := by
        have h1' : N k * b ^ k ≤ (V / b ^ k) * b ^ k :=
          Nat.mul_le_mul_right _ (Nat.le_of_lt hcc)
        have h2' : (V / b ^ k) * b ^ k ≤ V := Nat.div_mul_le_self V (b ^ k)
        omega
      have hle : V - N k * b ^ k ≤ sumRange (fun s => N s * b ^ s) k := by omega
      obtain ⟨ν, hν, hsum⟩ := ih (fun t ht => hgap t (by omega)) (V - N k * b ^ k) hle
      refine ⟨fun t => if t = k then N k else ν t, ?_, ?_⟩
      · intro t
        by_cases h : t = k
        · subst h; simp
        · simpa [h] using hν t
      · show sumRange _ k + _ = V
        rw [sumRange_congr (f := fun t => (if t = k then N k else ν t) * b ^ t)
              (g := fun t => ν t * b ^ t) k
              (by intro t ht; rw [ite_eq_right (Nat.ne_of_lt ht)]), hsum]
        show V - N k * b ^ k + (if k = k then N k else ν k) * b ^ k = V
        rw [ite_eq_left rfl]
        omega

/--
@isnad1 id=eq.3h5v.s6.14655e97c3f3 from=translated src=- shape=61b926ce vocab=f66cd819
-/
theorem sumRange_update {f g : Nat → Nat} {t0 x : Nat} :
    ∀ j, t0 < j → (∀ t, t ≠ t0 → g t = f t) → x + g t0 = f t0 →
    x + sumRange g j = sumRange f j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ k ih =>
    intro ht hne hx
    show x + (sumRange g k + g k) = sumRange f k + f k
    rcases Nat.lt_or_ge t0 k with hlt | hge
    · rw [hne k (by omega), ← ih hlt hne hx]; omega
    · have : t0 = k := by omega
      subst this
      rw [sumRange_congr (f := g) (g := f) _ (fun t htk => hne t (by omega))]
      omega

/-! ### Dealing the blocks into slots -/

/-- Walk a list of slot-classes, taking the head of the named block.  Returns
the values placed, and what is left of each block.-/
def deal : (Nat → List Nat) → List Nat → List Nat × (Nat → List Nat)
  | B, [] => ([], B)
  | B, t :: cs =>
      ((B t).headD 0 :: (deal (fun u => if u = t then (B t).tail else B u) cs).1,
       (deal (fun u => if u = t then (B t).tail else B u) cs).2)

/--
@isnad1 id=eq.0h2v.s4.e2c95e238fc4 from=translated src=- shape=4a68cdaf vocab=ccf14add
-/
theorem deal_len : ∀ (l : List Nat) (B : Nat → List Nat),
    (deal B l).1.length = l.length := by
  intro l
  induction l with
  | nil => intro B; rfl
  | cons t cs ih => intro B; show (deal _ cs).1.length + 1 = cs.length + 1; rw [ih]

/-- What is left of block `t` is exactly `B t` with its dealt prefix dropped.
@isnad1 id=eq.0h3v.s5.0f4704ea9d4d from=translated src=- shape=08604168 vocab=5df8f739
-/
theorem deal_res : ∀ (l : List Nat) (B : Nat → List Nat) (t : Nat),
    (deal B l).2 t = (B t).drop (occ t l) := by
  intro l
  induction l with
  | nil => intro B t; rfl
  | cons t0 cs ih =>
    intro B t
    show (deal (fun u => if u = t0 then (B t0).tail else B u) cs).2 t = _
    rw [ih]
    show (if t = t0 then (B t0).tail else B t).drop (occ t cs)
        = (B t).drop ((if t0 = t then 1 else 0) + occ t cs)
    by_cases h : t = t0
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl,
          show (B t).tail = (B t).drop 1 from by cases B t <;> rfl, List.drop_drop]
    · rw [ite_eq_right h, ite_eq_right (fun hh => h hh.symm)]
      congr 1
      omega

/--
@isnad1 id=eq.0h3v.s6.878e422fc1ad from=translated src=- shape=1f5da3e3 vocab=263114b2
-/
theorem deal_app : ∀ (l1 l2 : List Nat) (B : Nat → List Nat),
    (deal B (l1 ++ l2)).1 = (deal B l1).1 ++ (deal (deal B l1).2 l2).1 := by
  intro l1
  induction l1 with
  | nil => intro l2 B; rfl
  | cons t cs ih =>
    intro l2 B
    show (B t).headD 0 :: (deal _ (cs ++ l2)).1
        = ((B t).headD 0 :: (deal _ cs).1) ++ _
    rw [ih]
    rfl

/-- `Σ_i b^(clsᵢ) · dᵢ` — the weight a slot-class list gives a digit list.-/
def wcls (b : Nat) : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | t :: cs, d :: ds => b ^ t * d + wcls b cs ds

/-- The bookkeeping shared by the next two lemmas: dealing one slot of class
`t0` shortens block `t0` by its head and leaves the others alone.
@isnad1 id=and.2h4v.s6.cc3f64a613a1 from=translated src=- shape=717e2e3f vocab=49b1efd7
-/
theorem deal_step_hyps {j t0 : Nat} {cs : List Nat} {B : Nat → List Nat}
    (hmem : ∀ t, t ∈ (t0 :: cs) → t < j) (hlen : ∀ t, occ t (t0 :: cs) ≤ (B t).length) :
    t0 < j ∧ 0 < (B t0).length ∧ (∀ t, t ∈ cs → t < j) ∧
      (∀ t, occ t cs ≤ ((fun u => if u = t0 then (B t0).tail else B u) t).length) := by
  refine ⟨hmem t0 List.mem_cons_self, ?_, fun t ht => hmem t (List.mem_cons_of_mem _ ht), ?_⟩
  · have h := hlen t0
    rw [occ_cons_self] at h
    omega
  · intro t
    by_cases h : t = t0
    · subst h
      have h1' := hlen t
      rw [occ_cons_self] at h1'
      show occ t cs ≤ (if t = t then (B t).tail else B t).length
      rw [ite_eq_left rfl, show (B t).tail.length = (B t).length - 1 from by cases B t <;> rfl]
      omega
    · have h1' := hlen t
      show occ t cs ≤ (if t = t0 then (B t0).tail else B t).length
      rw [ite_eq_right h]
      show occ t cs ≤ (B t).length
      have : occ t (t0 :: cs) = (if t0 = t then 1 else 0) + occ t cs := rfl
      rw [ite_eq_right (fun hh => h hh.symm)] at this
      omega

/-- **Dealing conserves values.**  Nothing is created or lost: what is placed
plus what is left equals what there was.
@isnad1 id=eq.2h4v.s6.02343272fee1 from=translated src=- shape=b8712c6c vocab=5b1dfe4b
-/
theorem deal_occ (v j : Nat) : ∀ (l : List Nat) (B : Nat → List Nat),
    (∀ t, t ∈ l → t < j) → (∀ t, occ t l ≤ (B t).length) →
    occ v (deal B l).1 + sumRange (fun t => occ v ((deal B l).2 t)) j
      = sumRange (fun t => occ v (B t)) j := by
  intro l
  induction l with
  | nil =>
    intro B _ _
    show occ v ([] : List Nat) + sumRange (fun t => occ v (B t)) j
        = sumRange (fun t => occ v (B t)) j
    rw [occ_nil, Nat.zero_add]
  | cons t0 cs ih =>
    intro B hmem hlen
    obtain ⟨ht0, hpos, hmem', hlen'⟩ := deal_step_hyps hmem hlen
    have key := ih (fun u => if u = t0 then (B t0).tail else B u) hmem' hlen'
    show (if (B t0).headD 0 = v then 1 else 0)
        + occ v (deal (fun u => if u = t0 then (B t0).tail else B u) cs).1
        + sumRange (fun t => occ v ((deal (fun u => if u = t0 then (B t0).tail else B u) cs).2 t)) j
      = _
    rw [Nat.add_assoc, key]
    refine sumRange_update (x := if (B t0).headD 0 = v then 1 else 0) j ht0 ?_ ?_
    · intro t hne
      show occ v (if t = t0 then (B t0).tail else B t) = occ v (B t)
      rw [ite_eq_right hne]
    · show (if (B t0).headD 0 = v then 1 else 0)
          + occ v (if t0 = t0 then (B t0).tail else B t0) = occ v (B t0)
      rw [ite_eq_left rfl]
      cases hB : B t0 with
      | nil => rw [hB] at hpos; exact absurd hpos (by simp)
      | cons x xs => show (if x = v then 1 else 0) + occ v xs = occ v (x :: xs); rfl

/-- **Dealing conserves the weighted block totals.**  Slot `i` of class `t`
carries weight `b^t`, so the value dealt there is charged to block `t`.
@isnad1 id=eq.2h4v.s7.63306ab50bd9 from=translated src=- shape=93fa384d vocab=596b3f4b
-/
theorem deal_wcls (b j : Nat) : ∀ (l : List Nat) (B : Nat → List Nat),
    (∀ t, t ∈ l → t < j) → (∀ t, occ t l ≤ (B t).length) →
    wcls b l (deal B l).1 + sumRange (fun t => b ^ t * ((deal B l).2 t).sum) j
      = sumRange (fun t => b ^ t * (B t).sum) j := by
  intro l
  induction l with
  | nil =>
    intro B _ _
    show 0 + sumRange (fun t => b ^ t * (B t).sum) j = sumRange (fun t => b ^ t * (B t).sum) j
    rw [Nat.zero_add]
  | cons t0 cs ih =>
    intro B hmem hlen
    obtain ⟨ht0, hpos, hmem', hlen'⟩ := deal_step_hyps hmem hlen
    have key := ih (fun u => if u = t0 then (B t0).tail else B u) hmem' hlen'
    show b ^ t0 * (B t0).headD 0
        + wcls b cs (deal (fun u => if u = t0 then (B t0).tail else B u) cs).1
        + sumRange (fun t => b ^ t * ((deal (fun u => if u = t0 then (B t0).tail else B u) cs).2 t).sum) j
      = _
    rw [Nat.add_assoc, key]
    refine sumRange_update (x := b ^ t0 * (B t0).headD 0) j ht0 ?_ ?_
    · intro t hne
      show b ^ t * (if t = t0 then (B t0).tail else B t).sum = b ^ t * (B t).sum
      rw [ite_eq_right hne]
    · show b ^ t0 * (B t0).headD 0
          + b ^ t0 * (if t0 = t0 then (B t0).tail else B t0).sum = b ^ t0 * (B t0).sum
      rw [ite_eq_left rfl, ← Nat.mul_add]
      cases hB : B t0 with
      | nil => rw [hB] at hpos; exact absurd hpos (by simp)
      | cons x xs => show b ^ t0 * (x + xs.sum) = b ^ t0 * (x :: xs).sum; rfl

/-- The classes of `n` consecutive slots starting at class `t`.-/
def clsOf (j : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | t, n + 1 => t :: clsOf j ((t + 1) % j) n

/--
@isnad1 id=eq.0h3v.s3.9c0b98d0a2a9 from=translated src=- shape=247bb1a2 vocab=67bc8d15
-/
theorem clsOf_length (j : Nat) : ∀ n t, (clsOf j t n).length = n := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ k ih => intro t; show (clsOf j ((t+1) % j) k).length + 1 = k + 1; rw [ih]

/--
@isnad1 id=lt.3h4v.s5.ac50280b8a6e from=translated src=- shape=3fb44c87 vocab=52e70cc4
-/
theorem clsOf_mem {j : Nat} (hj : 0 < j) : ∀ n t, t < j → ∀ x, x ∈ clsOf j t n → x < j := by
  intro n
  induction n with
  | zero => intro t _ x hx; exact absurd hx (by simp [clsOf])
  | succ k ih =>
    intro t ht x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ht
    · exact ih ((t+1) % j) (Nat.mod_lt _ hj) x hx'

/--
@isnad1 id=eq.2h3v.s6.d97e54c28e17 from=translated src=- shape=f26845ca vocab=75fd5c47
-/
theorem clsOf_snoc {j : Nat} (hj : 0 < j) : ∀ n t, t < j →
    clsOf j t (n + 1) = clsOf j t n ++ [(t + n) % j] := by
  intro n
  induction n with
  | zero => intro t ht; show [t] = [] ++ [(t + 0) % j]; rw [Nat.add_zero, Nat.mod_eq_of_lt ht]; rfl
  | succ k ih =>
    intro t ht
    show t :: clsOf j ((t+1) % j) (k+1) = (t :: clsOf j ((t+1) % j) k) ++ [(t + (k+1)) % j]
    rw [ih ((t+1) % j) (Nat.mod_lt _ hj)]
    show t :: (clsOf j ((t+1) % j) k ++ [((t+1) % j + k) % j])
        = t :: (clsOf j ((t+1) % j) k ++ [(t + (k+1)) % j])
    rw [Nat.mod_add_mod, show t + 1 + k = t + (k+1) from by omega]

/-- `wsum` is `wcls` against the slot-class list — the bridge from the file's
existing block congruence to the arrangement built here.
@isnad1 id=eq.0h4v.s4.666508bf6368 from=translated src=- shape=57ccd384 vocab=053b4397
-/
theorem wsum_eq_wcls (b j : Nat) : ∀ (ds : List Nat) (t : Nat),
    wsum b j t ds = wcls b (clsOf j t ds.length) ds := by
  intro ds
  induction ds with
  | nil => intro t; rfl
  | cons d ds ih =>
    intro t
    show b ^ t * d + wsum b j ((t+1) % j) ds = wcls b (t :: clsOf j ((t+1) % j) ds.length) (d :: ds)
    rw [ih]
    rfl

/--
@isnad1 id=eq.1h5v.s6.989093add68f from=translated src=- shape=bbfa9e62 vocab=fd3447d0
-/
theorem wcls_append (b : Nat) : ∀ (l1 : List Nat) (d1 : List Nat) (l2 d2 : List Nat),
    l1.length = d1.length →
    wcls b (l1 ++ l2) (d1 ++ d2) = wcls b l1 d1 + wcls b l2 d2 := by
  intro l1
  induction l1 with
  | nil =>
    intro d1 l2 d2 h
    have : d1 = [] := List.eq_nil_of_length_eq_zero h.symm
    subst this
    show wcls b l2 d2 = 0 + wcls b l2 d2
    omega
  | cons t cs ih =>
    intro d1 l2 d2 h
    cases d1 with
    | nil => exact absurd h (by simp)
    | cons d ds =>
      show b ^ t * d + wcls b (cs ++ l2) (ds ++ d2) = b ^ t * d + wcls b cs ds + wcls b l2 d2
      rw [ih ds l2 d2 (by simpa using h)]
      omega

/-- The `j` classes account for every slot.
@isnad1 id=eq.1h2v.s5.843af057733c from=translated src=- shape=c73949eb vocab=273a8dc4
-/
theorem sumRange_occ_length {j : Nat} : ∀ (l : List Nat), (∀ x, x ∈ l → x < j) →
    sumRange (fun t => occ t l) j = l.length := by
  intro l
  induction l with
  | nil =>
    intro _
    show sumRange (fun t => occ t ([] : List Nat)) j = 0
    have : ∀ n, sumRange (fun t => occ t ([] : List Nat)) n = 0 := by
      intro n; induction n with
      | zero => rfl
      | succ k ihk => show sumRange _ k + occ k ([] : List Nat) = 0; rw [ihk]; rfl
    exact this j
  | cons t0 cs ih =>
    intro hmem
    have ht0 : t0 < j := hmem t0 List.mem_cons_self
    have := sumRange_update (f := fun t => occ t (t0 :: cs)) (g := fun t => occ t cs)
      (t0 := t0) (x := 1) j ht0
      (by intro t hne
          show occ t cs = occ t (t0 :: cs)
          show occ t cs = (if t0 = t then 1 else 0) + occ t cs
          rw [ite_eq_right (fun hh => hne hh.symm)]
          omega)
      (by rw [occ_cons_self])
    rw [← this, ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))]
    show 1 + cs.length = cs.length + 1
    omega

/--
@isnad1 id=eq.0h3v.s5.cf9f7b37ec9e from=translated src=- shape=9bf0e71e vocab=5bc23739
-/
theorem sumRange_add (f g : Nat → Nat) : ∀ n,
    sumRange (fun t => f t + g t) n = sumRange f n + sumRange g n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumRange (fun t => f t + g t) k + (f k + g k) = (sumRange f k + f k) + (sumRange g k + g k)
    rw [ih]; omega

/--
@isnad1 id=eq.0h3v.s5.cfaa8d8981de from=translated src=- shape=bcfac8c9 vocab=23da36ea
-/
theorem sumRange_mul (k : Nat) (f : Nat → Nat) : ∀ n,
    k * sumRange f n = sumRange (fun t => k * f t) n := by
  intro n
  induction n with
  | zero => show k * 0 = 0; omega
  | succ m ih => show k * (sumRange f m + f m) = sumRange (fun t => k * f t) m + k * f m
                 rw [← ih, Nat.mul_add]

/--
@isnad1 id=eq.0h2v.s5.0488e31e0e18 from=translated src=- shape=63c28c72 vocab=5bc23739
-/
theorem sumRange_front (f : Nat → Nat) : ∀ n,
    sumRange f (n + 1) = f 0 + sumRange (fun t => f (t + 1)) n := by
  intro n
  induction n with
  | zero => show (0 : Nat) + f 0 = f 0 + 0; omega
  | succ k ih =>
    show sumRange f (k+1) + f (k+1) = f 0 + (sumRange (fun t => f (t+1)) k + f (k+1))
    rw [ih]; omega

/-! ### Cyclic indices -/

/-- The next class, cyclically.-/
def nxt (j t : Nat) : Nat := (t + 1) % j

/-- The previous class, cyclically.-/
def prv (j t : Nat) : Nat := (t + (j - 1)) % j

/--
@isnad1 id=lt.1h2v.s4.638464145109 from=translated src=- shape=7155da86 vocab=b788b02f
-/
theorem nxt_lt {j : Nat} (hj : 0 < j) (t : Nat) : nxt j t < j := Nat.mod_lt _ hj

/--
@isnad1 id=lt.1h2v.s4.8fe103d0596e from=translated src=- shape=7155da86 vocab=f9787ea1
-/
theorem prv_lt {j : Nat} (hj : 0 < j) (t : Nat) : prv j t < j := Nat.mod_lt _ hj

/--
@isnad1 id=eq.2h2v.s4.965e27bfd4df from=translated src=- shape=908806d4 vocab=62d7deb3
-/
theorem nxt_prv {j : Nat} (hj : 0 < j) {t : Nat} (ht : t < j) : nxt j (prv j t) = t := by
  show ((t + (j-1)) % j + 1) % j = t
  rw [Nat.mod_add_mod, show t + (j-1) + 1 = t + j from by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt ht]

/--
@isnad1 id=eq.1h1v.s5.fb4994ed89f4 from=translated src=- shape=6a311c38 vocab=9c680410
-/
theorem prv_zero {j : Nat} (hj : 0 < j) : prv j 0 = j - 1 := by
  show (0 + (j-1)) % j = j - 1
  rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]

/--
@isnad1 id=eq.2h2v.s5.ea9b060b4532 from=translated src=- shape=d6266a87 vocab=cdfc7d37
-/
theorem prv_succ {j t : Nat} (hj : 0 < j) (ht : t + 1 < j) : prv j (t + 1) = t := by
  show (t + 1 + (j-1)) % j = t
  rw [show t + 1 + (j-1) = t + j from by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Summing a function of the previous class is summing the function.
@isnad1 id=eq.1h2v.s4.169464d0297d from=translated src=- shape=1872b284 vocab=1ae7f7a3
-/
theorem sumRange_prv {j : Nat} (hj : 0 < j) (f : Nat → Nat) :
    sumRange (fun t => f (prv j t)) j = sumRange f j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [sumRange_front (fun t => f (prv (m+1) t)) m]
  show f (prv (m+1) 0) + sumRange (fun t => f (prv (m+1) (t+1))) m = sumRange f m + f m
  rw [prv_zero (by omega),
      sumRange_congr (f := fun t => f (prv (m+1) (t+1))) (g := f) m
        (by intro t ht; rw [prv_succ (by omega) (by omega)])]
  show f m + sumRange f m = sumRange f m + f m
  omega

/-- …and so is summing a function of the next class.
@isnad1 id=eq.1h2v.s4.2eaa66f05857 from=translated src=- shape=1872b284 vocab=be00d5e1
-/
theorem sumRange_nxt {j : Nat} (hj : 0 < j) (f : Nat → Nat) :
    sumRange (fun t => f (nxt j t)) j = sumRange f j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  show sumRange (fun t => f (nxt (m+1) t)) m + f (nxt (m+1) m) = sumRange f (m+1)
  rw [sumRange_congr (f := fun t => f (nxt (m+1) t)) (g := fun t => f (t+1)) m
        (by intro t ht; show f ((t+1) % (m+1)) = f (t+1); rw [Nat.mod_eq_of_lt (by omega)]),
      show nxt (m+1) m = 0 from by show (m+1) % (m+1) = 0; simp,
      sumRange_front f m]
  omega

/-- Consecutive runs tile `[0, Σ a)`.
@isnad1 id=eq.0h3v.s5.b0740012c3f5 from=translated src=- shape=4351c90e vocab=271b09d3
-/
theorem occ_runs (v : Nat) (a : Nat → Nat) : ∀ n,
    sumRange (fun t => occ v (run (sumRange a t) (a t))) n = occ v (run 0 (sumRange a n)) := by
  intro n
  induction n with
  | zero => show 0 = occ v (run 0 0); rfl
  | succ k ih =>
    show sumRange (fun t => occ v (run (sumRange a t) (a t))) k
        + occ v (run (sumRange a k) (a k)) = occ v (run 0 (sumRange a k + a k))
    rw [ih, run_add 0 (sumRange a k) (a k), occ_append, Nat.zero_add]

/-! ### The blocks -/

/-- How many values run `t` passes up to class `t+1`.-/
def qOf (j : Nat) (c p : Nat → Nat) (t : Nat) : Nat := c (nxt j t) - p (nxt j t)

/-- The length of run `t`.-/
def aOf (j : Nat) (c p : Nat → Nat) (t : Nat) : Nat := p t + qOf j c p t

/-- Where run `t` starts.-/
def offOf (j : Nat) (c p : Nat → Nat) (t : Nat) : Nat := sumRange (aOf j c p) t

/-- Run `t`, split into what it keeps for class `t` and what it passes up to
class `t+1`.-/
def picked (j : Nat) (c p ν : Nat → Nat) (t : Nat) : List Nat × List Nat :=
  pick (offOf j c p t) (p t) (qOf j c p t) (ν t)

/-- Class `t`'s block: what run `t` keeps, plus what run `t-1` passes up.-/
def blk (j : Nat) (c p ν : Nat → Nat) (t : Nat) : List Nat :=
  (picked j c p ν t).1 ++ (picked j c p ν (prv j t)).2

/--
@isnad1 id=eq.2h4v.s5.a8f26c6d8a76 from=translated src=- shape=850184d3 vocab=58e99c9e
-/
theorem qOf_prv {j : Nat} (hj : 0 < j) (c p : Nat → Nat) {t : Nat} (ht : t < j) :
    qOf j c p (prv j t) = c t - p t := by
  show c (nxt j (prv j t)) - p (nxt j (prv j t)) = _
  rw [nxt_prv hj ht]

/--
@isnad1 id=eq.3h5v.s5.644bdbff4e2e from=translated src=- shape=ac6a3a8f vocab=7f1400d3
-/
theorem blk_length {j : Nat} (hj : 0 < j) (c p ν : Nat → Nat)
    (hpc : ∀ t, t < j → p t ≤ c t) {t : Nat} (ht : t < j) :
    (blk j c p ν t).length = c t := by
  rw [blk, List.length_append, picked, picked, pick_len1, pick_len2, qOf_prv hj c p ht]
  have := hpc t ht
  omega

/--
@isnad1 id=eq.2h3v.s5.012dbb41a62b from=translated src=- shape=7b5f3eaa vocab=67619149
-/
theorem sum_aOf {j : Nat} (hj : 0 < j) (c p : Nat → Nat)
    (hpc : ∀ t, t < j → p t ≤ c t) : sumRange (aOf j c p) j = sumRange c j := by
  have h1' : sumRange (aOf j c p) j
      = sumRange p j + sumRange (fun t => c (nxt j t) - p (nxt j t)) j := by
    rw [← sumRange_add]
    exact sumRange_congr j (fun t _ => rfl)
  rw [h1', sumRange_nxt hj (fun u => c u - p u), ← sumRange_add]
  exact sumRange_congr j (fun t ht => by have := hpc t ht; omega)

/--
@isnad1 id=eq.1h5v.s5.aa430e36ccc9 from=translated src=- shape=fc48b4be vocab=ffbbcc67
-/
theorem blk_occ {j : Nat} (hj : 0 < j) (c p ν : Nat → Nat) (v : Nat) :
    sumRange (fun t => occ v (blk j c p ν t)) j
      = occ v (run 0 (sumRange (aOf j c p) j)) := by
  have h1' : sumRange (fun t => occ v (blk j c p ν t)) j
      = sumRange (fun t => occ v (picked j c p ν t).1) j
        + sumRange (fun t => occ v (picked j c p ν (prv j t)).2) j := by
    rw [← sumRange_add]
    exact sumRange_congr j (fun t _ => occ_append v _ _)
  rw [h1', sumRange_prv hj (fun t => occ v (picked j c p ν t).2), ← sumRange_add,
      sumRange_congr (f := fun t => occ v (picked j c p ν t).1 + occ v (picked j c p ν t).2)
        (g := fun t => occ v (run (offOf j c p t) (aOf j c p t))) j
        (fun t _ => pick_occ v (offOf j c p t) (p t) (qOf j c p t) (ν t)),
      ← occ_runs v (aOf j c p) j]
  exact sumRange_congr j (fun t _ => rfl)

/-- The wraparound: reading the block totals with weight `b^(t+1)` differs from
reading them with `b^t` at the previous class by one multiple of `b^j - 1`.
@isnad1 id=eq.2h3v.s7.82daffcf10c9 from=translated src=- shape=3f915922 vocab=7ca3b9fd
-/
theorem wrap_sum {b j : Nat} (hb : 0 < b) (hj : 0 < j) (τ : Nat → Nat) :
    sumRange (fun t => b ^ t * τ (prv j t)) j + (b ^ j - 1) * τ (j - 1)
      = sumRange (fun t => b ^ (t + 1) * τ t) j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hpow : 1 ≤ b ^ (m + 1) := Nat.one_le_pow _ _ hb
  rw [sumRange_front (fun t => b ^ t * τ (prv (m+1) t)) m]
  show b ^ 0 * τ (prv (m+1) 0) + sumRange (fun t => b ^ (t+1) * τ (prv (m+1) (t+1))) m
      + (b ^ (m+1) - 1) * τ (m + 1 - 1) = sumRange (fun t => b ^ (t+1) * τ t) m + b ^ (m+1) * τ m
  rw [prv_zero (by omega), Nat.pow_zero, Nat.one_mul,
      sumRange_congr (f := fun t => b ^ (t+1) * τ (prv (m+1) (t+1)))
        (g := fun t => b ^ (t+1) * τ t) m
        (by intro t ht; rw [prv_succ (by omega) (by omega)]),
      show m + 1 - 1 = m from by omega]
  have : (b ^ (m+1) - 1) * τ m + τ m = b ^ (m+1) * τ m := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  omega

/-- **The exact identity.**  `X` is the arrangement's block-sum value; increasing
the kept-sums by one moves `X` down by `b-1` times that, up to one wrap of
`b^j - 1`.  No congruence yet: this is an equation in `ℕ`.
@isnad1 id=eq.2h5v.s8.032e316d5d06 from=translated src=- shape=6413593b vocab=8cc3e4e7
-/
theorem blk_identity {b j : Nat} (hb : 0 < b) (hj : 0 < j) (c p ν : Nat → Nat) :
    sumRange (fun t => b ^ t * (blk j c p ν t).sum) j
        + (b - 1) * sumRange (fun t => b ^ t * (picked j c p ν t).1.sum) j
        + (b ^ j - 1) * (picked j c p ν (j - 1)).2.sum
      = sumRange (fun t => b ^ (t + 1) * (run (offOf j c p t) (aOf j c p t)).sum) j := by
  have hsplit : sumRange (fun t => b ^ t * (blk j c p ν t).sum) j
      = sumRange (fun t => b ^ t * (picked j c p ν t).1.sum) j
        + sumRange (fun t => b ^ t * (picked j c p ν (prv j t)).2.sum) j := by
    rw [← sumRange_add]
    exact sumRange_congr j (fun t _ => by
      show b ^ t * ((picked j c p ν t).1 ++ (picked j c p ν (prv j t)).2).sum = _
      rw [List.sum_append, Nat.mul_add])
  rw [hsplit]
  have hw := wrap_sum hb hj (fun t => (picked j c p ν t).2.sum)
  have hb1 : (b - 1) * sumRange (fun t => b ^ t * (picked j c p ν t).1.sum) j
      + sumRange (fun t => b ^ t * (picked j c p ν t).1.sum) j
      = sumRange (fun t => b ^ (t+1) * (picked j c p ν t).1.sum) j := by
    rw [← Nat.succ_mul]
    show (b - 1 + 1) * sumRange (fun t => b ^ t * (picked j c p ν t).1.sum) j = _
    rw [show b - 1 + 1 = b from by omega, sumRange_mul]
    exact sumRange_congr j (fun t _ => by rw [← Nat.mul_assoc, ← Nat.pow_succ'])
  have hfin : sumRange (fun t => b ^ (t+1) * (picked j c p ν t).1.sum) j
      + sumRange (fun t => b ^ (t+1) * (picked j c p ν t).2.sum) j
      = sumRange (fun t => b ^ (t + 1) * (run (offOf j c p t) (aOf j c p t)).sum) j := by
    rw [← sumRange_add]
    refine sumRange_congr j (fun t _ => ?_)
    rw [← Nat.mul_add]
    congr 1
    exact pick_sum_total _ _ _ _
  omega

/-! ### The coset `{z : z ≡ T (mod b-1)}` inside `ℤ/(b^j-1)` -/

/-- `1 + b + … + b^(j-1)` — the number of residues mod `b^j - 1` that the
digit-sum congruence leaves open.  Kept as a sum, so no division appears.-/
def cosetSize (b j : Nat) : Nat := sumRange (fun t => b ^ t) j

/--
@isnad1 id=eq.1h2v.s5.911093f43ff2 from=translated src=- shape=80240b51 vocab=d209cd09
-/
theorem geom {b : Nat} (hb : 1 ≤ b) : ∀ j, (b - 1) * cosetSize b j + 1 = b ^ j := by
  intro j
  induction j with
  | zero => show (b - 1) * 0 + 1 = 1; omega
  | succ k ih =>
    show (b - 1) * (cosetSize b k + b ^ k) + 1 = b ^ (k + 1)
    rw [Nat.mul_add]
    have h1' : (b - 1) * b ^ k + b ^ k = b * b ^ k := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    rw [Nat.pow_succ, Nat.mul_comm (b ^ k) b, ← h1']
    omega

/--
@isnad1 id=lt.1h2v.s4.27ba0ad477da from=translated src=- shape=61bdc3e7 vocab=5696d9b6
-/
theorem cosetSize_pos {b j : Nat} (hj : 0 < j) : 0 < cosetSize b j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  show 0 < sumRange (fun t => b ^ t) (m + 1)
  rw [sumRange_front (fun t => b ^ t) m]
  show 0 < b ^ 0 + sumRange (fun t => b ^ (t + 1)) m
  rw [Nat.pow_zero]
  omega

/-- **The coset is a cycle.**  Inside `ℤ/(g·K)`, the residues congruent to a
given value mod `g` are the `K` numbers `z, z+g, …, z+(K-1)g`; so any two
members of the class are joined by adding `g` some `W < K` times.
@isnad1 id=ex.2h4v.s6.2ab85a321e7f from=translated src=- shape=4e3b8088 vocab=cb088a8e
-/
theorem coset_hit {g K z C : Nat} (hK : 0 < K) (h : z % g = C % g) :
    ∃ W, W < K ∧ (z + g * W) % (g * K) = C % (g * K) := by
  have hC := Nat.div_add_mod C g
  have hz := Nat.div_add_mod z g
  have hstep : g * (K - 1) + g = g * K := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  have hmul : g * ((K - 1) * (z / g)) + g * (z / g) = g * K * (z / g) := by
    rw [← Nat.mul_assoc, ← Nat.add_mul, hstep]
  have hD : g * (C / g + (K - 1) * (z / g))
      = g * (C / g) + g * ((K - 1) * (z / g)) := Nat.mul_add _ _ _
  have key : g * (C / g + (K - 1) * (z / g)) + z = C + g * K * (z / g) := by omega
  refine ⟨(C / g + (K - 1) * (z / g)) % K, Nat.mod_lt _ hK, ?_⟩
  have hDK := Nat.div_add_mod (C / g + (K - 1) * (z / g)) K
  have hsplit : g * (C / g + (K - 1) * (z / g))
      = g * K * ((C / g + (K - 1) * (z / g)) / K)
        + g * ((C / g + (K - 1) * (z / g)) % K) := by
    rw [Nat.mul_assoc, ← Nat.mul_add, hDK]
  have hfin : z + g * ((C / g + (K - 1) * (z / g)) % K)
      + g * K * ((C / g + (K - 1) * (z / g)) / K) = C + g * K * (z / g) := by omega
  have h1' : (z + g * ((C / g + (K - 1) * (z / g)) % K)
      + g * K * ((C / g + (K - 1) * (z / g)) / K)) % (g * K)
      = (z + g * ((C / g + (K - 1) * (z / g)) % K)) % (g * K) :=
    Nat.add_mul_mod_self_left _ _ _
  have h2' : (C + g * K * (z / g)) % (g * K) = C % (g * K) := Nat.add_mul_mod_self_left _ _ _
  rw [← h1', hfin, h2']

/-! ### Where the digit `0` lands -/

/--
@isnad1 id=eq.2h3v.s5.4169cf69fa87 from=translated src=- shape=3e7781b1 vocab=4902b010
-/
theorem sumRange_eq_zero {f : Nat → Nat} : ∀ n, sumRange f n = 0 → ∀ t, t < n → f t = 0 := by
  intro n
  induction n with
  | zero => intro _ t ht; omega
  | succ k ih =>
    intro h t ht
    have h' : sumRange f k + f k = 0 := h
    rcases Nat.lt_or_ge t k with hlt | hge
    · exact ih (by omega) t hlt
    · have : t = k := by omega
      subst this; omega

/--
@isnad1 id=ex.1h2v.s5.f92361c69dac from=translated src=- shape=7226ae70 vocab=4902b010
-/
theorem sumRange_eq_one {f : Nat → Nat} : ∀ n, sumRange f n = 1 →
    ∃ t0, t0 < n ∧ f t0 = 1 ∧ ∀ t, t < n → t ≠ t0 → f t = 0 := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by simp [sumRange])
  | succ k ih =>
    intro h
    have h' : sumRange f k + f k = 1 := h
    rcases Nat.eq_zero_or_pos (f k) with hk | hk
    · obtain ⟨t0, ht0, hf, hz⟩ := ih (by omega)
      exact ⟨t0, by omega, hf, fun t ht hne => by
        rcases Nat.lt_or_ge t k with hlt | hge
        · exact hz t hlt hne
        · have : t = k := by omega
          subst this; exact hk⟩
    · refine ⟨k, by omega, by omega, fun t ht hne => ?_⟩
      exact sumRange_eq_zero k (by omega) t (by omega)

/-! ### Reading a list by index, and moving the `0` -/

/-- The value at index `m`, read through `drop` so that no `Fin` is needed.-/
def nth (l : List Nat) (m : Nat) : Nat := (l.drop m).headD 0

/--
@isnad1 id=ne.2h2v.s5.de211b33e993 from=translated src=- shape=3ed661f7 vocab=ff3c5d04
-/
theorem nth_ne_zero : ∀ (l : List Nat), occ 0 l = 0 → ∀ m, m < l.length → nth l m ≠ 0 := by
  intro l
  induction l with
  | nil => intro _ m hm; exact absurd hm (by simp)
  | cons x xs ih =>
    intro h0 m hm
    have hx : x ≠ 0 ∧ occ 0 xs = 0 := by
      have : (if x = 0 then 1 else 0) + occ 0 xs = 0 := h0
      by_cases hx0 : x = 0
      · rw [ite_eq_left hx0] at this; omega
      · exact ⟨hx0, by rw [ite_eq_right hx0] at this; omega⟩
    cases m with
    | zero => show (x :: xs).headD 0 ≠ 0; exact hx.1
    | succ i => exact ih hx.2 i (by simpa using hm)

/--
@isnad1 id=eq.1h3v.s5.f442960465d2 from=translated src=- shape=807fdf82 vocab=2f0edb01
-/
theorem nth_append_left : ∀ (l1 : List Nat) (l2 : List Nat) (m : Nat), m < l1.length →
    nth (l1 ++ l2) m = nth l1 m := by
  intro l1
  induction l1 with
  | nil => intro l2 m hm; exact absurd hm (by simp)
  | cons x xs ih =>
    intro l2 m hm
    cases m with
    | zero => rfl
    | succ i => exact ih l2 i (by simpa using hm)

/--
@isnad1 id=eq.1h3v.s5.1b49a5bf975c from=translated src=- shape=de68e6a1 vocab=23654af7
-/
theorem nth_append_right : ∀ (l1 : List Nat) (l2 : List Nat) (m : Nat), l1.length ≤ m →
    nth (l1 ++ l2) m = nth l2 (m - l1.length) := by
  intro l1
  induction l1 with
  | nil => intro l2 m _; rfl
  | cons x xs ih =>
    intro l2 m hm
    cases m with
    | zero => exact absurd hm (by simp)
    | succ i =>
      have h : xs.length ≤ i := by simpa using hm
      show nth (xs ++ l2) i = nth l2 (i + 1 - (xs.length + 1))
      rw [ih l2 i h]
      congr 1
      omega

/-- `l` with a `0` inserted at index `k`.-/
def ins0 (k : Nat) (l : List Nat) : List Nat := l.take k ++ 0 :: l.drop k

/--
@isnad1 id=eq.0h3v.s4.a9272a713a07 from=translated src=- shape=59e8783a vocab=3ca35259
-/
theorem ins0_occ (k : Nat) (l : List Nat) (v : Nat) : occ v (ins0 k l) = occ v (0 :: l) := by
  show occ v (l.take k ++ 0 :: l.drop k) = (if 0 = v then 1 else 0) + occ v l
  rw [occ_append]
  show occ v (l.take k) + ((if 0 = v then 1 else 0) + occ v (l.drop k)) = _
  have := occ_append v (l.take k) (l.drop k)
  rw [List.take_append_drop] at this
  omega

/--
@isnad1 id=eq.0h2v.s4.7e52342e84f6 from=translated src=- shape=f0fb6b79 vocab=5866ebb9
-/
theorem ins0_sum (k : Nat) (l : List Nat) : (ins0 k l).sum = l.sum := by
  show (l.take k ++ 0 :: l.drop k).sum = l.sum
  rw [List.sum_append]
  show (l.take k).sum + (0 + (l.drop k).sum) = l.sum
  -- `l₁`/`l₂` are core's own parameter names for `List.sum_append`; this file's
  -- identifiers are ASCII, but a named argument must spell the callee's.
  have := List.sum_append (l₁ := l.take k) (l₂ := l.drop k)
  rw [List.take_append_drop] at this
  omega

/--
@isnad1 id=eq.1h2v.s5.28ef74176b48 from=translated src=- shape=2295992c vocab=326a677f
-/
theorem ins0_length {k : Nat} {l : List Nat} (hk : k ≤ l.length) :
    (ins0 k l).length = l.length + 1 := by
  show (l.take k ++ 0 :: l.drop k).length = l.length + 1
  rw [List.length_append, List.length_take, Nat.min_eq_left hk]
  show k + ((l.drop k).length + 1) = l.length + 1
  rw [List.length_drop]
  omega

/-- Away from index `k`, the inserted list has no zeros — which is exactly what
a leading digit needs.
@isnad1 id=ne.4h3v.s6.83405091a473 from=translated src=- shape=429b0cbc vocab=0e3b23ec
-/
theorem ins0_nth_ne {k : Nat} {l : List Nat} (h0 : occ 0 l = 0) (hk : k ≤ l.length)
    {m : Nat} (hm : m < l.length + 1) (hmk : m ≠ k) : nth (ins0 k l) m ≠ 0 := by
  have hsplit := occ_append 0 (l.take k) (l.drop k)
  rw [List.take_append_drop, h0] at hsplit
  have htk : (l.take k).length = k := by rw [List.length_take, Nat.min_eq_left hk]
  have hdk : (l.drop k).length = l.length - k := List.length_drop
  rcases Nat.lt_or_ge m k with hlt | hge
  · show nth (l.take k ++ 0 :: l.drop k) m ≠ 0
    rw [nth_append_left _ _ m (by omega)]
    exact nth_ne_zero _ (by omega) m (by omega)
  · have hgt : k < m := by omega
    show nth (l.take k ++ 0 :: l.drop k) m ≠ 0
    rw [nth_append_right _ _ m (by omega), htk]
    have : m - k = (m - k - 1) + 1 := by omega
    rw [this]
    show nth (l.drop k) (m - k - 1) ≠ 0
    exact nth_ne_zero _ (by omega) _ (by omega)

/-- Dropping the zeros of a list: same sum, same non-zero values.-/
def dropZeros : List Nat → List Nat
  | [] => []
  | x :: xs => if x = 0 then dropZeros xs else x :: dropZeros xs

/--
@isnad1 id=eq.0h1v.s4.7631aae47d29 from=translated src=- shape=d2a47a63 vocab=5ad587c7
-/
theorem dropZeros_occ_zero : ∀ l : List Nat, occ 0 (dropZeros l) = 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show occ 0 (if x = 0 then dropZeros xs else x :: dropZeros xs) = 0
    by_cases h : x = 0
    · rw [ite_eq_left h]; exact ih
    · rw [ite_eq_right h]; show (if x = 0 then 1 else 0) + occ 0 (dropZeros xs) = 0
      rw [ite_eq_right h]; omega

/--
@isnad1 id=eq.1h2v.s4.cff333e3f14f from=translated src=- shape=06df6ac0 vocab=5ad587c7
-/
theorem dropZeros_occ {v : Nat} (hv : v ≠ 0) : ∀ l : List Nat, occ v (dropZeros l) = occ v l := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show occ v (if x = 0 then dropZeros xs else x :: dropZeros xs)
        = (if x = v then 1 else 0) + occ v xs
    by_cases h : x = 0
    · rw [ite_eq_left h, ih, ite_eq_right (by omega : ¬ x = v)]; omega
    · rw [ite_eq_right h]; show (if x = v then 1 else 0) + occ v (dropZeros xs) = _
      rw [ih]

/--
@isnad1 id=eq.0h1v.s4.3a7bacb6e2dd from=translated src=- shape=744721d0 vocab=4c2dfca9
-/
theorem dropZeros_sum : ∀ l : List Nat, (dropZeros l).sum = l.sum := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show (if x = 0 then dropZeros xs else x :: dropZeros xs).sum = x + xs.sum
    by_cases h : x = 0
    · rw [ite_eq_left h, ih, h]; omega
    · rw [ite_eq_right h]; show x + (dropZeros xs).sum = _; rw [ih]

/--
@isnad1 id=eq.1h1v.s4.352012e93765 from=translated src=- shape=7439e570 vocab=51fed8bd
-/
theorem dropZeros_length_zero : ∀ l : List Nat, occ 0 l = 0 →
    (dropZeros l).length = l.length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    have h' : (if x = 0 then 1 else 0) + occ 0 xs = 0 := h
    have hxne : x ≠ 0 := by
      intro hx0
      rw [ite_eq_left hx0] at h'
      omega
    rw [ite_eq_right hxne] at h'
    show (if x = 0 then dropZeros xs else x :: dropZeros xs).length = xs.length + 1
    rw [ite_eq_right hxne]
    show (dropZeros xs).length + 1 = xs.length + 1
    rw [ih (by omega)]

/--
@isnad1 id=eq.1h1v.s5.b90f235f9669 from=translated src=- shape=eb12f33d vocab=3b17eabf
-/
theorem dropZeros_length : ∀ l : List Nat, occ 0 l = 1 →
    (dropZeros l).length + 1 = l.length := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by decide)
  | cons x xs ih =>
    intro h
    have h' : (if x = 0 then 1 else 0) + occ 0 xs = 1 := h
    show (if x = 0 then dropZeros xs else x :: dropZeros xs).length + 1 = xs.length + 1
    rcases Nat.eq_zero_or_pos x with hx | hx
    · rw [ite_eq_left hx]
      rw [ite_eq_left hx] at h'
      rw [dropZeros_length_zero xs (by omega)]
    · have hxne : x ≠ 0 := by omega
      rw [ite_eq_right hxne]
      rw [ite_eq_right hxne] at h'
      show (dropZeros xs).length + 1 + 1 = xs.length + 1
      rw [ih (by omega)]

/--
@isnad1 id=eq.1h2v.s5.b86d350982ee from=translated src=- shape=81f55e72 vocab=4902b010
-/
theorem sumRange_zero {f : Nat → Nat} : ∀ n, (∀ t, t < n → f t = 0) → sumRange f n = 0 := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    show sumRange f k + f k = 0
    rw [ih (fun t ht => h t (by omega)), h k (by omega)]

/--
@isnad1 id=eq.1h4v.s6.2937e51f3e06 from=translated src=- shape=8cfc6517 vocab=4e2a050f
-/
theorem sumRange_mod_congr {f g : Nat → Nat} {d : Nat} : ∀ n,
    (∀ t, t < n → f t % d = g t % d) → sumRange f n % d = sumRange g n % d := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    show (sumRange f k + f k) % d = (sumRange g k + g k) % d
    rw [Nat.add_mod, ih (fun t ht => h t (by omega)), h k (by omega), ← Nat.add_mod]

/--
@isnad1 id=mem.1h2v.s4.08dcd18ab2ab from=translated src=- shape=7f7f1c27 vocab=c88483c0
-/
theorem mem_of_occ_pos : ∀ (l : List Nat) (t : Nat), 0 < occ t l → t ∈ l := by
  intro l
  induction l with
  | nil => intro t h; exact absurd h (by simp [occ_nil])
  | cons x xs ih =>
    intro t h
    by_cases hx : x = t
    · exact hx ▸ List.mem_cons_self
    · refine List.mem_cons_of_mem _ (ih t ?_)
      have hh : occ t (x :: xs) = (if x = t then 1 else 0) + occ t xs := rfl
      rw [ite_eq_right hx] at hh
      omega

/--
@isnad1 id=eq.1h3v.s4.49a29e621ed6 from=translated src=- shape=9029dd0f vocab=71045009
-/
theorem occ_run_lt : ∀ n s v, v < s → occ v (run s n) = 0 := by
  intro n
  induction n with
  | zero => intro s v _; rfl
  | succ k ih =>
    intro s v hv
    show (if s = v then 1 else 0) + occ v (run (s+1) k) = 0
    rw [ite_eq_right (by omega), ih (s+1) v (by omega)]

/-- Every value below `b` occurs exactly once in `run 0 b`.
@isnad1 id=eq.2h3v.s5.7de13e907d1b from=translated src=- shape=eb7a0f99 vocab=e89e8ac3
-/
theorem occ_run : ∀ n s v, s ≤ v → v < s + n → occ v (run s n) = 1 := by
  intro n
  induction n with
  | zero => intro s v h1' h2'; omega
  | succ k ih =>
    intro s v h1' h2'
    show (if s = v then 1 else 0) + occ v (run (s+1) k) = 1
    by_cases h : s = v
    · rw [ite_eq_left h, occ_run_lt k (s+1) v (by omega)]
    · rw [ite_eq_right h, ih (s+1) v (by omega) (by omega)]

/-- Consecutive runs tile `[0, Σ a)` — the sum form.
@isnad1 id=eq.0h2v.s5.36a025e211c4 from=translated src=- shape=cf5d1da5 vocab=c87320db
-/
theorem sum_runs (a : Nat → Nat) : ∀ n,
    sumRange (fun t => (run (sumRange a t) (a t)).sum) n = (run 0 (sumRange a n)).sum := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumRange (fun t => (run (sumRange a t) (a t)).sum) k + (run (sumRange a k) (a k)).sum
        = (run 0 (sumRange a k + a k)).sum
    rw [ih, run_add 0 (sumRange a k) (a k), List.sum_append, Nat.zero_add]

/-! ### From blocks to a pair of digit lists -/

/-- **Realisation.**  Blocks of the right sizes become a pandigital pair of digit
lists: value-for-value the same multiset, and block `t` is charged weight `b^t`,
which is exactly what the block congruence sees.
@isnad1 id=and.2h5v.s8.d3cfec8089be from=translated src=- shape=9ad5b728 vocab=3445f61b
-/
theorem realise_pair {b j L1 L2 : Nat} (hj : 0 < j) (B : Nat → List Nat)
    (hlen : ∀ t, t < j → (B t).length = occ t (clsOf j 0 L1) + occ t (clsOf j 0 L2)) :
    ((deal B (clsOf j 0 L1)).1.length = L1) ∧
    ((deal (deal B (clsOf j 0 L1)).2 (clsOf j 0 L2)).1.length = L2) ∧
    (∀ v, occ v ((deal B (clsOf j 0 L1)).1
              ++ (deal (deal B (clsOf j 0 L1)).2 (clsOf j 0 L2)).1)
        = sumRange (fun t => occ v (B t)) j) ∧
    (wsum b j 0 (deal B (clsOf j 0 L1)).1
        + wsum b j 0 (deal (deal B (clsOf j 0 L1)).2 (clsOf j 0 L2)).1
      = sumRange (fun t => b ^ t * (B t).sum) j) := by
  have hmem : ∀ t, t ∈ (clsOf j 0 L1 ++ clsOf j 0 L2) → t < j := by
    intro t ht
    rcases List.mem_append.mp ht with h | h
    · exact clsOf_mem hj L1 0 hj t h
    · exact clsOf_mem hj L2 0 hj t h
  have hocc : ∀ t, occ t (clsOf j 0 L1 ++ clsOf j 0 L2) ≤ (B t).length := by
    intro t
    by_cases ht : t < j
    · rw [occ_append, hlen t ht]
      omega
    · have h1' : occ t (clsOf j 0 L1 ++ clsOf j 0 L2) = 0 := by
        rcases Nat.eq_zero_or_pos (occ t (clsOf j 0 L1 ++ clsOf j 0 L2)) with h | h
        · exact h
        · exact absurd (hmem t (mem_of_occ_pos _ t h)) ht
      omega
  have hres : ∀ t, t < j →
      (deal B (clsOf j 0 L1 ++ clsOf j 0 L2)).2 t = [] := by
    intro t ht
    rw [deal_res, occ_append, ← hlen t ht]
    exact List.drop_eq_nil_of_le (by omega)
  have happ := deal_app (clsOf j 0 L1) (clsOf j 0 L2) B
  refine ⟨by rw [deal_len, clsOf_length], by rw [deal_len, clsOf_length], ?_, ?_⟩
  · intro v
    rw [← happ]
    have h := deal_occ v j (clsOf j 0 L1 ++ clsOf j 0 L2) B hmem hocc
    rw [sumRange_zero j (fun t ht => by rw [hres t ht]; rfl)] at h
    omega
  · rw [wsum_eq_wcls, wsum_eq_wcls, deal_len, deal_len, clsOf_length, clsOf_length,
        ← wcls_append b (clsOf j 0 L1) _ _ _ (by rw [deal_len, clsOf_length]), ← happ]
    have h := deal_wcls b j (clsOf j 0 L1 ++ clsOf j 0 L2) B hmem hocc
    rw [sumRange_zero j (fun t ht => by rw [hres t ht]; rfl)] at h
    omega

/-- Any residue mod `K` is reachable by adding `V < K`.
@isnad1 id=ex.2h3v.s5.2829156776eb from=translated src=- shape=92bc0415 vocab=fd2b17b6
-/
theorem shift_mod {K M W : Nat} (hK : 0 < K) (hW : W < K) :
    ∃ V, V < K ∧ (M + V) % K = W := by
  have hr : M % K < K := Nat.mod_lt _ hK
  have hMr := Nat.div_add_mod M K
  by_cases hU : W + K - M % K < K
  · refine ⟨W + K - M % K, hU, ?_⟩
    have hrw : M + (W + K - M % K) = W + K * (M / K + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hW]
  · refine ⟨W + K - M % K - K, by omega, ?_⟩
    have hrw : M + (W + K - M % K - K) = W + K * (M / K) := by omega
    rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hW]

/-- `N_t = p_t·q_t`, the width of class `t`'s independent choice.-/
def Nof (j : Nat) (c p : Nat → Nat) (t : Nat) : Nat := p t * qOf j c p t

/-- **Theorem 5, block level.**  Under the no-gap hypothesis, the block-sum
value `Σ_t b^t S_t` of an arrangement with class sizes `c` runs over the whole
coset `{z : z ≡ T (mod b-1)}` of `ℤ/(b^j - 1)`.  Leading digits are not yet in
play; that is the next theorem's business.
@isnad1 id=ex.6h5v.s8.1ac00d50cb3e from=translated src=- shape=b970603c vocab=d2f691e6
-/
theorem blocks_hit {b j : Nat} (hb : 1 < b) (hj : 0 < j) (c p : Nat → Nat)
    (hpc : ∀ t, t < j → p t ≤ c t)
    (hgap : ∀ t, t < j → b ^ t ≤ sumRange (fun s => Nof j c p s * b ^ s) t + 1)
    (hreach : cosetSize b j ≤ sumRange (fun s => Nof j c p s * b ^ s) j + 1)
    {z : Nat} (hz : z % (b - 1) = (run 0 (sumRange c j)).sum % (b - 1)) :
    ∃ ν : Nat → Nat, (∀ t, ν t ≤ Nof j c p t) ∧
      sumRange (fun t => b ^ t * (blk j c p ν t).sum) j % (b ^ j - 1) = z % (b ^ j - 1) := by
  have hbpos : 0 < b := by omega
  have hbj : 2 ≤ b ^ j := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have : 1 ≤ b ^ i := Nat.one_le_pow _ _ hbpos
    rw [Nat.pow_succ]
    have := Nat.mul_le_mul_right (k := b) this
    omega
  have hm : (b - 1) * cosetSize b j = b ^ j - 1 := by
    have := geom (b := b) (by omega) j
    omega
  have hK : 0 < cosetSize b j := cosetSize_pos hj
  -- the constant the identity lands on
  have hac : sumRange (aOf j c p) j = sumRange c j := sum_aOf hj c p hpc
  have hA : sumRange (fun t => (run (offOf j c p t) (aOf j c p t)).sum) j
      = (run 0 (sumRange c j)).sum := by
    have h := sum_runs (aOf j c p) j
    rw [hac] at h
    exact h
  have hConst : sumRange (fun t => b ^ (t + 1) * (run (offOf j c p t) (aOf j c p t)).sum) j
      % (b - 1) = (run 0 (sumRange c j)).sum % (b - 1) := by
    rw [sumRange_mod_congr (g := fun t => (run (offOf j c p t) (aOf j c p t)).sum) j
          (fun t _ => by
            rw [Nat.mul_mod, pow_mod_pred (by omega : 1 ≤ b) (t + 1), ← Nat.mul_mod,
                Nat.one_mul]), hA]
  -- move the target into the coset coordinate
  obtain ⟨W, hWlt, hWeq⟩ := coset_hit (g := b - 1) (K := cosetSize b j) (z := z)
    (C := sumRange (fun t => b ^ (t + 1) * (run (offOf j c p t) (aOf j c p t)).sum) j)
    hK (by rw [hz, hConst])
  rw [hm] at hWeq
  obtain ⟨V, hVlt, hVeq⟩ := shift_mod (K := cosetSize b j)
    (M := sumRange (fun t => b ^ t * (p t * offOf j c p t + tri (p t))) j) (W := W) hK hWlt
  obtain ⟨ν, hν, hsum⟩ := cover_exists hbpos (Nof j c p) j hgap V (by omega)
  refine ⟨ν, hν, ?_⟩
  -- the kept-sums, in closed form
  have hsigma : sumRange (fun t => b ^ t * (picked j c p ν t).1.sum) j
      = sumRange (fun t => b ^ t * (p t * offOf j c p t + tri (p t))) j + V := by
    rw [sumRange_congr
          (g := fun t => b ^ t * (p t * offOf j c p t + tri (p t)) + ν t * b ^ t) j
          (fun t _ => by
            rw [picked, pick_sum (offOf j c p t) (p t) (qOf j c p t) (ν t) (hν t),
                Nat.mul_add, Nat.mul_comm (ν t) (b ^ t)]),
        sumRange_add, hsum]
  have hid := blk_identity (b := b) hbpos hj c p ν
  rw [hsigma] at hid
  -- and the arithmetic
  have hmpos : 0 < b ^ j - 1 := by omega
  have hMV := Nat.div_add_mod (sumRange (fun t => b ^ t * (p t * offOf j c p t + tri (p t))) j + V)
    (cosetSize b j)
  rw [hVeq] at hMV
  have hexp : (b - 1) * (sumRange (fun t => b ^ t * (p t * offOf j c p t + tri (p t))) j + V)
      = (b - 1) * W + (b ^ j - 1)
          * ((sumRange (fun t => b ^ t * (p t * offOf j c p t + tri (p t))) j + V)
              / cosetSize b j) := by
    have h1' : (b - 1) * (sumRange (fun t => b ^ t * (p t * offOf j c p t + tri (p t))) j + V)
        = (b - 1) * (cosetSize b j
            * ((sumRange (fun t => b ^ t * (p t * offOf j c p t + tri (p t))) j + V)
                / cosetSize b j) + W) := by
      rw [hMV]
    rw [h1', Nat.mul_add, ← Nat.mul_assoc, hm]
    omega
  refine mod_add_cancel hmpos (c :=
    (b - 1) * (sumRange (fun t => b ^ t * (p t * offOf j c p t + tri (p t))) j + V)
      + (b ^ j - 1) * (picked j c p ν (j - 1)).2.sum) ?_
  rw [← Nat.add_assoc, hid, hexp]
  have hfold : z + ((b - 1) * W + (b ^ j - 1)
      * ((sumRange (fun t => b ^ t * (p t * offOf j c p t + tri (p t))) j + V)
          / cosetSize b j) + (b ^ j - 1) * (picked j c p ν (j - 1)).2.sum)
      = z + (b - 1) * W + (b ^ j - 1)
          * (((sumRange (fun t => b ^ t * (p t * offOf j c p t + tri (p t))) j + V)
              / cosetSize b j) + (picked j c p ν (j - 1)).2.sum) := by
    rw [Nat.mul_add]
    omega
  rw [hfold, Nat.add_mul_mod_self_left, hWeq]

/-- The leading digit of a dealt list is the head of whatever is left of the
block named by the last slot.
@isnad1 id=eq.0h3v.s5.2543e04ad76c from=translated src=- shape=ac97f1c5 vocab=a2ed1828
-/
theorem deal_last (B : Nat → List Nat) (u : List Nat) (t : Nat) :
    nth (deal B (u ++ [t])).1 u.length = nth (B t) (occ t u) := by
  rw [deal_app]
  have hlen : (deal B u).1.length = u.length := deal_len u B
  rw [nth_append_right _ _ _ (by omega), hlen, Nat.sub_self]
  show nth [((deal B u).2 t).headD 0] 0 = nth (B t) (occ t u)
  rw [deal_res]
  rfl

/--
@isnad1 id=eq.0h1v.s4.8e68abff7334 from=translated src=- shape=ae5ce9d3 vocab=d39c1124
-/
theorem occ_single (x : Nat) : occ x [x] = 1 := by rw [occ_cons_self, occ_nil]

/--
@isnad1 id=eq.0h3v.s4.6b05576a18d1 from=translated src=- shape=886a4c87 vocab=5c8271e3
-/
theorem nth_drop (l : List Nat) (s m : Nat) : nth (l.drop s) m = nth l (s + m) := by
  show ((l.drop s).drop m).headD 0 = (l.drop (s + m)).headD 0
  rw [List.drop_drop]

/-- **The digit-list half.**  Blocks of the right sizes, holding each value once
and keeping `0` off the two leading slots, read out as a genuine pandigital pair
of digit lists whose sum the sieve sees as `Σ_t b^t S_t`.
@isnad1 id=ex.8h5v.s9.83689a240296 from=translated src=- shape=694f4f7a vocab=28297409
-/
theorem blocks_to_pair {b j L1 L2 : Nat} (hb : 1 < b) (hj : 0 < j)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (B : Nat → List Nat)
    (hlen : ∀ t, t < j → (B t).length = occ t (clsOf j 0 L1) + occ t (clsOf j 0 L2))
    (hone : ∀ v, v < b → sumRange (fun t => occ v (B t)) j = 1)
    (hlead1 : nth (B ((L1 - 1) % j)) (occ ((L1 - 1) % j) (clsOf j 0 L1) - 1) ≠ 0)
    (hlead2 : nth (B ((L2 - 1) % j))
        (occ ((L2 - 1) % j) (clsOf j 0 L1) + occ ((L2 - 1) % j) (clsOf j 0 L2) - 1) ≠ 0) :
    ∃ d1 d2 : List Nat,
      d1.length = L1 ∧ d2.length = L2 ∧
      (∀ v, v < b → occ v (d1 ++ d2) = 1) ∧
      nth d1 (L1 - 1) ≠ 0 ∧ nth d2 (L2 - 1) ≠ 0 ∧
      (valOf b d1 + valOf b d2) % (b ^ j - 1)
        = sumRange (fun t => b ^ t * (B t).sum) j % (b ^ j - 1) := by
  obtain ⟨hd1, hd2, hocc, hw⟩ := realise_pair (b := b) hj B hlen
  have hsplit1 : clsOf j 0 L1 = clsOf j 0 (L1 - 1) ++ [(L1 - 1) % j] := by
    have h := clsOf_snoc hj (L1 - 1) 0 hj
    rw [show L1 - 1 + 1 = L1 from by omega, Nat.zero_add] at h
    exact h
  have hsplit2 : clsOf j 0 L2 = clsOf j 0 (L2 - 1) ++ [(L2 - 1) % j] := by
    have h := clsOf_snoc hj (L2 - 1) 0 hj
    rw [show L2 - 1 + 1 = L2 from by omega, Nat.zero_add] at h
    exact h
  have hu1 : (clsOf j 0 (L1 - 1)).length = L1 - 1 := clsOf_length j (L1 - 1) 0
  have hu2 : (clsOf j 0 (L2 - 1)).length = L2 - 1 := clsOf_length j (L2 - 1) 0
  have hcnt1 : occ ((L1 - 1) % j) (clsOf j 0 L1)
      = occ ((L1 - 1) % j) (clsOf j 0 (L1 - 1)) + 1 := by
    rw [hsplit1, occ_append, occ_single]
  have hcnt2 : occ ((L2 - 1) % j) (clsOf j 0 L2)
      = occ ((L2 - 1) % j) (clsOf j 0 (L2 - 1)) + 1 := by
    rw [hsplit2, occ_append, occ_single]
  refine ⟨_, _, hd1, hd2, fun v hv => by rw [hocc v, hone v hv], ?_, ?_, ?_⟩
  · have hdl := deal_last B (clsOf j 0 (L1 - 1)) ((L1 - 1) % j)
    rw [hu1, ← hsplit1] at hdl
    rw [hcnt1] at hlead1
    rw [hdl]
    simpa using hlead1
  · have hdl := deal_last (deal B (clsOf j 0 L1)).2 (clsOf j 0 (L2 - 1)) ((L2 - 1) % j)
    rw [hu2, ← hsplit2] at hdl
    rw [hdl, deal_res, nth_drop,
        show occ ((L2 - 1) % j) (clsOf j 0 L1) + occ ((L2 - 1) % j) (clsOf j 0 (L2 - 1))
          = occ ((L2 - 1) % j) (clsOf j 0 L1) + occ ((L2 - 1) % j) (clsOf j 0 L2) - 1 from by
          omega]
    exact hlead2
  · rw [pair_mod_pow_sub_one hb hj, hw]

/-- **Theorem 5.**  Suppose the class sizes `c_t` forced by the digit lengths
satisfy the no-gap conditions for some legal `p`, that `c_t ≥ 2` for every class,
and that `c_t ≥ 3` at the one class `(L2-1) % j` holding the second number's
leading slot.  Then every residue mod `b^j - 1` that the digit-sum congruence
permits is realised by a genuine pandigital pair with those digit lengths —
leading digits included.  So no modulus of order `j` prunes more than casting
out `b-1`s does.

The rider is sharper than the informal proof's `c_t ≥ 3` for all `t`,
and sharpening it was worth doing: the gap between this theorem and the
conjecture that `c_t ≥ 2` suffices is now a single class, not every
class.
@isnad1 id=ex.12h7v.s9.0549b4f6a04d from=translated src=- shape=67e262c9 vocab=e93d051d
-/
theorem sieve_complete {b j L1 L2 : Nat} (hb : 1 < b) (hj : 0 < j)
    (hL : L1 + L2 = b) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (c p : Nat → Nat)
    (hc : ∀ t, c t = occ t (clsOf j 0 L1) + occ t (clsOf j 0 L2))
    (hpc : ∀ t, t < j → p t ≤ c t)
    (h2' : ∀ t, t < j → 2 ≤ c t)
    (h3 : 3 ≤ c ((L2 - 1) % j))
    (hgap : ∀ t, t < j → b ^ t ≤ sumRange (fun s => Nof j c p s * b ^ s) t + 1)
    (hreach : cosetSize b j ≤ sumRange (fun s => Nof j c p s * b ^ s) j + 1)
    {z : Nat} (hz : z % (b - 1) = tri b % (b - 1)) :
    ∃ d1 d2 : List Nat,
      d1.length = L1 ∧ d2.length = L2 ∧
      (∀ v, v < b → occ v (d1 ++ d2) = 1) ∧
      nth d1 (L1 - 1) ≠ 0 ∧ nth d2 (L2 - 1) ≠ 0 ∧
      (valOf b d1 + valOf b d2) % (b ^ j - 1) = z % (b ^ j - 1) := by
  have hmem1 : ∀ x, x ∈ clsOf j 0 L1 → x < j := clsOf_mem hj L1 0 hj
  have hmem2 : ∀ x, x ∈ clsOf j 0 L2 → x < j := clsOf_mem hj L2 0 hj
  have hcb : sumRange c j = b := by
    rw [sumRange_congr (g := fun t => occ t (clsOf j 0 L1) + occ t (clsOf j 0 L2)) j
          (fun t _ => hc t), sumRange_add,
        sumRange_occ_length _ hmem1, sumRange_occ_length _ hmem2,
        clsOf_length, clsOf_length]
    exact hL
  have hrunsum : (run 0 (sumRange c j)).sum = tri b := by rw [hcb, run_sum]; omega
  obtain ⟨ν, hν, hX⟩ := blocks_hit hb hj c p hpc hgap hreach (z := z) (by rw [hz, hrunsum])
  have hBlen : ∀ t, t < j → (blk j c p ν t).length = c t := fun t ht =>
    blk_length hj c p ν hpc ht
  have hBocc : ∀ v, sumRange (fun t => occ v (blk j c p ν t)) j = occ v (run 0 b) := by
    intro v
    rw [blk_occ hj c p ν v, sum_aOf hj c p hpc, hcb]
  -- the one block holding the digit `0`
  obtain ⟨t0, ht0j, ht0one, ht0zero⟩ := sumRange_eq_one j (by
    rw [hBocc 0]; exact occ_run b 0 0 (by omega) (by omega))
  have hlen0 : (dropZeros (blk j c p ν t0)).length + 1 = c t0 := by
    rw [dropZeros_length _ ht0one, hBlen t0 ht0j]
  -- the two leading slots, and the index chosen for `0`
  have ht1j : (L1 - 1) % j < j := Nat.mod_lt _ hj
  have ht2j : (L2 - 1) % j < j := Nat.mod_lt _ hj
  have hpos1 : 1 ≤ occ ((L1 - 1) % j) (clsOf j 0 L1) := by
    have h := clsOf_snoc hj (L1 - 1) 0 hj
    rw [show L1 - 1 + 1 = L1 from by omega, Nat.zero_add] at h
    rw [h, occ_append, occ_single]
    omega
  have hpos2 : 1 ≤ occ ((L2 - 1) % j) (clsOf j 0 L2) := by
    have h := clsOf_snoc hj (L2 - 1) 0 hj
    rw [show L2 - 1 + 1 = L2 from by omega, Nat.zero_add] at h
    rw [h, occ_append, occ_single]
    omega
  obtain ⟨k, hkdef⟩ : ∃ k, k = if occ t0 (clsOf j 0 L1) = 1 then 1 else 0 := ⟨_, rfl⟩
  have hk1' : k ≤ 1 := by rw [hkdef]; by_cases h : occ t0 (clsOf j 0 L1) = 1 <;> simp [h]
  have hkle : k ≤ (dropZeros (blk j c p ν t0)).length := by have := h2' t0 ht0j; omega
  obtain ⟨B, hBdef⟩ : ∃ B : Nat → List Nat, B = fun t =>
      if t = t0 then ins0 k (dropZeros (blk j c p ν t0)) else blk j c p ν t := ⟨_, rfl⟩
  have hB0 : B t0 = ins0 k (dropZeros (blk j c p ν t0)) := by rw [hBdef]; simp
  have hBn : ∀ t, t ≠ t0 → B t = blk j c p ν t := by intro t ht; rw [hBdef]; simp [ht]
  -- the modified blocks have the same sizes, the same values and the same sums
  have hlen : ∀ t, t < j → (B t).length = occ t (clsOf j 0 L1) + occ t (clsOf j 0 L2) := by
    intro t ht
    by_cases h : t = t0
    · subst h; rw [hB0, ins0_length hkle, hlen0, hc]
    · rw [hBn t h, hBlen t ht, hc]
  have hBocc' : ∀ v t, occ v (B t) = occ v (blk j c p ν t) := by
    intro v t
    by_cases h : t = t0
    · subst h
      rw [hB0, ins0_occ]
      show (if 0 = v then 1 else 0) + occ v (dropZeros (blk j c p ν t)) = _
      by_cases hv : v = 0
      · subst hv
        rw [ite_eq_left rfl, dropZeros_occ_zero, ht0one]
      · rw [ite_eq_right (fun hh => hv hh.symm), dropZeros_occ (by omega)]
        omega
    · rw [hBn t h]
  have hone : ∀ v, v < b → sumRange (fun t => occ v (B t)) j = 1 := by
    intro v hv
    rw [sumRange_congr (g := fun t => occ v (blk j c p ν t)) j (fun t _ => hBocc' v t), hBocc v]
    exact occ_run b 0 v (by omega) (by omega)
  have hBsum : ∀ t, (B t).sum = (blk j c p ν t).sum := by
    intro t
    by_cases h : t = t0
    · subst h; rw [hB0, ins0_sum, dropZeros_sum]
    · rw [hBn t h]
  -- the two leading digits are non-zero
  have hnz : ∀ t, t < j → t ≠ t0 → ∀ m, m < c t → nth (B t) m ≠ 0 := by
    intro t ht hne m hm
    rw [hBn t hne]
    exact nth_ne_zero _ (ht0zero t ht hne) m (by rw [hBlen t ht]; exact hm)
  have hlead1 : nth (B ((L1 - 1) % j)) (occ ((L1 - 1) % j) (clsOf j 0 L1) - 1) ≠ 0 := by
    have hlt : occ ((L1 - 1) % j) (clsOf j 0 L1) - 1 < c ((L1 - 1) % j) := by
      rw [hc]; omega
    by_cases h : (L1 - 1) % j = t0
    · rw [h] at hlt ⊢
      rw [hB0]
      refine ins0_nth_ne (dropZeros_occ_zero _) hkle (by omega) ?_
      rw [← h] at hkdef ⊢
      by_cases h1' : occ ((L1 - 1) % j) (clsOf j 0 L1) = 1 <;> rw [hkdef] <;> simp [h1'] <;> omega
    · exact hnz _ ht1j h _ hlt
  have hlead2 : nth (B ((L2 - 1) % j))
      (occ ((L2 - 1) % j) (clsOf j 0 L1) + occ ((L2 - 1) % j) (clsOf j 0 L2) - 1) ≠ 0 := by
    have hlt : occ ((L2 - 1) % j) (clsOf j 0 L1) + occ ((L2 - 1) % j) (clsOf j 0 L2) - 1
        < c ((L2 - 1) % j) := by rw [hc]; omega
    have h32 := h3
    rw [hc] at h32
    by_cases h : (L2 - 1) % j = t0
    · rw [h] at hlt h32 ⊢
      rw [hB0]
      refine ins0_nth_ne (dropZeros_occ_zero _) hkle (by omega) (by omega)
    · exact hnz _ ht2j h _ hlt
  obtain ⟨d1, d2, h1', h2', h4, h5, h6, h7⟩ :=
    blocks_to_pair (b := b) hb hj hL1 hL2 B hlen hone hlead1 hlead2
  refine ⟨d1, d2, h1', h2', h4, h5, h6, ?_⟩
  rw [h7, sumRange_congr (g := fun t => b ^ t * (blk j c p ν t).sum) j
        (fun t _ => by rw [hBsum t])]
  exact hX

/-! ### Non-vacuity, and where the hypothesis bites -/

/--
@isnad1 id=eq.3h4v.s5.e84e8135b240 from=translated src=- shape=87f0d3c0 vocab=9419a325
-/
theorem occ_clsOf_zero {j s n t : Nat} (hj : 0 < j) (hs : s < j) (ht : j ≤ t) :
    occ t (clsOf j s n) = 0 := by
  rcases Nat.eq_zero_or_pos (occ t (clsOf j s n)) with h | h
  · exact h
  · exact absurd (clsOf_mem hj n s hs t (mem_of_occ_pos _ t h)) (by omega)

/-- At base 10, `j = 2`, digit lengths `(4,6)` — the lengths of `69^2 = 4761` and
`69^3 = 328509` — both classes hold five values.
@isnad1 id=eq.0h1v.s6.6aa2c2d1761f from=translated src=- shape=08457707 vocab=5f57ebd1
-/
theorem base_ten_two_classes : ∀ t,
    (if t < 2 then 5 else 0) = occ t (clsOf 2 0 4) + occ t (clsOf 2 0 6) := by
  intro t
  rcases Nat.lt_or_ge t 2 with h | h
  · rw [ite_eq_left h]
    rcases t with _ | _ | t
    · rfl
    · rfl
    · omega
  · rw [ite_eq_right (by omega), occ_clsOf_zero (by omega) (by omega) h,
        occ_clsOf_zero (by omega) (by omega) h]

/-- **Theorem 5 fires at the base and the digit lengths of the only known nice
number.**  Every residue mod `99` that casting out 9s permits really is the sum
of a genuine pandigital `(4,6)` pair in base 10, so the modulus `99` — and with
it every modulus of order 2 — buys nothing over casting out 9s.
@isnad1 id=ex.1h1v.s7.4f1be56f71c3 from=translated src=- shape=3f7be1bb vocab=9da452b8
-/
theorem base_ten_j_two_complete {z : Nat} (hz : z % 9 = 0) :
    ∃ d1 d2 : List Nat,
      d1.length = 4 ∧ d2.length = 6 ∧
      (∀ v, v < 10 → occ v (d1 ++ d2) = 1) ∧
      nth d1 3 ≠ 0 ∧ nth d2 5 ≠ 0 ∧
      (valOf 10 d1 + valOf 10 d2) % 99 = z % 99 := by
  have h := sieve_complete (b := 10) (j := 2) (L1 := 4) (L2 := 6)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun t => if t < 2 then 5 else 0) (fun t => if t = 0 then 5 else 0)
    base_ten_two_classes
    (by intro t ht; rcases t with _ | _ | t <;> first | decide | omega)
    (by intro t ht; rcases t with _ | _ | t <;> first | decide | omega)
    (by decide)
    (by intro t ht; rcases t with _ | _ | t <;> first | decide | omega)
    (by decide)
    (z := z) (by rw [hz]; rfl)
  exact h

/-- …and it does **not** fire at `j = 5`, which is exactly where base 10's sieve
does gain: `11111 = 41 · 271` has order 5 and two residues are unreachable.  The
class sizes there are `(3,2,2,2,1)`, so the `c_t ≥ 2` half of the rider fails —
the theorem's hypothesis and the measured counterexample agree.
@isnad1 id=not.0h0v.s6.42cebee19fbc from=translated src=- shape=b945804c vocab=dbb3dbd4
-/
theorem base_ten_j_five_rider_fails :
    ¬ ∀ t, t < 5 → 2 ≤ occ t (clsOf 5 0 4) + occ t (clsOf 5 0 6) := by decide

/-- Base 4, lengths `(2,2)` — the counterexample of §6.1 — clears `c_t ≥ 2`, and
it even satisfies the no-gap conditions: `p = (2,0)` gives `N = (4,0)`, and
`b^1 = 4 ≤ 5`, `K - 1 = 4`.  What stops it is the *other* half of the rider.  So
the two witnesses fail on different halves and neither half is slack — without
the second one this theorem would contradict `base_four_sieve_is_incomplete`.
@isnad1 id=not.0h0v.s6.4183ba32e3e4 from=translated src=- shape=aded7f0b vocab=f8611c50
-/
theorem base_four_rider_fails :
    ¬ 3 ≤ occ ((2 - 1) % 2) (clsOf 2 0 2) + occ ((2 - 1) % 2) (clsOf 2 0 2) := by decide

/--
@isnad1 id=le.1h1v.s5.28fc8ae09655 from=translated src=- shape=401a7ac1 vocab=dbb3dbd4
-/
theorem base_four_clears_the_other_half :
    ∀ t, t < 2 → 2 ≤ occ t (clsOf 2 0 2) + occ t (clsOf 2 0 2) := by decide

/-- …and it clears the no-gap conditions too, with `c = (2,2)` and `p = (2,0)`.
Without this the previous theorem would prove nothing about the rider: a witness
that fails several hypotheses at once says which one is load-bearing only if the
others are checked to hold.
@isnad1 id=and.0h0v.s8.7a1a6d7497b3 from=translated src=- shape=736de731 vocab=83d35970
-/
theorem base_four_clears_the_no_gap :
    (∀ t, t < 2 → 4 ^ t ≤ sumRange (fun s => Nof 2 (fun u => if u < 2 then 2 else 0)
        (fun u => if u = 0 then 2 else 0) s * 4 ^ s) t + 1)
      ∧ cosetSize 4 2 ≤ sumRange (fun s => Nof 2 (fun u => if u < 2 then 2 else 0)
          (fun u => if u = 0 then 2 else 0) s * 4 ^ s) 2 + 1 :=
  ⟨by intro t ht; rcases t with _ | _ | t <;> first | decide | omega, by decide⟩

/-! ## §7  Theorem 4 — the complete classification of `R_b = ∅`

The residue set `R_b = {ρ : ρ^e1 + ρ^e2 ≡ T (mod b-1)}`, `2T = b(b-1)`, is the
second necessary condition every solution satisfies (§2 refuted it for
`b ≡ 3 mod 4`).  This section decides emptiness **for every base and every pair**,
and the answer is entirely 2-adic: writing `b - 1 = 2^a · m` with `m` odd,

> `R_b = ∅`  ⟺  `a = 1`, or (`a ≥ 3` and `e2 - e1` even and `e1 ∤ a - 1`).

The reason no odd prime enters is `ρ = 0`.  Modulo the odd part of `b-1` the
target `T` vanishes — `2T = b(b-1)` and `b-1`'s odd part divides `T` — so the odd
part imposes no condition at all, and the CRT decomposition the informal proof
reaches for is never needed.  What is left is the 2-part, where `T ≡ 2^(a-1)`,
and the whole question becomes: which 2-adic valuations can `ρ^e1 + ρ^e2` have?
Exactly `1` (from odd `ρ` with `e2-e1` even), whatever `v_2(1 + ρ^(e2-e1))` is
(odd `ρ`, `e2-e1` odd — always `≥ 1`), and the multiples of `e1` (from even `ρ`).
Never `0`, which is Theorem 3.

Theorem 3 is therefore the `a = 1` case of this theorem, and the three "extra"
2-adic dead classes found by computer search for `(2,4)`, `(4,6)` and `(3,7)` are the
second clause.  §7.5 runs both ends on numerals.
-/

/-! ### §7.0  A two-adic toolkit -/

/--
@isnad1 id=eq.0h1v.s4.8b00658ca4d2 from=translated src=- shape=18b02a30 vocab=de4a4c74
-/
theorem pow_two_eq (x : Nat) : x ^ 2 = x * x := by rw [Nat.pow_succ, Nat.pow_one]

/--
@isnad1 id=eq.0h3v.s6.2534ec0262ae from=translated src=- shape=d983bf58 vocab=30ba1354
-/
theorem mul_pow_two_comm (p q m : Nat) : (2^p * m) * (2^q * m) = 2^(p+q) * (m*m) := by
  rw [Nat.pow_add, Nat.mul_assoc, ← Nat.mul_assoc m (2^q) m, Nat.mul_comm m (2^q),
      Nat.mul_assoc, ← Nat.mul_assoc]

/--
@isnad1 id=eq.1h2v.s5.26db361cda4f from=translated src=- shape=395e3d0d vocab=df461349
-/
theorem odd_pow {u : Nat} (hu : u % 2 = 1) (e : Nat) : u ^ e % 2 = 1 := by
  induction e with
  | zero => simp
  | succ j ih => rw [Nat.pow_succ, Nat.mul_mod, ih, hu]

/-- an odd square is `1` mod 4 -- the only fact about squares this section needs.
@isnad1 id=eq.1h1v.s6.9db4d287fef2 from=translated src=- shape=cb0dfa3d vocab=df461349
-/
theorem odd_sq_mod_four {x : Nat} (hx : x % 2 = 1) : x ^ 2 % 4 = 1 % 4 := by
  obtain ⟨t, ht⟩ : ∃ t, x = 2 * t + 1 := ⟨x / 2, by omega⟩
  have hsq : x ^ 2 = 4 * (t * t) + 4 * t + 1 := by
    rw [pow_two_eq, ht, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul,
        Nat.mul_assoc, Nat.mul_left_comm t 2 t, ← Nat.mul_assoc]
    omega
  omega

/-- `(b-1)/2 = 2^(a-1)·m` is `2^(a-1)` mod `2^a`: the target, localised.
@isnad1 id=eq.1h2v.s6.963cb5555351 from=translated src=- shape=c220c0a5 vocab=84e92033
-/
theorem half_mod {a m : Nat} (hm : m % 2 = 1) : (2 ^ a * m) % (2 ^ (a+1)) = 2 ^ a := by
  obtain ⟨t, ht⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
  have h : 2 ^ a * m = 2 ^ a + 2 ^ (a+1) * t := by
    rw [ht, Nat.mul_add, Nat.mul_one, Nat.pow_succ, Nat.mul_comm (2^a) 2, ← Nat.mul_assoc,
        Nat.mul_comm (2^a) 2, Nat.mul_assoc, Nat.add_comm]
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- every positive natural is `2^v` times an odd number
@isnad1 id=ex.1h1v.s6.1e199b50cf4b from=translated src=- shape=ffa4f5d6 vocab=1795eeb0
-/
theorem two_adic_split : ∀ x : Nat, 0 < x → ∃ v u, x = 2 ^ v * u ∧ u % 2 = 1 := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx
    by_cases h : x % 2 = 1
    · exact ⟨0, x, by simp, h⟩
    · obtain ⟨y, hy⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
      obtain ⟨v, u, hu, hodd⟩ := ih y (by omega) (by omega)
      refine ⟨v + 1, u, ?_, hodd⟩
      rw [hy, hu, Nat.pow_succ, Nat.mul_comm (2^v) 2, Nat.mul_assoc]

/-- ...and the exponent is determined, which is the whole of "the 2-adic
valuation is well defined".  Used only through the equality `2^i·U = 2^j·V`.
@isnad1 id=eq.3h4v.s6.90d004bfd3f4 from=translated src=- shape=070f4b57 vocab=d5c43088
-/
theorem two_pow_odd_unique {i j U V : Nat} (hU : U % 2 = 1) (hV : V % 2 = 1)
    (h : 2 ^ i * U = 2 ^ j * V) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · obtain ⟨s, hs⟩ : ∃ s, j = i + (s + 1) := ⟨j - i - 1, by omega⟩
    rw [hs, Nat.pow_add, Nat.mul_assoc] at h
    have := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide) (n := i)) h
    have h2' : (2 ^ (s+1) * V) % 2 = 0 := by
      rw [Nat.pow_succ, Nat.mul_comm (2^s) 2, Nat.mul_assoc, Nat.mul_mod_right]
    omega
  · exact heq
  · obtain ⟨s, hs⟩ : ∃ s, i = j + (s + 1) := ⟨i - j - 1, by omega⟩
    rw [hs, Nat.pow_add, Nat.mul_assoc] at h
    have := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide) (n := j)) h
    have h2' : (2 ^ (s+1) * U) % 2 = 0 := by
      rw [Nat.pow_succ, Nat.mul_comm (2^s) 2, Nat.mul_assoc, Nat.mul_mod_right]
    omega

/--
@isnad1 id=eq.1h3v.s6.f7aa1d8dd7a6 from=translated src=- shape=b8e28657 vocab=df461349
-/
theorem pow_mod_one {x M : Nat} (h : x % M = 1 % M) (c : Nat) : x ^ c % M = 1 % M := by
  induction c with
  | zero => simp
  | succ j ih => rw [Nat.pow_succ, Nat.mul_mod, ih, h, ← Nat.mul_mod, Nat.one_mul]

/-- a square root of `1` is fixed by odd powers and trivialised by even ones
@isnad1 id=and.1h3v.s7.aca68f6e05a6 from=translated src=- shape=41224b5d vocab=84e92033
-/
theorem pow_mod_sq_one {x M : Nat} (h : x ^ 2 % M = 1 % M) :
    ∀ k, x ^ (2 * k) % M = 1 % M ∧ x ^ (2 * k + 1) % M = x % M := by
  have h' : x * x % M = 1 % M := by rw [← pow_two_eq]; exact h
  intro k
  induction k with
  | zero => simp
  | succ j ih =>
    have heven : x ^ (2 * (j+1)) % M = 1 % M := by
      have hstep : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [hstep, Nat.pow_succ, Nat.mul_mod, ih.2, ← Nat.mul_mod, h']
    exact ⟨heven, by rw [Nat.pow_succ, Nat.mul_mod, heven, ← Nat.mul_mod, Nat.one_mul]⟩

/-! ### §7.1  The target `T`, reduced

`T = b(b-1)/2` mod `b-1` is `(b-1)/2` when `b` is odd and `0` when `b` is even.
Both are one line and neither needs `b` again afterwards. -/

/--
@isnad1 id=eq.3h3v.s6.9827277100de from=translated src=- shape=d84937d3 vocab=8d1d45fb
-/
theorem target_eq {b T A : Nat} (hb : 1 < b) (hT : 2 * T = b * (b - 1))
    (hA : 2 * A = b - 1) : T % (b - 1) = A % (b - 1) := by
  have hb1 : b = (b - 1) + 1 := by omega
  have h2' : 2 * T = ((b-1) + 1) * (b - 1) := by rw [← hb1]; exact hT
  rw [← hA] at h2'
  have hAA : A * (2 * A) = 2 * (A * A) := by rw [Nat.mul_left_comm]
  have hexp : (2 * A + 1) * (2 * A) = 4 * (A * A) + 2 * A := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, hAA]; omega
  rw [hexp] at h2'
  have hTv : T = A + (b - 1) * A := by
    have hswap : (b - 1) * A = 2 * (A * A) := by rw [← hA, Nat.mul_assoc]
    omega
  rw [hTv, Nat.add_mul_mod_self_left]

/--
@isnad1 id=eq.3h2v.s6.75e98bba9b5d from=translated src=- shape=7df24af4 vocab=8d1d45fb
-/
theorem target_zero {b T : Nat} (hb : 1 < b) (hT : 2 * T = b * (b - 1))
    (hbe : b % 2 = 0) : T % (b - 1) = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, b = 2 * c := ⟨b / 2, by omega⟩
  have hstep : b * (b - 1) = 2 * (c * (b - 1)) := by rw [hc, Nat.mul_assoc]
  have hTv : T = c * (b - 1) := by omega
  rw [hTv, Nat.mul_mod_left]

/-! ### §7.2  The live direction: four explicit residues

Each live class gets a residue written down, so this half of the theorem needs
no existence argument and, in particular, no Chinese remainder theorem. -/

/-- The shape two of the four witnesses reduce to: if the sum is `2^w · m · W`
with `W` odd and `b - 1 = 2^(w+1)·m`, it is congruent to `T`.
@isnad1 id=eq.5h6v.s7.f4b796c40957 from=translated src=- shape=48caef73 vocab=f572c56f
-/
theorem residue_of_odd_cofactor {b T w m W S : Nat} (hb : 1 < b) (hT : 2 * T = b * (b - 1))
    (hM : b - 1 = 2 ^ (w+1) * m) (hW : W % 2 = 1) (hS : S = 2 ^ w * (m * W)) :
    S % (b - 1) = T % (b - 1) := by
  have h2A : 2 * (2 ^ w * m) = b - 1 := by rw [hM, ← Nat.mul_assoc, ← Nat.pow_succ']
  obtain ⟨W', hW'⟩ : ∃ W', W = 2 * W' + 1 := ⟨W / 2, by omega⟩
  have hval : S = 2 ^ w * m + (b - 1) * W' := by
    rw [hS, hW', hM, Nat.pow_succ, Nat.mul_add m (2 * W') 1, Nat.mul_one,
        Nat.mul_add (2 ^ w) (m * (2 * W')) m, Nat.mul_left_comm m 2 W',
        ← Nat.mul_assoc (2 ^ w) 2 (m * W'), ← Nat.mul_assoc (2 ^ w * 2) m W']
    omega
  rw [hval, Nat.add_mul_mod_self_left, target_eq hb hT h2A]

/-- `a = 0`, i.e. `b` even: `ρ = 0`, because then `T ≡ 0 (mod b-1)`.
@isnad1 id=eq.5h4v.s7.9660b67544bc from=translated src=- shape=79859545 vocab=407ce26c
-/
theorem residue_of_even_base {b e1 e2 T : Nat} (hb : 1 < b) (he1 : 1 ≤ e1) (he2 : 1 ≤ e2)
    (hT : 2 * T = b * (b - 1)) (hbe : b % 2 = 0) :
    (0 ^ e1 + 0 ^ e2) % (b - 1) = T % (b - 1) := by
  rw [Nat.zero_pow (by omega), Nat.zero_pow (by omega), target_zero hb hT hbe]
  simp

/-- `x + 1 = A`, `2A = M` and `M ∣ A^2` make `x` a square root of `1` mod `M`.
With `A = M/2` the cross term `2x = M - 2` is the point: it wipes out `-2A`.
@isnad1 id=eq.4h4v.s6.ee7549d7749c from=translated src=- shape=93671f33 vocab=daab4b83
-/
theorem sq_one_of_half {x A M K : Nat} (hx1 : x + 1 = A) (h2A : 2 * A = M)
    (hAA : A * A = M * K) (hK : 0 < K) : x ^ 2 % M = 1 % M := by
  have hexp : (x + 1) * (x + 1) = x * x + 2 * x + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.one_mul]
    omega
  have hsq : x * x + 2 * x + 1 = A * A := by rw [← hexp, hx1]
  obtain ⟨K', hK'⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hMK : M * K = M * K' + M := by rw [hK', Nat.mul_add, Nat.mul_one]
  have hxx : x * x = 1 + M * K' := by omega
  rw [pow_two_eq, hxx, Nat.add_mul_mod_self_left]

/-- a square root of `1` raised to exponents of opposite parity contributes
`x + 1` — one power gives `x`, the other `1`.
@isnad1 id=eq.2h4v.s7.d6584266faab from=translated src=- shape=a93e356c vocab=b2ffaa0b
-/
theorem pair_pow_sq_one {x M e1 e2 : Nat} (h : x ^ 2 % M = 1 % M) (hpar : e1 % 2 ≠ e2 % 2) :
    (x ^ e1 + x ^ e2) % M = (x + 1) % M := by
  have hpow := pow_mod_sq_one h
  have hfin : ∀ f g : Nat, f % 2 = 0 → g % 2 = 1 →
      (x ^ f % M + x ^ g % M) % M = (x + 1) % M := by
    intro f g hf hg
    obtain ⟨k, hk⟩ : ∃ k, f = 2 * k := ⟨f / 2, by omega⟩
    obtain ⟨l, hl⟩ : ∃ l, g = 2 * l + 1 := ⟨g / 2, by omega⟩
    rw [hk, hl, (hpow k).1, (hpow l).2, ← Nat.add_mod, Nat.add_comm]
  rw [Nat.add_mod]
  rcases Nat.lt_or_ge (e1 % 2) (e2 % 2) with h' | h'
  · exact hfin e1 e2 (by omega) (by omega)
  · rw [Nat.add_comm (x ^ e1 % M)]
    exact hfin e2 e1 (by omega) (by omega)

/-- `a ≥ 2` and `e2 - e1` odd: `ρ = (b-1)/2 - 1`, whose square is `1`, so the two
powers contribute `ρ` and `1` and their sum is `(b-1)/2 ≡ T`.  Note the witness
is *not* `≡ 0` mod the odd part of `b-1`: there it is `-1`, and the two opposite
parities cancel it.
@isnad1 id=eq.5h6v.s8.3cae71742e07 from=translated src=- shape=c36b64eb vocab=f572c56f
-/
theorem residue_of_odd_gap {b e1 e2 T c m : Nat} (hb : 1 < b) (hm : m % 2 = 1)
    (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ (c + 2) * m) (hpar : e1 % 2 ≠ e2 % 2) :
    ((2 ^ (c+1) * m - 1) ^ e1 + (2 ^ (c+1) * m - 1) ^ e2) % (b - 1) = T % (b - 1) := by
  have hmpos : 0 < m := by omega
  have hApos : 0 < 2 ^ (c+1) * m := Nat.mul_pos (Nat.pow_pos (by decide)) hmpos
  have h2A : 2 * (2 ^ (c+1) * m) = b - 1 := by
    rw [hM, ← Nat.mul_assoc, ← Nat.pow_succ']
  have hAA : (2 ^ (c+1) * m) * (2 ^ (c+1) * m) = (b - 1) * (2 ^ c * m) := by
    rw [hM, mul_pow_two_comm, mul_pow_two_comm]
    have hidx : c + 1 + (c + 1) = c + 2 + c := by omega
    rw [hidx]
  have hK : 0 < 2 ^ c * m := Nat.mul_pos (Nat.pow_pos (by decide)) hmpos
  have hsq := sq_one_of_half (x := 2 ^ (c+1) * m - 1) (A := 2 ^ (c+1) * m) (M := b - 1)
    (K := 2 ^ c * m) (by omega) h2A hAA hK
  rw [pair_pow_sq_one hsq hpar]
  have hx1 : (2 ^ (c+1) * m - 1) + 1 = 2 ^ (c+1) * m := by omega
  rw [hx1, target_eq hb hT h2A]

/-- `a = 2`: `ρ = m^2`, where `b - 1 = 4m`.  An odd square is `1` mod 8, so the
sum is `m` times something `≡ 2 (mod 4)` — valuation exactly `1 = a - 1`.
@isnad1 id=eq.6h5v.s7.1a4d1db0d800 from=translated src=- shape=6ebab85a vocab=407ce26c
-/
theorem residue_of_two_adic_two {b e1 e2 T m : Nat} (hb : 1 < b) (he1 : 1 ≤ e1) (he2 : 1 ≤ e2)
    (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ 2 * m) :
    ((m ^ 2) ^ e1 + (m ^ 2) ^ e2) % (b - 1) = T % (b - 1) := by
  obtain ⟨f, rfl⟩ : ∃ f, e1 = f + 1 := ⟨e1 - 1, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g, e2 = g + 1 := ⟨e2 - 1, by omega⟩
  have hpow : ∀ e : Nat, (m ^ 2) ^ (e+1) = m ^ (2 * e + 1) * m := by
    intro e
    rw [← Nat.pow_mul]
    have hidx : 2 * (e + 1) = (2 * e + 1) + 1 := by omega
    rw [hidx, Nat.pow_succ]
  have hZ : (m ^ (2*f+1) + m ^ (2*g+1)) % 4 = 2 := by
    have h1' := (pow_mod_sq_one (M := 4) (odd_sq_mod_four hm) f).2
    have h2' := (pow_mod_sq_one (M := 4) (odd_sq_mod_four hm) g).2
    rw [Nat.add_mod, h1', h2', ← Nat.add_mod]
    omega
  obtain ⟨s, hs⟩ : ∃ s, m ^ (2*f+1) + m ^ (2*g+1) = 2 * (2 * s + 1) :=
    ⟨(m ^ (2*f+1) + m ^ (2*g+1) - 2) / 4, by omega⟩
  refine residue_of_odd_cofactor (w := 1) (m := m) (W := 2 * s + 1) hb hT (by rw [hM])
    (by omega) ?_
  rw [hpow f, hpow g, ← Nat.add_mul, hs, Nat.pow_one, Nat.mul_comm m (2 * s + 1),
      ← Nat.mul_assoc]

/-- `a - 1 = e1·V` with `V ≥ 1`: `ρ = 2^V·m`, where `b - 1 = 2^a·m`.  Here
`v_2(ρ^e1 + ρ^e2) = V·e1` exactly, because `1 + ρ^(e2-e1)` is odd.
@isnad1 id=eq.7h6v.s8.448cbd656afc from=translated src=- shape=7248be19 vocab=407ce26c
-/
theorem residue_of_dvd {b e1 e2 T m V : Nat} (hb : 1 < b) (he1 : 1 ≤ e1) (hlt : e1 < e2)
    (hV : 1 ≤ V) (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1))
    (hM : b - 1 = 2 ^ (V * e1 + 1) * m) :
    ((2 ^ V * m) ^ e1 + (2 ^ V * m) ^ e2) % (b - 1) = T % (b - 1) := by
  obtain ⟨V, rfl⟩ : ∃ V', V = V' + 1 := ⟨V - 1, by omega⟩
  obtain ⟨f, hf⟩ : ∃ f, e1 = f + 1 := ⟨e1 - 1, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, e2 = e1 + (d + 1) := ⟨e2 - e1 - 1, by omega⟩
  have hlow : (2 ^ (V+1) * m) ^ e1 = 2 ^ ((V+1) * e1) * (m * m ^ f) := by
    rw [Nat.mul_pow, ← Nat.pow_mul, hf, Nat.pow_succ (m := f), Nat.mul_comm (m ^ f) m]
  have hhigh : (2 ^ (V+1) * m) ^ e2
      = 2 ^ ((V+1) * e1) * (m * (2 ^ ((V+1) * (d+1)) * (m ^ f * m ^ (d+1)))) := by
    rw [Nat.mul_pow, ← Nat.pow_mul, hd, Nat.mul_add (V+1) e1 (d+1),
        Nat.pow_add 2 ((V+1) * e1) ((V+1) * (d+1)),
        Nat.pow_add m e1 (d+1), hf, Nat.pow_succ (m := f), Nat.mul_comm (m ^ f) m,
        Nat.mul_assoc m (m ^ f) (m ^ (d+1)),
        Nat.mul_assoc (2 ^ ((V+1) * (f+1))) (2 ^ ((V+1) * (d+1))) (m * (m ^ f * m ^ (d+1))),
        Nat.mul_left_comm (2 ^ ((V+1) * (d+1))) m (m ^ f * m ^ (d+1))]
  refine residue_of_odd_cofactor (w := (V+1) * e1) (m := m)
    (W := m ^ f + 2 ^ ((V+1) * (d+1)) * (m ^ f * m ^ (d+1))) hb hT ?_ ?_ ?_
  · rw [hM, Nat.mul_comm (V+1) e1]
  · have h1' : m ^ f % 2 = 1 := odd_pow hm f
    have h2' : (2 ^ ((V+1) * (d+1)) * (m ^ f * m ^ (d+1))) % 2 = 0 := by
      obtain ⟨p, hp⟩ : ∃ p, (V+1) * (d+1) = p + 1 :=
        ⟨(V+1)*(d+1) - 1, by
          have := Nat.mul_pos (n := V+1) (m := d+1) (by omega) (by omega); omega⟩
      rw [hp, Nat.pow_succ, Nat.mul_comm (2^p) 2, Nat.mul_assoc, Nat.mul_mod_right]
    omega
  · rw [hlow, hhigh, ← Nat.mul_add (2 ^ ((V+1) * e1)),
        ← Nat.mul_add m (m ^ f) (2 ^ ((V+1) * (d+1)) * (m ^ f * m ^ (d+1)))]

/-! ### §7.3  The dead direction -/

/--
@isnad1 id=eq.0h3v.s6.6cc9b2f55955 from=translated src=- shape=5f6228a5 vocab=30ba1354
-/
theorem sum_factor (ρ e1 d : Nat) : ρ ^ e1 + ρ ^ (e1 + (d+1)) = ρ ^ e1 * (1 + ρ ^ (d+1)) := by
  rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]

/--
@isnad1 id=eq.1h3v.s6.d78cc49e6071 from=translated src=- shape=1ab7e7cf vocab=30ba1354
-/
theorem sum_shape {S a' q : Nat} (hdiv : 2 ^ (a'+1) * q + 2 ^ a' = S) :
    S = 2 ^ a' * (2 * q + 1) := by
  have hexp : 2 ^ a' * (2 * q + 1) = 2 ^ (a'+1) * q + 2 ^ a' := by
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.pow_succ]
  omega

/-- The 2-adic admissibility condition of Theorem 4, in terms of `a = v_2(b-1)`.
`a ≠ 1` is Theorem 3; the rest bites only at `a ≥ 3` with `e2 - e1` even.-/
def LiveTwoAdic (a e1 e2 : Nat) : Prop :=
  a ≠ 1 ∧ (a ≤ 2 ∨ (e2 - e1) % 2 = 1 ∨ e1 ∣ (a - 1))

/-- **Theorem 4, necessity.**  A residue exists only in the classes above.  The
argument is one valuation count: `ρ^e1 + ρ^e2 = ρ^e1·(1 + ρ^(e2-e1))` must have
`v_2` exactly `a - 1`, and the three cases of `ρ` (zero, odd, even) supply the
three clauses.
@isnad1 id=livetwoa.7h7v.s7.854d428a1bba from=translated src=- shape=994263fe vocab=35b3ed67
-/
theorem live_of_residue {b e1 e2 T a m ρ : Nat} (hb : 1 < b) (he1 : 1 ≤ e1) (hlt : e1 < e2)
    (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ a * m)
    (hρ : (ρ ^ e1 + ρ ^ e2) % (b - 1) = T % (b - 1)) :
    LiveTwoAdic a e1 e2 := by
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · exact ⟨by omega, Or.inl (by omega)⟩
  obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  subst ha'
  obtain ⟨d, hd⟩ : ∃ d, e2 = e1 + (d + 1) := ⟨e2 - e1 - 1, by omega⟩
  -- the sum is `2^(a-1)` times an odd number
  have h2A : 2 * (2 ^ a' * m) = b - 1 := by rw [hM, ← Nat.mul_assoc, ← Nat.pow_succ']
  have hdvd : 2 ^ (a' + 1) ∣ (b - 1) := ⟨m, hM⟩
  have hstep : ∀ x y : Nat, x % (b - 1) = y % (b - 1) → x % 2 ^ (a'+1) = y % 2 ^ (a'+1) := by
    intro x y hxy
    rw [← Nat.mod_mod_of_dvd x hdvd, ← Nat.mod_mod_of_dvd y hdvd, hxy]
  have hSA : (ρ ^ e1 + ρ ^ e2) % 2 ^ (a'+1) = 2 ^ a' := by
    rw [hstep _ _ (hρ.trans (target_eq hb hT h2A)), half_mod hm]
  have hSodd : ρ ^ e1 + ρ ^ e2 = 2 ^ a' * (2 * ((ρ ^ e1 + ρ ^ e2) / 2 ^ (a'+1)) + 1) := by
    refine sum_shape ?_
    have := Nat.div_add_mod (ρ ^ e1 + ρ ^ e2) (2 ^ (a'+1))
    omega
  have hUodd : (2 * ((ρ ^ e1 + ρ ^ e2) / 2 ^ (a'+1)) + 1) % 2 = 1 := by omega
  -- `ρ = 0` gives the sum `0`, which has no valuation at all
  rcases Nat.eq_zero_or_pos ρ with rfl | hρpos
  · have hz : (0:Nat) ^ e1 + 0 ^ e2 = 0 := by
      rw [Nat.zero_pow (by omega), Nat.zero_pow (by omega)]
    have hpos : 0 < 2 ^ a' * (2 * ((0 ^ e1 + 0 ^ e2) / 2 ^ (a'+1)) + 1) :=
      Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
    omega
  obtain ⟨w, u, hu, huodd⟩ := two_adic_split ρ hρpos
  rw [hd] at hSodd hUodd ⊢
  rw [sum_factor] at hSodd hUodd
  rcases Nat.eq_zero_or_pos w with rfl | hwpos
  · -- `ρ` odd
    have hρodd : ρ % 2 = 1 := by rw [hu] at *; simpa using huodd
    by_cases hpar : (d + 1) % 2 = 0
    · -- `e2 - e1` even: `ρ^(e2-e1) ≡ 1 (mod 4)`, so the valuation is exactly 1
      obtain ⟨k, hk⟩ : ∃ k, d + 1 = 2 * k := ⟨(d+1) / 2, by omega⟩
      have hpow4 : ρ ^ (d+1) % 4 = 1 := by
        rw [hk, Nat.pow_mul, pow_mod_one (odd_sq_mod_four hρodd) k]
      obtain ⟨t, ht⟩ : ∃ t, 1 + ρ ^ (d+1) = 2 * (2 * t + 1) := ⟨(ρ ^ (d+1) - 1) / 4, by omega⟩
      have hfac : ρ ^ e1 * (1 + ρ ^ (d+1)) = 2 ^ 1 * (ρ ^ e1 * (2 * t + 1)) := by
        rw [ht, Nat.pow_one, Nat.mul_left_comm]
      have hodd2 : (ρ ^ e1 * (2 * t + 1)) % 2 = 1 := by
        rw [Nat.mul_mod, odd_pow hρodd e1]
        omega
      have := two_pow_odd_unique hodd2 hUodd (hfac.symm.trans hSodd)
      exact ⟨by omega, Or.inl (by omega)⟩
    · -- `e2 - e1` odd: the valuation is unconstrained, but positive
      have hodd : ρ ^ (d+1) % 2 = 1 := odd_pow hρodd _
      obtain ⟨c, U, hcU, hUo⟩ := two_adic_split (1 + ρ ^ (d+1)) (by omega)
      have hcpos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with rfl | h
        · rw [Nat.pow_zero, Nat.one_mul] at hcU; omega
        · exact h
      have hfac : ρ ^ e1 * (1 + ρ ^ (d+1)) = 2 ^ c * (ρ ^ e1 * U) := by
        rw [hcU, Nat.mul_left_comm]
      have hodd2 : (ρ ^ e1 * U) % 2 = 1 := by
        rw [Nat.mul_mod, odd_pow hρodd e1, hUo]
      have := two_pow_odd_unique hodd2 hUodd (hfac.symm.trans hSodd)
      exact ⟨by omega, Or.inr (Or.inl (by omega))⟩
  · -- `ρ` even: `1 + ρ^(e2-e1)` is odd, so the valuation is `v_2(ρ)·e1`
    have hρeven : ρ % 2 = 0 := by
      rw [hu]
      obtain ⟨p, hp⟩ : ∃ p, w = p + 1 := ⟨w - 1, by omega⟩
      rw [hp, Nat.pow_succ, Nat.mul_comm (2^p) 2, Nat.mul_assoc, Nat.mul_mod_right]
    have hcof : (1 + ρ ^ (d+1)) % 2 = 1 := by
      have := pow_mod_two (n := ρ) (d+1) (by omega)
      omega
    have hfac : ρ ^ e1 * (1 + ρ ^ (d+1)) = 2 ^ (w * e1) * (u ^ e1 * (1 + ρ ^ (d+1))) := by
      rw [hu, Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]
    have hodd2 : (u ^ e1 * (1 + ρ ^ (d+1))) % 2 = 1 := by
      rw [Nat.mul_mod, odd_pow huodd e1, hcof]
    have hwe := two_pow_odd_unique hodd2 hUodd (hfac.symm.trans hSodd)
    have : 0 < w * e1 := Nat.mul_pos hwpos (by omega)
    exact ⟨by omega, Or.inr (Or.inr ⟨w, by rw [Nat.mul_comm]; omega⟩)⟩

/-! ### §7.4  Theorem 4 -/

/--
**Theorem 4.**  For every base `b > 1`, every pair `1 ≤ e1 < e2` and every
factorisation `b - 1 = 2^a·m` with `m` odd, the residue set is nonempty **iff**
`a ≠ 1` and one of `a ≤ 2`, `e2 - e1` odd, `e1 ∣ a - 1` holds.

No odd prime divisor of `b-1` appears anywhere: the classification is a
condition on `v_2(b-1)` and the pair alone, which is why the dead bases form a
union of congruence classes mod powers of two.
@isnad1 id=iff.6h6v.s7.6e4ca2ffde9d from=translated src=- shape=8090a17b vocab=35b3ed67
-/
theorem residues_nonempty_iff {b e1 e2 T a m : Nat} (hb : 1 < b) (he1 : 1 ≤ e1) (hlt : e1 < e2)
    (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ a * m) :
    (∃ ρ, (ρ ^ e1 + ρ ^ e2) % (b - 1) = T % (b - 1)) ↔ LiveTwoAdic a e1 e2 := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact live_of_residue hb he1 hlt hm hT hM hρ
  · rintro ⟨hne, hcases⟩
    rcases Nat.lt_or_ge a 3 with hsmall | hbig
    · have ha : a = 0 ∨ a = 2 := by omega
      rcases ha with rfl | rfl
      · rw [Nat.pow_zero, Nat.one_mul] at hM
        exact ⟨0, residue_of_even_base hb he1 (by omega) hT (by omega)⟩
      · exact ⟨m ^ 2, residue_of_two_adic_two hb he1 (by omega) hm hT hM⟩
    · rcases hcases with h | h | h
      · omega
      · obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
        exact ⟨_, residue_of_odd_gap hb hm hT hM (by omega)⟩
      · obtain ⟨V, hV⟩ := h
        have hVpos : 1 ≤ V := by
          rcases Nat.eq_zero_or_pos V with rfl | h'
          · omega
          · exact h'
        have hMV : b - 1 = 2 ^ (V * e1 + 1) * m := by
          rw [hM, Nat.mul_comm V e1]
          have hidx : e1 * V + 1 = a := by omega
          rw [hidx]
        exact ⟨_, residue_of_dvd hb he1 hlt hVpos hm hT hMV⟩

/-- **Theorem 4, dead form** — the classification read as a list of dead classes,
which is how the informal account states it.
@isnad1 id=iff.6h6v.s8.717f7b46c764 from=translated src=- shape=6fdb4716 vocab=1ed20a06
-/
theorem residues_empty_iff {b e1 e2 T a m : Nat} (hb : 1 < b) (he1 : 1 ≤ e1) (hlt : e1 < e2)
    (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ a * m) :
    (∀ ρ, (ρ ^ e1 + ρ ^ e2) % (b - 1) ≠ T % (b - 1))
      ↔ (a = 1 ∨ (3 ≤ a ∧ (e2 - e1) % 2 = 0 ∧ ¬ e1 ∣ (a - 1))) := by
  have hiff := residues_nonempty_iff hb he1 hlt hm hT hM
  constructor
  · intro hall
    have hnot : ¬ LiveTwoAdic a e1 e2 := fun hl => (hiff.2 hl).elim (fun ρ hρ => hall ρ hρ)
    by_cases h1' : a = 1
    · exact Or.inl h1'
    by_cases h2' : a ≤ 2
    · exact absurd ⟨h1', Or.inl h2'⟩ hnot
    by_cases h3 : (e2 - e1) % 2 = 1
    · exact absurd ⟨h1', Or.inr (Or.inl h3)⟩ hnot
    by_cases h4 : e1 ∣ (a - 1)
    · exact absurd ⟨h1', Or.inr (Or.inr h4)⟩ hnot
    exact Or.inr ⟨by omega, by omega, h4⟩
  · intro hdead ρ hρ
    obtain ⟨hne, hcases⟩ := live_of_residue hb he1 hlt hm hT hM hρ
    rcases hdead with rfl | ⟨h3, hpar, hnd⟩
    · exact hne rfl
    · rcases hcases with h | h | h
      · omega
      · omega
      · exact hnd h

/-- The operative form: a base in a dead 2-adic class admits no `n` whose digit
sums satisfy the identity, hence no solution.  Same shape as
`no_nice_of_mod_four`, of which this is the generalisation.
@isnad1 id=false.7h6v.s7.d29d91813dd9 from=translated src=- shape=eee48da8 vocab=837dace5
-/
theorem no_nice_of_two_adic {b e1 e2 a m n : Nat} (hb : 1 < b) (he1 : 1 ≤ e1) (hlt : e1 < e2)
    (hm : m % 2 = 1) (hM : b - 1 = 2 ^ a * m)
    (hdead : a = 1 ∨ (3 ≤ a ∧ (e2 - e1) % 2 = 0 ∧ ¬ e1 ∣ (a - 1)))
    (hT : 2 * (digitSum b (n ^ e1) + digitSum b (n ^ e2)) = b * (b - 1)) : False := by
  have hd1' : n ^ e1 % (b-1) = digitSum b (n ^ e1) % (b-1) := digitSum_mod hb _
  have hd2' : n ^ e2 % (b-1) = digitSum b (n ^ e2) % (b-1) := digitSum_mod hb _
  have hsum : (n ^ e1 + n ^ e2) % (b-1)
      = (digitSum b (n ^ e1) + digitSum b (n ^ e2)) % (b-1) := by
    rw [Nat.add_mod, hd1', hd2', ← Nat.add_mod]
  exact (residues_empty_iff hb he1 hlt hm hT hM).2 hdead n hsum

/-! ### §7.5  Non-vacuity, and the theorem firing

The `(2,4)` pair at base 17 is the sharpest example available: `17 % 3 = 2` so
Theorem 1 says nothing, `17 % 4 = 1` so Theorem 3 says nothing, and
`N(2,4) = 12` with `17 ∤ 12` so Theorem 2 says nothing.  `v_2(16) = 4`, the gap
`4 - 2 = 2` is even and `2 ∤ 3`, so Theorem 4 alone kills it.  Base 33 — the very
next base with `v_2(b-1) ≥ 3` that A leaves alive — is *not* killed, and the
witness is exhibited, so the boundary `e1 ∣ a-1` is sharp and not slack. -/

/-- `(2,4)` in base 17: no residue at all.  `T = 136`, `2·136 = 17·16`.
@isnad1 id=ne.0h1v.s6.b29481ea222e from=translated src=- shape=589029cd vocab=b2ffaa0b
-/
theorem two_four_base_seventeen_dead (ρ : Nat) : (ρ ^ 2 + ρ ^ 4) % 16 ≠ 136 % 16 :=
  (residues_empty_iff (b := 17) (a := 4) (m := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).2 (Or.inr ⟨by decide, by decide, by decide⟩) ρ

/-- ...and base 33 is alive, with the witness `ρ = 2^2·1 = 4` the theorem
predicts: `v_2(32) = 5` and `e1 = 2 ∣ 4`.
@isnad1 id=eq.0h0v.s6.356c1302ec4b from=translated src=- shape=8c5e922d vocab=b2ffaa0b
-/
theorem two_four_base_thirtythree_live : (4 ^ 2 + 4 ^ 4) % 32 = 528 % 32 := by decide

/-- Base 10 had better be alive, or the theorem would contradict 69.
`v_2(9) = 0`, so the `a = 0` clause applies and `ρ = 0` is a residue — as is 69
itself, which is the residue the solution actually lives in.
@isnad1 id=livetwoa.0h0v.s4.73f0b43615ec from=translated src=- shape=b850a97b vocab=ef792921
-/
theorem base_ten_live : LiveTwoAdic 0 2 3 := ⟨by decide, Or.inl (by decide)⟩

/--
@isnad1 id=eq.0h0v.s6.1c9bbc6092af from=translated src=- shape=8c5e922d vocab=b2ffaa0b
-/
theorem base_ten_residue : (69 ^ 2 + 69 ^ 3) % 9 = 45 % 9 := by decide

/-- Theorem 3 is the `a = 1` case: `b ≡ 3 (mod 4)` is exactly `v_2(b-1) = 1`.
Re-deriving `residues_empty_of_mod_four` from Theorem 4, for every pair.
@isnad1 id=ne.5h5v.s7.e7c1f05cc2c8 from=translated src=- shape=d2901dc6 vocab=407ce26c
-/
theorem residues_empty_of_mod_four_via_two_adic {b e1 e2 T ρ : Nat}
    (hb : 1 < b) (he1 : 1 ≤ e1) (hlt : e1 < e2) (hmod : b % 4 = 3)
    (hT : 2 * T = b * (b - 1)) :
    (ρ ^ e1 + ρ ^ e2) % (b - 1) ≠ T % (b - 1) := by
  refine (residues_empty_iff (a := 1) (m := (b-1)/2) hb he1 hlt (by omega) hT ?_).2
    (Or.inl rfl) ρ
  rw [Nat.pow_one]
  omega

/-! ### §7.6  The single-exponent family

`n^e` alone pandigital is the `E = e` member of the family, and it has been
proposed as a compute target in its own right — which makes "which bases are
live" load-bearing there.  The same valuation count answers it, and more simply,
because `v_2(ρ^e) = e·v_2(ρ)` with no cofactor `1 + ρ^d` to think about:

> `R_b = ∅`  ⟺  `a ≥ 1` and `e ∤ a - 1`.

Note `a = 1` is **live** here — Theorem 3 needs the sum `ρ^e1 + ρ^e2 ≡ 2ρ`, and a
single exponent has no partner to pair with — which is why `b ≡ 3 (mod 4)`
survives for `n^4` and not for `(1,3)`. -/

/-- `a - 1 = e·V` (including `V = 0`, i.e. `a = 1`): `ρ = 2^V·m`.
@isnad1 id=eq.5h5v.s7.39608ea06247 from=translated src=- shape=cad59cf6 vocab=407ce26c
-/
theorem residue_single_of_dvd {b e T m V : Nat} (hb : 1 < b) (he : 1 ≤ e) (hm : m % 2 = 1)
    (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ (V * e + 1) * m) :
    (2 ^ V * m) ^ e % (b - 1) = T % (b - 1) := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  refine residue_of_odd_cofactor (w := V * (f+1)) (m := m) (W := m ^ f) hb hT hM
    (odd_pow hm f) ?_
  rw [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_succ (m := f), Nat.mul_comm (m ^ f) m]

/-- `a = 0`, i.e. `b` even: `ρ = 0`.
@isnad1 id=eq.4h3v.s7.53683a51aad7 from=translated src=- shape=d15b7e1e vocab=c7cb47a2
-/
theorem residue_single_of_even_base {b e T : Nat} (hb : 1 < b) (he : 1 ≤ e)
    (hT : 2 * T = b * (b - 1)) (hbe : b % 2 = 0) : (0:Nat) ^ e % (b - 1) = T % (b - 1) := by
  rw [Nat.zero_pow (by omega), target_zero hb hT hbe]
  simp

/-- **Theorem 4, single-exponent form.**  (`a - 1` is truncated subtraction, so
the `a = 0` disjunct is formally implied by the second; it is kept because the
mathematics has two cases — even base, and `v_2(b-1) ≡ 1 mod e` — not one.)
@isnad1 id=iff.5h5v.s7.602d65fbcad7 from=translated src=- shape=3924eb23 vocab=db831e56
-/
theorem residues_single_nonempty_iff {b e T a m : Nat} (hb : 1 < b) (he : 1 ≤ e)
    (hm : m % 2 = 1) (hT : 2 * T = b * (b - 1)) (hM : b - 1 = 2 ^ a * m) :
    (∃ ρ, ρ ^ e % (b - 1) = T % (b - 1)) ↔ (a = 0 ∨ e ∣ (a - 1)) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · exact Or.inl rfl
    obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    subst ha'
    have h2A : 2 * (2 ^ a' * m) = b - 1 := by rw [hM, ← Nat.mul_assoc, ← Nat.pow_succ']
    have hdvd : 2 ^ (a' + 1) ∣ (b - 1) := ⟨m, hM⟩
    have hstep : ∀ x y : Nat, x % (b - 1) = y % (b - 1) → x % 2 ^ (a'+1) = y % 2 ^ (a'+1) := by
      intro x y hxy
      rw [← Nat.mod_mod_of_dvd x hdvd, ← Nat.mod_mod_of_dvd y hdvd, hxy]
    have hSA : ρ ^ e % 2 ^ (a'+1) = 2 ^ a' := by
      rw [hstep _ _ (hρ.trans (target_eq hb hT h2A)), half_mod hm]
    have hSodd : ρ ^ e = 2 ^ a' * (2 * (ρ ^ e / 2 ^ (a'+1)) + 1) := by
      refine sum_shape ?_
      have := Nat.div_add_mod (ρ ^ e) (2 ^ (a'+1))
      omega
    have hUodd : (2 * (ρ ^ e / 2 ^ (a'+1)) + 1) % 2 = 1 := by omega
    rcases Nat.eq_zero_or_pos ρ with rfl | hρpos
    · have hz : (0:Nat) ^ e = 0 := Nat.zero_pow (by omega)
      have hpos : 0 < 2 ^ a' * (2 * ((0:Nat) ^ e / 2 ^ (a'+1)) + 1) :=
        Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
      omega
    obtain ⟨w, u, hu, huodd⟩ := two_adic_split ρ hρpos
    have hfac : ρ ^ e = 2 ^ (w * e) * u ^ e := by rw [hu, Nat.mul_pow, ← Nat.pow_mul]
    have hwe := two_pow_odd_unique (odd_pow huodd e) hUodd (hfac.symm.trans hSodd)
    exact Or.inr ⟨w, by rw [Nat.mul_comm]; omega⟩
  · intro h
    rcases h with rfl | ⟨V, hV⟩
    · rw [Nat.pow_zero, Nat.one_mul] at hM
      exact ⟨0, residue_single_of_even_base hb he hT (by omega)⟩
    · rcases Nat.eq_zero_or_pos a with rfl | hapos
      · rw [Nat.pow_zero, Nat.one_mul] at hM
        exact ⟨0, residue_single_of_even_base hb he hT (by omega)⟩
      · refine ⟨2 ^ V * m, residue_single_of_dvd hb he hm hT ?_⟩
        rw [hM, Nat.mul_comm V e]
        have hidx : e * V + 1 = a := by omega
        rw [hidx]

/-- `n^4` in base 29 has no residue: `v_2(28) = 2` and `4 ∤ 1`.  This is one of the
bases the single-exponent family loses, and base 8 — where the only known
solution `42^4` lives — is even, hence `a = 0`, hence live.
@isnad1 id=ne.0h1v.s5.b1ff2675d08d from=translated src=- shape=13b567fb vocab=df461349
-/
theorem single_four_base_twentynine_dead (ρ : Nat) : ρ ^ 4 % 28 ≠ 406 % 28 := by
  intro h
  rcases (residues_single_nonempty_iff (b := 29) (e := 4) (a := 2) (m := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide)).1 ⟨ρ, h⟩ with h' | h' <;>
    revert h' <;> decide

/-- ...and base 33 is live, with the residue `2^1·1 = 2` the theorem predicts:
`v_2(32) = 5` and `4 ∣ 4`.
@isnad1 id=eq.0h0v.s5.bef9773609cc from=translated src=- shape=2990c449 vocab=df461349
-/
theorem single_four_base_thirtythree_live : (2:Nat) ^ 4 % 32 = 528 % 32 := by decide

/-! ## §8  Theorem 7 — the `2/E` greedy construction

`n mod b^(i+1)` pins digit `i` of `n^e1` *and* digit `i` of `n^e2`: two slots per
digit of `n`, the conservation law the exhaustive search runs on.  Theorem 7 turns
that budget into a construction.  Build `n` from the bottom; at level `i` the new
digit `x` moves each of the two slots along an arithmetic progression, and if the
common differences are units the progressions are bijections, so each already-used
value kills at most one `x` and the two progressions collide at most once.  With
`|Used| = 2i` that is `4i + 2` losses out of `b` choices, and `i ≤ d-1 ≈ b/E - 1`.

The output is a `d`-digit `n` whose `2d` low slots are pairwise distinct, hence a
digit deficiency of at most `b - 2d ≈ b(1 - 2/E)`. -/

/-! ### §8.0  Digit slots -/

/-- Digit `i` of `x` in base `b`, counting from the least significant.-/
def slot (b i x : Nat) : Nat := x / b ^ i % b

/--
@isnad1 id=lt.1h3v.s4.ee52c3a1c188 from=translated src=- shape=e93141a0 vocab=e75e975b
-/
theorem slot_lt {b : Nat} (hb : 0 < b) (i x : Nat) : slot b i x < b := Nat.mod_lt _ hb

/--
@isnad1 id=eq.0h2v.s4.dee7f9474a20 from=translated src=- shape=4ca1e92e vocab=3cd93737
-/
theorem slot_zero (b x : Nat) : slot b 0 x = x % b := by
  show x / b ^ 0 % b = x % b
  rw [Nat.pow_zero, Nat.div_one]

/-- A slot sees only the low `i+1` digits: this is the p-adic boundary, stated.
@isnad1 id=eq.1h4v.s6.be10b79674c1 from=translated src=- shape=bac06d9c vocab=fc408ed2
-/
theorem slot_of_mod {b i x y : Nat} (h : x % b ^ (i + 1) = y % b ^ (i + 1)) :
    slot b i x = slot b i y := by
  have hp : b ^ (i + 1) = b ^ i * b := Nat.pow_succ b i
  show x / b ^ i % b = y / b ^ i % b
  rw [← Nat.mod_mul_right_div_self x (b ^ i) b, ← Nat.mod_mul_right_div_self y (b ^ i) b,
      ← hp, h]

/-- Hence `n mod b^(i+1)` pins slot `i` of `n^e` — two slots per digit of `n`.
@isnad1 id=eq.1h5v.s6.38ee9df1cb99 from=translated src=- shape=2c8aab83 vocab=fc408ed2
-/
theorem slot_pow_of_mod {b i x y e : Nat} (h : x % b ^ (i + 1) = y % b ^ (i + 1)) :
    slot b i (x ^ e) = slot b i (y ^ e) := by
  refine slot_of_mod ?_
  rw [Nat.pow_mod, h, ← Nat.pow_mod]

/-- Every slot below the digit count really is one of the digits.
@isnad1 id=mem.2h3v.s5.00f4c9396354 from=translated src=- shape=f1a45e9d vocab=356bb6e6
-/
theorem slot_mem_digits {b : Nat} (hb : 1 < b) :
    ∀ x i, i < numDigits b x → slot b i x ∈ digits b x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro i hi
    have hx : 0 < x := by
      rcases Nat.eq_zero_or_pos x with rfl | h
      · rw [numDigits_zero] at hi; omega
      · exact h
    have hnum : numDigits b x = numDigits b (x / b) + 1 := by
      rw [numDigits, dite_eq_left ⟨hb, hx⟩]
    rw [digits_step hb hx]
    match i with
    | 0 => rw [slot_zero]; exact List.Mem.head _
    | (j + 1) =>
      have hd : slot b (j + 1) x = slot b j (x / b) := by
        show x / b ^ (j + 1) % b = x / b / b ^ j % b
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (b ^ j) b]
      rw [hd]
      exact List.Mem.tail _ (ih (x / b) (Nat.div_lt_self hx hb) j (by omega))

/-! ### §8.1  The digit ladder

`(r + x·b^i)^e ≡ r^e + e·r^(e-1)·x·b^i (mod b^(i+1))` for `i ≥ 1`: every binomial
term from `x^2b^{2i}` up is divisible by `b^(i+1)`, because `2i ≥ i+1`.  This is the
same recurrence the CUDA and Vulkan kernels advance the digit with. -/

/--
@isnad1 id=eq.1h5v.s7.4f2aa857e1c3 from=translated src=- shape=9ba23979 vocab=f7476a03
-/
theorem add_pow_ladder {b i : Nat} (hi : 1 ≤ i) (r x : Nat) : ∀ e,
    (r + x * b ^ i) ^ e % b ^ (i + 1)
      = (r ^ e + e * r ^ (e - 1) * x * b ^ i) % b ^ (i + 1) := by
  obtain ⟨c, hc⟩ : ∃ c, b ^ i * b ^ i = b ^ (i + 1) * c := by
    refine ⟨b ^ (i - 1), ?_⟩
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  intro e
  induction e with
  | zero => simp
  | succ e ih =>
    match e with
    | 0 => simp
    | (e' + 1) =>
      -- `E = e'+1 ≥ 1`, so `r^(E-1) * r = r^E` and the cross term is a genuine
      -- multiple of `b^i·b^i`.
      have key : (r ^ (e' + 1) + (e' + 1) * r ^ e' * x * b ^ i) * (r + x * b ^ i)
          = (r ^ (e' + 2) + (e' + 2) * r ^ (e' + 1) * x * b ^ i)
            + ((e' + 1) * r ^ e' * x * x) * (b ^ i * b ^ i) := by
        have hr : r ^ (e' + 2) = r ^ (e' + 1) * r := by rw [Nat.pow_succ]
        have hr' : r ^ (e' + 1) = r ^ e' * r := by rw [Nat.pow_succ]
        rw [hr, hr']
        simp only [Nat.add_mul, Nat.mul_add, Nat.succ_mul]
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
      have hmul : (e' + 1) * r ^ e' * x * x * (b ^ i * b ^ i)
          = b ^ (i + 1) * ((e' + 1) * r ^ e' * x * x * c) := by
        rw [hc]; exact Nat.mul_left_comm _ _ _
      calc (r + x * b ^ i) ^ (e' + 2) % b ^ (i + 1)
          = (r + x * b ^ i) ^ (e' + 1) % b ^ (i + 1) * ((r + x * b ^ i) % b ^ (i + 1))
              % b ^ (i + 1) := by rw [Nat.pow_succ, Nat.mul_mod]
        _ = (r ^ (e' + 1) + (e' + 1) * r ^ e' * x * b ^ i) % b ^ (i + 1)
              * ((r + x * b ^ i) % b ^ (i + 1)) % b ^ (i + 1) := by
              rw [show (e' + 1) - 1 = e' from rfl] at ih; rw [ih]
        _ = (r ^ (e' + 1) + (e' + 1) * r ^ e' * x * b ^ i) * (r + x * b ^ i)
              % b ^ (i + 1) := by rw [← Nat.mul_mod]
        _ = ((r ^ (e' + 2) + (e' + 2) * r ^ (e' + 1) * x * b ^ i)
              + b ^ (i + 1) * ((e' + 1) * r ^ e' * x * x * c)) % b ^ (i + 1) := by
              rw [key, hmul]
        _ = (r ^ (e' + 2) + (e' + 2) * r ^ (e' + 1) * x * b ^ i) % b ^ (i + 1) :=
              Nat.add_mul_mod_self_left _ _ _

/-- The ladder as the greedy uses it: adding digit `x` at level `i` moves slot `i`
of `n^e` along the progression with common difference `e·r^(e-1) (mod b)`.
@isnad1 id=eq.2h5v.s7.42daaab8ef54 from=translated src=- shape=c8cf8615 vocab=d2a51d15
-/
theorem slot_step {b i : Nat} (hb : 0 < b) (hi : 1 ≤ i) (r x e : Nat) :
    slot b i ((r + x * b ^ i) ^ e) = (slot b i (r ^ e) + e * r ^ (e - 1) * x) % b := by
  have hstep : slot b i ((r + x * b ^ i) ^ e)
      = slot b i (r ^ e + e * r ^ (e - 1) * x * b ^ i) := slot_of_mod (add_pow_ladder hi r x e)
  have hbi : 0 < b ^ i := Nat.pow_pos hb
  rw [hstep]
  show (r ^ e + e * r ^ (e - 1) * x * b ^ i) / b ^ i % b = (r ^ e / b ^ i % b + _) % b
  rw [Nat.mul_comm (e * r ^ (e - 1) * x) (b ^ i), Nat.add_mul_div_left _ _ hbi,
      Nat.mod_add_mod]

/-! ### §8.2  Two injectivity lemmas

The progressions are bijections when their common differences are units, and the
*difference* of the two progressions is a bijection when `α1 - α2` is — which is
the side condition Theorem 7 carries, here supplied as an explicit unit `β`. -/

/-- `x ↦ (A + α·x) mod b` is injective on `{0,…,b-1}` when `α` is a unit.
@isnad1 id=eq.5h5v.s6.d57bc5b5027e from=translated src=- shape=7bc8241c vocab=b6618d57
-/
theorem lin_inj {b α A x y : Nat} (hb : 0 < b) (hα : Nat.Coprime b α)
    (hx : x < b) (hy : y < b) (h : (A + α * x) % b = (A + α * y) % b) : x = y := by
  rcases Nat.le_total x y with hle | hle
  · obtain ⟨t, rfl⟩ : ∃ t, y = x + t := ⟨y - x, by omega⟩
    have hmul : α * (x + t) = α * x + α * t := Nat.mul_add α x t
    have h1' : A + α * x ≤ A + α * (x + t) := by omega
    have hd : b ∣ A + α * (x + t) - (A + α * x) :=
      (dvd_sub_iff_mod_eq hb h1').mpr h.symm
    have he : A + α * (x + t) - (A + α * x) = α * t := by omega
    rw [he] at hd
    have ht : t = 0 := Nat.eq_zero_of_dvd_of_lt (hα.dvd_of_dvd_mul_left hd) (by omega)
    omega
  · obtain ⟨t, rfl⟩ : ∃ t, x = y + t := ⟨x - y, by omega⟩
    have hmul : α * (y + t) = α * y + α * t := Nat.mul_add α y t
    have h1' : A + α * y ≤ A + α * (y + t) := by omega
    have hd : b ∣ A + α * (y + t) - (A + α * y) :=
      (dvd_sub_iff_mod_eq hb h1').mpr h
    have he : A + α * (y + t) - (A + α * y) = α * t := by omega
    rw [he] at hd
    have ht : t = 0 := Nat.eq_zero_of_dvd_of_lt (hα.dvd_of_dvd_mul_left hd) (by omega)
    omega

/-- The two progressions collide for at most one digit `x`.  This is the side
condition of Theorem 7: `α1 - α2` must be a unit, supplied as `β` with
`α2 + β ≡ α1`.
@isnad1 id=eq.7h8v.s7.8e260bf6dec6 from=translated src=- shape=741d22c2 vocab=b6618d57
-/
theorem clash_inj {b α1 α2 β A1 A2 x y : Nat} (hb : 0 < b) (hβ : Nat.Coprime b β)
    (hsep : (α2 + β) % b = α1 % b) (hx : x < b) (hy : y < b)
    (h1 : (A1 + α1 * x) % b = (A2 + α2 * x) % b)
    (h2 : (A1 + α1 * y) % b = (A2 + α2 * y) % b) : x = y := by
  -- add the two collision equations, so that `A1`, `A2` cancel
  have hsum : (A1 + α1 * x + (A2 + α2 * y)) % b = (A2 + α2 * x + (A1 + α1 * y)) % b := by
    rw [Nat.add_mod, h1, ← h2, ← Nat.add_mod]
  have hcomm1 : A1 + α1 * x + (A2 + α2 * y) = α1 * x + α2 * y + (A1 + A2) := by omega
  have hcomm2 : A2 + α2 * x + (A1 + α1 * y) = α2 * x + α1 * y + (A1 + A2) := by omega
  rw [hcomm1, hcomm2] at hsum
  have hcancel : (α1 * x + α2 * y) % b = (α2 * x + α1 * y) % b := mod_add_cancel hb hsum
  -- replace `α1` by `α2 + β`
  have hsub : ∀ z, (α1 * z) % b = (α2 * z + β * z) % b := by
    intro z
    rw [Nat.mul_mod, ← hsep, ← Nat.mul_mod, Nat.add_mul]
  have hL : (α1 * x + α2 * y) % b = (α2 * x + α2 * y + β * x) % b := by
    rw [Nat.add_mod, hsub x, ← Nat.add_mod]
    congr 1
    omega
  have hR : (α2 * x + α1 * y) % b = (α2 * x + α2 * y + β * y) % b := by
    rw [Nat.add_mod, hsub y, ← Nat.add_mod]
    congr 1
    omega
  rw [hL, hR] at hcancel
  have hL' : α2 * x + α2 * y + β * x = β * x + (α2 * x + α2 * y) := by omega
  have hR' : α2 * x + α2 * y + β * y = β * y + (α2 * x + α2 * y) := by omega
  rw [hL', hR'] at hcancel
  have hfin : (β * x) % b = (β * y) % b := mod_add_cancel hb hcancel
  exact lin_inj (A := 0) hb hβ hx hy (by rw [Nat.zero_add, Nat.zero_add]; exact hfin)

/-! ### §8.3  Counting

Core has `List.countP` but not the four facts the pigeonhole needs, so they are
proved here.  `memb` is a decidable membership test that reduces in the kernel,
in the style of `occ` in §5. -/

/-- Membership as a `Bool`, so it can be counted.-/
def memb (v : Nat) : List Nat → Bool
  | [] => false
  | a :: l => (a == v) || memb v l

/--
@isnad1 id=eq.0h1v.s3.7650e98b33cd from=translated src=- shape=3df3c22a vocab=d75f8160
-/
theorem memb_nil (v : Nat) : memb v [] = false := rfl

/--
@isnad1 id=eq.0h3v.s4.0c9749189262 from=translated src=- shape=6194dc8f vocab=5f89e98b
-/
theorem memb_cons (v a : Nat) (l : List Nat) :
    memb v (a :: l) = ((a == v) || memb v l) := rfl

/--
@isnad1 id=iff.0h2v.s4.81808fbae7a0 from=translated src=- shape=d6702376 vocab=06ea8aa4
-/
theorem memb_iff (v : Nat) : ∀ l : List Nat, memb v l = true ↔ v ∈ l := by
  intro l
  induction l with
  | nil => rw [memb_nil]; simp
  | cons a t ih =>
    rw [memb_cons, List.mem_cons, Bool.or_eq_true, beq_iff_eq, ih]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

/--
@isnad1 id=le.0h3v.s5.67284cf291c3 from=translated src=- shape=0509e946 vocab=14720d2a
-/
theorem countP_or_le (p q : Nat → Bool) : ∀ l : List Nat,
    List.countP (fun a => p a || q a) l ≤ List.countP p l + List.countP q l := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    by_cases hp : p a = true <;> by_cases hq : q a = true <;> simp [hp, hq] <;> omega

/-- A predicate that can hold at only one element of a duplicate-free list is
counted at most once.
@isnad1 id=le.2h2v.s6.40fa6b325d08 from=translated src=- shape=58efd042 vocab=a1e4dc30
-/
theorem countP_le_one {p : Nat → Bool} : ∀ l : List Nat, l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, p x = true → p y = true → x = y) → List.countP p l ≤ 1 := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
    intro hnd huniq
    rw [List.nodup_cons] at hnd
    rw [List.countP_cons]
    by_cases hpa : p a = true
    · have hzero : List.countP p t = 0 := by
        refine List.countP_eq_zero.mpr ?_
        intro y hy hpy
        have : y = a := huniq y (List.Mem.tail _ hy) a (List.Mem.head _) hpy hpa
        exact hnd.1 (this ▸ hy)
      simp [hpa, hzero]
    · have := ih hnd.2 (fun x hx y hy => huniq x (List.Mem.tail _ hx) y (List.Mem.tail _ hy))
      simp [hpa]
      omega

/-- If `f` is injective on `l`, at most `U.length` of `l`'s elements land in `U`.
@isnad1 id=le.2h3v.s6.8586d42a840c from=translated src=- shape=4abbad5a vocab=de721b1e
-/
theorem countP_memb_le {f : Nat → Nat} {l : List Nat} (hl : l.Nodup)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    ∀ U : List Nat, List.countP (fun x => memb (f x) U) l ≤ U.length := by
  intro U
  induction U with
  | nil =>
    have : List.countP (fun x => memb (f x) ([] : List Nat)) l = 0 :=
      List.countP_eq_zero.mpr (fun a _ h => by simp [memb] at h)
    omega
  | cons u U' ih =>
    have hsplit : ∀ x : Nat, memb (f x) (u :: U') = ((f x == u) || memb (f x) U') := by
      intro x
      rw [memb_cons]
      by_cases h : u = f x
      · rw [h]
      · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]
    have hrw : List.countP (fun x => memb (f x) (u :: U')) l
        = List.countP (fun x => (f x == u) || memb (f x) U') l := by
      refine List.countP_congr ?_
      intro x _
      rw [hsplit x]
    have hone : List.countP (fun x => f x == u) l ≤ 1 := by
      refine countP_le_one l hl ?_
      intro x hx y hy hpx hpy
      exact hinj x hx y hy (by simp at hpx hpy; rw [hpx, hpy])
    have := countP_or_le (fun x => f x == u) (fun x => memb (f x) U') l
    simp only [List.length_cons]
    omega

/--
@isnad1 id=eq.0h2v.s5.4457f9f210d8 from=translated src=- shape=1409dffb vocab=52d85661
-/
theorem countP_split (p : Nat → Bool) : ∀ l : List Nat,
    List.countP p l + List.countP (fun a => !p a) l = l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.length_cons]
    by_cases hp : p a = true <;> simp [hp] <;> omega

/--
@isnad1 id=ex.1h2v.s5.0046d3eed659 from=translated src=- shape=7e02af4f vocab=70641547
-/
theorem exists_of_countP_pos {p : Nat → Bool} : ∀ l : List Nat, 0 < List.countP p l →
    ∃ a, a ∈ l ∧ p a = true := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    rw [List.countP_cons] at h
    by_cases hp : p a = true
    · exact ⟨a, List.Mem.head _, hp⟩
    · simp only [hp] at h
      obtain ⟨y, hy, hpy⟩ := ih h
      exact ⟨y, List.Mem.tail _ hy, hpy⟩

/--
@isnad1 id=eq.0h2v.s4.3ae308c510ef from=translated src=- shape=cbe05cfc vocab=286b3144
-/
theorem countP_eq_length_filter (p : Nat → Bool) : ∀ l : List Nat,
    List.countP p l = (l.filter p).length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.filter_cons]
    by_cases hp : p a = true <;> simp [hp, ih]

/-! ### §8.4  One greedy step

At most `2|U| + 2` of the `b` digits are lost: `|U|` to each progression hitting an
already-used value, one to the two progressions colliding, and one to the leading
digit having to be nonzero. -/

/-- The pigeonhole, over abstract slot maps: two maps injective on `{0,…,b-1}`
whose coincidence set has at most one element leave a nonzero digit avoiding `U`
in both, as soon as `2|U| + 2 < b`.
@isnad1 id=ex.5h4v.s7.27e9621a6b37 from=translated src=- shape=1b6dce9a vocab=0a946462
-/
theorem exists_good_digit {b : Nat} (hb : 0 < b) (s1 s2 : Nat → Nat)
    (hinj1 : ∀ x, x < b → ∀ y, y < b → s1 x = s1 y → x = y)
    (hinj2 : ∀ x, x < b → ∀ y, y < b → s2 x = s2 y → x = y)
    (hclash : ∀ x, x < b → ∀ y, y < b → s1 x = s2 x → s1 y = s2 y → x = y)
    (U : List Nat) (hcount : 2 * U.length + 2 < b) :
    ∃ x, 0 < x ∧ x < b ∧ s1 x ∉ U ∧ s2 x ∉ U ∧ s1 x ≠ s2 x := by
  have hrange : ∀ x ∈ List.range b, x < b := fun x hx => List.mem_range.mp hx
  -- each of the four losses is bounded
  have hz : List.countP (fun x => x == 0) (List.range b) ≤ 1 := by
    refine countP_le_one _ List.nodup_range ?_
    intro x _ y _ hx hy
    simp only [beq_iff_eq] at hx hy
    omega
  have hm1 : List.countP (fun x => memb (s1 x) U) (List.range b) ≤ U.length :=
    countP_memb_le List.nodup_range
      (fun x hx y hy h => hinj1 x (hrange x hx) y (hrange y hy) h) U
  have hm2 : List.countP (fun x => memb (s2 x) U) (List.range b) ≤ U.length :=
    countP_memb_le List.nodup_range
      (fun x hx y hy h => hinj2 x (hrange x hx) y (hrange y hy) h) U
  have hc : List.countP (fun x => s1 x == s2 x) (List.range b) ≤ 1 := by
    refine countP_le_one _ List.nodup_range ?_
    intro x hx y hy hpx hpy
    simp only [beq_iff_eq] at hpx hpy
    exact hclash x (hrange x hx) y (hrange y hy) hpx hpy
  -- so the bad digits do not exhaust the base
  have hsum1 := countP_or_le (fun x => (x == 0) || memb (s1 x) U)
      (fun x => memb (s2 x) U || (s1 x == s2 x)) (List.range b)
  have hsum2 := countP_or_le (fun x => x == 0) (fun x => memb (s1 x) U) (List.range b)
  have hsum3 := countP_or_le (fun x => memb (s2 x) U) (fun x => s1 x == s2 x) (List.range b)
  have hlen : (List.range b).length = b := List.length_range
  have hsplit := countP_split
    (fun x => ((x == 0) || memb (s1 x) U) || (memb (s2 x) U || (s1 x == s2 x)))
    (List.range b)
  have hpos : 0 < List.countP
      (fun x => !(((x == 0) || memb (s1 x) U) || (memb (s2 x) U || (s1 x == s2 x))))
      (List.range b) := by omega
  obtain ⟨x, hxmem, hxbad⟩ := exists_of_countP_pos _ hpos
  have hxb : x < b := hrange x hxmem
  simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hxbad
  obtain ⟨⟨hx0, hu1⟩, hu2, hne⟩ := hxbad
  refine ⟨x, Nat.pos_of_ne_zero hx0, hxb, ?_, ?_, hne⟩
  · intro hmem
    rw [(memb_iff _ U).mpr hmem] at hu1
    exact Bool.noConfusion hu1
  · intro hmem
    rw [(memb_iff _ U).mpr hmem] at hu2
    exact Bool.noConfusion hu2

/-! ### §8.5  The greedy induction

The invariant carried up the levels: `r` has exactly `i` digits, its last digit is
the chosen unit `ρ` (so every progression's common difference stays the same), and
`U` is the list of the `2i` slot values already placed — pairwise distinct, all
`< b`, and each genuinely a slot of `r^e1` or of `r^e2`. -/

/-- The greedy state after `i` levels.-/
def GreedyInv (b e1 e2 ρ i r : Nat) (U : List Nat) : Prop :=
  b ^ (i - 1) ≤ r ∧ r < b ^ i ∧ r % b = ρ ∧
  U.length = 2 * i ∧ U.Nodup ∧ (∀ v ∈ U, v < b) ∧
  (∀ v ∈ U, ∃ j, j < i ∧ (v = slot b j (r ^ e1) ∨ v = slot b j (r ^ e2)))

/-- Level 0: the starting digit `ρ`, whose two slots already differ.
@isnad1 id=greedyin.4h4v.s7.d39db0fbd152 from=translated src=- shape=f482b890 vocab=7a9e5b62
-/
theorem greedy_base {b e1 e2 ρ : Nat} (hb : 1 < b) (hρ : 0 < ρ) (hρb : ρ < b)
    (hstart : ρ ^ e1 % b ≠ ρ ^ e2 % b) :
    GreedyInv b e1 e2 ρ 1 ρ [ρ ^ e1 % b, ρ ^ e2 % b] := by
  refine ⟨?_, ?_, Nat.mod_eq_of_lt hρb, rfl, ?_, ?_, ?_⟩
  · rw [show (1 : Nat) - 1 = 0 from rfl, Nat.pow_zero]; omega
  · rw [Nat.pow_one]; exact hρb
  · rw [List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, List.nodup_nil⟩
    · intro h
      rcases List.mem_singleton.mp h with h'
      exact hstart h'
    · intro h; cases h
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact Nat.mod_lt _ (by omega)
    · rcases List.mem_singleton.mp hv' with rfl
      exact Nat.mod_lt _ (by omega)
  · intro v hv
    refine ⟨0, by omega, ?_⟩
    rw [slot_zero, slot_zero]
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact Or.inl rfl
    · rcases List.mem_singleton.mp hv' with rfl
      exact Or.inr rfl

/-- One level of the greedy.  `4i + 2 < b` is the whole content: `2i` used values,
each killing at most one digit in each of the two progressions, plus the one digit
where the progressions collide and the one that would make the leading digit `0`.
@isnad1 id=ex.9h8v.s7.fd1fd36f6237 from=translated src=- shape=d79b1c75 vocab=823707b3
-/
theorem greedy_step {b e1 e2 ρ β i r : Nat} (hb : 1 < b)
    (hce1 : Nat.Coprime b e1) (hce2 : Nat.Coprime b e2) (hcρ : Nat.Coprime b ρ)
    (hβ : Nat.Coprime b β)
    (hsep : (e2 * ρ ^ (e2 - 1) + β) % b = e1 * ρ ^ (e1 - 1) % b)
    (hi : 1 ≤ i) (hcount : 4 * i + 2 < b)
    (U : List Nat) (hinv : GreedyInv b e1 e2 ρ i r U) :
    ∃ r' U', GreedyInv b e1 e2 ρ (i + 1) r' U' := by
  obtain ⟨hlo, hhi, hmod, hlen, hnd, hltb, hslot⟩ := hinv
  have hb0 : 0 < b := by omega
  have hbi : 0 < b ^ i := Nat.pow_pos hb0
  -- the last digit of `r` is `ρ`, so `r` is a unit and the two common differences
  -- are the ones `hsep` speaks about
  have hcr : Nat.Coprime b r := by
    have hg : Nat.gcd b r = Nat.gcd ρ b := by rw [Nat.gcd_rec b r, hmod]
    show Nat.gcd b r = 1
    rw [hg]
    exact Nat.coprime_comm.mp hcρ
  have hα : ∀ e : Nat, (e * r ^ (e - 1)) % b = (e * ρ ^ (e - 1)) % b := by
    intro e
    rw [Nat.mul_mod, Nat.pow_mod, hmod, ← Nat.mul_mod]
  have hcα1 : Nat.Coprime b (e1 * r ^ (e1 - 1)) := hce1.mul_right (hcr.pow_right _)
  have hcα2 : Nat.Coprime b (e2 * r ^ (e2 - 1)) := hce2.mul_right (hcr.pow_right _)
  have hsep' : (e2 * r ^ (e2 - 1) + β) % b = e1 * r ^ (e1 - 1) % b := by
    rw [Nat.add_mod, hα e2, ← Nat.add_mod, hsep, ← hα e1]
  -- the pigeonhole picks the next digit
  obtain ⟨x, hx0, hxb, hxu1, hxu2, hxne⟩ :=
    exists_good_digit hb0
      (fun x => (slot b i (r ^ e1) + e1 * r ^ (e1 - 1) * x) % b)
      (fun x => (slot b i (r ^ e2) + e2 * r ^ (e2 - 1) * x) % b)
      (fun x hx y hy h => lin_inj hb0 hcα1 hx hy h)
      (fun x hx y hy h => lin_inj hb0 hcα2 hx hy h)
      (fun x hx y hy h1 h2 => clash_inj hb0 hβ hsep' hx hy h1 h2)
      U (by omega)
  refine ⟨r + x * b ^ i,
    slot b i ((r + x * b ^ i) ^ e1) :: slot b i ((r + x * b ^ i) ^ e2) :: U, ?_⟩
  -- the two new slots are exactly the two progression values
  have hs1 : slot b i ((r + x * b ^ i) ^ e1)
      = (slot b i (r ^ e1) + e1 * r ^ (e1 - 1) * x) % b := slot_step hb0 hi r x e1
  have hs2 : slot b i ((r + x * b ^ i) ^ e2)
      = (slot b i (r ^ e2) + e2 * r ^ (e2 - 1) * x) % b := slot_step hb0 hi r x e2
  -- the earlier slots are untouched: `r' ≡ r (mod b^(j+1))` for every `j < i`
  have hlow : ∀ j, j < i → ∀ e, slot b j ((r + x * b ^ i) ^ e) = slot b j (r ^ e) := by
    intro j hj e
    refine slot_pow_of_mod ?_
    obtain ⟨c, hc⟩ : ∃ c, b ^ i = b ^ (j + 1) * c :=
      ⟨b ^ (i - (j + 1)), by rw [← Nat.pow_add]; congr 1; omega⟩
    rw [hc, Nat.mul_left_comm]
    exact Nat.add_mul_mod_self_left _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : b ^ i = 1 * b ^ i := (Nat.one_mul _).symm
    rw [show i + 1 - 1 = i from rfl]
    calc b ^ i = 1 * b ^ i := this
      _ ≤ x * b ^ i := Nat.mul_le_mul_right _ hx0
      _ ≤ r + x * b ^ i := Nat.le_add_left _ _
  · calc r + x * b ^ i < b ^ i + x * b ^ i := by omega
      _ = (1 + x) * b ^ i := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ b * b ^ i := Nat.mul_le_mul_right _ (by omega)
      _ = b ^ (i + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  · obtain ⟨c, hc⟩ : ∃ c, b ^ i = b * c := ⟨b ^ (i - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩
    rw [hc, Nat.mul_left_comm, Nat.add_mul_mod_self_left, hmod]
  · rw [List.length_cons, List.length_cons, hlen]; omega
  · rw [List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, hnd⟩
    · intro h
      rcases List.mem_cons.mp h with heq | hmem
      · rw [hs1, hs2] at heq; exact hxne heq
      · rw [hs1] at hmem; exact hxu1 hmem
    · rw [hs2]; exact hxu2
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · rw [hs1]; exact Nat.mod_lt _ hb0
    · rcases List.mem_cons.mp hv' with rfl | hv''
      · rw [hs2]; exact Nat.mod_lt _ hb0
      · exact hltb v hv''
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact ⟨i, by omega, Or.inl rfl⟩
    · rcases List.mem_cons.mp hv' with rfl | hv''
      · exact ⟨i, by omega, Or.inr rfl⟩
      · obtain ⟨j, hj, hval⟩ := hslot v hv''
        exact ⟨j, by omega, by rw [hlow j hj e1, hlow j hj e2]; exact hval⟩

/-- The greedy runs to depth `d`.
@isnad1 id=ex.11h6v.s8.4cc36d76aaf4 from=translated src=- shape=5638e793 vocab=823707b3
-/
theorem greedy_reaches {b e1 e2 ρ β d : Nat} (hb : 1 < b)
    (hce1 : Nat.Coprime b e1) (hce2 : Nat.Coprime b e2)
    (hρ : 0 < ρ) (hρb : ρ < b) (hcρ : Nat.Coprime b ρ)
    (hstart : ρ ^ e1 % b ≠ ρ ^ e2 % b) (hβ : Nat.Coprime b β)
    (hsep : (e2 * ρ ^ (e2 - 1) + β) % b = e1 * ρ ^ (e1 - 1) % b)
    (hd : 1 ≤ d) (hcount : 4 * (d - 1) + 2 < b) :
    ∃ r U, GreedyInv b e1 e2 ρ d r U := by
  have main : ∀ i, 1 ≤ i → i ≤ d → ∃ r U, GreedyInv b e1 e2 ρ i r U := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ hle
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact ⟨ρ, _, greedy_base hb hρ hρb hstart⟩
      · obtain ⟨r, U, hinv⟩ := ih hi (by omega)
        exact greedy_step hb hce1 hce2 hcρ hβ hsep hi (by omega) U hinv
  exact main d hd (Nat.le_refl d)

/-! ### §8.6  Theorem 7

The `2d` distinct slots are `2d` distinct *digit values*, so at most `b - 2d` of
the `b` values can be missing.  With `d ≈ b/E` that is the `b(1 - 2/E)` of the
header — less than a random candidate's `≈ b/e`, which is the point: this is what
a *constructive* argument can reach, not what is typical. -/

/--
**Theorem 7, slot form** — the statement the `2/E` accounting is really about:
some `d`-digit `n` has `2d` *pairwise distinct* values among the low `d` slots of
`n^e1` and of `n^e2`.  The deficiency bound below is its corollary.
@isnad1 id=ex.11h6v.s8.59cc17d604fd from=translated src=- shape=ee7ad1f8 vocab=7182bf0d
-/
theorem greedy_distinct_slots {b e1 e2 ρ β d : Nat} (hb : 1 < b)
    (hce1 : Nat.Coprime b e1) (hce2 : Nat.Coprime b e2)
    (hρ : 0 < ρ) (hρb : ρ < b) (hcρ : Nat.Coprime b ρ)
    (hstart : ρ ^ e1 % b ≠ ρ ^ e2 % b) (hβ : Nat.Coprime b β)
    (hsep : (e2 * ρ ^ (e2 - 1) + β) % b = e1 * ρ ^ (e1 - 1) % b)
    (hd : 1 ≤ d) (hcount : 4 * (d - 1) + 2 < b) :
    ∃ n, ∃ U : List Nat, b ^ (d - 1) ≤ n ∧ n < b ^ d ∧ U.length = 2 * d ∧ U.Nodup ∧
      ∀ v ∈ U, ∃ j, j < d ∧ (v = slot b j (n ^ e1) ∨ v = slot b j (n ^ e2)) := by
  obtain ⟨r, U, hlo, hhi, hmod, hlen, hnd, hltb, hslot⟩ :=
    greedy_reaches hb hce1 hce2 hρ hρb hcρ hstart hβ hsep hd hcount
  exact ⟨r, U, hlo, hhi, hlen, hnd, hslot⟩

/-- How many of the `b` digit values appear nowhere in `n^e1` or `n^e2`.-/
def deficiency (b e1 e2 n : Nat) : Nat :=
  List.countP (fun v => !memb v (digits b (n ^ e1) ++ digits b (n ^ e2))) (List.range b)

/--
**Theorem 7.**  Fix a base `b` and exponents `e1, e2` with `gcd(e1e2, b) = 1`, a
starting digit `ρ` — a unit whose two last digits already differ — and a unit `β`
witnessing that the two progressions have invertible difference
(`e2ρ^(e2-1) + β ≡ e1ρ^(e1-1)`).  If `4(d-1) + 2 < b`, then some `d`-digit `n`
has combined digit deficiency at most `b - 2d`.

Since `d ≈ b/E` with `E = e1+e2`, the counting condition is `4b/E < b`, i.e.
`E ≥ 5` up to the rounding, and the bound is `b(1 - 2/E) + O(1)`.
@isnad1 id=ex.13h6v.s8.0c56142cfe77 from=translated src=- shape=30608106 vocab=8dbb8c15
-/
theorem greedy_deficiency_le {b e1 e2 ρ β d : Nat} (hb : 1 < b) (he1 : 1 ≤ e1) (he2 : 1 ≤ e2)
    (hce1 : Nat.Coprime b e1) (hce2 : Nat.Coprime b e2)
    (hρ : 0 < ρ) (hρb : ρ < b) (hcρ : Nat.Coprime b ρ)
    (hstart : ρ ^ e1 % b ≠ ρ ^ e2 % b) (hβ : Nat.Coprime b β)
    (hsep : (e2 * ρ ^ (e2 - 1) + β) % b = e1 * ρ ^ (e1 - 1) % b)
    (hd : 1 ≤ d) (hcount : 4 * (d - 1) + 2 < b) :
    ∃ n, b ^ (d - 1) ≤ n ∧ n < b ^ d ∧ deficiency b e1 e2 n + 2 * d ≤ b := by
  obtain ⟨r, U, hlo, hhi, hmod, hlen, hnd, hltb, hslot⟩ :=
    greedy_reaches hb hce1 hce2 hρ hρb hcρ hstart hβ hsep hd hcount
  refine ⟨r, hlo, hhi, ?_⟩
  have hb0 : 0 < b := by omega
  have hr1 : 1 ≤ r := Nat.le_trans (Nat.pow_pos hb0) hlo
  -- `r^e` has at least `d` digits, so slots `0 .. d-1` really are digits of it
  have hnum : ∀ e, 1 ≤ e → d ≤ numDigits b (r ^ e) := by
    intro e he
    have : b ^ (d - 1) ≤ r ^ e :=
      Nat.le_trans hlo (by simpa using Nat.pow_le_pow_right hr1 he)
    have := le_numDigits_of_pow_le hb this
    omega
  -- every used value is a digit of `r^e1` or of `r^e2`
  have hmem : ∀ v ∈ U, v ∈ digits b (r ^ e1) ++ digits b (r ^ e2) := by
    intro v hv
    obtain ⟨j, hj, hval⟩ := hslot v hv
    refine List.mem_append.mpr ?_
    rcases hval with rfl | rfl
    · exact Or.inl (slot_mem_digits hb _ j (by have := hnum e1 he1; omega))
    · exact Or.inr (slot_mem_digits hb _ j (by have := hnum e2 he2; omega))
  -- so `U` embeds in the digits-that-occur sublist of `range b`
  have hsub : U ⊆ (List.range b).filter
      (fun v => memb v (digits b (r ^ e1) ++ digits b (r ^ e2))) := by
    intro v hv
    refine List.mem_filter.mpr ⟨List.mem_range.mpr (hltb v hv), ?_⟩
    exact (memb_iff v _).mpr (hmem v hv)
  have hle : U.length ≤ ((List.range b).filter
      (fun v => memb v (digits b (r ^ e1) ++ digits b (r ^ e2)))).length :=
    List.Nodup.length_le_of_subset hnd hsub
  have hcount' := countP_eq_length_filter
    (fun v => memb v (digits b (r ^ e1) ++ digits b (r ^ e2))) (List.range b)
  have hsplit := countP_split
    (fun v => memb v (digits b (r ^ e1) ++ digits b (r ^ e2))) (List.range b)
  have hlenr : (List.range b).length = b := List.length_range
  show List.countP (fun v => !memb v (digits b (r ^ e1) ++ digits b (r ^ e2)))
    (List.range b) + 2 * d ≤ b
  omega

/-! ### §8.7  Non-vacuity

The hypotheses are satisfiable, the conclusion is a real restriction, and the
theorem fires at a pair the informal account says the counting bound cannot reach. -/

/-- `deficiency` says what it should: 69 in base 10 misses nothing.  (`digits` is
defined by well-founded recursion and does not reduce in the kernel, so the two
digit lists are supplied by §5's evaluations rather than by `decide` alone.)
@isnad1 id=eq.0h0v.s4.1bd0af4a73b6 from=translated src=- shape=06995877 vocab=a6a266ef
-/
theorem deficiency_sixtynine : deficiency 10 2 3 69 = 0 := by
  show List.countP (fun v => !memb v (digits 10 (69 ^ 2) ++ digits 10 (69 ^ 3)))
    (List.range 10) = 0
  rw [digits_69sq, digits_69cb]
  decide

/-- Theorem 7 at base 13, `(2,3)`: a 3-digit `n` whose six low slots are distinct.
@isnad1 id=ex.0h0v.s6.8277ad012227 from=translated src=- shape=fa1899e5 vocab=ac8da1c3
-/
theorem greedy_deficiency_thirteen :
    ∃ n, 13 ^ 2 ≤ n ∧ n < 13 ^ 3 ∧ deficiency 13 2 3 n + 6 ≤ 13 :=
  greedy_deficiency_le (b := 13) (e1 := 2) (e2 := 3) (ρ := 2) (β := 5) (d := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Theorem 7 at base 65, `(2,3)`: 26 of the 65 digit values are forced to occur.
@isnad1 id=ex.0h0v.s6.993844542458 from=translated src=- shape=fa1899e5 vocab=ac8da1c3
-/
theorem greedy_deficiency_sixtyfive :
    ∃ n, 65 ^ 12 ≤ n ∧ n < 65 ^ 13 ∧ deficiency 65 2 3 n + 26 ≤ 65 :=
  greedy_deficiency_le (b := 65) (e1 := 2) (e2 := 3) (ρ := 2) (β := 57) (d := 13)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- And at `(1,3)`, where `E = 4` — the informal account says the counting bound fails
for `E = 3, 4`, but `4(d-1) + 2 < b` is sharper than `4b/E < b` and `E = 4` clears
it at every base where the arithmetic side conditions hold. `E = 3` never does.
@isnad1 id=ex.0h0v.s6.3aee701591d7 from=translated src=- shape=fa1899e5 vocab=ac8da1c3
-/
theorem greedy_deficiency_fortyseven :
    ∃ n, 47 ^ 11 ≤ n ∧ n < 47 ^ 12 ∧ deficiency 47 1 3 n + 24 ≤ 47 :=
  greedy_deficiency_le (b := 47) (e1 := 1) (e2 := 3) (ρ := 2) (β := 36) (d := 12)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The conclusion is a genuine selection, not a property of the range: `169 = 13^2`
lies in the very interval `greedy_deficiency_thirteen` quantifies over, and it fails the
bound.  `169^2 = 13^4` and `169^3 = 13^6`, so between them they show two digit values
and miss eleven.
@isnad1 id=eq.0h0v.s6.725b235d230e from=translated src=- shape=4a9848ef vocab=c2c693df
-/
theorem digits_169sq : digits 13 (169 ^ 2) = [0, 0, 0, 0, 1] := by
  show digits 13 28561 = [0, 0, 0, 0, 1]
  rw [digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_zero]

/--
@isnad1 id=eq.0h0v.s6.0d2058297ea1 from=translated src=- shape=400058ff vocab=c2c693df
-/
theorem digits_169cb : digits 13 (169 ^ 3) = [0, 0, 0, 0, 0, 0, 1] := by
  show digits 13 4826809 = [0, 0, 0, 0, 0, 0, 1]
  rw [digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_zero]

/--
@isnad1 id=and.0h0v.s6.0b18d2aa84c2 from=translated src=- shape=1d67c116 vocab=ac8da1c3
-/
theorem greedy_deficiency_not_automatic :
    13 ^ 2 ≤ 169 ∧ 169 < 13 ^ 3 ∧ ¬ (deficiency 13 2 3 169 + 6 ≤ 13) := by
  refine ⟨by decide, by decide, ?_⟩
  show ¬ (List.countP (fun v => !memb v (digits 13 (169 ^ 2) ++ digits 13 (169 ^ 3)))
    (List.range 13) + 6 ≤ 13)
  rw [digits_169sq, digits_169cb]
  decide

/-- Odd naturals, as the coprimality hypotheses deliver them.
@isnad1 id=eq.1h1v.s4.ef917d99b70a from=translated src=- shape=fe4d3c0f vocab=368387ec
-/
theorem odd_of_coprime_two {x : Nat} (hx : Nat.Coprime 2 x) : x % 2 = 1 := by
  rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with h | h
  · exfalso
    have hd : (2 : Nat) ∣ Nat.gcd 2 x := Nat.dvd_gcd (Nat.dvd_refl 2) (Nat.dvd_of_mod_eq_zero h)
    rw [show Nat.gcd 2 x = 1 from hx] at hd
    exact absurd hd (by decide)
  · exact h

/--
**Where Theorem 7 stops, and it is a theorem rather than the edge of a scan: no
even base is ever covered.**  If `b` is even then `gcd(e1e2, b) = 1` forces both
exponents odd and `gcd(ρ, b) = 1` forces `ρ` odd, so both progression differences
`e·ρ^(e-1)` are odd and their gap is even — no unit `β` can separate them.

This is the honest limitation: every `(1,3)` base that can hold a
solution is even, and so is `(2,3)` base 34.  `(2,3)` base
57 is odd but loses the coprimality instead, `3 ∣ 57`.
@isnad1 id=false.6h5v.s7.372b93a7e866 from=translated src=- shape=244288fd vocab=7fbe2e61
-/
theorem no_even_base {b e1 e2 ρ β : Nat} (hbe : b % 2 = 0)
    (hce1 : Nat.Coprime b e1) (hce2 : Nat.Coprime b e2) (hcρ : Nat.Coprime b ρ)
    (hβ : Nat.Coprime b β)
    (hsep : (e2 * ρ ^ (e2 - 1) + β) % b = e1 * ρ ^ (e1 - 1) % b) : False := by
  have hdvd : (2 : Nat) ∣ b := Nat.dvd_of_mod_eq_zero hbe
  have ho : ∀ e : Nat, Nat.Coprime b e → (e * ρ ^ (e - 1)) % 2 = 1 := by
    intro e hce
    have he : e % 2 = 1 := odd_of_coprime_two (hce.coprime_dvd_left hdvd)
    have hr : ρ % 2 = 1 := odd_of_coprime_two (hcρ.coprime_dvd_left hdvd)
    rw [Nat.mul_mod, he, odd_pow hr]
  -- reduce the separation identity mod 2, where both differences are odd
  have h2' : (e2 * ρ ^ (e2 - 1) + β) % 2 = e1 * ρ ^ (e1 - 1) % 2 := by
    rw [← Nat.mod_mod_of_dvd _ hdvd, hsep, Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.add_mod, ho e2 hce2, ho e1 hce1] at h2'
  have hβodd : β % 2 = 1 := odd_of_coprime_two (hβ.coprime_dvd_left hdvd)
  rw [hβodd] at h2'
  exact absurd h2' (by decide)

/-- Two `(2,3)` bases often used as search benchmarks, and why each is outside.
@isnad1 id=eq.0h0v.s4.d154610f54e8 from=translated src=- shape=7f6a8e6b vocab=b6301362
-/
theorem base_thirtyfour_is_even : 34 % 2 = 0 := by decide

/--
@isnad1 id=not.0h0v.s3.4c597a90bd56 from=translated src=- shape=90d9b386 vocab=8c9e6272
-/
theorem base_fiftyseven_not_coprime : ¬ Nat.Coprime 57 3 := by decide

/-! ## §9  Theorem 6 — a rigorous upper bound on how many nice numbers a base has

Everything provable about this problem comes from three places, and all three are
*finite* conditions on `n`:

  * the length identity, which confines `n` to a band;
  * casting out `b-1`s, which confines `n mod (b-1)`;
  * `n mod b^k`, which pins slot `i < k` of `n^e1` *and* of `n^e2` (§8's two slots
    per digit), and pandigitality makes those `2k` values pairwise distinct.

Counting the `n` that survive all three is an upper bound on the number of nice
numbers.  The last two are congruences on coprime moduli, so the survivor test has
period `W = (b-1)·b^k` and the count follows from one window of that length rather
than from the band.

Nothing here is asymptotic.  `README-lean.md` priced this result at "not worth it —
an asymptotic statement with error terms"; the error term was an artefact of
writing the bound as `… + O(b^k)` instead of with an exact ceiling.
-/

/-! ### §9.0  The low slots of a number -/

/-- The low `k` digits of `x`, least significant first.  Unlike `digits` this is
total — it pads with zeros — which is exactly why `k ≤ numDigits b x` appears as a
hypothesis everywhere below.-/
def lowSlots (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, x => x % b :: lowSlots b k (x / b)

/--
@isnad1 id=eq.0h2v.s4.a1fa2ed4910b from=translated src=- shape=23b069da vocab=215275d5
-/
theorem lowSlots_zero (b x : Nat) : lowSlots b 0 x = [] := rfl

/--
@isnad1 id=eq.0h3v.s5.bf57c822ce68 from=translated src=- shape=b65b7a23 vocab=c876f2c8
-/
theorem lowSlots_succ (b k x : Nat) :
    lowSlots b (k + 1) x = x % b :: lowSlots b k (x / b) := rfl

/--
@isnad1 id=lt.2h4v.s5.1142cf9107f0 from=translated src=- shape=8ade4901 vocab=784b315c
-/
theorem lowSlots_lt {b : Nat} (hb : 0 < b) : ∀ k x v, v ∈ lowSlots b k x → v < b := by
  intro k
  induction k with
  | zero => intro x v hv; cases hv
  | succ j ih =>
    intro x v hv
    rw [lowSlots_succ] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact Nat.mod_lt _ hb
    · exact ih (x / b) v hv'

/-- The low slots see only `x mod b^k`: the p-adic boundary, in the form the
counting argument needs.
@isnad1 id=eq.1h3v.s5.7581f571d078 from=translated src=- shape=1ed0e526 vocab=a5fadc95
-/
theorem lowSlots_mod {b : Nat} (hb : 0 < b) :
    ∀ k x, lowSlots b k (x % b ^ k) = lowSlots b k x := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ j ih =>
    intro x
    have hsplit : b ^ (j + 1) = b * b ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1' : x % b ^ (j + 1) % b = x % b := by
      rw [hsplit]; exact Nat.mod_mul_right_mod x b (b ^ j)
    have h2' : x % b ^ (j + 1) / b = x / b % b ^ j := by
      rw [hsplit]; exact Nat.mod_mul_right_div_self x b (b ^ j)
    rw [lowSlots_succ, lowSlots_succ, h1', h2', ih (x / b)]

/-- A `k` below the digit count really does name `k` digits: `digits` splits as the
low `k` slots followed by the digits of what is left.
@isnad1 id=eq.2h3v.s6.c80d6c90066a from=translated src=- shape=eeeb0be8 vocab=597bd3e7
-/
theorem digits_split {b : Nat} (hb : 1 < b) :
    ∀ k x, k ≤ numDigits b x → digits b x = lowSlots b k x ++ digits b (x / b ^ k) := by
  intro k
  induction k with
  | zero => intro x _; rw [lowSlots_zero, Nat.pow_zero, Nat.div_one]; rfl
  | succ j ih =>
    intro x hx
    have hpos : 0 < x := by
      rcases Nat.eq_zero_or_pos x with rfl | h
      · rw [numDigits_zero] at hx; omega
      · exact h
    have hnum : numDigits b x = numDigits b (x / b) + 1 := by
      rw [numDigits, dite_eq_left ⟨hb, hpos⟩]
    have hj : j ≤ numDigits b (x / b) := by omega
    have hdiv : x / b / b ^ j = x / b ^ (j + 1) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    rw [digits_step hb hpos, lowSlots_succ, ih (x / b) hj, hdiv]
    rfl

/-- Hence every value occurs at least as often among the digits as among the low
slots — the only thing the low-slot filter needs from pandigitality.
@isnad1 id=le.2h4v.s5.38422a4ef6af from=translated src=- shape=92ca0e6e vocab=ea0400ee
-/
theorem occ_lowSlots_le {b : Nat} (hb : 1 < b) {k x : Nat} (hk : k ≤ numDigits b x) (v : Nat) :
    occ v (lowSlots b k x) ≤ occ v (digits b x) := by
  rw [digits_split hb k x hk, occ_append]
  omega

/-! ### §9.1  Two list utilities -/

/-- `List.all`, written out so it reduces in the kernel the way `occ` does.-/
def allb (p : Nat → Bool) : List Nat → Bool
  | [] => true
  | a :: l => p a && allb p l

/--
@isnad1 id=eq.1h2v.s4.d1f27f0b6306 from=translated src=- shape=4f323958 vocab=643249cc
-/
theorem allb_of_mem {p : Nat → Bool} :
    ∀ l : List Nat, (∀ v, v ∈ l → p v = true) → allb p l = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    show (p a && allb p t) = true
    rw [h a List.mem_cons_self, ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]
    rfl

/--
@isnad1 id=eq.2h3v.s4.fc8ccc6696b0 from=translated src=- shape=67b89981 vocab=643249cc
-/
theorem allb_mem {p : Nat → Bool} :
    ∀ l : List Nat, allb p l = true → ∀ v, v ∈ l → p v = true := by
  intro l
  induction l with
  | nil => intro _ v hv; cases hv
  | cons a t ih =>
    intro h v hv
    have h' : (p a && allb p t) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact h'.1
    · exact ih h'.2 v hv'

/--
@isnad1 id=and.1h3v.s5.ba1f3ae14e74 from=translated src=- shape=341e8e30 vocab=6c56e49d
-/
theorem mem_run : ∀ n s v, v ∈ run s n → s ≤ v ∧ v < s + n := by
  intro n
  induction n with
  | zero => intro s v hv; cases hv
  | succ m ih =>
    intro s v hv
    have hv' : v ∈ s :: run (s + 1) m := hv
    rcases List.mem_cons.mp hv' with rfl | hv''
    · omega
    · have := ih (s + 1) v hv''; omega

/--
@isnad1 id=mem.2h3v.s5.23dec2c78457 from=translated src=- shape=85e4740e vocab=6c56e49d
-/
theorem mem_run_of : ∀ n s v, s ≤ v → v < s + n → v ∈ run s n := by
  intro n
  induction n with
  | zero => intro s v h1' h2'; omega
  | succ m ih =>
    intro s v h1' h2'
    show v ∈ s :: run (s + 1) m
    rcases Nat.eq_or_lt_of_le h1' with rfl | h
    · exact List.Mem.head _
    · exact List.Mem.tail _ (ih (s + 1) v (by omega) (by omega))

/-! ### §9.2  The filters, as one decidable test -/

/-- The `2k` low slots of the pair, in one list.-/
def lowPair (b e1 e2 k r : Nat) : List Nat :=
  lowSlots b k (r ^ e1) ++ lowSlots b k (r ^ e2)

/-- `Q_k`: the low `k` slots of `r^e1` and `r^e2` are `2k` pairwise-distinct values.
Costs `b^k` to tabulate, and `k = 1` is Theorem 2.-/
def lowOK (b e1 e2 k r : Nat) : Bool :=
  allb (fun v => decide (occ v (lowPair b e1 e2 k r) ≤ 1)) (run 0 b)

/-- `R_b`: casting out `b-1`s.-/
def resOK (b e1 e2 T r : Nat) : Bool :=
  decide ((r ^ e1 + r ^ e2) % (b - 1) = T % (b - 1))

/-- Everything the two congruence filters know about `n`.  Its period is
`(b-1)·b^k` (`adm_period`), which is what turns Theorem 6 into a closed form.-/
def adm (b e1 e2 k T n : Nat) : Bool :=
  resOK b e1 e2 T (n % (b - 1)) && lowOK b e1 e2 k (n % b ^ k)

/-- Pandigitality, as a `Bool`, so it can be counted.-/
def isPandigital (b e1 e2 n : Nat) : Bool :=
  allb (fun v => decide (occ v (digits b (n ^ e1) ++ digits b (n ^ e2)) = 1)) (run 0 b)

/--
@isnad1 id=iff.0h4v.s4.c660d3d7b26b from=translated src=- shape=614422a2 vocab=7d2ac1cb
-/
theorem isPandigital_iff {b e1 e2 n : Nat} :
    isPandigital b e1 e2 n = true ↔ Pandigital b e1 e2 n := by
  constructor
  · intro h v hv
    have hd := allb_mem _ h v (mem_run_of b 0 v (by omega) (by omega))
    exact of_decide_eq_true hd
  · intro hp
    refine allb_of_mem _ ?_
    intro v hv
    have hvb : v < b := by have := (mem_run b 0 v hv).2; omega
    show decide (occ v (digits b (n ^ e1) ++ digits b (n ^ e2)) = 1) = true
    exact decide_eq_true (hp v hvb)

/-! ### §9.3  Pandigitality implies each filter -/

/--
@isnad1 id=lt.2h3v.s5.728fad811a3a from=translated src=- shape=8f809611 vocab=12835a20
-/
theorem digits_lt {b : Nat} (hb : 1 < b) : ∀ x v, v ∈ digits b x → v < b := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro v hv
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [digits_zero] at hv; cases hv
    · rw [digits_step hb hx] at hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact Nat.mod_lt _ (by omega)
      · exact ih (x / b) (Nat.div_lt_self hx hb) v hv'

/--
@isnad1 id=eq.1h2v.s4.f19332eaa16e from=translated src=- shape=f133cd39 vocab=3c0c603d
-/
theorem digits_length {b : Nat} (hb : 1 < b) : ∀ x, (digits b x).length = numDigits b x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [digits_zero, numDigits_zero]; rfl
    · rw [digits_step hb hx, numDigits, dite_eq_left ⟨hb, hx⟩,
          ← ih (x / b) (Nat.div_lt_self hx hb)]
      rfl

/-- The weighted companion of `sumRange_occ_length`: a list of values below `j` is
worth `Σ_t t · occ t l`.
@isnad1 id=eq.1h2v.s5.d3033ad6fad8 from=translated src=- shape=38e00064 vocab=ddbb9a80
-/
theorem sumRange_occ_wsum {j : Nat} : ∀ (l : List Nat), (∀ x, x ∈ l → x < j) →
    sumRange (fun t => t * occ t l) j = l.sum := by
  intro l
  induction l with
  | nil =>
    intro _
    show sumRange (fun t => t * occ t ([] : List Nat)) j = 0
    have h : ∀ n, sumRange (fun t => t * occ t ([] : List Nat)) n = 0 := by
      intro n; induction n with
      | zero => rfl
      | succ m ihm =>
        show sumRange _ m + m * occ m ([] : List Nat) = 0
        rw [ihm]; rfl
    exact h j
  | cons t0 cs ih =>
    intro hmem
    have ht0 : t0 < j := hmem t0 List.mem_cons_self
    have hupd := sumRange_update (f := fun t => t * occ t (t0 :: cs))
      (g := fun t => t * occ t cs) (t0 := t0) (x := t0) j ht0
      (by intro t hne
          show t * occ t cs = t * occ t (t0 :: cs)
          show t * occ t cs = t * ((if t0 = t then 1 else 0) + occ t cs)
          rw [ite_eq_right (fun hh => hne hh.symm), Nat.zero_add])
      (by show t0 + t0 * occ t0 cs = t0 * occ t0 (t0 :: cs)
          rw [occ_cons_self, Nat.mul_add, Nat.mul_one])
    rw [← hupd, ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))]
    rfl

/--
@isnad1 id=eq.0h1v.s3.dc4b40050148 from=translated src=- shape=2729d924 vocab=851e6271
-/
theorem sumRange_one : ∀ n, sumRange (fun _ => 1) n = n := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih => show sumRange _ m + 1 = m + 1; rw [ih]

/--
@isnad1 id=eq.0h1v.s5.22a5a8656f24 from=translated src=- shape=a570214a vocab=b4c6976d
-/
theorem two_sumRange_id : ∀ n, 2 * sumRange (fun t => t) (n + 1) = (n + 1) * n := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    show 2 * (sumRange (fun t => t) (m + 1) + (m + 1)) = (m + 1 + 1) * (m + 1)
    rw [Nat.mul_add, ih]
    calc (m + 1) * m + 2 * (m + 1)
        = (m + 1) * m + (m + 1) * 2 := by rw [Nat.mul_comm 2 (m + 1)]
      _ = (m + 1) * (m + 2) := (Nat.mul_add (m + 1) m 2).symm
      _ = (m + 1 + 1) * (m + 1) := Nat.mul_comm _ _

/-- The length identity, derived from pandigitality rather than assumed.
@isnad1 id=eq.2h4v.s5.d5f3a3360c0e from=translated src=- shape=ecb4bc26 vocab=10bf11c3
-/
theorem pandigital_length {b e1 e2 n : Nat} (hb : 1 < b) (hp : Pandigital b e1 e2 n) :
    numDigits b (n ^ e1) + numDigits b (n ^ e2) = b := by
  have hmem : ∀ x, x ∈ digits b (n ^ e1) ++ digits b (n ^ e2) → x < b := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact digits_lt hb _ x h
    · exact digits_lt hb _ x h
  have h1' := sumRange_occ_length (j := b) (digits b (n ^ e1) ++ digits b (n ^ e2)) hmem
  have h2' : sumRange (fun t => occ t (digits b (n ^ e1) ++ digits b (n ^ e2))) b
      = sumRange (fun _ => 1) b :=
    sumRange_congr b (fun t ht => hp t ht)
  rw [h2', sumRange_one] at h1'
  rw [← digits_length hb, ← digits_length hb, ← List.length_append]
  omega

/-- The digit-sum identity, likewise.
@isnad1 id=eq.2h4v.s6.d97d8e70d623 from=translated src=- shape=590fcc39 vocab=3dbec344
-/
theorem pandigital_digitSum {b e1 e2 n : Nat} (hb : 1 < b) (hp : Pandigital b e1 e2 n) :
    2 * (digitSum b (n ^ e1) + digitSum b (n ^ e2)) = b * (b - 1) := by
  have hmem : ∀ x, x ∈ digits b (n ^ e1) ++ digits b (n ^ e2) → x < b := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact digits_lt hb _ x h
    · exact digits_lt hb _ x h
  have h1' := sumRange_occ_wsum (j := b) (digits b (n ^ e1) ++ digits b (n ^ e2)) hmem
  have h2' : sumRange (fun t => t * occ t (digits b (n ^ e1) ++ digits b (n ^ e2))) b
      = sumRange (fun t => t) b :=
    sumRange_congr b (fun t ht => by rw [hp t ht, Nat.mul_one])
  rw [h2'] at h1'
  have hb1 : b - 1 + 1 = b := by omega
  have h3 := two_sumRange_id (b - 1)
  rw [hb1, h1', List.sum_append, ← digitSum_eq_sum hb, ← digitSum_eq_sum hb] at h3
  exact h3

/-! ### §9.4  The band, from the length identity alone

No jump structure and no roots: `n^e1 < b^L1` and `n^e2 < b^L2` multiply to
`n^E < b^b`, and the lower bounds multiply to `b^(b-2) ≤ n^E`.  That is a slightly
wider interval than the exact band — the union of the exact band with its two
neighbouring length splits — and it costs nothing to prove. -/

/--
@isnad1 id=and.2h4v.s6.dd04374795be from=translated src=- shape=96417a28 vocab=1b02cd21
-/
theorem pandigital_pow_bounds {b e1 e2 n : Nat} (hb : 1 < b) (hp : Pandigital b e1 e2 n) :
    b ^ (b - 2) ≤ n ^ (e1 + e2) ∧ n ^ (e1 + e2) < b ^ b := by
  have hn : 0 < n := pos_of_pandigital hb hp
  have hlen := pandigital_length hb hp
  have hp1 : 0 < n ^ e1 := Nat.pow_pos hn
  have hp2 : 0 < n ^ e2 := Nat.pow_pos hn
  obtain ⟨j1, hj1⟩ : ∃ j, numDigits b (n ^ e1) = j + 1 :=
    ⟨numDigits b (n ^ e1) - 1, by have := numDigits_pos hb hp1; omega⟩
  obtain ⟨j2, hj2⟩ : ∃ j, numDigits b (n ^ e2) = j + 1 :=
    ⟨numDigits b (n ^ e2) - 1, by have := numDigits_pos hb hp2; omega⟩
  obtain ⟨lo1, hi1⟩ := bounds_of_numDigits hb _ j1 hj1
  obtain ⟨lo2, hi2⟩ := bounds_of_numDigits hb _ j2 hj2
  have hsum : j1 + j2 = b - 2 := by omega
  have hsum' : (j1 + 1) + (j2 + 1) = b := by omega
  have hmul : n ^ e1 * n ^ e2 = n ^ (e1 + e2) := (Nat.pow_add n e1 e2).symm
  refine ⟨?_, ?_⟩
  · calc b ^ (b - 2) = b ^ j1 * b ^ j2 := by rw [← Nat.pow_add, hsum]
      _ ≤ n ^ e1 * n ^ e2 := Nat.mul_le_mul lo1 lo2
      _ = n ^ (e1 + e2) := hmul
  · have hstep : n ^ e1 * n ^ e2 < b ^ (j1 + 1) * b ^ (j2 + 1) := by
      calc n ^ e1 * n ^ e2 ≤ n ^ e1 * b ^ (j2 + 1) :=
            Nat.mul_le_mul_left _ (Nat.le_of_lt hi2)
        _ < b ^ (j1 + 1) * b ^ (j2 + 1) :=
            Nat.mul_lt_mul_of_lt_of_le hi1 (Nat.le_refl _) (Nat.pow_pos (by omega))
    calc n ^ (e1 + e2) = n ^ e1 * n ^ e2 := hmul.symm
      _ < b ^ (j1 + 1) * b ^ (j2 + 1) := hstep
      _ = b ^ b := by rw [← Nat.pow_add, hsum']

/--
@isnad1 id=lt.3h5v.s6.ceff459e88ec from=translated src=- shape=c02832fb vocab=06be250f
-/
theorem pandigital_gt {b e1 e2 n lo : Nat} (hb : 1 < b) (hp : Pandigital b e1 e2 n)
    (hlo : lo ^ (e1 + e2) < b ^ (b - 2)) : lo < n := by
  rcases Nat.lt_or_ge lo n with h | h
  · exact h
  · exfalso
    have h1' : n ^ (e1 + e2) ≤ lo ^ (e1 + e2) := Nat.pow_le_pow_left h _
    have h2' := (pandigital_pow_bounds hb hp).1
    omega

/--
@isnad1 id=lt.3h5v.s6.194e19d217b6 from=translated src=- shape=efc0efa6 vocab=dcb0a75f
-/
theorem pandigital_lt {b e1 e2 n hi : Nat} (hb : 1 < b) (hp : Pandigital b e1 e2 n)
    (hhi : b ^ b ≤ hi ^ (e1 + e2)) : n < hi := by
  rcases Nat.lt_or_ge n hi with h | h
  · exact h
  · exfalso
    have h1' : hi ^ (e1 + e2) ≤ n ^ (e1 + e2) := Nat.pow_le_pow_left h _
    have h2' := (pandigital_pow_bounds hb hp).2
    omega

/-- `k` digits, from `b^(k-1) ≤ x`.  §3's `le_numDigits_of_pow_le` shifted by one so
that `k` counts digits rather than the exponent.
@isnad1 id=le.3h3v.s5.5b1cd855ac8e from=translated src=- shape=36a7d3a3 vocab=31edcded
-/
theorem numDigits_ge {b k x : Nat} (hb : 1 < b) (hk : 0 < k)
    (h : b ^ (k - 1) ≤ x) : k ≤ numDigits b x := by
  have := le_numDigits_of_pow_le hb h
  omega

/-! ### §9.5  The two filters fire -/

/--
@isnad1 id=eq.3h5v.s6.2522cb20ae60 from=translated src=- shape=5cb0bad5 vocab=e16d57f2
-/
theorem pandigital_resOK {b e1 e2 T n : Nat} (hb : 1 < b) (hT : 2 * T = b * (b - 1))
    (hp : Pandigital b e1 e2 n) : resOK b e1 e2 T (n % (b - 1)) = true := by
  have hds : digitSum b (n ^ e1) + digitSum b (n ^ e2) = T := by
    have := pandigital_digitSum hb hp; omega
  have hs := sieve_sound (b := b) (x := n ^ e1) (y := n ^ e2) (T := T) hb hds
  have hmod : ((n % (b - 1)) ^ e1 + (n % (b - 1)) ^ e2) % (b - 1)
      = (n ^ e1 + n ^ e2) % (b - 1) := by
    rw [Nat.add_mod, ← Nat.pow_mod, ← Nat.pow_mod, ← Nat.add_mod]
  exact decide_eq_true (hmod.trans hs)

/--
@isnad1 id=eq.4h5v.s6.5af79af2853c from=translated src=- shape=eb8fbcb1 vocab=8a36f48f
-/
theorem pandigital_lowOK {b e1 e2 k n : Nat} (hb : 1 < b)
    (hk1 : k ≤ numDigits b (n ^ e1)) (hk2 : k ≤ numDigits b (n ^ e2))
    (hp : Pandigital b e1 e2 n) : lowOK b e1 e2 k (n % b ^ k) = true := by
  have hb0 : 0 < b := by omega
  have hslot : ∀ e, lowSlots b k ((n % b ^ k) ^ e) = lowSlots b k (n ^ e) := by
    intro e
    have heq : (n % b ^ k) ^ e % b ^ k = n ^ e % b ^ k := (Nat.pow_mod n e (b ^ k)).symm
    rw [← lowSlots_mod hb0 k ((n % b ^ k) ^ e), heq, lowSlots_mod hb0]
  refine allb_of_mem _ ?_
  intro v hv
  have hvb : v < b := by have := (mem_run b 0 v hv).2; omega
  refine decide_eq_true ?_
  show occ v (lowSlots b k ((n % b ^ k) ^ e1) ++ lowSlots b k ((n % b ^ k) ^ e2)) ≤ 1
  rw [hslot e1, hslot e2, occ_append]
  have hone := hp v hvb
  rw [occ_append] at hone
  have a1 := occ_lowSlots_le hb hk1 v
  have a2 := occ_lowSlots_le hb hk2 v
  omega

/-! ### §9.6  Counting a periodic test on a segment -/

/--
@isnad1 id=le.1h3v.s5.f42688d1055d from=translated src=- shape=6041a2bd vocab=aa377db1
-/
theorem countP_mono {p q : Nat → Bool} (h : ∀ x, p x = true → q x = true) :
    ∀ l : List Nat, List.countP p l ≤ List.countP q l := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons]
    by_cases hp : p a = true
    · rw [ite_eq_left hp, ite_eq_left (h a hp)]; omega
    · rw [ite_eq_right hp]
      by_cases hq : q a = true
      · rw [ite_eq_left hq]; omega
      · rw [ite_eq_right hq]; omega

/--
@isnad1 id=eq.1h4v.s5.8bc3f02f2173 from=translated src=- shape=7ff13fc5 vocab=2ce9334c
-/
theorem countP_run_shift {p : Nat → Bool} {W : Nat} (hper : ∀ x, p (x + W) = p x) :
    ∀ n s, List.countP p (run (s + W) n) = List.countP p (run s n) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ m ih =>
    intro s
    show List.countP p ((s + W) :: run (s + W + 1) m) = List.countP p (s :: run (s + 1) m)
    rw [List.countP_cons, List.countP_cons, hper s]
    have he : s + W + 1 = (s + 1) + W := by omega
    rw [he, ih (s + 1)]

/--
@isnad1 id=eq.1h3v.s5.dcf85f21e9e2 from=translated src=- shape=3edb6c78 vocab=2ce9334c
-/
theorem countP_run_window {p : Nat → Bool} {W : Nat} (hper : ∀ x, p (x + W) = p x) :
    ∀ s, List.countP p (run s W) = List.countP p (run 0 W) := by
  intro s
  induction s with
  | zero => rfl
  | succ t ih =>
    rw [← ih]
    have hcons : List.countP p (run t (W + 1))
        = List.countP p (run (t + 1) W) + (if p t = true then 1 else 0) := by
      show List.countP p (t :: run (t + 1) W) = _
      rw [List.countP_cons]
    have happ : List.countP p (run t (W + 1))
        = List.countP p (run t W) + (if p (t + W) = true then 1 else 0) := by
      rw [run_add t W 1, List.countP_append]
      have hone : List.countP p (run (t + W) 1) = (if p (t + W) = true then 1 else 0) := by
        show List.countP p ((t + W) :: []) = _
        rw [List.countP_cons, List.countP_nil, Nat.zero_add]
      rw [hone]
    rw [hper t] at happ
    exact Nat.add_right_cancel (hcons.symm.trans happ)

/--
@isnad1 id=le.2h4v.s6.7831c98b8408 from=translated src=- shape=0708b670 vocab=ef967497
-/
theorem countP_run_le {p : Nat → Bool} {W : Nat} (hW : 0 < W) (hper : ∀ x, p (x + W) = p x) :
    ∀ len s, List.countP p (run s len)
      ≤ List.countP p (run 0 W) * ((len + W - 1) / W) := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro s
    rcases Nat.eq_zero_or_pos len with rfl | hlen
    · show List.countP p [] ≤ _
      simp
    rcases Nat.lt_or_ge len (W + 1) with hle | hgt
    · have hsplit : run s W = run s len ++ run (s + len) (W - len) := by
        have he : W = len + (W - len) := by omega
        calc run s W = run s (len + (W - len)) := by rw [← he]
          _ = run s len ++ run (s + len) (W - len) := run_add s len (W - len)
      have h1' : List.countP p (run s len) ≤ List.countP p (run 0 W) := by
        rw [← countP_run_window hper s, hsplit, List.countP_append]
        omega
      have h2' : 1 ≤ (len + W - 1) / W := (Nat.le_div_iff_mul_le hW).mpr (by omega)
      calc List.countP p (run s len) ≤ List.countP p (run 0 W) := h1'
        _ ≤ List.countP p (run 0 W) * ((len + W - 1) / W) :=
            Nat.le_mul_of_pos_right _ (by omega)
    · have hsplit : run s len = run s W ++ run (s + W) (len - W) := by
        have he : len = W + (len - W) := by omega
        calc run s len = run s (W + (len - W)) := by rw [← he]
          _ = run s W ++ run (s + W) (len - W) := run_add s W (len - W)
      have hIH := ih (len - W) (by omega) (s + W)
      have hdiv : (len + W - 1) / W = (len - W + W - 1) / W + 1 := by
        have h1' : len + W - 1 = (len - W + W - 1) + W := by omega
        rw [h1', Nat.add_div_right _ hW]
      rw [hsplit, List.countP_append, countP_run_window hper s, hdiv,
          Nat.mul_add, Nat.mul_one]
      omega

/--
@isnad1 id=eq.1h6v.s6.7bfdfe8c910c from=translated src=- shape=293be3aa vocab=15db5d25
-/
theorem adm_period {b e1 e2 k T : Nat} (hb : 1 < b) (x : Nat) :
    adm b e1 e2 k T (x + (b - 1) * b ^ k) = adm b e1 e2 k T x := by
  have h1' : (x + (b - 1) * b ^ k) % (b - 1) = x % (b - 1) :=
    Nat.add_mul_mod_self_left x (b - 1) (b ^ k)
  have h2' : (x + (b - 1) * b ^ k) % b ^ k = x % b ^ k := by
    rw [Nat.mul_comm]
    exact Nat.add_mul_mod_self_left x (b ^ k) (b - 1)
  show (resOK b e1 e2 T ((x + (b - 1) * b ^ k) % (b - 1))
        && lowOK b e1 e2 k ((x + (b - 1) * b ^ k) % b ^ k))
      = (resOK b e1 e2 T (x % (b - 1)) && lowOK b e1 e2 k (x % b ^ k))
  rw [h1', h2']

/-! ### §9.7  Theorem 6 -/

/--
**Theorem 6.**  Every `(e1,e2)`-pandigital `n` lies in the crude
band `(lo, hi)` and passes the admissibility test `adm`, which depends on `n` only
through `n mod (b-1)` and `n mod b^k`.

`hlo` and `hhi` are the band: any `lo` below it and any `hi` at or above its top.
`hk1`/`hk2` say only that the powers of the smallest surviving `n` already have `k`
digits, which is what makes the low-`k`-slot filter legitimate — without them the
padding zeros of `lowSlots` would be counted as digits.
@isnad1 id=and.8h8v.s8.d2745d610906 from=translated src=- shape=802c6f7b vocab=e37e327e
-/
theorem adm_of_pandigital {b e1 e2 k T lo hi n : Nat} (hb : 1 < b) (hk : 0 < k)
    (hT : 2 * T = b * (b - 1))
    (hlo : lo ^ (e1 + e2) < b ^ (b - 2)) (hhi : b ^ b ≤ hi ^ (e1 + e2))
    (hk1 : b ^ (k - 1) ≤ (lo + 1) ^ e1) (hk2 : b ^ (k - 1) ≤ (lo + 1) ^ e2)
    (hp : Pandigital b e1 e2 n) :
    (lo < n ∧ n < hi) ∧ adm b e1 e2 k T n = true := by
  have hgt := pandigital_gt hb hp hlo
  have hlt := pandigital_lt hb hp hhi
  have hle : lo + 1 ≤ n := by omega
  have hd1 : k ≤ numDigits b (n ^ e1) :=
    numDigits_ge hb hk (Nat.le_trans hk1 (Nat.pow_le_pow_left hle _))
  have hd2 : k ≤ numDigits b (n ^ e2) :=
    numDigits_ge hb hk (Nat.le_trans hk2 (Nat.pow_le_pow_left hle _))
  refine ⟨⟨hgt, hlt⟩, ?_⟩
  show (resOK b e1 e2 T (n % (b - 1)) && lowOK b e1 e2 k (n % b ^ k)) = true
  rw [pandigital_resOK hb hT hp, pandigital_lowOK hb hd1 hd2 hp]
  rfl

/--
**Theorem 6, counting form.**  At most `countP adm` numbers of the crude band are
nice.  This is the quantity a program evaluating the bound computes.
@isnad1 id=le.7h7v.s8.942a42fd278a from=translated src=- shape=b982fb14 vocab=6ed22182
-/
theorem countP_pandigital_le_adm {b e1 e2 k T lo hi : Nat} (hb : 1 < b) (hk : 0 < k)
    (hT : 2 * T = b * (b - 1))
    (hlo : lo ^ (e1 + e2) < b ^ (b - 2)) (hhi : b ^ b ≤ hi ^ (e1 + e2))
    (hk1 : b ^ (k - 1) ≤ (lo + 1) ^ e1) (hk2 : b ^ (k - 1) ≤ (lo + 1) ^ e2) :
    List.countP (isPandigital b e1 e2) (run (lo + 1) (hi - lo - 1))
      ≤ List.countP (adm b e1 e2 k T) (run (lo + 1) (hi - lo - 1)) :=
  countP_mono (fun x hx =>
    (adm_of_pandigital hb hk hT hlo hhi hk1 hk2 (isPandigital_iff.mp hx)).2) _

/--
**Theorem 6, closed form.**  `adm` has period `W = (b-1)·b^k`, so the count over the
band is at most the count over one window times `⌈band/W⌉` — `O(b^k)` work, with no
reference to the band beyond its length.
@isnad1 id=le.1h7v.s7.fe0a9fdbef59 from=translated src=- shape=38170005 vocab=2a6eb0a5
-/
theorem countP_pandigital_le_window {b e1 e2 k T lo hi : Nat} (hb : 1 < b) :
    List.countP (adm b e1 e2 k T) (run (lo + 1) (hi - lo - 1))
      ≤ List.countP (adm b e1 e2 k T) (run 0 ((b - 1) * b ^ k))
        * ((hi - lo - 1 + (b - 1) * b ^ k - 1) / ((b - 1) * b ^ k)) := by
  refine countP_run_le ?_ (adm_period hb) _ _
  have hp : 0 < b ^ k := Nat.pow_pos (by omega)
  exact Nat.mul_pos (by omega) hp

/-! ### §9.8  Base 10: the bound is sharp, and it settles 69

At `k = 4` the filters leave exactly one survivor in the whole crude band, and it is
69.  So the classical problem's only known solution is its *only* solution, certified
by the three provable filters — nothing about the middle digits is used.

This is a *sharpness* witness, not a new result: base 10's band is 53 numbers and has
been scanned since the problem was posed.  What it shows is that the bound of §9.7 can
be attained, which an upper bound with no equality case would not.

Note which filter does the work: at `k = 4` the low slots alone already pin 69, so
`base_ten_survivors` survives deleting `resOK` from `adm`.  `base_seventeen_window`
below is the witness that catches that deletion, which is why both are here. -/

/-- The crude band at base 10 for `(2,3)`: `39^5 < 10^8` and `10^10 ≤ 100^5`.
@isnad1 id=lt.0h0v.s5.7030e71bc6ee from=translated src=- shape=d88261e9 vocab=7ddce274
-/
theorem base_ten_lo : (39 : Nat) ^ 5 < 10 ^ 8 := by decide
/--
@isnad1 id=le.0h0v.s5.7f42c677385e from=translated src=- shape=d88261e9 vocab=74f5fafa
-/
theorem base_ten_hi : (10 : Nat) ^ 10 ≤ 100 ^ 5 := by decide

/-- The whole content of the bound at base 10: over `[40, 100)`, `adm` at `k = 4`
admits exactly one number.
@isnad1 id=eq.0h0v.s5.72b347fe6a15 from=translated src=- shape=11adfbf9 vocab=8e561867
-/
theorem base_ten_survivors : (run 40 60).filter (adm 10 2 3 4 45) = [69] := by decide

/-- **69 is the only `(2,3)`-nice number in base 10.**
@isnad1 id=eq.1h1v.s4.eca44c156f60 from=translated src=- shape=028bbed8 vocab=f94668c8
-/
theorem sixtynine_unique {n : Nat} (hp : Pandigital 10 2 3 n) : n = 69 := by
  have h := adm_of_pandigital (b := 10) (e1 := 2) (e2 := 3) (k := 4) (T := 45) (lo := 39) (hi := 100)
    (by decide) (by decide) (by decide) base_ten_lo base_ten_hi (by decide) (by decide) hp
  have hmem : n ∈ run 40 60 := mem_run_of 60 40 n (by omega) (by omega)
  have hfil : n ∈ (run 40 60).filter (adm 10 2 3 4 45) :=
    List.mem_filter.mpr ⟨hmem, h.2⟩
  rw [base_ten_survivors] at hfil
  simpa using hfil

/-- **The set of `(2,3)`-nice numbers in base 10 is exactly `{69}`.**
@isnad1 id=iff.0h1v.s4.a6ab56d78d34 from=translated src=- shape=ffc0a5fa vocab=f94668c8
-/
theorem base_ten_nice_iff {n : Nat} : Pandigital 10 2 3 n ↔ n = 69 :=
  ⟨sixtynine_unique, fun h => h ▸ sixtynine_pandigital⟩

/-! ### §9.9  Where the closed form earns its keep

Base 10 is the wrong shape for it: `W = (b-1)·b^k` is 90 000 against a band of 60, so
the window is larger than the thing it bounds and only the *sharp* form says anything.
Base 17 at `k = 1` is the other way round — a 272-number window bounds a band 38 times
longer, and comes within 2.5% of the exact count over the same interval (571). -/

set_option maxRecDepth 4000 in
/-- The whole cost of the closed form at base 17, `k = 1`: 272 kernel evaluations.
@isnad1 id=eq.0h0v.s5.f00f880bd945 from=translated src=- shape=ee786766 vocab=f81fd813
-/
theorem base_seventeen_window : List.countP (adm 17 2 3 1 136) (run 0 272) = 15 := by decide

/--
@isnad1 id=mem.1h1v.s5.7f0672311e2f from=translated src=- shape=09574e3f vocab=9e3c54b0
-/
theorem base_seventeen_all {n : Nat} (hp : Pandigital 17 2 3 n) : n ∈ run 4913 10347 := by
  have h := adm_of_pandigital (b := 17) (e1 := 2) (e2 := 3) (k := 1) (T := 136)
    (lo := 4912) (hi := 15260) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hp
  exact mem_run_of 10347 4913 n (by omega) (by omega)

/-- **At most 585 `(2,3)`-nice numbers in base 17** — from `base_seventeen_window`
and a division, with nothing evaluated over the band itself.  (The truth is 0.)
@isnad1 id=le.0h0v.s5.e6cf30815ca6 from=translated src=- shape=67fc0f4e vocab=40df0d7c
-/
theorem base_seventeen_bound :
    List.countP (isPandigital 17 2 3) (run 4913 10347) ≤ 585 := by
  have hlen : 15260 - 4912 - 1 = 10347 := rfl
  have hstart : (4912 : Nat) + 1 = 4913 := rfl
  have h1' := countP_pandigital_le_adm (b := 17) (e1 := 2) (e2 := 3) (k := 1) (T := 136)
    (lo := 4912) (hi := 15260) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have h2' := countP_pandigital_le_window (b := 17) (e1 := 2) (e2 := 3) (k := 1) (T := 136)
    (lo := 4912) (hi := 15260) (by decide)
  rw [hstart, hlen] at h1' h2'
  have hW : (17 - 1) * 17 ^ 1 = 272 := rfl
  rw [hW, base_seventeen_window] at h2'
  have h3 : (10347 + 272 - 1) / 272 = 39 := rfl
  rw [h3] at h2'
  omega

/-! ### §9.10  The top slots — condition 4 of Theorem 6

§9.2's three filters all read `n` from the *bottom*: the band from its size,
`resOK` from `n mod (b-1)`, `lowOK` from `n mod b^k`.  The fourth condition
reads it from the other end — the `h` leading digits of each `n^(e_i)`, `2h` slots
for the pair, pairwise distinct and distinct from the low `2k`.

Two things make the top end different from the bottom, and both appear as
hypotheses below.  It is **not a congruence**: the top slots depend on `n` through
its size, so the refined test has no period and §9.6's closed form does not apply
to it.  And it needs the **exact** band rather than §9.4's crude one: a top slot is
read at position `L - h`, so the length `L` has to be known, and the crude band is
the union of three length splits.  §9.12 is what buys the cost back — the test is
constant on intervals, so one evaluation retires a whole run of candidates. -/

/-- `lowSlots` splits at any depth, exactly as `digits` does.
@isnad1 id=eq.0h4v.s5.90484c194696 from=translated src=- shape=1306f39e vocab=e04c732e
-/
theorem lowSlots_add (b : Nat) : ∀ k j x,
    lowSlots b (k + j) x = lowSlots b k x ++ lowSlots b j (x / b ^ k) := by
  intro k
  induction k with
  | zero => intro j x; rw [Nat.zero_add, Nat.pow_zero, Nat.div_one]; rfl
  | succ i ih =>
    intro j x
    have hdiv : x / b / b ^ i = x / b ^ (i + 1) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    have hsum : i + 1 + j = (i + j) + 1 := by omega
    calc lowSlots b (i + 1 + j) x
        = x % b :: lowSlots b (i + j) (x / b) := by rw [hsum, lowSlots_succ]
      _ = x % b :: (lowSlots b i (x / b) ++ lowSlots b j (x / b / b ^ i)) := by
            rw [ih j (x / b)]
      _ = lowSlots b (i + 1) x ++ lowSlots b j (x / b ^ (i + 1)) := by
            rw [hdiv, lowSlots_succ]; rfl

/-- A number with exactly `L` digits is its own low `L` slots.  `lowSlots` pads
with zeros and `digits` does not, so this needs the length on the nose.
@isnad1 id=eq.2h3v.s5.aaadf40d0e05 from=translated src=- shape=edcaf2b6 vocab=a7db9741
-/
theorem digits_eq_lowSlots {b : Nat} (hb : 1 < b) :
    ∀ L x, numDigits b x = L → digits b x = lowSlots b L x := by
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [eq_zero_of_numDigits_eq_zero hb hx, digits_zero, lowSlots_zero]
  | succ j ih =>
    intro x hx
    have hpos : 0 < x := by
      rcases Nat.eq_zero_or_pos x with rfl | h
      · rw [numDigits_zero] at hx; omega
      · exact h
    have hnum : numDigits b x = numDigits b (x / b) + 1 := by
      rw [numDigits, dite_eq_left ⟨hb, hpos⟩]
    rw [digits_step hb hpos, lowSlots_succ, ih (x / b) (by omega)]

/-- Dividing by `b^j` drops exactly `j` digits — no hypothesis needed, since past
the top of `x` both sides are zero.
@isnad1 id=eq.1h3v.s5.b4174a631362 from=translated src=- shape=f17775df vocab=91ea7160
-/
theorem numDigits_div_pow {b : Nat} (hb : 1 < b) :
    ∀ j x, numDigits b (x / b ^ j) = numDigits b x - j := by
  have hstep : ∀ y, numDigits b (y / b) = numDigits b y - 1 := by
    intro y
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · rw [Nat.zero_div, numDigits_zero]
    · have h : numDigits b y = numDigits b (y / b) + 1 := by
        rw [numDigits, dite_eq_left ⟨hb, hy⟩]
      omega
  intro j
  induction j with
  | zero => intro x; rw [Nat.pow_zero, Nat.div_one]; omega
  | succ i ih =>
    intro x
    have hdiv : x / b ^ (i + 1) = x / b / b ^ i := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    rw [hdiv, ih (x / b), hstep x]
    omega

/-- The length in the shape the interval hypotheses below produce.
@isnad1 id=eq.4h3v.s6.e333ba380744 from=translated src=- shape=e25b8611 vocab=31edcded
-/
theorem numDigits_eq_of_len {b x L : Nat} (hb : 1 < b) (hL : 0 < L)
    (h1 : b ^ (L - 1) ≤ x) (h2 : x < b ^ L) : numDigits b x = L := by
  have he : L - 1 + 1 = L := by omega
  have h := numDigits_eq_of_bounds (b := b) (x := x) (k := L - 1) hb h1 (by rw [he]; exact h2)
  omega

/-- The top `h` digits of `x`, least significant of them first, given that `x` has
`L` digits.  The length is a *parameter* rather than `numDigits b x` because the
filter is evaluated in the kernel and `numDigits` is well-founded recursion; the
theorems below carry `numDigits b x = L` as a hypothesis instead.-/
def topSlots (b h L x : Nat) : List Nat := lowSlots b h (x / b ^ (L - h))

/-- The digit list splits as the low `L-h` slots followed by the top `h`.
@isnad1 id=eq.3h4v.s6.6e2aa9d8cd68 from=translated src=- shape=db2bda49 vocab=5d1b34ad
-/
theorem digits_split_top {b : Nat} (hb : 1 < b) {L h x : Nat}
    (hL : numDigits b x = L) (hh : h ≤ L) :
    digits b x = lowSlots b (L - h) x ++ topSlots b h L x := by
  have h1 : digits b x = lowSlots b (L - h) x ++ digits b (x / b ^ (L - h)) :=
    digits_split hb (L - h) x (by omega)
  have h2 : numDigits b (x / b ^ (L - h)) = h := by
    rw [numDigits_div_pow hb, hL]; omega
  rw [h1, digits_eq_lowSlots hb h _ h2]
  rfl

/-- The low `k` slots and the top `h` slots are disjoint stretches of the digit
list, so their occurrence counts add up inside it.  This is everything conditions
3 and 4 take from pandigitality, and it is where `k + h ≤ L` is used.
@isnad1 id=le.3h6v.s6.e65817281b70 from=translated src=- shape=f6fc8e6b vocab=80c5293d
-/
theorem occ_low_top_le {b : Nat} (hb : 1 < b) {k h L x : Nat}
    (hL : numDigits b x = L) (hkh : k + h ≤ L) (v : Nat) :
    occ v (lowSlots b k x) + occ v (topSlots b h L x) ≤ occ v (digits b x) := by
  have hsplit := digits_split_top hb hL (by omega : h ≤ L)
  have hlow : lowSlots b (L - h) x
      = lowSlots b k x ++ lowSlots b (L - h - k) (x / b ^ k) := by
    rw [← lowSlots_add b k (L - h - k) x, show k + (L - h - k) = L - h from by omega]
  rw [hsplit, hlow, occ_append, occ_append]
  omega

/-! ### §9.11  The refined test, and Theorem 6 with all four conditions -/

/-- The `2(k+h)` boundary slots of the pair: the low `k` and the top `h` of each
power.  The low-slot and top-slot conditions together say these are `2(k+h)`
pairwise-distinct values.-/
def boundary (b e1 e2 k h L1 L2 n : Nat) : List Nat :=
  (lowSlots b k (n ^ e1) ++ topSlots b h L1 (n ^ e1))
    ++ (lowSlots b k (n ^ e2) ++ topSlots b h L2 (n ^ e2))

/-- Condition 4, as a decidable test: no value occupies two boundary slots.-/
def boundaryOK (b e1 e2 k h L1 L2 n : Nat) : Bool :=
  allb (fun v => decide (occ v (boundary b e1 e2 k h L1 L2 n) ≤ 1)) (run 0 b)

/-- `adm` of §9.2 with condition 4 added: all four filters in one
`Bool`.  At `h = 0` the top slots are empty and `boundaryOK` degenerates to the low
distinctness `adm` already tests, so nothing is added and nothing is lost.-/
def admTop (b e1 e2 k h L1 L2 T n : Nat) : Bool :=
  adm b e1 e2 k T n && boundaryOK b e1 e2 k h L1 L2 n

/-- Condition 4 can only remove candidates.
@isnad1 id=eq.1h9v.s5.3fcda97c64d1 from=translated src=- shape=5e40f77c vocab=a086b9d4
-/
theorem admTop_le_adm {b e1 e2 k h L1 L2 T n : Nat}
    (h' : admTop b e1 e2 k h L1 L2 T n = true) : adm b e1 e2 k T n = true :=
  (Bool.and_eq_true _ _).mp h' |>.1

/--
@isnad1 id=eq.6h8v.s6.a9c6da2086fc from=translated src=- shape=676a1794 vocab=392d9d81
-/
theorem pandigital_boundaryOK {b e1 e2 k h L1 L2 n : Nat} (hb : 1 < b)
    (hd1 : numDigits b (n ^ e1) = L1) (hd2 : numDigits b (n ^ e2) = L2)
    (hkh1 : k + h ≤ L1) (hkh2 : k + h ≤ L2)
    (hp : Pandigital b e1 e2 n) : boundaryOK b e1 e2 k h L1 L2 n = true := by
  refine allb_of_mem _ ?_
  intro v hv
  have hvb : v < b := by have := (mem_run b 0 v hv).2; omega
  refine decide_eq_true ?_
  show occ v ((lowSlots b k (n ^ e1) ++ topSlots b h L1 (n ^ e1))
      ++ (lowSlots b k (n ^ e2) ++ topSlots b h L2 (n ^ e2))) ≤ 1
  rw [occ_append, occ_append, occ_append]
  have a1 := occ_low_top_le hb hd1 hkh1 v
  have a2 := occ_low_top_le hb hd2 hkh2 v
  have hone := hp v hvb
  rw [occ_append] at hone
  omega

/--
**Theorem 6, condition 4 (the top-digit refinement).**  On an interval
`[a, c)` where the two digit lengths are constant, every `(e1,e2)`-pandigital `n`
passes `admTop` — conditions 1-3 of §9.7 *and* the top-digit condition.

The four length hypotheses are what pin `L1` and `L2` across the whole interval,
and at a concrete base each is a `decide` on numerals.  They are also the reason
this theorem is stated over an interval rather than over §9.4's crude band: that
band is the union of three length splits, and `L1` is not constant on it.
@isnad1 id=eq.13h11v.s8.4bfa92293db9 from=translated src=- shape=36c008eb vocab=7a7bbea5
-/
theorem admTop_of_pandigital {b e1 e2 k h L1 L2 T a c n : Nat} (hb : 1 < b)
    (hT : 2 * T = b * (b - 1))
    (hL1 : 0 < L1) (hL2 : 0 < L2)
    (ha1 : b ^ (L1 - 1) ≤ a ^ e1) (hc1 : (c - 1) ^ e1 < b ^ L1)
    (ha2 : b ^ (L2 - 1) ≤ a ^ e2) (hc2 : (c - 1) ^ e2 < b ^ L2)
    (hkh1 : k + h ≤ L1) (hkh2 : k + h ≤ L2)
    (han : a ≤ n) (hnc : n < c) (hp : Pandigital b e1 e2 n) :
    admTop b e1 e2 k h L1 L2 T n = true := by
  have hlen : ∀ e L, 0 < L → b ^ (L - 1) ≤ a ^ e → (c - 1) ^ e < b ^ L →
      numDigits b (n ^ e) = L := by
    intro e L hL h1 h2
    refine numDigits_eq_of_len hb hL (Nat.le_trans h1 (Nat.pow_le_pow_left han e)) ?_
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (by omega : n ≤ c - 1) e) h2
  have hd1 := hlen e1 L1 hL1 ha1 hc1
  have hd2 := hlen e2 L2 hL2 ha2 hc2
  have hlow := pandigital_lowOK hb (by omega : k ≤ numDigits b (n ^ e1))
    (by omega : k ≤ numDigits b (n ^ e2)) hp
  have hres := pandigital_resOK hb hT hp
  have hbnd := pandigital_boundaryOK hb hd1 hd2 hkh1 hkh2 hp
  show (adm b e1 e2 k T n && boundaryOK b e1 e2 k h L1 L2 n) = true
  show ((resOK b e1 e2 T (n % (b - 1)) && lowOK b e1 e2 k (n % b ^ k))
      && boundaryOK b e1 e2 k h L1 L2 n) = true
  rw [hres, hlow, hbnd]
  rfl

/-- `countP_mono` where the implication is only available on the list — which is
the shape a filter valid on one interval has.
@isnad1 id=le.1h3v.s5.f5bed7a77b76 from=translated src=- shape=9b6b1200 vocab=3e95f10f
-/
theorem countP_mono_mem {p q : Nat → Bool} : ∀ l : List Nat,
    (∀ x, x ∈ l → p x = true → q x = true) →
      List.countP p l ≤ List.countP q l := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    rw [List.countP_cons, List.countP_cons]
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases hp : p a = true
    · rw [ite_eq_left hp, ite_eq_left (h a List.mem_cons_self hp)]; omega
    · rw [ite_eq_right hp]
      by_cases hq : q a = true
      · rw [ite_eq_left hq]; omega
      · rw [ite_eq_right hq]; omega

/--
**Theorem 6 with condition 4, counting form.**  At most `countP admTop` of the
interval is nice.  Unlike §9.7's this is a scan of the interval: `admTop` has no
period, which is exactly what §9.12 pays for.
@isnad1 id=le.10h10v.s8.725d74b8e5b2 from=translated src=- shape=0920734a vocab=eb83b7e9
-/
theorem countP_pandigital_le_admTop {b e1 e2 k h L1 L2 T a c : Nat} (hb : 1 < b)
    (hT : 2 * T = b * (b - 1))
    (hL1 : 0 < L1) (hL2 : 0 < L2)
    (ha1 : b ^ (L1 - 1) ≤ a ^ e1) (hc1 : (c - 1) ^ e1 < b ^ L1)
    (ha2 : b ^ (L2 - 1) ≤ a ^ e2) (hc2 : (c - 1) ^ e2 < b ^ L2)
    (hkh1 : k + h ≤ L1) (hkh2 : k + h ≤ L2) :
    List.countP (isPandigital b e1 e2) (run a (c - a))
      ≤ List.countP (admTop b e1 e2 k h L1 L2 T) (run a (c - a)) :=
  countP_mono_mem _ (fun x hx hpx =>
    have hm := mem_run (c - a) a x hx
    admTop_of_pandigital hb hT hL1 hL2 ha1 hc1 ha2 hc2 hkh1 hkh2 hm.1 (by omega)
      (isPandigital_iff.mp hpx))

/-- And the refinement really is one: it never counts more than §9.7 does.
@isnad1 id=le.0h9v.s5.6199f8cdd76f from=translated src=- shape=12f4b5e9 vocab=ca4c8f3f
-/
theorem countP_admTop_le {b e1 e2 k h L1 L2 T : Nat} (l : List Nat) :
    List.countP (admTop b e1 e2 k h L1 L2 T) l ≤ List.countP (adm b e1 e2 k T) l :=
  countP_mono (fun _ hx => admTop_le_adm hx) l

/-! ### §9.12  The decomposition: one evaluation retires a whole interval

Condition 4 costs a scan where conditions 2 and 3 cost a window, and this is what
pays for it.  `n ↦ ⌊n^e / b^(L-h)⌋` is nondecreasing, so the band splits into
maximal intervals on which the top slots are *constant* — the cut points being the
least `n` with `n^e ≥ c·b^(L-h)`, an exact `e`-th root.  Inside one such interval
the test is a constant, so an interval whose top digits already clash is retired
whole.

**No root is extracted below, and none is needed.**  Finding the cuts is
the job of a program evaluating the bound; all a proof needs is that where the top quotient agrees at an
interval's two ends it agrees throughout, which is two divisions and monotonicity of
`/`.  Formalise the property the construction has, not the construction. -/

/-- The engine of the decomposition: where the top quotient agrees at the two ends
of an interval it is constant throughout, and so are the top slots.
@isnad1 id=eq.3h7v.s7.87a4f322e40f from=translated src=- shape=6af4c690 vocab=5d72f2c4
-/
theorem topSlots_const {b e h L a c n : Nat} (han : a ≤ n) (hnc : n < c)
    (hq : a ^ e / b ^ (L - h) = (c - 1) ^ e / b ^ (L - h)) :
    topSlots b h L (n ^ e) = topSlots b h L (a ^ e) := by
  have d1 : a ^ e / b ^ (L - h) ≤ n ^ e / b ^ (L - h) :=
    Nat.div_le_div_right (Nat.pow_le_pow_left han e)
  have d2 : n ^ e / b ^ (L - h) ≤ (c - 1) ^ e / b ^ (L - h) :=
    Nat.div_le_div_right (Nat.pow_le_pow_left (by omega : n ≤ c - 1) e)
  have heq : n ^ e / b ^ (L - h) = a ^ e / b ^ (L - h) := by omega
  show lowSlots b h (n ^ e / b ^ (L - h)) = lowSlots b h (a ^ e / b ^ (L - h))
  rw [heq]

/--
**The interval filter.**  If two of the `2h` top digits read at the *left end* of
such an interval agree, the interval contains no nice number at all.  Nothing about
`n mod b^k` is used, and nothing is evaluated per candidate: the whole interval
costs the four divisions that produce `hq1` and `hq2`.
@isnad1 id=not.14h10v.s8.1db6a4ec95f6 from=translated src=- shape=dad7285e vocab=96562fc4
-/
theorem no_pandigital_of_top_clash {b e1 e2 h L1 L2 a c v : Nat} (hb : 1 < b)
    (hL1 : 0 < L1) (hL2 : 0 < L2)
    (ha1 : b ^ (L1 - 1) ≤ a ^ e1) (hc1 : (c - 1) ^ e1 < b ^ L1)
    (ha2 : b ^ (L2 - 1) ≤ a ^ e2) (hc2 : (c - 1) ^ e2 < b ^ L2)
    (hh1 : h ≤ L1) (hh2 : h ≤ L2)
    (hq1 : a ^ e1 / b ^ (L1 - h) = (c - 1) ^ e1 / b ^ (L1 - h))
    (hq2 : a ^ e2 / b ^ (L2 - h) = (c - 1) ^ e2 / b ^ (L2 - h))
    (hclash : 2 ≤ occ v (topSlots b h L1 (a ^ e1) ++ topSlots b h L2 (a ^ e2)))
    {n : Nat} (han : a ≤ n) (hnc : n < c) : ¬ Pandigital b e1 e2 n := by
  intro hp
  have hb0 : 0 < b := by omega
  have hv : v < b := by
    have hmem : v ∈ topSlots b h L1 (a ^ e1) ++ topSlots b h L2 (a ^ e2) :=
      mem_of_occ_pos _ v (by omega)
    rcases List.mem_append.mp hmem with hm | hm
    · exact lowSlots_lt hb0 h _ v hm
    · exact lowSlots_lt hb0 h _ v hm
  have hlen : ∀ e L, 0 < L → b ^ (L - 1) ≤ a ^ e → (c - 1) ^ e < b ^ L →
      numDigits b (n ^ e) = L := by
    intro e L hL x1 x2
    refine numDigits_eq_of_len hb hL (Nat.le_trans x1 (Nat.pow_le_pow_left han e)) ?_
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (by omega : n ≤ c - 1) e) x2
  have hok := pandigital_boundaryOK (k := 0) (h := h) hb (hlen e1 L1 hL1 ha1 hc1)
    (hlen e2 L2 hL2 ha2 hc2) (by omega) (by omega) hp
  have hd := allb_mem _ hok v (mem_run_of b 0 v (by omega) (by omega))
  have hle : occ v (boundary b e1 e2 0 h L1 L2 n) ≤ 1 := of_decide_eq_true hd
  have hb' : occ v (boundary b e1 e2 0 h L1 L2 n)
      = occ v (topSlots b h L1 (a ^ e1)) + occ v (topSlots b h L2 (a ^ e2)) := by
    show occ v (([] ++ topSlots b h L1 (n ^ e1)) ++ ([] ++ topSlots b h L2 (n ^ e2))) = _
    rw [List.nil_append, List.nil_append, occ_append,
        topSlots_const han hnc hq1, topSlots_const han hnc hq2]
  rw [occ_append] at hclash
  omega

/-! ### §9.13  Both witnesses: the refinement is sharp, and it is not free

Two things have to be shown, and they are different.  That condition 4 *tightens*
the bound: at base 10 it reaches the same equality case `{69}` at `k = 2` that §9.8
needed `k = 4` for, and there all three filters are load-bearing — unlike §9.8's
witness, which survives deleting `resOK`.  And that §9.12 is worth having: an
interval is retired by four divisions, at a cost that does not grow with its length,
where the congruence filters pay per candidate and reach the same answer only at a
depth whose table is orders of magnitude larger.  `base_seventeen_dead_interval`
is that witness, over 95 consecutive candidates. -/

/-- The **exact** band at base 10, which is what condition 4 needs and §9.4 does
not give: `47 ≤ n < 100`, with `n^2` of 4 digits and `n^3` of 6.  The crude band
also holds `40 ≤ n < 47`, where the split is `(4,5)` — and `4 + 5 ≠ 10`, so the
length identity is what removes it.
@isnad1 id=and.1h1v.s6.da12fcacc3ea from=translated src=- shape=4285e721 vocab=9114883a
-/
theorem base_ten_exact_band {n : Nat} (hp : Pandigital 10 2 3 n) :
    (47 ≤ n ∧ n < 100) ∧ numDigits 10 (n ^ 2) = 4 ∧ numDigits 10 (n ^ 3) = 6 := by
  have hb : (1 : Nat) < 10 := by decide
  have hcrude := (adm_of_pandigital (b := 10) (e1 := 2) (e2 := 3) (k := 1) (T := 45)
    (lo := 39) (hi := 100) hb (by decide) (by decide)
    base_ten_lo base_ten_hi (by decide) (by decide) hp).1
  have hlen := pandigital_length hb hp
  have h47 : 47 ≤ n := by
    rcases Nat.lt_or_ge n 47 with h | h
    · exfalso
      have hsq : numDigits 10 (n ^ 2) = 4 :=
        numDigits_eq_of_len hb (by decide)
          (Nat.le_trans (by decide : (10:Nat) ^ 3 ≤ 40 ^ 2)
            (Nat.pow_le_pow_left (by omega : 40 ≤ n) 2))
          (Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (by omega : n ≤ 46) 2) (by decide))
      have hcb : numDigits 10 (n ^ 3) = 5 :=
        numDigits_eq_of_len hb (by decide)
          (Nat.le_trans (by decide : (10:Nat) ^ 4 ≤ 40 ^ 3)
            (Nat.pow_le_pow_left (by omega : 40 ≤ n) 3))
          (Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (by omega : n ≤ 46) 3) (by decide))
      omega
    · exact h
  refine ⟨⟨h47, hcrude.2⟩, ?_, ?_⟩
  · exact numDigits_eq_of_len hb (by decide)
      (Nat.le_trans (by decide : (10:Nat) ^ 3 ≤ 47 ^ 2) (Nat.pow_le_pow_left h47 2))
      (Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (by omega : n ≤ 99) 2) (by decide))
  · exact numDigits_eq_of_len hb (by decide)
      (Nat.le_trans (by decide : (10:Nat) ^ 5 ≤ 47 ^ 3) (Nat.pow_le_pow_left h47 3))
      (Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (by omega : n ≤ 99) 3) (by decide))

set_option maxRecDepth 8000 in
/-- The whole content of the four-condition bound at base 10: over the exact band
`[47, 100)`, `admTop` at `(k, h) = (2, 2)` admits exactly one number.  §9.8 reached
the same conclusion at `(4, 0)`: `b^4 = 10 000` tabulated residues there, against
`b^2 = 100` and two divisions per candidate here.
@isnad1 id=eq.0h0v.s6.fd48cd91c761 from=translated src=- shape=d5378fe3 vocab=d29e3db5
-/
theorem base_ten_top_survivors :
    (run 47 53).filter (admTop 10 2 3 2 2 4 6 45) = [69] := by decide

/-- **69 is the only `(2,3)`-nice number in base 10** — again, and this time with
condition 4 doing part of the work.  The two proofs are independent: §9.8 uses the
low slots to depth 4 and no top digit, this one uses depth 2 at both ends.
@isnad1 id=eq.1h1v.s4.eca44c156f60 from=translated src=- shape=028bbed8 vocab=f94668c8
-/
theorem sixtynine_unique_top {n : Nat} (hp : Pandigital 10 2 3 n) : n = 69 := by
  obtain ⟨⟨h1, h2⟩, -, -⟩ := base_ten_exact_band hp
  have h := admTop_of_pandigital (b := 10) (e1 := 2) (e2 := 3) (k := 2) (h := 2)
    (L1 := 4) (L2 := 6) (T := 45) (a := 47) (c := 100) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h1 h2 hp
  have hmem : n ∈ run 47 53 := mem_run_of 53 47 n (by omega) (by omega)
  have hfil : n ∈ (run 47 53).filter (admTop 10 2 3 2 2 4 6 45) :=
    List.mem_filter.mpr ⟨hmem, h⟩
  rw [base_ten_top_survivors] at hfil
  simpa using hfil

/-- **Ninety-five candidates retired by four divisions.**  At base 17 the top two
digits of `n^2` and of `n^3` are constant across `[4913, 5008)` — the start of the
exact band — and both read `(0, 1)`, so the digit `0` occupies two slots and
nothing in that interval can be nice.  For contrast, the congruence filters of §9.2
leave five of these 95 alive at `k = 1`, three at `k = 2`, one at `k = 3` and at
`k = 4`, and clear the interval only at `k = 5` — 1 419 857 tabulated residues and
a test per candidate, against `h = 2` and four divisions for the whole run.
@isnad1 id=not.2h1v.s5.998fa67433ff from=translated src=- shape=1c4077fc vocab=901f3045
-/
theorem base_seventeen_dead_interval {n : Nat} (h1 : 4913 ≤ n) (h2 : n < 5008) :
    ¬ Pandigital 17 2 3 n :=
  no_pandigital_of_top_clash (b := 17) (e1 := 2) (e2 := 3) (h := 2)
    (L1 := 7) (L2 := 10) (a := 4913) (c := 5008) (v := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h2

/-! ## §10  Infinitude — the reduction, the divergence, and the one missing input

Whether there are infinitely many `(e1,e2)`-nice numbers is **open**, and far
out of reach: it is a statement about all
`b` digits of two powers at once, where the state of the art handles one digit
statistic (Mauduit–Rivat) or one *missing* digit in a base above `10^23` (Maynard).
Nothing here closes that gap.  What this section does is cut the question into the
half that is provable and the half that is not, and prove the first half in full.

  * **Theorem 8** (`infinitude_iff`) — there are infinitely many nice numbers **iff**
    infinitely many bases host one.  Both directions are the crude band
    `b^(b-2) ≤ n^E < b^b` of §9.4: a solution in a large base is a large number, and
    a large number needs a large base.  This is §3's "one base per `n`" upgraded
    from disjointness to a two-sided size estimate.
  * **Theorem 9** (`model_diverges`) — the *heuristic* count `|band|·b!/b^b` exceeds
    any `M`, along an explicit infinite family of bases, unconditionally and with no
    asymptotic notation.  The band is **exhibited** — `b^q` consecutive candidates,
    §10.1 — rather than estimated, and `b^b ≤ 4^b·b!` comes from
    `b!·b^b ≤ (2b)! ≤ 4^b·(b!)^2`: two inductions, no Stirling, no reals.
  * **Theorem 10** (`conditional_infinitude`) — `ModelPositive → infinitude`, where
    `ModelPositive` says that a base of that family whose heuristic count exceeds one
    fixed `M0` hosts a solution.  That is the only input left.
  * **The guard** (`divergence_is_not_existence`) — and it is not a formality.  For
    `(2,3)` the bases `b = 20s+7` sit in the *same* family, their heuristic counts
    diverge at the same rate, and **every one of them is provably empty** (Theorem 3:
    `b ≡ 3 mod 4`).  So no argument from the size of the heuristic alone can ever
    produce a solution.  `ModelPositive` has to carry arithmetic input, and the whole
    difficulty of the problem is that no such input is both true and provable.
-/

/-! ### §10.0  Factorials, and the one analytic fact

`b! ≥ b^b/c^b` for a *constant* `c` is what makes the heuristic diverge — the
`b^(b/E)` band beats `c^b` for every constant `c` — so the sharp `c = e` of Stirling
is not needed and `c = 4` is free: `(2b)!` contains `b` factors above `b`, and
`(2b)! ≤ 4^b·(b!)^2` is an induction whose only arithmetic step is
`(2b+1) ≤ (2b+2)`. -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/--
@isnad1 id=eq.0h1v.s5.2b5e82bc9a71 from=translated src=- shape=48355f7a vocab=01aabeca
-/
theorem fact_succ (n : Nat) : fact (n + 1) = (n + 1) * fact n := rfl

/--
@isnad1 id=lt.0h1v.s3.22413da9d591 from=translated src=- shape=8a62b088 vocab=0e941b03
-/
theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih => rw [fact_succ]; exact Nat.mul_pos (Nat.succ_pos n) ih

/-- The top `j` factors of `(b+j)!` are each at least `b`.
@isnad1 id=le.0h2v.s5.8cf001ac96e6 from=translated src=- shape=bb30f873 vocab=1d8a5a16
-/
theorem fact_mul_pow_le (b : Nat) : ∀ j, fact b * b ^ j ≤ fact (b + j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc fact b * b ^ (j + 1) = fact b * b ^ j * b := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ fact (b + j) * b := Nat.mul_le_mul ih (Nat.le_refl b)
      _ ≤ fact (b + j) * (b + j + 1) := Nat.mul_le_mul (Nat.le_refl _) (by omega)
      _ = (b + j + 1) * fact (b + j) := Nat.mul_comm _ _
      _ = fact (b + (j + 1)) := by rw [← Nat.add_assoc, fact_succ]

/--
@isnad1 id=eq.0h3v.s6.d64ec6121481 from=translated src=- shape=ab7bf578 vocab=662b3218
-/
theorem prod_shuffle (x P F : Nat) :
    (2 * x) * ((2 * x) * (P * (F * F))) = P * 4 * ((x * F) * (x * F)) := by
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- `(2b)! ≤ 4^b·(b!)^2` — the central-binomial bound, proved directly so that no
binomial coefficients are needed.
@isnad1 id=le.0h1v.s5.6150b9255258 from=translated src=- shape=15aaeb71 vocab=4e0ea197
-/
theorem fact_two_mul_le (b : Nat) : fact (2 * b) ≤ 4 ^ b * (fact b * fact b) := by
  induction b with
  | zero => decide
  | succ b ih =>
    have e1' : 2 * (b + 1) = 2 * b + 1 + 1 := by omega
    have e2' : 2 * b + 1 + 1 = 2 * (b + 1) := by omega
    rw [e1', fact_succ, fact_succ]
    calc (2 * b + 1 + 1) * ((2 * b + 1) * fact (2 * b))
        ≤ (2 * b + 1 + 1) * ((2 * b + 1 + 1) * (4 ^ b * (fact b * fact b))) :=
          Nat.mul_le_mul (Nat.le_refl _) (Nat.mul_le_mul (by omega) ih)
      _ = 4 ^ (b + 1) * (fact (b + 1) * fact (b + 1)) := by
          rw [e2', fact_succ, Nat.pow_succ]
          exact prod_shuffle (b + 1) (4 ^ b) (fact b)

/-- **`b^b ≤ 4^b · b!`.**  The whole analytic content of Theorem 9, in one
cancellation: `b!·b^b ≤ (2b)! ≤ 4^b·(b!)^2`.
@isnad1 id=le.0h1v.s5.2654dcd94f3d from=translated src=- shape=e479d15c vocab=4e0ea197
-/
theorem pow_self_le_fact (b : Nat) : b ^ b ≤ 4 ^ b * fact b := by
  have h1' : fact b * b ^ b ≤ fact (2 * b) := by
    have h := fact_mul_pow_le b b
    have e : b + b = 2 * b := by omega
    rwa [e] at h
  have h2' : fact b * b ^ b ≤ fact b * (4 ^ b * fact b) := by
    calc fact b * b ^ b ≤ fact (2 * b) := h1'
      _ ≤ 4 ^ b * (fact b * fact b) := fact_two_mul_le b
      _ = fact b * (4 ^ b * fact b) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_left h2' (fact_pos b)

/-! ### §10.1  A base whose band is exhibited, not estimated

For any `b` with `E ∣ b-2`, put `q = (b-2)/E`.  Then `b^q` is in the band, and so is
every `n` below `2b^q`, because `n^e < 2^e·b^(qe) ≤ b^(qe+1)` as soon as `2^e ≤ b`.
That is `b^q` consecutive candidates with no root extraction anywhere — a factor
`⌊b^(1/e2)⌋-1` short of the true band, which is nothing on the scale of `b^q`. -/

/--
@isnad1 id=eq.5h4v.s7.49ee72a33c99 from=translated src=- shape=3a45d5ed vocab=523c6e27
-/
theorem numDigits_pow_of_interval {b q e n : Nat} (hb : 1 < b) (he : 0 < e)
    (hpow : 2 ^ e ≤ b) (hlo : b ^ q ≤ n) (hhi : n < 2 * b ^ q) :
    numDigits b (n ^ e) = q * e + 1 := by
  refine numDigits_eq_of_bounds hb ?_ ?_
  · calc b ^ (q * e) = (b ^ q) ^ e := by rw [Nat.pow_mul]
      _ ≤ n ^ e := Nat.pow_le_pow_left hlo e
  · calc n ^ e < (2 * b ^ q) ^ e := pow_lt_pow_left' hhi e (by omega)
      _ = 2 ^ e * (b ^ q) ^ e := by rw [Nat.mul_pow]
      _ = 2 ^ e * b ^ (q * e) := by rw [Nat.pow_mul]
      _ ≤ b * b ^ (q * e) := Nat.mul_le_mul hpow (Nat.le_refl _)
      _ = b ^ (q * e + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- **The band, exhibited.**  With `q·E + 2 = b` and `2^e1, 2^e2 ≤ b`, every one of
the `b^q` integers in `[b^q, 2b^q)` is a candidate in base `b`.
@isnad1 id=inband.8h5v.s7.5e960dc98c4a from=translated src=- shape=25f075d1 vocab=984d072f
-/
theorem band_of_interval {b e1 e2 q n : Nat} (hb : 1 < b) (he1 : 0 < e1) (he2 : 0 < e2)
    (h1' : 2 ^ e1 ≤ b) (h2' : 2 ^ e2 ≤ b) (hq : q * (e1 + e2) + 2 = b)
    (hlo : b ^ q ≤ n) (hhi : n < 2 * b ^ q) : InBand b e1 e2 n := by
  have hd : q * (e1 + e2) = q * e1 + q * e2 := Nat.left_distrib q e1 e2
  show numDigits b (n ^ e1) + numDigits b (n ^ e2) = b
  rw [numDigits_pow_of_interval hb he1 h1' hlo hhi,
      numDigits_pow_of_interval hb he2 h2' hlo hhi]
  omega

/-! ### §10.2  The heuristic count of that base, and why it diverges

`|band|·b!/b^b ≥ b^q·b!/b^b ≥ b^q/4^b`, and `b^q ≥ 4^(2Eq) = 4^(2b-4)` once
`b ≥ 4^(2E)`, which beats `M·4^b` as soon as `4^(b-4) ≥ M`.  The `4` is the crude
Stirling constant of §10.0; the real crossover is near `b = e^E` (148 for `(2,3)`),
and this proof makes no attempt to find it — divergence is insensitive to the
constant, which is the point. -/

/--
@isnad1 id=lt.0h1v.s4.e71bcf1cd881 from=translated src=- shape=e17d9afa vocab=7ddce274
-/
theorem lt_pow_four (k : Nat) : k < 4 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have e : 4 ^ (k + 1) = 4 ^ k * 4 := Nat.pow_succ 4 k
    omega

/--
@isnad1 id=le.3h4v.s7.04dbd030804f from=translated src=- shape=ee137471 vocab=1d8a5a16
-/
theorem yield_ge {b q M E : Nat} (hq : q * E + 2 = b)
    (hbig : 4 ^ (2 * E) ≤ b) (hM : M + 4 ≤ b) : M * b ^ b ≤ b ^ q * fact b := by
  have h1' : 4 ^ (2 * E * q) ≤ b ^ q := by
    calc 4 ^ (2 * E * q) = (4 ^ (2 * E)) ^ q := by rw [Nat.pow_mul]
      _ ≤ b ^ q := Nat.pow_le_pow_left hbig q
  have hcomm : 2 * E * q = 2 * (q * E) := by rw [Nat.mul_assoc, Nat.mul_comm E q]
  have hexp : 2 * E * q = (b - 4) + b := by rw [hcomm]; omega
  have h2' : M * 4 ^ b ≤ 4 ^ (2 * E * q) := by
    rw [hexp, Nat.pow_add]
    exact Nat.mul_le_mul (Nat.le_trans (by omega) (Nat.le_of_lt (lt_pow_four (b - 4))))
      (Nat.le_refl _)
  calc M * b ^ b ≤ M * (4 ^ b * fact b) :=
        Nat.mul_le_mul (Nat.le_refl M) (pow_self_le_fact b)
    _ = M * 4 ^ b * fact b := (Nat.mul_assoc _ _ _).symm
    _ ≤ b ^ q * fact b := Nat.mul_le_mul (Nat.le_trans h2' h1') (Nat.le_refl _)

/--
**Theorem 9.**  For every exponent pair and every `M`, there are arbitrarily large
bases `b` which are even, satisfy `E ∣ b-2`, carry `b^q` consecutive candidates in
their band, and whose heuristic count `|band|·b!/b^b` exceeds `M`.

No hypothesis, no asymptotics, and the band is produced rather than estimated.
@isnad1 id=ex.2h4v.s7.997e36bee415 from=translated src=- shape=612e5977 vocab=e81385e1
-/
theorem model_diverges (e1 e2 M B : Nat) (he1 : 0 < e1) (he2 : 0 < e2) :
    ∃ b q, B < b ∧ 1 < b ∧ b % 2 = 0 ∧ q * (e1 + e2) + 2 = b ∧
      (∀ n, b ^ q ≤ n → n < 2 * b ^ q → InBand b e1 e2 n) ∧
      M * b ^ b ≤ b ^ q * fact b := by
  obtain ⟨t, ht⟩ : ∃ t, t = B + M + 4 ^ (2 * (e1 + e2)) + 2 ^ e1 + 2 ^ e2 + 4 := ⟨_, rfl⟩
  have hE : 1 ≤ e1 + e2 := by omega
  -- `omega` does not know that a power is nonnegative, so say so.
  have hq1 : 1 ≤ 4 ^ (2 * (e1 + e2)) := Nat.one_le_pow _ _ (by omega)
  have hq2 : 1 ≤ 2 ^ e1 := Nat.one_le_pow _ _ (by omega)
  have hq3 : 1 ≤ 2 ^ e2 := Nat.one_le_pow _ _ (by omega)
  have ht1 : 2 * t * 1 ≤ 2 * t * (e1 + e2) := Nat.mul_le_mul (Nat.le_refl _) hE
  have ht2 : 2 * t * (e1 + e2) = 2 * (t * (e1 + e2)) := by rw [Nat.mul_assoc]
  have hb1 : 1 < 2 * t * (e1 + e2) + 2 := by omega
  have hbB : B < 2 * t * (e1 + e2) + 2 := by omega
  have hbe : (2 * t * (e1 + e2) + 2) % 2 = 0 := by omega
  have hp1' : 2 ^ e1 ≤ 2 * t * (e1 + e2) + 2 := by omega
  have hp2' : 2 ^ e2 ≤ 2 * t * (e1 + e2) + 2 := by omega
  have hbig : 4 ^ (2 * (e1 + e2)) ≤ 2 * t * (e1 + e2) + 2 := by omega
  have hM : M + 4 ≤ 2 * t * (e1 + e2) + 2 := by omega
  exact ⟨2 * t * (e1 + e2) + 2, 2 * t, hbB, hb1, hbe, rfl,
    fun n hlo hhi => band_of_interval hb1 he1 he2 hp1' hp2' rfl hlo hhi,
    yield_ge rfl hbig hM⟩

/-! ### §10.3  The family is not one of the dead classes

Theorem 1 cannot touch it — its band is exhibited above — and for **even** members
neither can Theorem 3 nor Theorem 4: `b` even makes `b-1` odd, so `T ≡ 0 (mod b-1)` and `ρ = 0` is a
residue.  That is Theorem 4's `v_2(b-1) = 0` case, and it is why §10.2 builds the
family out of even bases in the first place. -/

/--
@isnad1 id=eq.5h4v.s6.33e81604d32b from=translated src=- shape=e129dc75 vocab=5f8565f1
-/
theorem resOK_zero_of_even {b e1 e2 T : Nat} (hb : 1 < b) (hev : b % 2 = 0)
    (he1 : 0 < e1) (he2 : 0 < e2) (hT : 2 * T = b * (b - 1)) :
    resOK b e1 e2 T 0 = true := by
  obtain ⟨c, hc⟩ : ∃ c, b = 2 * c := ⟨b / 2, by omega⟩
  have h2' : 2 * T = 2 * (c * (b - 1)) := by rw [hT, hc, Nat.mul_assoc]
  have hT' : T = c * (b - 1) := Nat.eq_of_mul_eq_mul_left (by omega) h2'
  have hmod : T % (b - 1) = 0 := by rw [hT', Nat.mul_mod_left]
  have hz : (0 : Nat) ^ e1 + 0 ^ e2 = 0 := by
    rw [Nat.zero_pow he1, Nat.zero_pow he2]
  show decide _ = true
  refine decide_eq_true ?_
  rw [hz, hmod, Nat.zero_mod]

/-- And Theorem 2 misses it as well: the clashing bases all divide `N(e1,e2)`, so
only finitely many of them exist and the family runs past all of them.  With the
band exhibited (Theorem 1), `ρ = 0` a residue (Theorems 3 and 4) and no clash (Theorem 2), **none of
the four proved obstructions touches §10.2's family**.
@isnad1 id=not.5h3v.s5.6e3d48a3911e from=translated src=- shape=3fe8cef1 vocab=2d85a270
-/
theorem no_clash_of_large {b e1 e2 : Nat} (hb : 0 < b) (he1 : 1 ≤ e1) (he : e1 < e2)
    (hN : 0 < clashMod e1 e2) (hgt : clashMod e1 e2 < b) : ¬ UniversalClash b e1 e2 := by
  intro h
  have hd := (clash_iff_dvd_clashMod hb he1 he).mp h
  have := Nat.le_of_dvd hN hd
  omega

/-! ### §10.4  Theorem 8 — infinitude of numbers is infinitude of bases -/

/-- There are infinitely many `(e1,e2)`-nice numbers.-/
def InfinitelyManyNice (e1 e2 : Nat) : Prop :=
  ∀ N, ∃ b n, N < n ∧ 1 < b ∧ Pandigital b e1 e2 n

/-- Infinitely many bases host an `(e1,e2)`-nice number.-/
def InfinitelyManyNiceBases (e1 e2 : Nat) : Prop :=
  ∀ B, ∃ b n, B < b ∧ 1 < b ∧ Pandigital b e1 e2 n

/--
@isnad1 id=le.1h2v.s4.c765129ffe0a from=translated src=- shape=d0dd947f vocab=191dae4c
-/
theorem le_self_pow' {m e : Nat} (he : 0 < e) : m ≤ m ^ e := by
  obtain ⟨j, hj⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
  subst hj
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · calc m = 1 * m := (Nat.one_mul m).symm
      _ ≤ m ^ j * m := Nat.mul_le_mul (Nat.one_le_pow _ _ h) (Nat.le_refl m)
      _ = m ^ (j + 1) := (Nat.pow_succ m j).symm

/-- §3's `base_unique` at the level of solutions: a nice number is nice in exactly one base.
@isnad1 id=eq.4h5v.s5.0e35313f833d from=translated src=- shape=263d0c3c vocab=71524155
-/
theorem nice_base_unique {b b' e1 e2 n : Nat} (hb : 1 < b) (hb' : 1 < b')
    (h : Pandigital b e1 e2 n) (h' : Pandigital b' e1 e2 n) : b = b' :=
  base_unique hb hb' (pandigital_length hb h) (pandigital_length hb' h')

/--
**Theorem 8.**  There are infinitely many `(e1,e2)`-nice numbers **iff** infinitely
many bases host one.  "Search more numbers" and "search more bases" are the same
axis — quantitatively, not just up to the disjointness of §3.
@isnad1 id=iff.2h2v.s4.9c1b24b3a982 from=translated src=- shape=4c218ca2 vocab=c1defa0d
-/
theorem infinitude_iff {e1 e2 : Nat} (he1 : 0 < e1) (he2 : 0 < e2) :
    InfinitelyManyNiceBases e1 e2 ↔ InfinitelyManyNice e1 e2 := by
  constructor
  · intro h N
    obtain ⟨b, n, hBb, hb, hp⟩ := h (N ^ (e1 + e2) + 2)
    refine ⟨b, n, ?_, hb, hp⟩
    have hlow := (pandigital_pow_bounds hb hp).1
    have hb1 : b ^ 1 ≤ b ^ (b - 2) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.pow_one] at hb1
    rcases Nat.lt_or_ge N n with h' | h'
    · exact h'
    · exact absurd (Nat.pow_le_pow_left h' (e1 + e2)) (by omega)
  · intro h B
    obtain ⟨b, n, hNn, hb, hp⟩ := h (B ^ B)
    refine ⟨b, n, ?_, hb, hp⟩
    have hhigh := (pandigital_pow_bounds hb hp).2
    have hn : n ≤ n ^ (e1 + e2) := le_self_pow' (by omega)
    rcases Nat.lt_or_ge B b with h' | h'
    · exact h'
    · have hB : 0 < B := by omega
      have hbb : b ^ b ≤ B ^ B :=
        Nat.le_trans (Nat.pow_le_pow_left h' b) (Nat.pow_le_pow_right hB h')
      omega

/-! ### §10.5  Theorem 10 — the conditional statement, and the missing input -/

/--
**The missing input.**  A base of §10.2's family — even, `E ∣ b-2`, large — whose
heuristic count `|band|·b!/b^b` (bounded below by the `b^q` exhibited candidates)
exceeds one fixed `M0`, hosts a solution.

This is *not* a weakening of the conjecture in any deep sense, and §10.6 shows it
cannot be proved from the size of the heuristic alone.  Its value is that everything
else in the chain is a theorem.-/
def ModelPositive (e1 e2 : Nat) : Prop :=
  ∃ M0 b0, ∀ b q, b0 ≤ b → b % 2 = 0 → q * (e1 + e2) + 2 = b →
    M0 * b ^ b ≤ b ^ q * fact b → ∃ n, Pandigital b e1 e2 n

/-- **Theorem 10.**  `ModelPositive` implies there are infinitely many nice numbers.
@isnad1 id=infinite.3h2v.s4.42a34800c150 from=translated src=- shape=5bfdd39e vocab=8466d281
-/
theorem conditional_infinitude {e1 e2 : Nat} (he1 : 0 < e1) (he2 : 0 < e2)
    (h : ModelPositive e1 e2) : InfinitelyManyNice e1 e2 := by
  obtain ⟨M0, b0, hmp⟩ := h
  refine (infinitude_iff he1 he2).mp ?_
  intro B
  obtain ⟨b, q, hBb, hb1, hev, hq, _, hyield⟩ := model_diverges e1 e2 M0 (B + b0) he1 he2
  obtain ⟨n, hn⟩ := hmp b q (by omega) hev hq hyield
  exact ⟨b, n, by omega, hb1, hn⟩

/-! ### §10.6  The guard — a divergent heuristic over a provably empty band

`ModelPositive` needs its parity clause, and this is why.  Take `(2,3)` and
`b = 20s+7`: then `5 ∣ b-2`, so §10.1 fills the band with `b^q` consecutive
candidates and §10.2 pushes the heuristic count past any `M` — and `b ≡ 3 (mod 4)`,
so Theorem 3 says the base is empty.  An infinite family where the heuristic diverges
and the truth is exactly zero.

The moral is the one this file keeps meeting from the other side: the three provable
sources are all *obstructions*.  They can empty a base; nothing here, and nothing in
the literature, can fill one. -/

/--
@isnad1 id=not.4h4v.s5.1e399cd0e4d0 from=translated src=- shape=6149ec0f vocab=97acedb1
-/
theorem no_pandigital_of_mod_four {b e1 e2 n : Nat} (hb : 1 < b) (he1 : e1 ≠ 0)
    (he2 : e2 ≠ 0) (hmod : b % 4 = 3) : ¬ Pandigital b e1 e2 n := fun hp =>
  no_nice_of_mod_four hb he1 he2 hmod (pandigital_digitSum hb hp)

/--
@isnad1 id=ex.0h2v.s7.977d75cc1b6e from=translated src=- shape=37c9c0fd vocab=15ef3d42
-/
theorem divergence_is_not_existence (M B : Nat) :
    ∃ b q, B < b ∧ 1 < b ∧ q * (2 + 3) + 2 = b ∧
      (∀ n, b ^ q ≤ n → n < 2 * b ^ q → InBand b 2 3 n) ∧
      M * b ^ b ≤ b ^ q * fact b ∧
      (∀ n, ¬ Pandigital b 2 3 n) := by
  have h4 : (4 : Nat) ^ (2 * (2 + 3)) = 1048576 := by decide
  have h22 : (2 : Nat) ^ 2 = 4 := by decide
  have h23 : (2 : Nat) ^ 3 = 8 := by decide
  refine ⟨(4 * (B + M + 1048576) + 1) * (2 + 3) + 2, 4 * (B + M + 1048576) + 1,
    by omega, by omega, rfl, ?_, ?_, ?_⟩
  · intro n hlo hhi
    exact band_of_interval (by omega) (by omega) (by omega) (by omega) (by omega)
      rfl hlo hhi
  · exact yield_ge rfl (by omega) (by omega)
  · intro n
    exact no_pandigital_of_mod_four (by omega) (by omega) (by omega) (by omega)

/-! ### §10.7  Non-vacuity

The family of §10.2 is not empty of solutions: base 8 is even, `3 ∣ 8-2`, and
`174 = 256_8` is `(1,2)`-nice there — `174^2 = 73104_8`, and `{2,5,6} ∪ {7,3,1,0,4}` is
all eight digits.  Base 8 is far below the crossover — its heuristic count is 0.15 —
so this witnesses the *shape* of `ModelPositive`, not its hypothesis. -/

/--
@isnad1 id=eq.0h0v.s5.b6cf7501d6b0 from=translated src=- shape=2287321b vocab=c2c693df
-/
theorem digits_174 : digits 8 (174 ^ 1) = [6, 5, 2] := by
  show digits 8 174 = [6, 5, 2]
  rw [digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_zero]

/--
@isnad1 id=eq.0h0v.s6.fc374a568804 from=translated src=- shape=4a9848ef vocab=c2c693df
-/
theorem digits_174sq : digits 8 (174 ^ 2) = [4, 0, 1, 3, 7] := by
  show digits 8 30276 = [4, 0, 1, 3, 7]
  rw [digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_zero]

/-- 174 is `(1,2)`-nice in base 8, and base 8 is a member of §10.2's family.
@isnad1 id=pandigit.0h0v.s4.68a492261738 from=translated src=- shape=147f988f vocab=f94668c8
-/
theorem base_eight_nice : Pandigital 8 1 2 174 := by
  have h : ∀ v, v < 8 → occ v ([6, 5, 2] ++ [4, 0, 1, 3, 7]) = 1 := by decide
  intro v hv
  rw [digits_174, digits_174sq]
  exact h v hv

/--
@isnad1 id=and.0h0v.s6.3c094069bd16 from=translated src=- shape=5745fa88 vocab=1d9bb786
-/
theorem base_eight_in_family : 2 * (1 + 2) + 2 = 8 ∧ 8 % 2 = 0 := by decide

/--
@isnad1 id=inband.2h1v.s6.ad495f0d10fc from=translated src=- shape=d96defbd vocab=093cf8a6
-/
theorem base_eight_band : ∀ n, 8 ^ 2 ≤ n → n < 2 * 8 ^ 2 → InBand 8 1 2 n := by
  intro n hlo hhi
  exact band_of_interval (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl hlo hhi

/-- The even-base residue lemma, firing: base 8, `T = 28`.
@isnad1 id=eq.0h0v.s4.0a71887816e4 from=translated src=- shape=4e73c06f vocab=262eb8b4
-/
theorem base_eight_live : resOK 8 1 2 28 0 = true :=
  resOK_zero_of_even (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## §11  Theorem 1's converse — every admissible base really has candidates

§1 proves the dead direction: `(e1+e2) ∣ e1(b-1)` forces the length identity to fail,
for every `n`.  The converse — every *other* base has a candidate — was the oldest
empirical claim in this file, checked by computer over `e1 ≤ 7, e2 ≤ 8, b < 120`.
It is what turns Theorem 1 from a filter into a classification, and with it the
admissibility question (Theorems 1-4) is settled in both directions.

**It is false without a threshold**, which is why the hypotheses below are not just the
congruence.  Base 3 at `(2,3)` is outside the dead class and still has no candidate:
`f(t) = ⌊2t⌋ + ⌊3t⌋` does take the value 1 on `[1/3, 1/2)`, but `3^(1/3) ≤ n < 3^(1/2)`
holds for no integer.  §11.5 proves that, so the threshold is witnessed rather than
assumed.

**No root is extracted anywhere below, and none is needed.**  The temptation is to build
the band — `⌈b^(t_lo)⌉`, an exact integer root — and show it is inhabited.  Instead
everything happens on the integers, through

  `g n = numDigits b (n^e1) + numDigits b (n^e2)`,

which is nondecreasing, starts small and grows without bound.  All the content is that
`g` steps by at most 2, and that a step of exactly 2 skips a value the congruence
identifies.  So `g` attains every non-skipped value, `b` among them. -/

/-! ### §11.0  A Bernoulli substitute in ℕ

`(1 + 1/x)^k ≤ 2` for `x ≥ 2k`, without leaving ℕ and without a binomial theorem.  The
induction step is `x + 2i ≤ 2x`, which is the hypothesis. -/

/--
@isnad1 id=le.1h2v.s6.8af6c4e6ce1e from=translated src=- shape=752cfbce vocab=f96c6fce
-/
theorem mul_succ_pow_le : ∀ k x, 2 * k ≤ x → x * (x + 1) ^ k ≤ (x + 2 * k) * x ^ k := by
  intro k
  induction k with
  | zero => intro x _; show x * 1 ≤ (x + 0) * 1; omega
  | succ i ih =>
    intro x hx
    have hi : 2 * i ≤ x := by omega
    have key : (x + 2 * i) * (x + 1) ≤ (x + 2 * (i + 1)) * x := by
      have k1 : (x + 2 * i) * (x + 1) = (x + 2 * i) * x + (x + 2 * i) := by
        rw [Nat.mul_succ]
      have k2 : (x + 2 * (i + 1)) * x = (x + 2 * i) * x + 2 * x := by
        rw [show x + 2 * (i + 1) = (x + 2 * i) + 2 from by omega, Nat.add_mul]
      omega
    calc x * (x + 1) ^ (i + 1)
        = (x * (x + 1) ^ i) * (x + 1) := by rw [Nat.pow_succ, ← Nat.mul_assoc]
      _ ≤ ((x + 2 * i) * x ^ i) * (x + 1) := Nat.mul_le_mul_right _ (ih x hi)
      _ = ((x + 2 * i) * (x + 1)) * x ^ i := by
            rw [Nat.mul_right_comm]
      _ ≤ ((x + 2 * (i + 1)) * x) * x ^ i := Nat.mul_le_mul_right _ key
      _ = (x + 2 * (i + 1)) * x ^ (i + 1) := by rw [Nat.mul_assoc, ← Nat.pow_succ']

/-- Hence one step of `n` multiplies `n^k` by less than the base, once `n ≥ 2k`.  This
is the only inequality §11 needs about powers, and both of the next two subsections
run on it.
@isnad1 id=le.3h3v.s6.6156db96afa8 from=translated src=- shape=76a071b3 vocab=3f16b8dd
-/
theorem succ_pow_le_base_mul {b k n : Nat} (hb : 1 < b) (hn : 0 < n) (hk : 2 * k ≤ n) :
    (n + 1) ^ k ≤ b * n ^ k := by
  have h1 := mul_succ_pow_le k n hk
  have h2 : (n + 2 * k) * n ^ k ≤ (2 * n) * n ^ k :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : n * (n + 1) ^ k ≤ n * (2 * n ^ k) := by
    calc n * (n + 1) ^ k ≤ (n + 2 * k) * n ^ k := h1
      _ ≤ (2 * n) * n ^ k := h2
      _ = n * (2 * n ^ k) := by
            rw [Nat.mul_comm 2 n, Nat.mul_assoc]
  have h4 : (n + 1) ^ k ≤ 2 * n ^ k := Nat.le_of_mul_le_mul_left h3 hn
  calc (n + 1) ^ k ≤ 2 * n ^ k := h4
    _ ≤ b * n ^ k := Nat.mul_le_mul_right _ (by omega)

/-! ### §11.1  `numDigits`, read from a power bound -/

/--
@isnad1 id=le.2h3v.s5.b8d45e4ea1f5 from=translated src=- shape=0088fa00 vocab=29965d7b
-/
theorem numDigits_le_of_lt_pow {b x j : Nat} (hb : 1 < b) (h : x < b ^ j) :
    numDigits b x ≤ j := by
  rcases Nat.lt_or_ge (numDigits b x) (j + 1) with hh | hh
  · omega
  · exfalso
    obtain ⟨i, hi⟩ : ∃ i, numDigits b x = i + 1 := ⟨numDigits b x - 1, by omega⟩
    obtain ⟨g1, -⟩ := bounds_of_numDigits hb x i hi
    have : b ^ j ≤ b ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- `x` always fits in its own digit count.
@isnad1 id=lt.1h2v.s5.a2d2172c6fe7 from=translated src=- shape=ae907648 vocab=9f8a2fd9
-/
theorem lt_pow_numDigits {b : Nat} (hb : 1 < b) (x : Nat) : x < b ^ numDigits b x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [numDigits_zero, Nat.pow_zero]; omega
  · obtain ⟨i, hi⟩ : ∃ i, numDigits b x = i + 1 :=
      ⟨numDigits b x - 1, by have := numDigits_pos hb hx; omega⟩
    obtain ⟨-, g2⟩ := bounds_of_numDigits hb x i hi
    rw [hi]; exact g2

/-- One step of `n` adds at most one digit to `n^e`.
@isnad1 id=le.3h3v.s6.5427a15512dd from=translated src=- shape=bb820452 vocab=523c6e27
-/
theorem numDigits_step_le {b e n : Nat} (hb : 1 < b) (hn : 0 < n) (he : 2 * e ≤ n) :
    numDigits b ((n + 1) ^ e) ≤ numDigits b (n ^ e) + 1 := by
  refine numDigits_le_of_lt_pow hb ?_
  calc (n + 1) ^ e ≤ b * n ^ e := succ_pow_le_base_mul hb hn he
    _ < b * b ^ numDigits b (n ^ e) :=
        (Nat.mul_lt_mul_left (by omega : 0 < b)).mpr (lt_pow_numDigits hb _)
    _ = b ^ (numDigits b (n ^ e) + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-! ### §11.2  A double step pins the two lengths

The heart of it.  If `n → n+1` adds a digit to *both* powers, then `b^(A1)` and `b^(A2)`
sit in the same interval `(n^(e1e2), (n+1)^(e1e2)]` after being raised to `e2` and `e1`
respectively — and §11.0 says that interval has ratio at most `b`, so it holds at most
one power of `b`. -/

/-- Two powers of `b` inside an interval of ratio at most `b` are the same power.
@isnad1 id=eq.6h5v.s6.7869c3c7aa12 from=translated src=- shape=c5fd4652 vocab=2a3f5b88
-/
theorem pow_eq_of_narrow {b A B p q : Nat} (hb : 1 < b) (hAB : B ≤ b * A)
    (h1 : A < b ^ p) (h2 : b ^ p ≤ B) (h3 : A < b ^ q) (h4 : b ^ q ≤ B) : p = q := by
  have step : ∀ r s : Nat, r < s → A < b ^ r → b ^ s ≤ B → False := by
    intro r s hrs hAr hsB
    have e1 : b * b ^ r ≤ b ^ s := by
      calc b * b ^ r = b ^ (r + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        _ ≤ b ^ s := Nat.pow_le_pow_right (by omega) (by omega)
    have e2 : b * A < b * b ^ r := (Nat.mul_lt_mul_left (by omega : 0 < b)).mpr hAr
    omega
  rcases Nat.lt_trichotomy p q with h | h | h
  · exact (step p q h h1 h4).elim
  · exact h
  · exact (step q p h h3 h2).elim

/-- At a double step the two digit counts are locked to each other: `A1·e2 = A2·e1`.
@isnad1 id=eq.9h6v.s7.2b90b0c997e9 from=translated src=- shape=18c40dc7 vocab=3f16b8dd
-/
theorem double_step_ratio {b e1 e2 n A1 A2 : Nat} (hb : 1 < b) (hn : 0 < n)
    (he1 : e1 ≠ 0) (he2 : e2 ≠ 0) (hk : 2 * (e1 * e2) ≤ n)
    (hlo1 : n ^ e1 < b ^ A1) (hhi1 : b ^ A1 ≤ (n + 1) ^ e1)
    (hlo2 : n ^ e2 < b ^ A2) (hhi2 : b ^ A2 ≤ (n + 1) ^ e2) :
    A1 * e2 = A2 * e1 := by
  have hmul : (n + 1) ^ (e1 * e2) ≤ b * n ^ (e1 * e2) := succ_pow_le_base_mul hb hn hk
  have raise : ∀ (e f A : Nat), f ≠ 0 → n ^ e < b ^ A → b ^ A ≤ (n + 1) ^ e →
      n ^ (e * f) < b ^ (A * f) ∧ b ^ (A * f) ≤ (n + 1) ^ (e * f) := by
    intro e f A hf hlo hhi
    constructor
    · calc n ^ (e * f) = (n ^ e) ^ f := Nat.pow_mul n e f
        _ < (b ^ A) ^ f := pow_lt_pow_left' hlo f hf
        _ = b ^ (A * f) := (Nat.pow_mul b A f).symm
    · calc b ^ (A * f) = (b ^ A) ^ f := Nat.pow_mul b A f
        _ ≤ ((n + 1) ^ e) ^ f := Nat.pow_le_pow_left hhi f
        _ = (n + 1) ^ (e * f) := (Nat.pow_mul (n + 1) e f).symm
  obtain ⟨p1, p2⟩ := raise e1 e2 A1 he2 hlo1 hhi1
  obtain ⟨q1, q2⟩ := raise e2 e1 A2 he1 hlo2 hhi2
  have hswap : e2 * e1 = e1 * e2 := Nat.mul_comm e2 e1
  rw [hswap] at q1 q2
  exact pow_eq_of_narrow hb hmul p1 p2 q1 q2

/-- …and that locking is exactly the divisibility Theorem 1 tests.  The `gcd` lives
only inside this proof: the statement is in the same shape as `no_nice_of_dvd`, so the
two compose into a biconditional with nothing in between.
@isnad1 id=dvd.3h4v.s6.76df79ae6632 from=translated src=- shape=d4d91f59 vocab=e4d01d9c
-/
theorem dvd_of_ratio {e1 e2 u v : Nat} (he1 : e1 ≠ 0) (he2 : e2 ≠ 0)
    (h : u * e2 = v * e1) : (e1 + e2) ∣ e1 * (u + v) := by
  have hg : 0 < Nat.gcd e1 e2 := Nat.gcd_pos_of_pos_left e2 (Nat.pos_of_ne_zero he1)
  have hac := Nat.coprime_div_gcd_div_gcd (m := e1) (n := e2) hg
  have ha : e1 = Nat.gcd e1 e2 * (e1 / Nat.gcd e1 e2) :=
    (Nat.eq_mul_of_div_eq_right (Nat.gcd_dvd_left e1 e2) rfl)
  have hc : e2 = Nat.gcd e1 e2 * (e2 / Nat.gcd e1 e2) :=
    (Nat.eq_mul_of_div_eq_right (Nat.gcd_dvd_right e1 e2) rfl)
  have hapos : 0 < e1 / Nat.gcd e1 e2 := by
    rcases Nat.eq_zero_or_pos (e1 / Nat.gcd e1 e2) with h0 | h0
    · rw [h0, Nat.mul_zero] at ha; exact absurd ha he1
    · exact h0
  -- strip the gcd: `u·c = v·a`
  have hstrip : u * (e2 / Nat.gcd e1 e2) = v * (e1 / Nat.gcd e1 e2) := by
    refine Nat.eq_of_mul_eq_mul_left hg ?_
    calc Nat.gcd e1 e2 * (u * (e2 / Nat.gcd e1 e2))
        = u * (Nat.gcd e1 e2 * (e2 / Nat.gcd e1 e2)) := by
          rw [Nat.mul_left_comm]
      _ = u * e2 := by rw [← hc]
      _ = v * e1 := h
      _ = v * (Nat.gcd e1 e2 * (e1 / Nat.gcd e1 e2)) := by rw [← ha]
      _ = Nat.gcd e1 e2 * (v * (e1 / Nat.gcd e1 e2)) := by rw [Nat.mul_left_comm]
  -- `a ∣ u`, so `u = a·d` and `v = c·d`
  obtain ⟨d, hd⟩ : (e1 / Nat.gcd e1 e2) ∣ u :=
    hac.dvd_of_dvd_mul_right ⟨v, by rw [hstrip, Nat.mul_comm]⟩
  have hv : v = (e2 / Nat.gcd e1 e2) * d := by
    refine (Nat.eq_of_mul_eq_mul_left hapos ?_).symm
    calc (e1 / Nat.gcd e1 e2) * ((e2 / Nat.gcd e1 e2) * d)
        = ((e1 / Nat.gcd e1 e2) * d) * (e2 / Nat.gcd e1 e2) := by
          rw [Nat.mul_comm (e2 / Nat.gcd e1 e2) d, ← Nat.mul_assoc]
      _ = u * (e2 / Nat.gcd e1 e2) := by rw [← hd]
      _ = v * (e1 / Nat.gcd e1 e2) := hstrip
      _ = (e1 / Nat.gcd e1 e2) * v := Nat.mul_comm _ _
  refine ⟨(e1 / Nat.gcd e1 e2) * d, ?_⟩
  calc e1 * (u + v)
      = e1 * ((e1 / Nat.gcd e1 e2) * d + (e2 / Nat.gcd e1 e2) * d) := by rw [hd, hv]
    _ = e1 * (((e1 / Nat.gcd e1 e2) + (e2 / Nat.gcd e1 e2)) * d) := by rw [Nat.add_mul]
    _ = (Nat.gcd e1 e2 * (e1 / Nat.gcd e1 e2))
          * (((e1 / Nat.gcd e1 e2) + (e2 / Nat.gcd e1 e2)) * d) := by rw [← ha]
    _ = (Nat.gcd e1 e2 * ((e1 / Nat.gcd e1 e2) + (e2 / Nat.gcd e1 e2)))
          * ((e1 / Nat.gcd e1 e2) * d) := by
          rw [Nat.mul_assoc, Nat.mul_assoc]
          rw [Nat.mul_left_comm (e1 / Nat.gcd e1 e2)
                ((e1 / Nat.gcd e1 e2) + (e2 / Nat.gcd e1 e2)) d]
    _ = (e1 + e2) * ((e1 / Nat.gcd e1 e2) * d) := by
          rw [Nat.mul_add, ← ha, ← hc]

/-! ### §11.3  Walking up to `b`

A nondecreasing `g` that starts below `b`, ends at or above it, and never steps *over*
it, must land on it.  Stated for exactly the range that is walked, because §11.2's
hypotheses hold only above the threshold. -/

/--
@isnad1 id=ex.3h4v.s6.1df30f26ce67 from=translated src=- shape=daf1d2e6 vocab=110a7538
-/
theorem hits_of_no_jump {g : Nat → Nat} {b N : Nat}
    (hjump : ∀ n, N ≤ n → g n < b → g (n + 1) ≤ b) :
    ∀ len, g N < b → b ≤ g (N + len) → ∃ n, g n = b := by
  intro len
  induction len generalizing N with
  | zero => intro h1 h2; rw [Nat.add_zero] at h2; omega
  | succ t ih =>
    intro h1 h2
    have hstep := hjump N (Nat.le_refl N) h1
    rcases Nat.lt_or_ge (g (N + 1)) b with h | h
    · refine ih (fun n hn => hjump n (by omega)) h ?_
      rw [show N + 1 + t = N + (t + 1) from by omega]
      exact h2
    · exact ⟨N + 1, by omega⟩

/-! ### §11.4  Theorem 1's converse -/

/--
**Theorem 1, converse.**  A base outside the dead class of §1 really does have a
candidate — every base large enough for the two explicit bounds, which is what §11.5
shows cannot be dropped.

`j1` and `j2` are digit-count certificates for the threshold `N = 2·e1·e2 + 1`, the
point above which one step of `n` can no longer add two digits to a power: any `j_i`
with `N^(e_i) < b^(j_i)` will do, and taking each as small as possible the three
hypotheses say exactly

    len_b(N^e1) + len_b(N^e2) < b,

i.e. the walk starts below the value it is looking for.  This form is stated with the
digit counts named because it is `decide`able at a concrete base and `numDigits` is
not.  The left side is nonincreasing in `b`, so each pair has a single first base from
which the theorem holds for good — 8 for `(2,3)` (`two_three_band_nonempty`), 6 for
`(1,2)`, 12 for `(3,4)`, 28 for `(8,9)`.
@isnad1 id=ex.7h5v.s7.3031b0c50b79 from=translated src=- shape=e40ccf43 vocab=785c8858
-/
theorem band_nonempty {b e1 e2 j1 j2 : Nat} (hb : 1 < b) (he1 : e1 ≠ 0) (he2 : e2 ≠ 0)
    (hj1 : (2 * (e1 * e2) + 1) ^ e1 < b ^ j1)
    (hj2 : (2 * (e1 * e2) + 1) ^ e2 < b ^ j2)
    (hsum : j1 + j2 < b)
    (hdvd : ¬ ((e1 + e2) ∣ e1 * (b - 1))) :
    ∃ n, InBand b e1 e2 n := by
  have hb0 : 0 < b := by omega
  have he1p : 0 < e1 := Nat.pos_of_ne_zero he1
  have he2p : 0 < e2 := Nat.pos_of_ne_zero he2
  -- the walk starts here, and `g N < b`
  have hNpos : 0 < 2 * (e1 * e2) + 1 := by omega
  have hstart : numDigits b ((2 * (e1 * e2) + 1) ^ e1)
      + numDigits b ((2 * (e1 * e2) + 1) ^ e2) < b := by
    have a1 := numDigits_le_of_lt_pow hb hj1
    have a2 := numDigits_le_of_lt_pow hb hj2
    omega
  -- no step jumps over `b`
  have hjump : ∀ n, 2 * (e1 * e2) + 1 ≤ n →
      numDigits b (n ^ e1) + numDigits b (n ^ e2) < b →
      numDigits b ((n + 1) ^ e1) + numDigits b ((n + 1) ^ e2) ≤ b := by
    intro n hn hlt
    have hn0 : 0 < n := by omega
    have s1 : numDigits b ((n + 1) ^ e1) ≤ numDigits b (n ^ e1) + 1 :=
      numDigits_step_le hb hn0 (by
        have : e1 ≤ e1 * e2 := Nat.le_mul_of_pos_right e1 he2p
        omega)
    have s2 : numDigits b ((n + 1) ^ e2) ≤ numDigits b (n ^ e2) + 1 :=
      numDigits_step_le hb hn0 (by
        have : e2 ≤ e1 * e2 := Nat.le_mul_of_pos_left e2 he1p
        omega)
    rcases Nat.lt_or_ge (numDigits b ((n + 1) ^ e1)
        + numDigits b ((n + 1) ^ e2)) (b + 1) with hle | hge
    · omega
    -- the only remaining case is a double step over `b`, and it is the dead class
    · exfalso
      have d1 : numDigits b ((n + 1) ^ e1) = numDigits b (n ^ e1) + 1 := by omega
      have d2 : numDigits b ((n + 1) ^ e2) = numDigits b (n ^ e2) + 1 := by omega
      have hsum' : numDigits b (n ^ e1) + numDigits b (n ^ e2) = b - 1 := by omega
      have hhi1 : b ^ numDigits b (n ^ e1) ≤ (n + 1) ^ e1 :=
        (bounds_of_numDigits hb _ _ d1).1
      have hhi2 : b ^ numDigits b (n ^ e2) ≤ (n + 1) ^ e2 :=
        (bounds_of_numDigits hb _ _ d2).1
      have hratio := double_step_ratio hb hn0 he1 he2 (by omega)
        (lt_pow_numDigits hb (n ^ e1)) hhi1 (lt_pow_numDigits hb (n ^ e2)) hhi2
      have := dvd_of_ratio he1 he2 hratio
      rw [hsum'] at this
      exact hdvd this
  -- and it gets there: `g (b^b) = (e1+e2)·b + 2 ≥ b`
  have hpow : ∀ i, numDigits b (b ^ i) = i + 1 := by
    intro i
    exact numDigits_eq_of_bounds hb (Nat.le_refl _)
      (Nat.pow_lt_pow_right hb (by omega))
  have hend : b ≤ numDigits b ((b ^ b) ^ e1) + numDigits b ((b ^ b) ^ e2) := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, hpow, hpow]
    have : b ≤ b * e1 := Nat.le_mul_of_pos_right b he1p
    omega
  -- the threshold is below `b^b`, so the walk has somewhere to go
  have hNle : 2 * (e1 * e2) + 1 ≤ b ^ b := by
    have hj2pos : 0 < j2 := by
      rcases Nat.eq_zero_or_pos j2 with rfl | h
      · rw [Nat.pow_zero] at hj2
        have : 1 ≤ (2 * (e1 * e2) + 1) ^ e2 := Nat.one_le_pow _ _ hNpos
        omega
      · exact h
    have h1 : 2 * (e1 * e2) + 1 ≤ (2 * (e1 * e2) + 1) ^ e1 :=
      Nat.le_self_pow he1 _
    have h2 : b ^ j1 ≤ b ^ b := Nat.pow_le_pow_right hb0 (by omega)
    omega
  obtain ⟨n, hn⟩ := hits_of_no_jump (g := fun n => numDigits b (n ^ e1) + numDigits b (n ^ e2))
    hjump (b ^ b - (2 * (e1 * e2) + 1)) hstart
    (by rw [show 2 * (e1 * e2) + 1 + (b ^ b - (2 * (e1 * e2) + 1)) = b ^ b from by omega]
        exact hend)
  exact ⟨n, hn⟩

/-- **Theorem 1, both directions.**  Above the threshold, a base has a candidate if and
only if it is outside the dead class — which is the classification the informal account states,
and of which, until §11, only the forward half was proved.
@isnad1 id=iff.6h5v.s7.bfdb77adeb33 from=translated src=- shape=e6cf1a36 vocab=785c8858
-/
theorem band_nonempty_iff {b e1 e2 j1 j2 : Nat} (hb : 1 < b) (he1 : e1 ≠ 0) (he2 : e2 ≠ 0)
    (hj1 : (2 * (e1 * e2) + 1) ^ e1 < b ^ j1)
    (hj2 : (2 * (e1 * e2) + 1) ^ e2 < b ^ j2)
    (hsum : j1 + j2 < b) :
    (∃ n, InBand b e1 e2 n) ↔ ¬ ((e1 + e2) ∣ e1 * (b - 1)) :=
  ⟨fun ⟨n, hn⟩ hdvd => no_nice_of_dvd hb he1 he2 hdvd hn,
   fun hdvd => band_nonempty hb he1 he2 hj1 hj2 hsum hdvd⟩

/-! ### §11.5  Both witnesses: the theorem fires, and the threshold is not decoration

`two_three_band_nonempty` is the classical problem's form of it, over *all* bases from 8
up at once — no root, no scan, and nothing about how large the band is.
`base_three_no_candidate` is the other half: base 3 is outside the dead class and has no
candidate anyway, so a converse without a threshold would be false, not merely unproved. -/

/-- **Every base `b ≥ 8` outside `b ≡ 1 (mod 5)` has a square/cube candidate.**  The
counterpart of `nice_no_solution`, and with it the `(2,3)` admissibility question is
closed in both directions from base 8 on.
@isnad1 id=ex.2h1v.s5.9157421a853d from=translated src=- shape=d0bb8e04 vocab=0522b4ea
-/
theorem two_three_band_nonempty {b : Nat} (hb : 8 ≤ b) (hmod : b % 5 ≠ 1) :
    ∃ n, InBand b 2 3 n := by
  refine band_nonempty (e1 := 2) (e2 := 3) (j1 := 3) (j2 := 4) (by omega) (by decide)
    (by decide) ?_ ?_ (by omega) ?_
  · calc (2 * (2 * 3) + 1) ^ 2 = 169 := by decide
      _ < 8 ^ 3 := by decide
      _ ≤ b ^ 3 := Nat.pow_le_pow_left hb 3
  · calc (2 * (2 * 3) + 1) ^ 3 = 2197 := by decide
      _ < 8 ^ 4 := by decide
      _ ≤ b ^ 4 := Nat.pow_le_pow_left hb 4
  · intro hdvd
    have h2 : (5 : Nat) ∣ 2 * (b - 1) := hdvd
    have hcop : Nat.Coprime 5 2 := by decide
    exact hmod (by have := hcop.dvd_of_dvd_mul_left h2; omega)

/-- Base 34 is one of them — a base whose band starts above `3·10^9`, exhibited by
nothing more than `169 < 34^2` and `2197 < 34^3`.
@isnad1 id=ex.0h0v.s4.f98284f88841 from=translated src=- shape=26e9acfe vocab=7d977a64
-/
theorem base_thirtyfour_band : ∃ n, InBand 34 2 3 n :=
  two_three_band_nonempty (by omega) (by decide)

/-- **The threshold is load-bearing.**  Base 3 is *not* in the dead class — `¬ (5 ∣ 2·2)`
— and still has no `(2,3)` candidate: `n^2` and `n^3` each need two base-3 digits as soon
as `n ≥ 2`, and `n ≤ 1` gives at most two digits in total, so the sum is never 3.  In the
real picture the level set of `⌊2t⌋ + ⌊3t⌋ = 1` is the interval `[1/3, 1/2)`, and
`3^(1/3) ≤ n < 3^(1/2)` catches no integer.
@isnad1 id=not.0h1v.s4.eb3defbce1de from=translated src=- shape=2e95bcf2 vocab=7d977a64
-/
theorem base_three_no_candidate (n : Nat) : ¬ InBand 3 2 3 n := by
  intro h
  have hb : (1 : Nat) < 3 := by decide
  have hsum : numDigits 3 (n ^ 2) + numDigits 3 (n ^ 3) = 3 := h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · match n, hn with
    | 0, _ => rw [numDigits_zero] at hsum; omega
    | 1, _ =>
      rw [numDigits_eq_of_bounds (b := 3) (x := 1 ^ 2) (k := 0) hb (by decide) (by decide)]
        at hsum
      omega
  · have h2 : 2 ≤ numDigits 3 (n ^ 2) := by
      have : (3 : Nat) ^ 1 ≤ n ^ 2 :=
        Nat.le_trans (by decide) (Nat.pow_le_pow_left hn 2)
      have := le_numDigits_of_pow_le hb this
      omega
    have h3 : 2 ≤ numDigits 3 (n ^ 3) := by
      have : (3 : Nat) ^ 1 ≤ n ^ 3 :=
        Nat.le_trans (by decide) (Nat.pow_le_pow_left hn 3)
      have := le_numDigits_of_pow_le hb this
      omega
    omega

/-- And base 3 fails the theorem's hypotheses exactly where it should: `2197 < 3^j2`
needs `j2 ≥ 7`, so `j1 + j2 < 3` is unreachable.
@isnad1 id=not.0h0v.s6.27a1248468b5 from=translated src=- shape=3e064da7 vocab=b9e5bafd
-/
theorem base_three_misses_the_threshold : ¬ ((2 : Nat) * (2 * 3) + 1) ^ 3 < 3 ^ 6 := by
  decide

end Nice

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/Janzert/nice-numbers-lean@28b958ea28f9, `NiceNumbers.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

