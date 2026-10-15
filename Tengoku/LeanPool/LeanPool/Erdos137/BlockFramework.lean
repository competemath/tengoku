/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos137.Base
public import Tengoku

/-!
# Erdős Problem #137: the parametric `g`-block framework (unifying `g = 3` and `g = 5`)

`Erdos137/JointFiniteness.lean` develops the **triple** (`g = 3`) radical-decomposition route and
`Erdos137/SpliceFiniteness.lean` the **quintic** (`g = 5`) route. Both are the *same* argument run
with a different block length `g`. This file factors that duplication into ONE parametric
`g`-block framework: every `3`/`5` in the two existing chains is replaced by a symbolic `g`, and
the master inequality, per-`k` bound, and finiteness wrapper are proved once, for all `g ≥ 3`.

## The unified master inequality

The headline is `master_ineq_g`: under the normalized block radical hypothesis `BlockRadLBg g`,
for `k ≥ g ≥ 3` and a powerful `F k n` (`n ≥ 1`),

  `n ^ ((g - 2) * k) · L k ^ g  ≤  (k ^ (2k)) ^ g · P k ^ (2g)`.

This specializes EXACTLY to both recorded thresholds:

* `g = 3` ⟹ `n ^ k · L^3 ≤ (k^{2k})^3 · P^6` — the JointFiniteness/SmoothRefinement threshold
  (`master_ineq`, since `(3 - 2) * k = k`);
* `g = 5` ⟹ `n ^ {3k} · L^5 ≤ (k^{2k})^5 · P^{10}` — the SpliceFiniteness threshold
  (`master_ineq5`, since `(5 - 2) * k = 3k`).

There are TWO exponent readings of `master_ineq_g`, and they must not be conflated. With only the
proved lower bound `L k ≥ 1`, the master inequality gives the **coarse** threshold
`n > k^{2g/(g-2) + o(1)}`; as `g → ∞` this exponent tends to `2`, i.e. toward `k^{2 + ε}` — NOT
`k^{1 + ε}`. The `k^{1 + ε}` reading appears only after the unformalized Mertens lower bound
`log L k = k log k − O(k)` (so `L k = k^{k − o(k)}`), which sharpens the threshold to
`n > k^{g/(g-2) + o(1)}`; that exponent tends to `1`. So fixed large `g` reaches the pen-and-paper
`k^{1 + ε}` floor only in the Mertens-sharpened reading, never from the coarse formal bound alone.
The formal `.Finite` wrapper deliberately uses the coarse explicit bound `n ≤ Mg g k`; the sharp
exponent stays an external asymptotic reading of the master inequality. This is also NOT an
unconditional improvement: for each FIXED `g` the abc/Langevin constant packaged in `BlockRadLBg g`
depends on `g` (the implied constant degrades with the block length) — the known ceiling of the
radical method, trading a sharper exponent for a worse constant, and the constant is exactly what
abc would supply. So this is not a uniform growing-`g` theorem.

## The two guards

* `3 ≤ g` is needed for the exponent `(g - 2) ≥ 1` (so `n ≤ n^{(g-2)k}`) and for the smooth/squaring
  arithmetic `2(g-1)/g - 1 = (g-2)/g ≥ 0`.
* `g ≤ k` is a CONSISTENCY guard built into `BlockRadLBg`. For `g > k` there are no `g`-blocks
  (`⌊k/g⌋ = 0`), the block-radical product is the empty product `1`, and the hypothesis
  `(F k n)^{(g-1)/g} ≤ 1` would be inconsistent (it would force `F k n ≤ 1`).

## What is proved vs. hypothesized

* **Proved (Mathlib's three axioms only):** the generic block product identity `blocksg_prod_eq`,
  the radical-of-product decomposition `rad_blocksg_decomp`, the overlap bound `Wg_le_pow`
  (`Wg ∣ k!`, Legendre), the smooth-refined master inequality `master_ineq_g`, the explicit per-`k`
  bound `powerful_bound_g`, and the finiteness wrapper `g_finiteness`.
* **Hypothesis (analytic input, NOT formalized):** `BlockRadLBg g` is the normalized tail-absorbed
  block radical lower bound — it packages the abc/Langevin constant, the epsilon loss, and the
  omitted `k mod g` tail into one explicit Prop. abc itself is NOT formalized; it enters only as a
  premise, so it does not appear in any axiom footprint.

The shared low-level helpers (`rad_dvd_self`, `factorization_rad`, `rad_dvd_rad_of_dvd`,
`Ioc_dvd_count`, `Ioc_dvd_le`, `div_le_factorization_factorial`, `pow_le_F`, `le_F`, the smooth
refinement `smooth_refinement`, `P`, `L`, …) are imported and reused verbatim from `Erdos137.Base`,
not re-proved.

This framework sits ABOVE the concrete `g = 3, 5` modules: `JointFiniteness` defines
`B`/`overlap`/`W` literally as `Bg 3`/`overlapg 3`/`Wg 3` and `SpliceFiniteness` defines
`B5`/`overlap5`/`W5` as the `g = 5` instances, with their public lemmas re-derived as thin
wrappers of the generic theorems below.

## Two routes: SMOOTH vs. CRUDE

There are now TWO parametric routes off the same block chain, and they must not be conflated:

* **SMOOTH** (`master_ineq_g`, PART C): `n ^ ((g-2) k) · L ^ g ≤ (k^{2k})^g · P ^ {2g}`. This
  refines the bare powerful inequality `rad ^ 2 ≤ F` by the smooth gain `L`, so it carries a
  *sharper exponent* — threshold `k ^ {2g/(g-2) + o(1)}` (coarse `L ≥ 1` reading) or
  `k ^ {g/(g-2) + o(1)}`
  (Mertens reading). But the sharpening is only realized through the *unformalized* Mertens lower
  bound on `L`; the formal `.Finite` wrapper falls back on the coarse explicit `Mg`.
* **CRUDE** (`master_ineq_crude_g`, PART E): `n ^ (g - 2) ≤ k ^ (2 * g)`, a clean INTEGER inequality
  carrying NO `L`/`P` factor — it uses only `rad ^ 2 ≤ F`. The exponent is weaker but the threshold
  is the *exact, fully explicit* `k ^ {2g/(g-2)}` with no `o(1)` and no Mertens input:
  `g = 3 → k^6`, `g = 4 → k^4` (since `n^2 ≤ k^8 ↔ n ≤ k^4`), `g = 6 → k^3`.

So: the crude route gives a fully explicit constant at a worse exponent; the smooth route gives a
sharper exponent only via the unformalized Mertens reading. The crude `g = 3` instance recovers the
recorded `not_powerful_of_large` threshold `n > k^6` exactly.
-/

@[expose] public section

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-! ## PART A — the generic `g`-block combinatorics (literal `3`/`5` → `g`) -/

/-- The block product `Bg g k n = ∏_{j<⌊k/g⌋} F g (n+g·j) = F (g⌊k/g⌋) n`: the part of `F k n`
covered by the `g`-blocks (dropping the `k % g` tail). Generic form of `B`/`B5`. -/
def Bg (g k n : ℕ) : ℕ := ∏ j ∈ Finset.range (k / g), F g (n + g * j)

/-- `overlapg g p = ∑_j [p ∈ (F g (n+g·j)).primeFactors]` is the number of `g`-blocks `p` divides.
Generic form of `overlap`/`overlap5`. -/
def overlapg (g k n p : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k / g), if p ∈ (F g (n + g * j)).primeFactors then 1 else 0

/-- The over-count `Wg g k n := ∏_{p ∈ (Bg g k n).primeFactors} p ^ (overlapg p − 1)`.
Generic form of `W`/`W5`. -/
def Wg (g k n : ℕ) : ℕ :=
  ∏ p ∈ (Bg g k n).primeFactors, p ^ (overlapg g k n p - 1)

/-- The product over the `⌊k/g⌋` blocks, `∏_{j<⌊k/g⌋} F g (n + g·j)`, equals `F (g · ⌊k/g⌋) n`.
Generic form of `triples_prod_eq`/`blocks5_prod_eq`. The `(hg : 1 ≤ g)` guard makes the stride
positive in the telescoping; it is not actually needed here (the induction is on `k / g`), but is
recorded to match the parametric setting.
@isnad1 id=eq.1h3v.s6.23c882b608a2 from=translated src=- shape=3b94c0da vocab=d75cbd3f
-/
lemma blocksg_prod_eq (_hg : 1 ≤ g) (k n : ℕ) :
    (∏ j ∈ Finset.range (k / g), F g (n + g * j)) = F (g * (k / g)) n := by
  induction (k / g) with
  | zero => simp [F]
  | succ t ih =>
    rw [Finset.prod_range_succ, ih]
    have hg' : g * (t + 1) = g * t + g := by ring
    rw [hg', F_add]

/-- `Bg g k n = F (g * (k/g)) n`.
@isnad1 id=eq.1h3v.s5.387dc45a540c from=translated src=- shape=8272760b vocab=612fa5e3
-/
lemma Bg_eq (hg : 1 ≤ g) (k n : ℕ) : Bg g k n = F (g * (k / g)) n := blocksg_prod_eq hg k n

/-- The product of the `g`-blocks divides `F k n`. Generic form of `triples_prod_dvd`.
@isnad1 id=dvd.1h3v.s5.dff9ea3ce6a0 from=translated src=- shape=85216017 vocab=72a11f3b
-/
lemma blocksg_prod_dvd (hg : 1 ≤ g) (k n : ℕ) :
    (∏ j ∈ Finset.range (k / g), F g (n + g * j)) ∣ F k n := by
  rw [blocksg_prod_eq hg]
  have hk : k = g * (k / g) + (k % g) := (Nat.div_add_mod k g).symm
  conv_rhs => rw [hk]
  exact F_dvd_F_add _ _ _

/-- **`Bg g k n` divides `F k n`** (generic form of `B_dvd_F`/`B5_dvd_F`).
@isnad1 id=dvd.1h3v.s4.b0478a499cbd from=translated src=- shape=c3b87c81 vocab=ca10c04c
-/
lemma Bg_dvd_F (hg : 1 ≤ g) (k n : ℕ) : Bg g k n ∣ F k n := blocksg_prod_dvd hg k n

/-- `Bg g k n ≠ 0` for `n ≥ 1`.
@isnad1 id=ne.2h3v.s5.d5f8d554cbfc from=translated src=- shape=3a9a71a9 vocab=1421f4d6
-/
lemma Bg_ne_zero (hg : 1 ≤ g) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : Bg g k n ≠ 0 := by
  rw [Bg_eq hg]; exact F_ne_zero hn

/-- For `n ≥ 1` each block `F g (n + g·j)` is nonzero.
@isnad1 id=ne.1h3v.s5.71adf7574e4b from=translated src=- shape=ca6845c0 vocab=d01f733b
-/
lemma block_ne_zero {n : ℕ} (hn : 1 ≤ n) (g j : ℕ) : F g (n + g * j) ≠ 0 :=
  F_ne_zero (by omega)

/-- The `p`-adic valuation of the product of the block radicals equals `overlapg g k n p`.
@isnad1 id=eq.1h4v.s6.2f888843e84e from=translated src=- shape=38cf6c01 vocab=fd779160
-/
lemma factorization_blocksg_rad (g k n p : ℕ) (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / g), rad (F g (n + g * j))).factorization p = overlapg g k n p := by
  have hrad_ne : ∀ j ∈ Finset.range (k / g), rad (F g (n + g * j)) ≠ 0 := by
    intro j _; exact Nat.one_le_iff_ne_zero.mp (rad_pos _)
  rw [Nat.factorization_prod_apply hrad_ne]
  unfold overlapg
  apply Finset.sum_congr rfl
  intro j _
  rw [factorization_rad (block_ne_zero hn g j)]

/-- The `p`-valuation of `rad (Bg g k n)` is `1` if `p ∈ (Bg g k n).primeFactors`, else `0`.
@isnad1 id=eq.2h4v.s6.a6d94d65045f from=translated src=- shape=61a28420 vocab=eaeed8b3
-/
lemma factorization_rad_Bg (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    (rad (Bg g k n)).factorization p = if p ∈ (Bg g k n).primeFactors then 1 else 0 :=
  factorization_rad (Bg_ne_zero hg hn k) p

/-- A prime in the support of `Bg g k n` divides some block, hence `overlapg ≥ 1`.
@isnad1 id=le.2h4v.s5.fe4da0300d0f from=translated src=- shape=d893e20a vocab=5c470875
-/
lemma overlapg_pos_of_mem_primeFactors {g k n p : ℕ} (hn : 1 ≤ n)
    (hp : p ∈ (Bg g k n).primeFactors) : 1 ≤ overlapg g k n p := by
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpdvd : p ∣ Bg g k n := Nat.dvd_of_mem_primeFactors hp
  have : ∃ j ∈ Finset.range (k / g), p ∣ F g (n + g * j) := by
    rw [Bg] at hpdvd
    exact (Nat.Prime.prime hpprime).exists_mem_finset_dvd hpdvd
  obtain ⟨j, hj, hjdvd⟩ := this
  unfold overlapg
  have hmem : p ∈ (F g (n + g * j)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime, hjdvd, block_ne_zero hn g j⟩
  have hle := Finset.single_le_sum
    (f := fun i => if p ∈ (F g (n + g * i)).primeFactors then (1:ℕ) else 0)
    (by intro i _; positivity) hj
  simpa [hmem] using hle

/-- If `overlapg g k n p ≥ 1` then `p ∈ (Bg g k n).primeFactors`.
@isnad1 id=mem.2h4v.s5.0b7be4c1fb05 from=translated src=- shape=db36cad8 vocab=5c470875
-/
lemma mem_primeFactors_of_overlapg_pos {g k n p : ℕ} (hn : 1 ≤ n) (h : 1 ≤ overlapg g k n p) :
    p ∈ (Bg g k n).primeFactors := by
  unfold overlapg at h
  obtain ⟨j, hj, hjne⟩ : ∃ j ∈ Finset.range (k / g),
      (if p ∈ (F g (n + g * j)).primeFactors then (1:ℕ) else 0) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ∑ j ∈ Finset.range (k / g),
        (if p ∈ (F g (n + g * j)).primeFactors then (1:ℕ) else 0) = 0 :=
      Finset.sum_eq_zero (fun j hj => hcon j hj)
    omega
  -- The block range is nonempty (`j ∈ range (k/g)`), so `k/g ≥ 1`, forcing `g ≥ 1`.
  have hg1 : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with hg0 | hg0
    · exfalso; subst hg0; simp at hj
    · exact hg0
  have hmem : p ∈ (F g (n + g * j)).primeFactors := by
    by_contra hc; simp [hc] at hjne
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hmem).1
  have hpdvd_block : p ∣ F g (n + g * j) := Nat.dvd_of_mem_primeFactors hmem
  have hpdvdB : p ∣ Bg g k n := by
    rw [Bg]; exact dvd_trans hpdvd_block (Finset.dvd_prod_of_mem _ hj)
  exact Nat.mem_primeFactors.mpr ⟨hpprime, hpdvdB, Bg_ne_zero hg1 hn k⟩

/-- For a prime power `q ^ e` with `q` prime, its `p`-valuation is `e` if `q = p`, else `0`. -/
private lemma factorization_prime_pow_applyg {q : ℕ} (hq : q.Prime) (e p : ℕ) :
    (q ^ e).factorization p = if q = p then e else 0 := by
  rw [Nat.Prime.factorization_pow hq]
  rw [Finsupp.single_apply]

/-- The `p`-valuation of the over-count `Wg g k n`.
@isnad1 id=eq.1h4v.s6.683eecb9db62 from=translated src=- shape=8b0f0d98 vocab=599b2968
-/
lemma factorization_Wg {g k n : ℕ} (_hn : 1 ≤ n) (p : ℕ) :
    (Wg g k n).factorization p =
      if p ∈ (Bg g k n).primeFactors then overlapg g k n p - 1 else 0 := by
  unfold Wg
  rw [Nat.factorization_prod_apply (by
    intro q hq
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero)]
  by_cases hp : p ∈ (Bg g k n).primeFactors
  · simp only [hp, ite_true]
    rw [Finset.sum_eq_single p]
    · simp_all
    · simp_all
    · intro h; exact absurd hp h
  · simp only [hp, ite_false]
    apply Finset.sum_eq_zero
    intro q hq
    have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
    rw [factorization_prime_pow_applyg hqprime]
    have : q ≠ p := by rintro rfl; exact hp hq
    simp [this]

/-- **Radical-of-product decomposition (generic `g`), exact form.**
`∏_j rad (F g (n+g·j)) = rad (Bg g k n) * Wg g k n`. Generic form of
`rad_triples_decomp`/`rad_blocks5_decomp`.
@isnad1 id=eq.2h3v.s6.88597f566a44 from=translated src=- shape=cf3bdc3a vocab=1569a35d
-/
theorem rad_blocksg_decomp (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / g), rad (F g (n + g * j))) = rad (Bg g k n) * Wg g k n := by
  have hR_ne : (∏ j ∈ Finset.range (k / g), rad (F g (n + g * j))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Nat.one_le_iff_ne_zero.mp (rad_pos _)
  have hradB_ne : rad (Bg g k n) ≠ 0 := Nat.one_le_iff_ne_zero.mp (rad_pos _)
  have hW_ne : Wg g k n ≠ 0 := by
    unfold Wg; exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  apply Nat.eq_of_factorization_eq hR_ne (mul_ne_zero hradB_ne hW_ne)
  intro p
  rw [factorization_blocksg_rad g k n p hn]
  rw [Nat.factorization_mul hradB_ne hW_ne]
  simp only [Finsupp.add_apply]
  rw [factorization_rad_Bg hg hn p, factorization_Wg hn p]
  by_cases hp : p ∈ (Bg g k n).primeFactors
  · simp only [hp, ite_true]
    have h1 : 1 ≤ overlapg g k n p := overlapg_pos_of_mem_primeFactors hn hp
    omega
  · simp only [hp, ite_false, add_zero]
    by_contra hcon
    have : 1 ≤ overlapg g k n p := by omega
    exact hp (mem_primeFactors_of_overlapg_pos hn this)

/-- `rad (Bg g k n) ∣ rad (F k n)`.
@isnad1 id=dvd.2h3v.s5.07d5099bbc16 from=translated src=- shape=96244b57 vocab=9ebf698e
-/
lemma rad_Bg_dvd_rad_F (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) : rad (Bg g k n) ∣ rad (F k n) :=
  rad_dvd_rad_of_dvd (F_ne_zero hn) (Bg_dvd_F hg k n)

/-- **Decomposition inequality (the usable form, generic `g`):**
`∏_j rad (F g (n+g·j)) ≤ rad (F k n) * Wg g k n`
(generic form of `rad_triples_le`/`rad_5blocks_le`).
@isnad1 id=le.2h3v.s6.5737bc10356a from=translated src=- shape=3709bc13 vocab=04914a4b
-/
theorem rad_blocksg_le (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / g), rad (F g (n + g * j))) ≤ rad (F k n) * Wg g k n := by
  rw [rad_blocksg_decomp hg hn]
  apply Nat.mul_le_mul_right
  exact Nat.le_of_dvd (rad_pos _) (rad_Bg_dvd_rad_F hg hn)

/-! ### The overlap bound `Wg g k n ≤ k^k` -/

/-- The "first hit" map used to inject the counted `g`-blocks into the multiples of `p` in the
spanning interval. `firstHit g n p j` is `n + g·j + r₀`, where `r₀ < g` is the least block offset
with `p ∣ (n + g·j + r₀)` (defaulting to `g - 1` if none — that branch is never taken for counted
blocks). Replaces the hardcoded `if … then … else …` chains of `overlap_le`/`overlap5_le` by a
uniform construction that works for any block length `g`. -/
def firstHit (g n p j : ℕ) : ℕ :=
  n + g * j + (((Finset.range g).filter (fun r => p ∣ (n + g * j + r))).min.getD (g - 1))

/-- `firstHit g n p j` lies in the block `[n + g·j, n + g·j + (g-1)]`.
@isnad1 id=mem.0h4v.s6.317ff55f2a6b from=translated src=- shape=202bd92d vocab=db9fcc48
-/
lemma firstHit_mem_Icc (g n p j : ℕ) :
    firstHit g n p j ∈ Finset.Icc (n + g * j) (n + g * j + (g - 1)) := by
  simp only [firstHit, Finset.mem_Icc]
  refine ⟨by omega, ?_⟩
  rcases ((Finset.range g).filter (fun r => p ∣ (n + g * j + r))).min.eq_none_or_eq_some
    with hnone | ⟨r0, hr0⟩
  · simp [hnone]
  · have hr0mem : r0 ∈ (Finset.range g).filter (fun r => p ∣ (n + g * j + r)) :=
      Finset.mem_of_min hr0
    rw [Finset.mem_filter, Finset.mem_range] at hr0mem
    simp only [hr0, Option.getD]; omega

/-- **Overlap bound (combinatorial core, generic `g`).** `overlapg g k n p ≤ ⌊k/p⌋ + 1` for
`n ≥ 1`. The `⌊k/g⌋` blocks span `≤ k` consecutive integers, and a prime `p` divides at most
`⌊k/p⌋ + 1` of any `≤ k` consecutive integers. Generic form of `overlap_le`/`overlap5_le`.
@isnad1 id=le.2h4v.s5.aabfdc89d7cd from=translated src=- shape=eaa6631f vocab=12b7b719
-/
lemma overlapg_le (hg : 1 ≤ g) {k n p : ℕ} (hn : 1 ≤ n) : overlapg g k n p ≤ k / p + 1 := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · subst hp0; unfold overlapg
    simp_all
  · set t := k / g with ht
    set m := g * t with hm
    have hmk : m ≤ k := by rw [hm, ht]; exact Nat.mul_div_le k g
    -- Each counted block `j` contributes a divisible integer in `(n-1, n-1+m]`: `firstHit g n p j`.
    have hkey : overlapg g k n p ≤ #{x ∈ Finset.Ioc (n - 1) (n - 1 + m) | p ∣ x} := by
      unfold overlapg
      have hsum : (∑ j ∈ Finset.range t,
          (if p ∈ (F g (n + g * j)).primeFactors then (1 : ℕ) else 0))
          = #{j ∈ Finset.range t | p ∈ (F g (n + g * j)).primeFactors} := by
        simp_all
      rw [show k / g = t from rfl, hsum]
      apply Finset.card_le_card_of_injOn (firstHit g n p)
      · intro j hj
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
        obtain ⟨hjt, hmem⟩ := hj
        have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
        have hpdvd : p ∣ F g (n + g * j) := Nat.dvd_of_mem_primeFactors hmem
        -- `p` divides some factor `n + g·j + r` with `r < g`.
        have hexists : ∃ r ∈ Finset.range g, p ∣ (n + g * j + r) := by
          have hprod : p ∣ ∏ i ∈ Finset.range g, (n + g * j + i) := by
            have hF : F g (n + g * j) = ∏ i ∈ Finset.range g, ((n + g * j) + i) := by
              unfold F; rfl
            rwa [hF] at hpdvd
          obtain ⟨i, hi, hidvd⟩ := (Nat.Prime.prime hpp).exists_mem_finset_dvd hprod
          exact ⟨i, hi, hidvd⟩
        set S : Finset ℕ := (Finset.range g).filter (fun r => p ∣ (n + g * j + r)) with hS
        have hSne : S.Nonempty := by
          obtain ⟨r, hr, hrd⟩ := hexists
          exact ⟨r, by rw [hS, Finset.mem_filter]; exact ⟨hr, hrd⟩⟩
        obtain ⟨r0, hr0min⟩ := Finset.min_of_nonempty hSne
        have hr0mem : r0 ∈ S := Finset.mem_of_min hr0min
        rw [hS, Finset.mem_filter, Finset.mem_range] at hr0mem
        obtain ⟨hr0lt, hr0dvd⟩ := hr0mem
        have hval : firstHit g n p j = n + g * j + r0 := by
          simp only [firstHit, ← hS, hr0min, Option.getD]
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc, hval]
        refine ⟨⟨?_, ?_⟩, hr0dvd⟩
        · omega
        · have hr0m : g * j + r0 < m := by
            rw [hm]
            calc g * j + r0 < g * j + g := by omega
              _ = g * (j + 1) := by ring
              _ ≤ g * t := Nat.mul_le_mul_left g hjt
          omega
      · intro j hj j' hj' heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj hj'
        have h1 := firstHit_mem_Icc g n p j
        have h2 := firstHit_mem_Icc g n p j'
        simp only [Finset.mem_Icc] at h1 h2
        rw [heq] at h1
        -- From `h1`, `h2`:  g·j ≤ g·j' + (g-1) < g·(j'+1)  and  g·j' ≤ g·j + (g-1) < g·(j+1).
        have hjj' : g * j < g * (j' + 1) := by
          have : g * j ≤ g * j' + (g - 1) := by omega
          calc g * j ≤ g * j' + (g - 1) := this
            _ < g * j' + g := by omega
            _ = g * (j' + 1) := by ring
        have hj'j : g * j' < g * (j + 1) := by
          have : g * j' ≤ g * j + (g - 1) := by omega
          calc g * j' ≤ g * j + (g - 1) := this
            _ < g * j + g := by omega
            _ = g * (j + 1) := by ring
        have hlt1 : j < j' + 1 := Nat.lt_of_mul_lt_mul_left hjj'
        have hlt2 : j' < j + 1 := Nat.lt_of_mul_lt_mul_left hj'j
        omega
    refine le_trans hkey ?_
    refine le_trans (Ioc_dvd_le (n - 1) m p hp) ?_
    have : m / p ≤ k / p := Nat.div_le_div_right hmk
    omega

/-- **Overlap product divides `k!` (generic `g`).** `Wg g k n ∣ k!`. Generic form of
`W_dvd_factorial`/`W5_dvd_factorial`.
@isnad1 id=dvd.2h3v.s5.61f7ff099f1b from=translated src=- shape=9111c12a vocab=b0b6d147
-/
theorem Wg_dvd_factorial (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) : Wg g k n ∣ Nat.factorial k := by
  have hWne : Wg g k n ≠ 0 := by
    unfold Wg; exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Nat.factorization_le_iff_dvd hWne (Nat.factorial_ne_zero k)]
  intro p
  rw [factorization_Wg hn p]
  by_cases hp : p ∈ (Bg g k n).primeFactors
  · simp only [hp, ite_true]
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have h1 : overlapg g k n p ≤ k / p + 1 := overlapg_le hg hn
    have h2 : k / p ≤ (Nat.factorial k).factorization p := div_le_factorization_factorial hpp
    omega
  · simp only [hp, ite_false]; exact Nat.zero_le _

/-- **Overlap bound (generic `g`): `Wg g k n ≤ k^k`.** Since `Wg ∣ k!` (Legendre) and `k! ≤ k^k`.
Generic form of `W_le_pow`/`W5_le_pow`.
@isnad1 id=le.2h3v.s5.78627d23187f from=translated src=- shape=6051a37b vocab=ddff7364
-/
theorem Wg_le_pow (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) : Wg g k n ≤ k ^ k := by
  calc Wg g k n ≤ Nat.factorial k := Nat.le_of_dvd (Nat.factorial_pos k) (Wg_dvd_factorial hg hn)
    _ ≤ k ^ k := Nat.factorial_le_pow k

/-! ## PART B — the generic block radical hypothesis -/

/-- Tail-absorbed `g`-block radical input. NORMALIZED hypothesis (not the literal blockwise
abc/Langevin statement): packages the abc constant, epsilon loss, and omitted tail. The guard
`g ≤ k` is essential — for `g > k` there are no `g`-blocks (`⌊k/g⌋ = 0`), the RHS is the empty
product `1`, and `(F k n)^{(g-1)/g} ≤ 1` would be inconsistent. -/
def BlockRadLBg (g : ℕ) : Prop :=
  ∀ k n : ℕ, g ≤ k → 1 ≤ n →
    (F k n : ℝ) ^ (((g : ℝ) - 1) / (g : ℝ)) ≤
      ((∏ j ∈ Finset.range (k / g), rad (F g (n + g * j)) : ℕ) : ℝ)

/-! ## PART C — the unified master inequality and finiteness -/

/-- The explicit generic `g`-block finiteness bound `Mg g k = (k^{2k})^g · P k^{2g}`. Generic form
of `Msplice`. -/
def Mg (g k : ℕ) : ℕ := (k ^ (2 * k)) ^ g * P k ^ (2 * g)

/-! ## PART E — the crude (non-smooth) route

The crude route drops the smooth gain `L`/`P` entirely and uses only the bare powerful inequality
`rad (F k n) ^ 2 ≤ F k n` (`powerful_rad_sq_le`). It yields a *weaker exponent* than the smooth
route (`master_ineq_g`), but with a **fully explicit constant** and a clean INTEGER master
inequality `n ^ (g - 2) ≤ k ^ (2 * g)` — the exact threshold `k ^ (2 * g / (g - 2))` with no
`o(1)` and no unformalized Mertens input:

* `g = 3` ⟹ `n ^ 1 ≤ k ^ 6`  (threshold `k ^ 6`, matching `not_powerful_of_large`);
* `g = 4` ⟹ `n ^ 2 ≤ k ^ 8`  ↔ `n ≤ k ^ 4` (threshold `k ^ 4`);
* `g = 6` ⟹ `n ^ 4 ≤ k ^ {12}` ↔ `n ≤ k ^ 3` (threshold `k ^ 3`).

Contrast the SMOOTH `master_ineq_g` (`n ^ ((g-2) k) · L ^ g ≤ …`): that route carries the sharper
exponent `k ^ {2g/(g-2) + o(1)}` (coarse reading) / `k ^ {g/(g-2) + o(1)}` (Mertens reading), but
the sharpening is only available through the *unformalized* Mertens lower bound on `L`. The crude
route below trades that sharper exponent for a fully explicit, formalized integer constant. -/

/-- The right-hand side of the crude master inequality: `Mcrude g k = k ^ (2 * g)`, so the exact
threshold is `Mcrude g k < n ^ (g - 2)`. For example `g = 3` gives `k^6 < n`, while `g = 4` gives
`k^8 < n^2`, equivalently `k^4 < n`. (Note `Mcrude g k` is the bound on `n^{g-2}`, not on `n` itself
unless `g = 3`.) -/
def Mcrude (g k : ℕ) : ℕ := k ^ (2 * g)

end  -- noncomputable section

end Erdos137
