import Tengoku.Jsp000290Lean.Jsp290.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The binary and Fibonacci constructions for the positive half of JSP290.
These proofs are written independently from the elementary arguments in
Geneson, arXiv:2609.25107v1, Section 3, which credits Brown and Graham.
No code from the earlier strong-completeness submission is copied here.
-/

namespace Jsp290

open Finset

def binarySequence (i : ℕ) : ℤ := 2 ^ i
def fibonacciSequence (i : ℕ) : ℤ := Nat.fib (i + 1)
def erasedSequence (a : Sequence) (D : Finset ℕ) (i : ℕ) : ℤ :=
  if i ∈ D then 0 else a i

/--
@isnad1 id=prefixre.4h3v.s6.ab7e2ea69487 from=translated src=- shape=cf1d2f42 vocab=9ebea1e7
-/
theorem brown_prefix (a : Sequence) (hpos : ∀ i, 0 ≤ a i)
    (hstep : ∀ i, a i ≤ PrefixSum a i + 1) :
    ∀ N x, 0 ≤ x → x ≤ PrefixSum a N → PrefixRep a N x := by
  intro N
  induction N with
  | zero =>
    intro x hx hxN
    have : x = 0 := by simpa [PrefixSum] using le_antisymm hxN hx
    subst x
    exact prefixRep_zero a 0
  | succ N ih =>
    intro x hx hxN
    rw [prefixSum_succ] at hxN
    by_cases h : x ≤ PrefixSum a N
    · exact (ih x hx h).mono (Nat.le_succ N)
    · have hxlo : 0 ≤ x - a N := by have := hstep N; omega
      have hxhi : x - a N ≤ PrefixSum a N := by omega
      have hh := (ih (x - a N) hxlo hxhi).add_term (le_refl N) (Nat.lt_succ_self N)
      simpa using hh

/--
@isnad1 id=le.1h2v.s4.24eff9a2ede5 from=translated src=- shape=96e971da vocab=423bd5e8
-/
theorem prefixSum_ge_index_of_one_le (a : Sequence) (hpos : ∀ i, 1 ≤ a i) (N : ℕ) :
    (N : ℤ) ≤ PrefixSum a N := by
  induction N with
  | zero => simp [PrefixSum]
  | succ N ih =>
    rw [prefixSum_succ]
    have := hpos N
    push_cast
    omega

/--
@isnad1 id=le.1h3v.s5.634349111446 from=translated src=- shape=6ef97163 vocab=8f014ef8
-/
theorem erased_nonneg {a : Sequence} (ha : ∀ i, 0 ≤ a i) (D : Finset ℕ) :
    ∀ i, 0 ≤ erasedSequence a D i := by
  intro i
  simp only [erasedSequence]
  split_ifs <;> simp_all

/--
@isnad1 id=represen.1h3v.s4.316fa6e23cdf from=translated src=- shape=156c2870 vocab=68b63885
-/
theorem erased_represents {a : Sequence} {D : Finset ℕ} {x : ℤ}
    (h : Represents (erasedSequence a D) x) : RepresentsAfter a D x := by
  classical
  obtain ⟨s, hs⟩ := h
  refine ⟨s.filter (fun i => i ∉ D), ?_, ?_⟩
  · exact disjoint_left.mpr (fun i hi hD => (mem_filter.mp hi).2 hD)
  · rw [sum_filter]
    convert hs using 1
    apply sum_congr rfl
    intro i hi
    by_cases hD : i ∈ D <;> simp [erasedSequence, hD]

/--
@isnad1 id=eq.0h3v.s5.ab051fa06640 from=translated src=- shape=82aed2ac vocab=7ceff7b5
-/
theorem erased_singleton_prefix (a : Sequence) (j N : ℕ) :
    PrefixSum (erasedSequence a {j}) N =
      PrefixSum a N - if j < N then a j else 0 := by
  induction N with
  | zero => simp [PrefixSum]
  | succ N ih =>
    rw [prefixSum_succ, prefixSum_succ, ih]
    by_cases hj : j = N
    · subst j
      simp [erasedSequence]
    · by_cases hjN : j < N
      · have hjN' : j < N + 1 := by omega
        simp [erasedSequence, hj, Ne.symm hj, hjN, hjN', sub_add_eq_add_sub]
      · have hjN' : ¬j < N + 1 := by omega
        simp [erasedSequence, hj, Ne.symm hj, hjN, hjN']

/--
@isnad1 id=le.3h3v.s6.14aa9254e32d from=translated src=- shape=2ea1b874 vocab=717be288
-/
theorem subset_range_of_sum_lt {a : Sequence} (hpos : ∀ i, 0 ≤ a i)
    (hmono : Monotone a) {s : Finset ℕ} {N : ℕ}
    (hs : ∑ i ∈ s, a i < a N) : s ⊆ range N := by
  intro i hi
  apply mem_range.mpr
  by_contra hn
  have hNi : N ≤ i := by omega
  have := single_le_sum (fun j (_ : j ∈ s) => hpos j) hi
  have := hmono hNi
  omega

/--
@isnad1 id=le.4h4v.s6.1d977e76fe1e from=translated src=- shape=6bc8742a vocab=053fbe2b
-/
theorem sum_add_omitted_le_prefix {a : Sequence} (hpos : ∀ i, 0 ≤ a i)
    {s : Finset ℕ} {N i : ℕ} (hs : s ⊆ range N) (hiN : i < N) (his : i ∉ s) :
    (∑ j ∈ s, a j) + a i ≤ PrefixSum a N := by
  have hsub : insert i s ⊆ range N := insert_subset (mem_range.mpr hiN) hs
  have h := sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hpos j)
  simpa [sum_insert his, PrefixSum, add_comm] using h

/--
@isnad1 id=le.0h1v.s3.191b27a52415 from=translated src=- shape=b9369acb vocab=efc6fdb7
-/
theorem binary_pos (i : ℕ) : 1 ≤ binarySequence i := by
  exact one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2)

/--
@isnad1 id=monotone.0h0v.s4.cecf2b151a4a from=translated src=- shape=54c8eceb vocab=9e88aa70
-/
theorem binary_mono : Monotone binarySequence := by
  intro i j hij
  exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hij

/--
@isnad1 id=eq.0h1v.s4.f89fa782e49f from=translated src=- shape=595a7b15 vocab=09a47e52
-/
theorem binary_prefix (N : ℕ) : PrefixSum binarySequence N = binarySequence N - 1 := by
  induction N with
  | zero => simp [PrefixSum, binarySequence]
  | succ N ih =>
    rw [prefixSum_succ, ih]
    simp [binarySequence, pow_succ]
    ring

/--
@isnad1 id=le.0h2v.s4.0516a07cac96 from=translated src=- shape=8dfd58a8 vocab=10f9cd39
-/
theorem binary_growth (j k : ℕ) : binarySequence j + k ≤ binarySequence (j + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp := binary_pos (j + k)
    have he : binarySequence (j + (k + 1)) = 2 * binarySequence (j + k) := by
      change (2 : ℤ) ^ (j + (k + 1)) = 2 * 2 ^ (j + k)
      rw [show j + (k + 1) = (j + k) + 1 by omega, pow_succ]
      ring
    rw [he]
    push_cast
    omega

/--
@isnad1 id=complete.0h0v.s1.00f0081ddc4e from=translated src=- shape=49959d42 vocab=2756d681
-/
theorem binary_complete : Complete binarySequence := by
  refine ⟨0, fun x hx => ?_⟩
  have hsum : x ≤ PrefixSum binarySequence x.toNat := by
    have h := prefixSum_ge_index_of_one_le binarySequence binary_pos x.toNat
    omega
  exact (brown_prefix binarySequence (fun i => le_trans (by norm_num) (binary_pos i))
    (fun i => by rw [binary_prefix]; omega) x.toNat x hx hsum).represents

/--
@isnad1 id=not.0h1v.s3.35f7307cef84 from=translated src=- shape=edd686c1 vocab=df4ecf2f
-/
theorem binary_delete_one (j : ℕ) : ¬ CompleteAfter binarySequence {j} := by
  rw [not_completeAfter_iff]
  intro T
  let N := j + (T.toNat + 1)
  let x := binarySequence N - binarySequence j
  have hlarge : T ≤ x := by
    have h := binary_growth j (T.toNat + 1)
    dsimp [x, N]
    push_cast at h
    omega
  refine ⟨x, hlarge, ?_⟩
  rintro ⟨s, hsD, hsx⟩
  have hj : j ∉ s := by simpa [disjoint_singleton_right] using hsD
  have hxN : x < binarySequence N := by
    dsimp [x]
    have := binary_pos j
    omega
  have hsub := subset_range_of_sum_lt
    (fun i => le_trans (by norm_num) (binary_pos i)) binary_mono
      (show ∑ i ∈ s, binarySequence i < binarySequence N by rw [hsx]; exact hxN)
  have hsum := sum_add_omitted_le_prefix
    (fun i => le_trans (by norm_num) (binary_pos i)) hsub (by dsimp [N]; omega) hj
  rw [hsx, binary_prefix] at hsum
  dsimp [x] at hsum
  omega

/--
@isnad1 id=le.0h1v.s3.12c84b29ff8a from=translated src=- shape=b9369acb vocab=e7f6946c
-/
theorem fibonacci_pos (i : ℕ) : 1 ≤ fibonacciSequence i := by
  have h : 0 < Nat.fib (i + 1) := Nat.fib_pos.mpr (by omega)
  dsimp [fibonacciSequence]
  omega

/--
@isnad1 id=monotone.0h0v.s4.7be5245ca5a2 from=translated src=- shape=54c8eceb vocab=e611ef2e
-/
theorem fibonacci_mono : Monotone fibonacciSequence := by
  intro i j hij
  dsimp [fibonacciSequence]
  exact_mod_cast Nat.fib_mono (Nat.add_le_add_right hij 1)

/--
@isnad1 id=eq.0h1v.s5.46b501325f4f from=translated src=- shape=58e287f5 vocab=ff8b1d4e
-/
theorem fibonacci_recurrence (i : ℕ) :
    fibonacciSequence (i + 2) = fibonacciSequence i + fibonacciSequence (i + 1) := by
  have h := Nat.fib_add_two (n := i + 1)
  dsimp [fibonacciSequence]
  exact_mod_cast h

/--
@isnad1 id=eq.0h1v.s5.6450ab1e27ee from=translated src=- shape=ebfd840f vocab=2c295848
-/
theorem fibonacci_prefix (N : ℕ) :
    PrefixSum fibonacciSequence N = fibonacciSequence (N + 1) - 1 := by
  induction N with
  | zero => simp [PrefixSum, fibonacciSequence]
  | succ N ih =>
    rw [prefixSum_succ, ih]
    have h := fibonacci_recurrence N
    norm_num only [Nat.add_assoc] at *
    omega

/--
@isnad1 id=eq.0h1v.s5.83407bb3232a from=translated src=- shape=ea58a925 vocab=47b8558c
-/
theorem fibonacci_prefix_two (N : ℕ) :
    PrefixSum fibonacciSequence (N + 2) =
      PrefixSum fibonacciSequence N + fibonacciSequence (N + 2) := by
  rw [show N + 2 = (N + 1) + 1 by omega, prefixSum_succ, prefixSum_succ]
  have h := fibonacci_recurrence N
  norm_num only [Nat.add_assoc] at *
  omega

/--
@isnad1 id=complete.0h1v.s3.8757aaf251b0 from=translated src=- shape=4e86ff51 vocab=07eba256
-/
theorem fibonacci_delete_one (j : ℕ) : CompleteAfter fibonacciSequence {j} := by
  let a := erasedSequence fibonacciSequence {j}
  have hpos : ∀ i, 0 ≤ a i :=
    erased_nonneg (fun i => le_trans (by norm_num) (fibonacci_pos i)) _
  have hstep : ∀ i, a i ≤ PrefixSum a i + 1 := by
    intro i
    by_cases hij : i = j
    · subst i
      have haj : a j = 0 := by simp [a, erasedSequence]
      rw [haj]
      have := prefixSum_nonneg hpos j
      omega
    · rw [show a i = fibonacciSequence i by simp [a, erasedSequence, hij]]
      rw [show PrefixSum a i = _ from erased_singleton_prefix fibonacciSequence j i,
        fibonacci_prefix]
      by_cases hji : j < i
      · rw [ite_eq_left hji]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        have hmono := fibonacci_mono (show j ≤ k by omega)
        have hrec := fibonacci_recurrence k
        norm_num only [Nat.succ_eq_add_one, Nat.add_assoc] at *
        omega
      · rw [ite_eq_right hji]
        have := fibonacci_mono (Nat.le_succ i)
        simp only [Nat.succ_eq_add_one] at *
        omega
  refine ⟨0, fun x hx => ?_⟩
  let N := (x + fibonacciSequence j).toNat
  have hxsum : x ≤ PrefixSum a N := by
    rw [show PrefixSum a N = _ from erased_singleton_prefix fibonacciSequence j N]
    have h := prefixSum_ge_index_of_one_le fibonacciSequence fibonacci_pos N
    have hp := fibonacci_pos j
    have hN : x + fibonacciSequence j ≤ (N : ℤ) := by dsimp [N]; omega
    split_ifs <;> omega
  exact erased_represents (brown_prefix a hpos hstep N x hx hxsum).represents

/--
@isnad1 id=not.1h3v.s5.b361c0e3ecc2 from=translated src=- shape=0d4bd8a2 vocab=7e59cafe
-/
theorem fibonacci_pair_missing (i j : ℕ) (hij : i < j) (t : ℕ) :
    ¬ RepresentsAfter fibonacciSequence {i, j} (PrefixSum fibonacciSequence (j + 2 * t)) := by
  have hp : ∀ k, 0 ≤ fibonacciSequence k :=
    fun k => le_trans (by norm_num) (fibonacci_pos k)
  induction t with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    rintro ⟨s, hD, hsum⟩
    have hj : j ∉ s := fun hj => disjoint_left.mp hD hj (by simp)
    have hi : i ∉ s := fun hi => disjoint_left.mp hD hi (by simp)
    have hlt : ∑ k ∈ s, fibonacciSequence k < fibonacciSequence (j + 1) := by
      rw [hsum, fibonacci_prefix]
      omega
    have hsub := subset_range_of_sum_lt hp fibonacci_mono hlt
    have hsub' : s ⊆ range j := by
      intro k hk
      have hkr := mem_range.mp (hsub hk)
      have hkj : k ≠ j := fun h => hj (h ▸ hk)
      exact mem_range.mpr (by omega)
    have h := sum_add_omitted_le_prefix hp hsub' hij hi
    rw [hsum] at h
    have := fibonacci_pos i
    omega
  | succ t ih =>
    let k := j + 2 * t
    have htarget : j + 2 * (t + 1) = k + 2 := by dsimp [k]; omega
    rw [htarget]
    rintro ⟨s, hD, hsum⟩
    have hi : i ∉ s := fun hi => disjoint_left.mp hD hi (by simp)
    have hlt : ∑ r ∈ s, fibonacciSequence r < fibonacciSequence (k + 2 + 1) := by
      rw [hsum, fibonacci_prefix]
      omega
    have hsub := subset_range_of_sum_lt hp fibonacci_mono hlt
    have hk : k + 2 ∈ s := by
      by_contra hh
      have hsub' : s ⊆ range (k + 2) := by
        intro r hr
        have hrr := mem_range.mp (hsub hr)
        have hrk : r ≠ k + 2 := fun h => hh (h ▸ hr)
        exact mem_range.mpr (by omega)
      have h := sum_add_omitted_le_prefix hp hsub' (by dsimp [k]; omega) hi
      rw [hsum] at h
      have := fibonacci_pos i
      omega
    apply ih
    refine ⟨s.erase (k + 2), hD.mono_left (erase_subset _ _), ?_⟩
    have he := sum_erase_add s fibonacciSequence hk
    rw [hsum, fibonacci_prefix_two] at he
    change ∑ r ∈ s.erase (k + 2), fibonacciSequence r = PrefixSum fibonacciSequence k
    omega

/--
@isnad1 id=not.1h2v.s4.384941eff963 from=translated src=- shape=7f3ef33d vocab=7f1ccdba
-/
theorem fibonacci_delete_pair (i j : ℕ) (hij : i < j) :
    ¬ CompleteAfter fibonacciSequence {i, j} := by
  rw [not_completeAfter_iff]
  intro T
  refine ⟨PrefixSum fibonacciSequence (j + 2 * T.toNat), ?_,
    fibonacci_pair_missing i j hij T.toNat⟩
  have h := prefixSum_ge_index_of_one_le fibonacciSequence fibonacci_pos (j + 2 * T.toNat)
  omega

/--
@isnad1 id=admissib.1h1v.s4.c17d77b60d44 from=translated src=- shape=2dea5467 vocab=c429d0cf
-/
theorem admissible_zero (n : ℕ) (hn : 0 < n) : Admissible 0 n := by
  refine ⟨binarySequence, binary_mono, ?_, ?_⟩
  · intro D hD
    have : D = ∅ := card_eq_zero.mp hD
    subst D
    exact completeAfter_empty.mpr binary_complete
  · intro D hD hC
    obtain ⟨j, hj⟩ := card_pos.mp (show 0 < D.card by omega)
    exact binary_delete_one j (hC.mono (singleton_subset_iff.mpr hj))

/--
@isnad1 id=admissib.1h1v.s4.2a3021e3a8fe from=translated src=- shape=2dea5467 vocab=c429d0cf
-/
theorem admissible_one (n : ℕ) (hn : 1 < n) : Admissible 1 n := by
  refine ⟨fibonacciSequence, fibonacci_mono, ?_, ?_⟩
  · intro D hD
    obtain ⟨j, rfl⟩ := card_eq_one.mp hD
    exact fibonacci_delete_one j
  · intro D hD hC
    obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp (show 1 < D.card by omega)
    have hpair : {i, j} ⊆ D := insert_subset hi (singleton_subset_iff.mpr hj)
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact fibonacci_delete_pair i j hij (hC.mono hpair)
    · have hpair' : {j, i} ⊆ D := insert_subset hj (singleton_subset_iff.mpr hi)
      exact fibonacci_delete_pair j i hji (hC.mono hpair')

/--
@isnad1 id=admissib.2h2v.s4.6a45f2107bb6 from=translated src=- shape=2238ea8a vocab=0ad91062
-/
theorem admissible_of_le_one (m n : ℕ) (hmn : m < n) (hm : m ≤ 1) :
    Admissible m n := by
  have : m = 0 ∨ m = 1 := by omega
  rcases this with rfl | rfl
  · exact admissible_zero n hmn
  · exact admissible_one n hmn

end Jsp290
