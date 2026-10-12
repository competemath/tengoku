/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Markus Rydh
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2025, Problem 4

A proper divisor of a positive integer N is a positive divisor of N other
than N itself. The infinite sequence a₁, a₂, ... consists of positive integers,
each of which has at least three proper divisors. For each n ⩾ 1, the integer
aₙ₊₁ is the sum of the three largest proper divisors of aₙ. Determine all
possible values of a₁.
-/

namespace Imo2025P4

open Finset

abbrev answer : Set ℕ := { x | ∃ e l : ℕ, x = 12^e * 6 * l ∧ l.Coprime 10 }

variable {a₁ : ℕ} {a : ℕ → ℕ} {x d d₁ d₂ d₃ : ℕ}

def ψ (n : ℕ) : ℕ := (((Nat.properDivisors n).sort (· ≤ ·)).reverse.take 3).sum

def S : Set ℕ := {x | 3 ≤ #(Nat.properDivisors x)}

def ValidSequence (a : ℕ → ℕ) := ∀ i, 0 < a i ∧ a i ∈ S ∧ a (i + 1) = ψ (a i)

def smallDivisors (n : ℕ) : List ℕ := (n.divisors.erase 1).sort (· ≤ ·)

def threeSmallestDivisors (n : ℕ) : List ℕ := (smallDivisors n).take 3

/--
@isnad1 id=eq.0h1v.s4.149376c9497f from=translated src=- shape=87d641ae vocab=b43d5dd7
-/
@[simp] lemma take_smallDivisors_eq_threeSmallestDivisors {n : ℕ} :
    List.take 3 (smallDivisors n) = threeSmallestDivisors n := rfl

/--
@isnad1 id=iff.0h2v.s5.dbc898b3fc7d from=translated src=- shape=c3669d95 vocab=f906ec50
-/
@[simp] lemma mem_divisors_erase_one {d n : ℕ} :
    d ∈ n.divisors.erase 1 ↔ d ≠ 1 ∧ d ∣ n ∧ n ≠ 0 := by
  rw [mem_erase, Nat.mem_divisors]

/--
@isnad1 id=dvd.1h2v.s4.2cc3c60875aa from=translated src=- shape=f14f50e9 vocab=f906ec50
-/
lemma dvd_of_mem_divisors_erase_one {d n : ℕ} (h : d ∈ n.divisors.erase 1) : d ∣ n :=
  (mem_divisors_erase_one.mp h).2.1

/--
@isnad1 id=lt.1h2v.s5.8a0ee17081ef from=translated src=- shape=7a2b0d43 vocab=194b429b
-/
lemma pos_of_mem_divisors_erase_one {d n : ℕ} (h : d ∈ n.divisors.erase 1) : 0 < d :=
  Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr (mem_divisors_erase_one.mp h).2)

/--
@isnad1 id=mem.3h2v.s5.5e7bd9b92d51 from=translated src=- shape=1d452a4d vocab=f906ec50
-/
lemma mem_divisors_erase_one_of_dvd_ne_one {d n : ℕ}
    (hd : d ∣ n) (hn : n ≠ 0) (hd1 : d ≠ 1) : d ∈ n.divisors.erase 1 :=
  mem_divisors_erase_one.mpr ⟨hd1, hd, hn⟩

/--
@isnad1 id=eq.1h1v.s5.5d52636b4ea4 from=translated src=- shape=acd097f6 vocab=198ae5b5
-/
lemma reverse_properDivisors_eq_div_divisors_erase_one {n : ℕ} (hn : n ≠ 0) :
    ((Nat.properDivisors n).sort (· ≤ ·)).reverse =
    (smallDivisors n).map (fun d => n / d) := by
  rw [List.reverse_eq_iff]
  apply List.SortedLT.eq_of_mem_iff
  · exact (sortedLT_sort (Nat.properDivisors n))
  · rw [List.sortedLT_iff_pairwise, List.pairwise_reverse, List.pairwise_map]
    apply List.Pairwise.imp ?_ (List.Pairwise.and_mem.mp (sortedLT_sort ((Nat.divisors n).erase 1)).pairwise)
    intro a b h
    rcases h with ⟨ha, hb, hab⟩
    rwa [Nat.div_lt_div_left hn]
    · exact dvd_of_mem_divisors_erase_one ((mem_sort (r := (· ≤ ·))).mp hb)
    · exact dvd_of_mem_divisors_erase_one ((mem_sort (r := (· ≤ ·))).mp ha)
  · intro x
    simp only [List.mem_reverse, mem_sort, List.mem_map]
    constructor
    · intro hx
      refine ⟨n / x, ?_, Nat.div_div_self (Nat.mem_properDivisors.mp hx).1 hn⟩
      simp [smallDivisors, mem_erase, Nat.mem_divisors]
      refine ⟨?_, ⟨Nat.div_dvd_of_dvd (Nat.mem_properDivisors.mp hx).1, hn⟩⟩
      exact ne_of_gt (Nat.one_lt_div_of_mem_properDivisors hx)
    · rintro ⟨d, hd, rfl⟩
      simp [smallDivisors] at hd
      rw [Nat.mem_properDivisors]
      refine ⟨Nat.div_dvd_of_dvd hd.2.1, Nat.div_lt_self (Nat.pos_of_ne_zero hn) ?_⟩
      have hdpos : 0 < d := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr hd.2)
      lia

/--
@isnad1 id=eq.2h4v.s6.f6b1d68f51b5 from=translated src=- shape=20445643 vocab=008b3273
-/
lemma psi_eq_of_threeSmallestDivisors_eq (hx0 : x ≠ 0)
    (hdiv : threeSmallestDivisors x = [d₁, d₂, d₃]) : ψ x = x / d₁ + x / d₂ + x / d₃ := by
  rw [ψ, reverse_properDivisors_eq_div_divisors_erase_one hx0, ← List.map_take,
    take_smallDivisors_eq_threeSmallestDivisors, hdiv]
  simp [add_assoc]

/--
@isnad1 id=mem.1h1v.s4.55918bdb1620 from=translated src=- shape=92d89710 vocab=58e17d98
-/
lemma answer_mem_S : a₁ ∈ answer → a₁ ∈ S := by
  intro ha₁
  obtain ⟨e, l, rfl, hl⟩ := ha₁
  have hlpos : 0 < l := by grind only
  have hge6 : 6 ≤ 12 ^ e * 6 * l := by
    nlinarith [Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 12) e), Nat.succ_le_of_lt hlpos]
  have h₁ : 1 ∈ Nat.properDivisors (12 ^ e * 6 * l) := by grind only [Nat.one_mem_properDivisors_iff_one_lt]
  have h₂ : 2 ∈ Nat.properDivisors (12 ^ e * 6 * l) := by grind only [Nat.mem_properDivisors]
  have h₃ : 3 ∈ Nat.properDivisors (12 ^ e * 6 * l) := by grind only [Nat.mem_properDivisors]
  have hsubset : ({1, 2, 3} : Finset ℕ) ⊆ Nat.properDivisors (12 ^ e * 6 * l) := by
    intro x hx
    simp only [mem_insert, Finset.mem_singleton] at hx
    grind only
  exact card_le_card hsubset

/--
@isnad1 id=lt.1h1v.s4.727b3cecc694 from=translated src=- shape=931ea0f4 vocab=49a9bb26
-/
lemma pos_of_mem_S {x : ℕ}: x ∈ S → 0 < x := by
  intro hx
  by_contra hzero
  simp at hzero
  have hcard : #x.properDivisors = 0 := by rw [hzero, Nat.properDivisors_zero, card_empty]
  have hcard' : 3 ≤ #x.properDivisors := hx
  lia

/--
@isnad1 id=lt.1h1v.s4.de3f4c4aa3f4 from=translated src=- shape=931ea0f4 vocab=ea55a8c3
-/
lemma answer_pos : a₁ ∈ answer → 0 < a₁ := fun ha ↦ pos_of_mem_S (answer_mem_S ha)

/--
@isnad1 id=eq.6h4v.s7.ff75e1fb8ba9 from=translated src=- shape=b1cd9032 vocab=a1e2f64c
-/
lemma sort_take_three_eq_of_first_three {s : Finset ℕ} {a b c : ℕ}
    (ha : a ∈ s) (hb : b ∈ s.erase a) (hc : c ∈ (s.erase a).erase b)
    (ha_le : ∀ x ∈ s, a ≤ x) (hb_le : ∀ x ∈ s.erase a, b ≤ x) (hc_le : ∀ x ∈ (s.erase a).erase b, c ≤ x) :
    (s.sort (· ≤ ·)).take 3 = [a, b, c] := by
  grind [insert_erase ha, insert_erase hb, insert_erase hc, sort_insert]

/--
@isnad1 id=eq.5h1v.s6.a0e2dd400628 from=translated src=- shape=f84950eb vocab=97ed7cfc
-/
lemma divisors_erase_one_sort_take_three_eq_two_three_six {n : ℕ}
    (hn : n ≠ 0) (h2 : 2 ∣ n) (h3 : 3 ∣ n) (h4 : ¬ 4 ∣ n) (h5 : ¬ 5 ∣ n) :
    threeSmallestDivisors n = [2, 3, 6] := by
  apply sort_take_three_eq_of_first_three (by grind) (by grind) (by grind)
  all_goals
    intro x hx
    simp [mem_erase, Nat.mem_divisors] at hx
    have hxpos : 0 < x := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr (by aesop))
    try lia
  by_contra hlt
  interval_cases x <;> simp_all

/--
@isnad1 id=eq.4h1v.s6.7963a43aa4ef from=translated src=- shape=d3bd26ed vocab=97ed7cfc
-/
lemma divisors_erase_one_sort_take_three_eq_two_three_four {n : ℕ}
    (hn : n ≠ 0) (h2 : 2 ∣ n) (h3 : 3 ∣ n) (h4 : 4 ∣ n) : threeSmallestDivisors n = [2, 3, 4] := by
  apply sort_take_three_eq_of_first_three (by grind) (by grind) (by grind)
  all_goals
  intro x hx
  simp [mem_erase, Nat.mem_divisors] at hx
  have hxpos : 0 < x := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr (by aesop))
  lia

/--
@isnad1 id=eq.5h1v.s6.0209ccdaf1ff from=translated src=- shape=1329d457 vocab=97ed7cfc
-/
lemma divisors_erase_one_sort_take_three_eq_two_three_five {n : ℕ}
    (hn : n ≠ 0) (h2 : 2 ∣ n) (h3 : 3 ∣ n) (h4 : ¬ 4 ∣ n) (h5 : 5 ∣ n) :
    threeSmallestDivisors n = [2, 3, 5] := by
  apply sort_take_three_eq_of_first_three (by grind) (by grind) (by grind)
  all_goals
    intro x hx
    simp [mem_erase, Nat.mem_divisors] at hx
    have hxpos : 0 < x := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr (by aesop))
    try lia
  by_contra hlt
  interval_cases x <;> simp_all

/--
@isnad1 id=mem.1h1v.s4.0c873a19e27e from=translated src=- shape=93b7e764 vocab=cc77562b
-/
lemma psi_answer_mem_S' {aᵢ : ℕ} : aᵢ ∈ answer → ψ aᵢ ∈ answer := by
  intro haᵢ
  have haᵢ0 : aᵢ ≠ 0 := by grind only [answer_pos haᵢ]
  obtain ⟨e, l, haᵢ, hl⟩ := haᵢ
  by_cases hcase : e = 0
  · refine ⟨0, l, ?_, hl⟩
    have h2 : ¬ 2 ∣ l := Nat.prime_two.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left (by lia) hl.symm)
    have h5 : ¬ 5 ∣ l := Nat.prime_five.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left (by lia) hl.symm)
    have h236 : threeSmallestDivisors (6 * l) = [2,3,6] :=
      divisors_erase_one_sort_take_three_eq_two_three_six (by simpa [haᵢ, hcase] using haᵢ0)
        (by lia) (by lia) (by lia) (by lia)
    rw [haᵢ, hcase]
    simp
    rw [psi_eq_of_threeSmallestDivisors_eq (by simpa [haᵢ, hcase] using haᵢ0) h236]
    grind
  · refine ⟨e-1, 13*l, ?_, ?_⟩
    · have h_e_pos : 0 < e := Nat.zero_lt_of_ne_zero hcase
      have h_four_dvd : 4 ∣ aᵢ := by grind
      have h234 : threeSmallestDivisors (12 ^ e * 6 * l) = [2,3,4] := by
        apply divisors_erase_one_sort_take_three_eq_two_three_four <;> lia
      have : 12 ^ e / 12 * 6 * (13 * l) = 12 ^ e * 6 * l * 13 / 12 := by
        have hdvd : 12 ∣ 12 ^ e := dvd_pow_self 12 hcase
        calc
          12 ^ e / 12 * 6 * (13 * l) = (6 * l * 13) * (12 ^ e / 12) := by ring_nf
          _ = (6 * l * 13) * 12 ^ e / 12 := by rw [Nat.mul_div_assoc _ hdvd]
          _ = 12 ^ e * 6 * l * 13 / 12 := by ring_nf
      rw [haᵢ, psi_eq_of_threeSmallestDivisors_eq (by simpa [haᵢ] using haᵢ0) h234]
      rw [Nat.pow_sub_one (by positivity) hcase, this]
      grind
    · grind [Nat.coprime_mul_iff_left]

/--
@isnad1 id=mem.1h2v.s4.92f9edbafd44 from=translated src=- shape=62eb807f vocab=fe70ee45
-/
lemma psi_answer_mem_S {i : ℕ} : a₁ ∈ answer → ψ^[i] a₁ ∈ answer := by
  intro h
  induction i with
  | zero => rwa [Function.iterate_zero ψ, id_eq]
  | succ j hj => simpa [Function.iterate_succ_apply' ψ j a₁] using psi_answer_mem_S' hj

/--
@isnad1 id=ex.1h1v.s5.53cee69dd556 from=translated src=- shape=16910c0d vocab=aab13f7d
-/
lemma answer_sufficient : a₁ ∈ answer → ∃ a : ℕ → ℕ, a 0 = a₁ ∧ ValidSequence a := by
  intro ha₁
  let a : ℕ → ℕ := fun i ↦ Nat.iterate ψ i a₁
  refine ⟨a, rfl, ?_⟩
  · intro i
    have : a i ∈ answer := psi_answer_mem_S ha₁
    exact ⟨answer_pos this, answer_mem_S this, Function.iterate_succ_apply' ψ i a₁⟩

/--
@isnad1 id=iff.1h1v.s5.4035c52a772d from=translated src=- shape=dd55b27b vocab=7b279025
-/
lemma odd_sum_iff_length_of_forall_odd {S : List ℕ} (hodd : ∀ x ∈ S, Odd x) : Odd S.sum ↔ Odd S.length := by
  induction S with
  | nil => simp
  | cons a S ih =>
      have hS : ∀ x ∈ S, Odd x := fun x hx ↦ hodd x (by simp [hx])
      rw [List.sum_cons, List.length_cons, Nat.odd_add, Nat.odd_add, ← Nat.not_odd_iff_even, ih hS]
      simp [hodd a (by simp)]

/--
@isnad1 id=odd.3h2v.s5.973d23ba4ceb from=translated src=- shape=10510459 vocab=74604fbe
-/
lemma odd_of_sum_odd {S : List ℕ} {n : ℕ} (hn : Odd n) (hlen : n ≤ S.length)
    (hodd : ∀ x ∈ S, Odd x) : Odd (S.take n).sum := by
  have hlen' : Odd (S.take n).length := by simpa [List.length_take, min_eq_left hlen] using hn
  exact (odd_sum_iff_length_of_forall_odd (fun x hx ↦ hodd x (List.mem_of_mem_take hx))).mpr hlen'

/--
@isnad1 id=dvd.2h1v.s4.2edd5eb2b803 from=translated src=- shape=cab61145 vocab=b05ace2b
-/
lemma two_dvd_of_two_dvd_psi {x : ℕ} : x ∈ S → 2 ∣ ψ x → 2 ∣ x := by
  intro hx h2psi
  by_contra hodd
  have : ∀ k ∈ x.properDivisors, Odd k := fun k hk ↦ Odd.of_dvd_nat
      (Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd]))
      (Nat.mem_properDivisors.mp hk).1
  simp [ψ] at h2psi
  replace : ∀ k ∈ (x.properDivisors.sort (· ≤ ·)).reverse, Odd k :=
    fun k hk ↦ this k ((mem_sort (· ≤ ·)).mp (List.mem_reverse.mp hk))
  have hlen : 3 ≤ ((x.properDivisors.sort (· ≤ ·)).reverse).length := by
    rwa [List.length_reverse, length_sort]
  have := odd_of_sum_odd (show Odd 3 by decide) hlen this
  set s := (List.take 3 (x.properDivisors.sort (· ≤ ·)).reverse).sum
  grind only [= Nat.odd_iff]

/--
@isnad1 id=le.5h4v.s7.8ec41c8b63aa from=translated src=- shape=064c7a61 vocab=4f659ef3
-/
lemma psi_le_of_three_smallest_ge {b₁ b₂ b₃ : ℕ} (hx : x ≠ 0)
    (hb₁0 : b₁ ≠ 0) (hb₂0 : b₂ ≠ 0) (hb₃0 : b₃ ≠ 0)
    (hge : ∃ d₁ d₂ d₃, threeSmallestDivisors x = [d₁, d₂, d₃] ∧
     b₁ ≤ d₁ ∧ b₂ ≤ d₂ ∧ b₃ ≤ d₃) : ψ x ≤ x / b₁ + x / b₂ + x / b₃ := by
  obtain ⟨d₁, d₂, d₃, htake, hb₁, hb₂, hb₃⟩ := hge
  rw [psi_eq_of_threeSmallestDivisors_eq hx htake]
  have h₁ : x / d₁ ≤ x / b₁ := by gcongr
  have h₂ : x / d₂ ≤ x / b₂ := by gcongr
  have h₃ : x / d₃ ≤ x / b₃ := by gcongr
  lia

/--
@isnad1 id=and.1h1v.s7.59d65673ac35 from=translated src=- shape=aae56d88 vocab=aa94eabc
-/
lemma min_divisors_of_mem_S {x : ℕ} : x ∈ S → (x ≠ 0) ∧ ∃ d₁ d₂ d₃, threeSmallestDivisors x = [d₁, d₂, d₃] ∧
    (d₁ ∈ (x.divisors.erase 1)) ∧ (d₂ ∈ (x.divisors.erase 1)) ∧ (d₃ ∈ (x.divisors.erase 1)) ∧
    (2 ≤ d₁) ∧ (d₁ < d₂) ∧ (d₂ < d₃) := by
  intro hx
  have hx0 : x ≠ 0 := Nat.ne_zero_of_lt (pos_of_mem_S hx)
  have hcard_eq : #x.properDivisors = #(x.divisors.erase 1) := by
    have := congrArg List.length (reverse_properDivisors_eq_div_divisors_erase_one hx0)
    simpa [List.length_reverse, smallDivisors, length_sort] using this
  have hcard : 3 ≤ #(x.divisors.erase 1) := by rwa [← hcard_eq]
  let L := threeSmallestDivisors x
  have hlen : L.length = 3 := by
    simp [L, threeSmallestDivisors, smallDivisors, List.length_take, length_sort, min_eq_left hcard]
  obtain ⟨d₁, d₂, d₃, htake⟩ := List.length_eq_three.mp hlen
  have hsorted : [d₁, d₂, d₃].SortedLT := by
    rw [List.sortedLT_iff_isChain, ← htake]
    exact (sortedLT_sort (x.divisors.erase 1)).isChain.take 3
  have hpair := List.sortedLT_iff_pairwise.mp hsorted
  simp at hpair
  have hdmem : ∀ d ∈ [d₁, d₂, d₃], d ∈ x.divisors.erase 1 := by
    intro d hd
    apply (mem_sort (r := (· ≤ ·))).mp
    exact List.mem_of_mem_take (by simp [L, htake, hd] : d ∈ L)
  have hd₁mem : d₁ ∈ x.divisors.erase 1 := hdmem d₁ (by simp)
  have hd₁ge : 2 ≤ d₁ := by
    have hd₁pos : 0 < d₁ := pos_of_mem_divisors_erase_one hd₁mem
    have hd₁ne : d₁ ≠ 1 := (mem_divisors_erase_one.mp hd₁mem).1
    lia
  exact ⟨hx0, d₁, d₂, d₃, htake, hd₁mem, hdmem d₂ (by simp), hdmem d₃ (by simp), hd₁ge, hpair.1.1, hpair.2⟩

/--
@isnad1 id=and.1h4v.s6.ae7f5bb3ef4c from=translated src=- shape=6f5c2a4f vocab=49c84345
-/
lemma mem_of_threeSmallestDivisors_eq (hdiv : threeSmallestDivisors x = [d₁, d₂, d₃]) :
    d₁ ∈ x.divisors.erase 1 ∧ d₂ ∈ x.divisors.erase 1 ∧ d₃ ∈ x.divisors.erase 1 := by
  have hmem {d : ℕ} (hd : d ∈ [d₁, d₂, d₃]) : d ∈ x.divisors.erase 1 := by
    have hd_take : d ∈ threeSmallestDivisors x := by simp [hdiv, hd]
    exact (mem_sort (r := (· ≤ ·))).mp (by simpa [smallDivisors] using List.mem_of_mem_take hd_take)
  exact ⟨hmem (by simp), hmem (by simp), hmem (by simp)⟩

/--
@isnad1 id=and.1h4v.s5.1618effaa18c from=translated src=- shape=01cfa989 vocab=97ed7cfc
-/
lemma dvd_of_threeSmallestDivisors_eq (hdiv : threeSmallestDivisors x = [d₁, d₂, d₃]) :
    d₁ ∣ x ∧ d₂ ∣ x ∧ d₃ ∣ x := by
  obtain ⟨hd₁mem, hd₂mem, hd₃mem⟩ := mem_of_threeSmallestDivisors_eq hdiv
  exact ⟨dvd_of_mem_divisors_erase_one hd₁mem, dvd_of_mem_divisors_erase_one hd₂mem,
    dvd_of_mem_divisors_erase_one hd₃mem⟩

structure ThreeMinDivisors (x d₁ d₂ d₃ : ℕ) : Prop where
  hdiv : threeSmallestDivisors x = [d₁, d₂, d₃]
  hd₁ge : 2 ≤ d₁
  hd₁₂ : d₁ < d₂
  hd₂₃ : d₂ < d₃

namespace ThreeMinDivisors

/--
@isnad1 id=and.1h4v.s6.ebf6472be430 from=translated src=- shape=6a58dcd4 vocab=4c88200d
-/
lemma mems (h : ThreeMinDivisors x d₁ d₂ d₃) :
    d₁ ∈ x.divisors.erase 1 ∧ d₂ ∈ x.divisors.erase 1 ∧ d₃ ∈ x.divisors.erase 1 :=
  mem_of_threeSmallestDivisors_eq h.hdiv

/--
@isnad1 id=and.1h4v.s4.b7b7da7928e2 from=translated src=- shape=5c0a0ea4 vocab=27f3480d
-/
lemma dvds (h : ThreeMinDivisors x d₁ d₂ d₃) : d₁ ∣ x ∧ d₂ ∣ x ∧ d₃ ∣ x := dvd_of_threeSmallestDivisors_eq h.hdiv

/--
@isnad1 id=eq.2h4v.s6.7e5569c07107 from=translated src=- shape=9be7f1e2 vocab=2b911952
-/
lemma psi_eq (h : ThreeMinDivisors x d₁ d₂ d₃) (hx0 : x ≠ 0) : ψ x = x / d₁ + x / d₂ + x / d₃ :=
  psi_eq_of_threeSmallestDivisors_eq hx0 h.hdiv

end ThreeMinDivisors

/--
@isnad1 id=and.1h1v.s5.455f5b910e6b from=translated src=- shape=df45028b vocab=31b58b8a
-/
lemma threeMinDivisors_of_mem_S {x : ℕ} (hx : x ∈ S) :
    x ≠ 0 ∧ ∃ d₁ d₂ d₃, ThreeMinDivisors x d₁ d₂ d₃ := by
  obtain ⟨hx0, d₁, d₂, d₃, hdiv, _, _, _, hd₁ge, hd₁₂, hd₂₃⟩ := min_divisors_of_mem_S hx
  exact ⟨hx0, d₁, d₂, d₃, ⟨hdiv, hd₁ge, hd₁₂, hd₂₃⟩⟩

/--
@isnad1 id=or.3h5v.s6.a300494fa0b6 from=translated src=- shape=4fa73ad6 vocab=36ded8f7
-/
lemma mem_take_or_gt_of_divisor : x ∈ S → d ∈ x.divisors.erase 1 →
    threeSmallestDivisors x = [d₁, d₂, d₃] → d ∈ [d₁, d₂, d₃] ∨ d₃ < d := by
  intro hx hd hdiv
  by_cases h : d ∈ [d₁, d₂, d₃]
  · exact Or.inl h
  · simp [h]
    by_contra h2
    let T := (x.divisors.erase 1).sort (· ≤ ·)
    have hdT : d ∈ T := (mem_sort fun x1 x2 ↦ x1 ≤ x2).mpr hd
    have hT : T = [d₁, d₂, d₃] ++ T.drop 3 := by
      rw [← hdiv]
      exact (List.take_append_drop 3 T).symm
    have hpairT : T.Pairwise (· < ·) := by
      simp [T, List.sortedLT_iff_pairwise.mp (sortedLT_sort (x.divisors.erase 1))]
    have hdTail : d ∈ T.drop 3 := by grind
    rw [hT] at hpairT
    simp at hpairT
    exact h2 (hpairT.2.2.1 d hdTail)

/--
@isnad1 id=mem.6h6v.s6.a7d58656f81a from=translated src=- shape=3c69a44d vocab=98fcdf4a
-/
lemma mem_of_dvd_mem_threeSmallest (hmin : ThreeMinDivisors x d₁ d₂ d₃) (hx : x ∈ S) (hx0 : x ≠ 0)
    {k d : ℕ} (hk_dvd : k ∣ d) (hd_mem : d ∈ [d₁, d₂, d₃]) (htwo_le : 2 ≤ k) :
    k ∈ [d₁, d₂, d₃] := by
  rcases hmin.dvds, hmin.hd₁ge, hmin.hd₁₂, hmin.hd₂₃ with ⟨⟨hd₁dvd, hd₂dvd, hd₃dvd⟩, hd₁ge, hd₁₂, hd₂₃⟩
  by_cases hcase : d₃ < k
  · by_contra
    simp at hd_mem
    rcases hd_mem with hd | hd | hd <;> grind [Nat.le_of_dvd (by lia) hk_dvd]
  · have hd_dvd_x : d ∣ x := by grind only [List.mem_cons, List.not_mem_nil]
    have hmem := mem_divisors_erase_one_of_dvd_ne_one (dvd_trans hk_dvd hd_dvd_x) hx0 (by lia)
    exact (mem_take_or_gt_of_divisor hx hmem hmin.hdiv).resolve_right hcase

/--
@isnad1 id=eq.3h4v.s5.09e6afbd8a03 from=translated src=- shape=90d16479 vocab=3571a84a
-/
lemma first_min_divisor_eq_two_of_two_dvd (hx : x ∈ S) (h2x : 2 ∣ x)
    (hmin : ThreeMinDivisors x d₁ d₂ d₃) : d₁ = 2 := by
  have hx0 : x ≠ 0 := Nat.ne_zero_of_lt (pos_of_mem_S hx)
  have hmem := mem_divisors_erase_one_of_dvd_ne_one h2x hx0 (by norm_num)
  have h := mem_take_or_gt_of_divisor hx hmem hmin.hdiv
  rcases hmin.hd₁ge, hmin.hd₁₂, hmin.hd₂₃ with ⟨hd₁ge, hd₁₂, hd₂₃⟩
  grind only [List.mem_cons, List.not_mem_nil]

/--
@isnad1 id=eq.6h4v.s6.4241ea819322 from=translated src=- shape=15771e3f vocab=3571a84a
-/
lemma second_min_divisor_eq_four_of_four_dvd (hx : x ∈ S) (hx0 : x ≠ 0)
    (h3x : ¬ 3 ∣ x) (h4 : 4 ∣ x)
    (hmin : ThreeMinDivisors x d₁ d₂ d₃) (hd₁ : d₁ = 2) : d₂ = 4 := by
  have hmem := mem_divisors_erase_one_of_dvd_ne_one h4 hx0 (by norm_num)
  have h := mem_take_or_gt_of_divisor hx hmem hmin.hdiv
  rcases hmin.hd₁₂, hmin.hd₂₃, hmin.dvds with ⟨hd₁₂, hd₂₃, ⟨_, hd₂dvd, _⟩⟩
  grind only [List.mem_cons, List.not_mem_nil]

/--
@isnad1 id=not.6h4v.s6.e229c86d34fe from=translated src=- shape=820a1eb4 vocab=9ac9be8d
-/
lemma not_three_dvd_psi_of_second_min_divisor_four (hx0 : x ≠ 0) (h3x : ¬ 3 ∣ x) (h4 : 4 ∣ x)
    (hmin : ThreeMinDivisors x d₁ d₂ d₃) (hd₁ : d₁ = 2) (hd₂ : d₂ = 4) : ¬ 3 ∣ ψ x := by
  have hpsi : ψ x = 3 * x / 4 + x / d₃ := by
    rw [hmin.psi_eq hx0]
    simp [hd₁, hd₂]
    lia
  have h3d₃ : ¬ 3 ∣ x / d₃ := fun h3 ↦ h3x (by
      convert! dvd_mul_of_dvd_right h3 d₃ using 1
      exact (Nat.mul_div_cancel' hmin.dvds.2.2).symm)
  grind

/--
@isnad1 id=prime.5h4v.s5.8b80dbce1385 from=translated src=- shape=e588c7f1 vocab=ac9034ef
-/
lemma second_min_divisor_prime_of_not_four_dvd (hx : x ∈ S) (hx0 : x ≠ 0)
    (hmin : ThreeMinDivisors x d₁ d₂ d₃) (hd₁ : d₁ = 2) (h4 : ¬ 4 ∣ x) : Nat.Prime d₂ := by
  rcases hmin.dvds, hmin.hd₁₂, hmin.hd₂₃ with ⟨⟨_, hd₂_dvd_x, _⟩, hd₁₂, hd₂₃⟩
  have hdvd_eq_d₁ : ∀ k > 1, k ∣ d₂ → k ≠ d₂ → k = d₁ := by
    intro k hgt_one hk hk_ne_d₂
    have hmem := mem_divisors_erase_one_of_dvd_ne_one (dvd_trans hk hd₂_dvd_x) hx0 (by lia)
    have h := mem_take_or_gt_of_divisor hx hmem hmin.hdiv
    have hlt_d₂ : k ≤ d₂ := Nat.le_of_dvd (by lia) hk
    rcases h with h | h
    · simp at h
      rcases h with h | h | h <;> lia
    · lia
  by_contra hnot_prime
  obtain ⟨m, hm_dvd, hm_ge_two, hm_lt⟩ := (Nat.not_prime_iff_exists_dvd_lt (by lia : 2 ≤ d₂)).mp hnot_prime
  obtain ⟨n, hmn⟩ := hm_dvd
  have hm_ne_d₂ : m ≠ d₂ := by lia
  have hn_ne_d₂ : n ≠ d₂ := by nlinarith
  have h₁ : m = 2 := by
    simpa [hd₁] using hdvd_eq_d₁ m (Nat.lt_of_succ_le hm_ge_two) (Dvd.intro n hmn.symm) hm_ne_d₂
  have h₂ : n = 2 := by simpa [hd₁] using hdvd_eq_d₁ n (by lia) (Dvd.intro_left m hmn.symm) hn_ne_d₂
  have : d₂ = 4 := by simpa [h₁, h₂] using hmn
  exact h4 (dvd_trans (dvd_of_eq this.symm) hd₂_dvd_x)

/--
@isnad1 id=prime.8h4v.s6.c9dd3c3ccda2 from=translated src=- shape=e92dafd4 vocab=10357d71
-/
lemma third_min_divisor_prime_of_not_double_second (hx : x ∈ S) (hx0 : x ≠ 0)
    (h2x : 2 ∣ x) (h4 : ¬ 4 ∣ x) (hmin : ThreeMinDivisors x d₁ d₂ d₃)
    (hd₁ : d₁ = 2)
    (hd₂prime : Nat.Prime d₂) (h2p : ¬ d₃ = 2 * d₂) : Nat.Prime d₃ := by
  rcases hmin.dvds, hmin.mems, hmin.hd₁₂, hmin.hd₂₃ with
    ⟨⟨_, hd₂_dvd_x, hd₃_dvd_x⟩, ⟨hd₁mem, hd₂mem, hd₃mem⟩, hd₁₂, hd₂₃⟩
  by_contra hnot_prime
  obtain ⟨m, hm_dvd, hm_ge_two, hm_lt⟩ := (Nat.not_prime_iff_exists_dvd_lt (by lia : 2 ≤ d₃)).mp hnot_prime
  obtain ⟨n, hmn⟩ := hm_dvd
  have hm_ne_d₃ : m ≠ d₃ := by lia
  have hn_ne_d₃ : n ≠ d₃ := by nlinarith
  have hm_mem := mem_of_dvd_mem_threeSmallest hmin hx hx0 (by simp [hmn] : m ∣ d₃) (by simp) hm_ge_two
  have hn_mem := mem_of_dvd_mem_threeSmallest hmin hx hx0 (by simp [hmn] : n ∣ d₃) (by simp) (by nlinarith)
  replace hm_mem : m ∈ [d₁, d₂] := by grind only [List.mem_cons, List.eq_or_mem_of_mem_cons]
  replace hn_mem : n ∈ [d₁, d₂] := by grind only [List.mem_cons, List.eq_or_mem_of_mem_cons]
  by_cases hm_eq_n : m = n
  · by_cases hm_eq_d₁ : m = d₁
    · exact h4 (dvd_trans (by lia : 4 ∣ d₃) hd₃_dvd_x)
    · have hm : m = d₂ := by simpa [hm_eq_d₁] using hm_mem
      have htwo_d₂_dvd := Nat.Prime.dvd_mul_of_dvd_ne (by lia) Nat.prime_two hd₂prime h2x hd₂_dvd_x
      replace htwo_d₂_dvd := mem_divisors_erase_one_of_dvd_ne_one htwo_d₂_dvd hx0 (by lia)
      have htwo_d₂_lt : 2 * d₂ < d₃ := by
        simp [hmn, ← hm_eq_n, hm, ← hd₁]
        nlinarith [hd₂prime.two_le]
      have htwo_d₂_mem := (mem_take_or_gt_of_divisor hx htwo_d₂_dvd hmin.hdiv).resolve_right (by lia)
      simp at htwo_d₂_mem
      rcases htwo_d₂_mem with h | h | h <;> lia
  · grind only [List.mem_cons, List.not_mem_nil]

/--
@isnad1 id=eq.7h4v.s6.c64dcc5dfa48 from=translated src=- shape=2150953c vocab=263a8efb
-/
lemma psi_mod_two_eq_one_of_min_divisors_prime (hx0 : x ≠ 0) (h2x : 2 ∣ x) (h4 : ¬ 4 ∣ x)
    (hmin : ThreeMinDivisors x d₁ d₂ d₃) (hd₁ : d₁ = 2)
    (hd₂prime : Nat.Prime d₂) (hd₃prime : Nat.Prime d₃) : ψ x % 2 = 1 := by
  obtain ⟨_, hd₂_dvd_x, hd₃_dvd_x⟩ := hmin.dvds
  have h_two_dvd : ∀ d, Nat.Prime d → d₁ < d → d ∣ x → 2 ∣ x / d := by
    intro d hprime hlt hdvd
    have hnot_two_dvd : ¬ 2 ∣ d := by grind [Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime]
    obtain ⟨k, hk⟩ := hdvd
    have : 2 ∣ d * k := by rwa [hk] at h2x
    grind [(Nat.prime_two.dvd_mul.mp this).resolve_left hnot_two_dvd, Nat.mul_div_right]
  simp [hmin.psi_eq hx0, hd₁]
  grind only [hmin.hd₁₂, hmin.hd₂₃]

/--
@isnad1 id=not.7h4v.s6.245bfb3220cd from=translated src=- shape=ab6d89e9 vocab=05a89095
-/
lemma not_six_dvd_psi_of_not_four_dvd (hx : x ∈ S) (hx0 : x ≠ 0)
    (h2x : 2 ∣ x) (h3x : ¬ 3 ∣ x) (hmin : ThreeMinDivisors x d₁ d₂ d₃)
    (hd₁ : d₁ = 2) (h4 : ¬ 4 ∣ x) : ¬ 6 ∣ ψ x := by
  have hd₂prime := second_min_divisor_prime_of_not_four_dvd hx hx0 hmin hd₁ h4
  by_cases h2p : d₃ = 2 * d₂
  · have hpsi : ψ x = x / 2 + x / d₂ + x / (2 * d₂) := by simp [hmin.psi_eq hx0, hd₁, h2p]
    replace hpsi : ψ x = x / 2 + 3 * (x / d₃) := by
      have h2d₂ : 2 * d₂ ∣ x := by simpa [h2p] using hmin.dvds.2.2
      obtain ⟨k, rfl⟩ := h2d₂
      calc
        ψ ((2 * d₂) * k) = (2 * d₂) * k / 2 + (2 * d₂) * k / d₂ + (2 * d₂) * k / (2 * d₂) := hpsi
        _ = (2 * d₂) * k / 2 + 3 * ((2 * d₂) * k / d₃) := by
          have hdivd₂ : d₂ * (2 * k) / d₂ = 2 * ((2 * d₂) * k / (2 * d₂)) := by aesop
          grind only
    lia
  · have hd₃prime := third_min_divisor_prime_of_not_double_second hx hx0 h2x h4 hmin hd₁ hd₂prime h2p
    have hmod2 := psi_mod_two_eq_one_of_min_divisors_prime hx0 h2x h4 hmin hd₁ hd₂prime hd₃prime
    grind only

/--
@isnad1 id=dvd.2h1v.s4.e33600488114 from=translated src=- shape=cab61145 vocab=b05ace2b
-/
lemma six_dvd_of_six_dvd_psi {x : ℕ} : x ∈ S → 6 ∣ ψ x → 6 ∣ x := by
  intro hx h6
  by_contra h6x
  have h2x := two_dvd_of_two_dvd_psi hx (by lia)
  have h3x : ¬ 3 ∣ x := by lia
  obtain ⟨hx0, d₁, d₂, d₃, hmin⟩ := threeMinDivisors_of_mem_S hx
  have hd₁ : d₁ = 2 := first_min_divisor_eq_two_of_two_dvd hx h2x hmin
  by_cases h4 : 4 ∣ x
  · have hd₂ := second_min_divisor_eq_four_of_four_dvd hx hx0 h3x h4 hmin hd₁
    exact not_three_dvd_psi_of_second_min_divisor_four hx0 h3x h4 hmin hd₁ hd₂
      (dvd_trans (by norm_num : 3 ∣ 6) h6)
  · exact not_six_dvd_psi_of_not_four_dvd hx hx0 h2x h3x hmin hd₁ h4 h6

/--
@isnad1 id=lt.2h1v.s4.b2c198a0c9ed from=translated src=- shape=1e7fca7b vocab=644f5898
-/
lemma psi_lt_of_not_two_dvd {x : ℕ} : x ∈ S → ¬ 2 ∣ x → ψ x < x := by
  intro hx h2
  obtain ⟨hx0, d₁, d₂, d₃, hdiv, _, _, _, hd₁ge, hd₁₂, hd₂₃⟩ := min_divisors_of_mem_S hx
  have h2div : ∀ d ∈ x.divisors, ¬ 2 ∣ d := fun d hd h2' ↦ h2 (dvd_trans h2' (Nat.mem_divisors.mp hd).1)
  have hle : ψ x ≤ x / 3 + x / 5 + x / 7 := by
    apply psi_le_of_three_smallest_ge hx0 (by norm_num) (by norm_num) (by norm_num)
    exact ⟨d₁, d₂, d₃, hdiv, (by grind), (by grind), (by grind)⟩
  have hlt : x / 3 + x / 5 + x / 7 < x := by lia
  exact lt_of_le_of_lt hle hlt

/--
@isnad1 id=lt.3h1v.s5.1e3156bad86e from=translated src=- shape=9d7fcc54 vocab=644f5898
-/
lemma psi_lt_of_two_dvd_not_three_dvd {x : ℕ} : x ∈ S → 2 ∣ x → ¬ 3 ∣ x → ψ x < x := by
  intro hx h2 h3
  obtain ⟨hx0, d₁, d₂, d₃, hdiv, _, _, _, hd₁ge, hd₁₂, hd₂₃⟩ := min_divisors_of_mem_S hx
  have hd₂ge : 4 ≤ d₂ := by grind only [= mem_erase, = Nat.mem_divisors]
  have hd₃ge : 5 ≤ d₃ := by lia
  have hle : ψ x ≤ x / 2 + x / 4 + x / 5 := by
    apply psi_le_of_three_smallest_ge hx0 (by norm_num) (by norm_num) (by norm_num)
    exact ⟨d₁, d₂, d₃, hdiv, hd₁ge, hd₂ge, hd₃ge⟩
  lia

/--
@isnad1 id=false.1h4v.s6.efc678d4e41e from=translated src=- shape=b1f8df0c vocab=13a96747
-/
lemma descending_contra (P : ℕ → Prop) (f : ℕ → ℕ) (h₀ : P 0) (h₁ : ∀ i, P i → P (i + 1))
    (h₂ : ∀ i, P i → f (i + 1) < f i) : False := by
  have h_bound : ∀ k, f k + k ≤ f 0 ∧ P k := by
    intro k
    induction k with
    | zero => lia
    | succ i hi => grind only [h₁ i hi.2]
  have := h_bound (f 0 + 1)
  lia

/--
@isnad1 id=dvd.3h3v.s6.bae2560d203f from=translated src=- shape=890d43e8 vocab=c455e6c6
-/
lemma dvd_of_ValidSequence {m : ℕ} : ValidSequence a → (∀ i, a i ∈ S → ¬ m ∣ a i → ψ (a i) < a i) →
    (∀ i, a i ∈ S → m ∣ ψ (a i) → m ∣ a i) → ∀ i, m ∣ a i := by
  intro hvalid h_dec h_step
  by_contra hm
  rw [not_forall] at hm
  obtain ⟨i, hi⟩ := hm
  replace h_dec : ∀ k, ¬ m ∣ a (i + k) → a (i + k + 1) < a (i + k) := by
    intro k hm
    have := h_dec (i + k) (hvalid (i + k)).2.1 hm
    rwa [(hvalid (i + k)).2.2]
  replace h_step : ∀ k, ¬ m ∣ a (i + k) → ¬ m ∣ a (i + k + 1) := by
    intro k hm
    by_contra
    rw [(hvalid (i + k)).2.2] at this
    have hm' := h_step (i + k) (hvalid (i + k)).2.1 this
    exact hm (by lia)
  exact descending_contra (fun k ↦ ¬ m ∣ a (i + k)) (fun k ↦ a (i + k)) hi h_step h_dec

/--
@isnad1 id=dvd.1h2v.s4.524173519530 from=translated src=- shape=b0c166db vocab=0bf84b7a
-/
lemma two_dvd_of_ValidSequence : ValidSequence a → ∀ i, 2 ∣ a i :=
  fun hvalid ↦ dvd_of_ValidSequence hvalid (fun _ ↦ psi_lt_of_not_two_dvd) (fun _ ↦ two_dvd_of_two_dvd_psi)

/--
@isnad1 id=dvd.1h2v.s4.860abaf2e8c2 from=translated src=- shape=b0c166db vocab=0bf84b7a
-/
lemma three_dvd_of_ValidSequence : ValidSequence a → ∀ i, 3 ∣ a i := by
  intro hvalid
  have h_dec := fun i hS h3 ↦ psi_lt_of_two_dvd_not_three_dvd hS (two_dvd_of_ValidSequence hvalid i) h3
  have h_step : ∀ i, a i ∈ S → 3 ∣ ψ (a i) → 3 ∣ a i := by
    intro i hS h3
    have h2 : 2 ∣ a (i + 1) := two_dvd_of_ValidSequence hvalid (i + 1)
    have h6 : 6 ∣ ψ (a i) := by rw [(hvalid i).2.2] at h2; lia
    replace h6 := six_dvd_of_six_dvd_psi hS h6
    lia
  exact dvd_of_ValidSequence hvalid h_dec h_step

/--
@isnad1 id=dvd.1h2v.s4.63dfa5a10a44 from=translated src=- shape=b0c166db vocab=0bf84b7a
-/
lemma six_dvd_of_ValidSequence : ValidSequence a → ∀ i, 6 ∣ a i := by
  intro hvalid i
  grind [two_dvd_of_ValidSequence hvalid i, three_dvd_of_ValidSequence hvalid i]

/--
@isnad1 id=eq.2h1v.s6.953b947f2141 from=translated src=- shape=eddec1a7 vocab=de95b9d4
-/
lemma psi_of_six_dvd {x : ℕ} : x ∈ S → 6 ∣ x →
    ψ x = if 4 ∣ x then x * 13 / 12 else if 5 ∣ x then x * 31 / 30 else x := by
  intro hx h6
  have h_ne_zero : x ≠ 0 := Nat.ne_zero_of_lt (pos_of_mem_S hx)
  by_cases h4 : 4 ∣ x
  · grind only [psi_eq_of_threeSmallestDivisors_eq h_ne_zero
      (divisors_erase_one_sort_take_three_eq_two_three_four h_ne_zero (by lia) (by lia) h4)]
  · by_cases h5 : 5 ∣ x
    · grind only [psi_eq_of_threeSmallestDivisors_eq h_ne_zero
        (divisors_erase_one_sort_take_three_eq_two_three_five h_ne_zero (by lia) (by lia) h4 h5)]
    · grind only [psi_eq_of_threeSmallestDivisors_eq h_ne_zero
        (divisors_erase_one_sort_take_three_eq_two_three_six h_ne_zero (by lia) (by lia) h4 h5)]

/--
@isnad1 id=not.3h1v.s6.232473ba3fa5 from=translated src=- shape=1666c076 vocab=a2e7c113
-/
lemma odd_of_five_branch {x : ℕ} (h6 : 6 ∣ x) (h5 : 5 ∣ x) (h4 : ¬ 4 ∣ x) : ¬ 2 ∣ x * 31 / 30 := by grind

/--
@isnad1 id=not.1h2v.s5.3c49647bc4ab from=translated src=- shape=cf75bc8b vocab=0bf84b7a
-/
lemma not_five_branch_of_ValidSequence : ValidSequence a → ∀ i, ¬ (¬ 4 ∣ a i ∧ 5 ∣ a i) := by
  intro hvalid i
  simp
  intro h4
  have := psi_of_six_dvd (hvalid i).2.1 (six_dvd_of_ValidSequence hvalid i)
  by_contra h5
  simp [h4, h5, ← (hvalid i).2.2] at this
  have hodd : ¬ 2 ∣ (a (i + 1)) := by
    rw [this]
    exact odd_of_five_branch (six_dvd_of_ValidSequence hvalid i) h5 h4
  exact hodd (two_dvd_of_ValidSequence hvalid (i + 1))

/--
@isnad1 id=eq.2h2v.s6.302cc066aab3 from=translated src=- shape=739c2f7b vocab=2da79b1b
-/
lemma padicValNat_step_thirteen_twelfths {x y : ℕ} (hx : x ≠ 0) (hy : 12 * y = 13 * x) :
    padicValNat 2 y + 2 = padicValNat 2 x := by
  have hy0 : y ≠ 0 := by lia
  have h12 : padicValNat 2 12 = 2 := by decide +kernel
  have hval := congrArg (padicValNat 2) hy
  norm_num [padicValNat.mul, hx, hy0, padicValNat.eq_zero_of_not_dvd, h12] at hval
  lia

/--
@isnad1 id=eq.2h2v.s6.b2791cc4fb57 from=translated src=- shape=6134d0ba vocab=2003ac2c
-/
lemma padicValNat_descends_thirteen_twelfths (hpos : ∀ j, 0 < a j) (hstep : ∀ j, 12 * a (j + 1) = 13 * a j) :
    ∀ j, padicValNat 2 (a j) + 2 * j = padicValNat 2 (a 0) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih => grind only [padicValNat_step_thirteen_twelfths (ne_zero_of_lt (hpos j)) (hstep j)]

/--
@isnad1 id=false.2h1v.s6.80e37ff290cf from=translated src=- shape=1d9cc597 vocab=304a85f3
-/
lemma not_forever_thirteen_twelfths (hpos : ∀ j, 0 < a j) (hstep : ∀ j, 12 * a (j + 1) = 13 * a j) : False := by
  have := padicValNat_descends_thirteen_twelfths hpos hstep
  set x := padicValNat 2 (a 1) + 2
  grind [this 1, this x]

/--
@isnad1 id=ex.1h1v.s5.61e000c28601 from=translated src=- shape=46ee6caf vocab=0bf84b7a
-/
lemma exists_fixed_branch_of_ValidSequence : ValidSequence a → ∃ j, ¬ 4 ∣ a j ∧ ¬ 5 ∣ a j := by
  intro hvalid
  by_contra
  simp at this
  by_cases hcase : ∃ j, ¬ 4 ∣ a j
  · obtain ⟨j, h4⟩ := hcase
    exact not_five_branch_of_ValidSequence hvalid j ⟨h4, this j h4⟩
  · simp at hcase
    have hstep : ∀ j, 12 * a (j + 1) = 13 * (a j) := by
      intro j
      have := psi_of_six_dvd (hvalid j).2.1 (six_dvd_of_ValidSequence hvalid j)
      simp [hcase j, ← (hvalid j).2.2] at this
      have h12 : 12 ∣ a j := by grind [hcase j, six_dvd_of_ValidSequence hvalid j]
      grind only
    exact not_forever_thirteen_twelfths (fun j ↦ (hvalid j).1) hstep

/--
@isnad1 id=ex.1h1v.s5.23f40d9bd4ea from=translated src=- shape=07981253 vocab=f851939f
-/
lemma exists_first_fixed_branch_of_ValidSequence : ValidSequence a →
    ∃ j, (∀ i < j, 4 ∣ a i) ∧ ¬ 4 ∣ a j ∧ ¬ 5 ∣ a j := by
  intro hvalid
  obtain ⟨j, h4, h5⟩ := exists_fixed_branch_of_ValidSequence hvalid
  let P : ℕ → Prop := fun i => ¬ 4 ∣ a i
  have hP : ∃ i, P i := ⟨j, h4⟩
  let j₀ := Nat.find hP
  have hj₀ : P j₀ := Nat.find_spec hP
  have hmin : ∀ i < j₀, 4 ∣ a i := by
    intro i hi
    by_contra h
    exact Nat.find_min hP hi h
  have h5₀ : ¬ 5 ∣ a j₀ := fun h5 ↦ not_five_branch_of_ValidSequence hvalid j₀ ⟨hj₀, h5⟩
  exact ⟨j₀, hmin, hj₀, h5₀⟩

/--
@isnad1 id=eq.2h2v.s6.372b5f64a45a from=translated src=- shape=77fe3532 vocab=e0d46af9
-/
lemma step_of_first_fixed_branch {i : ℕ} : ValidSequence a → 4 ∣ a i → 12 * a (i + 1) = 13 * a i := by
  intro hvalid h4
  have h6 := six_dvd_of_ValidSequence hvalid i
  have := psi_of_six_dvd (hvalid i).2.1 h6
  grind [(hvalid i).2.2]

/--
@isnad1 id=eq.2h2v.s6.e78ee8f697a2 from=translated src=- shape=2d87c66f vocab=82c14d79
-/
lemma twelve_pow_mul_of_first_fixed_branch : ValidSequence a → ∀ j, (∀ i < j, 4 ∣ a i) →
    12 ^ j * a j = 13 ^ j * a 0 := by
  intro hvalid j hmin
  have : ∀ k ≤ j, 12 ^ k * a k = 13 ^ k * a 0 := by
    intro k hk
    induction k with
    | zero => simp
    | succ n hn =>
      have : n < j := Nat.lt_of_succ_le hk
      have hstep := step_of_first_fixed_branch hvalid (hmin n this)
      grind
  exact this j (Nat.le_refl j)

/--
@isnad1 id=ex.2h2v.s6.0ce4ab4e89fa from=translated src=- shape=1ca3349b vocab=82c14d79
-/
lemma start_eq_pow_mul_of_first_fixed_branch : ValidSequence a → ∀ j, (∀ i < j, 4 ∣ a i) →
    ∃ m, a 0 = 12 ^ j * m ∧ a j = 13 ^ j * m := by
  intro hvalid j hmin
  let m := a j / 13 ^ j
  have hrel := twelve_pow_mul_of_first_fixed_branch hvalid j hmin
  have hcoprime : Nat.Coprime 12 13 := by decide
  have hcoprime' : Nat.Coprime (12 ^ j) (13 ^ j) := (hcoprime.pow_left j).pow_right j
  have h13 : 13 ^ j ∣ 12 ^ j * a j := Dvd.intro (a 0) hrel.symm
  replace h13 : 13 ^ j ∣ a j := hcoprime'.symm.dvd_of_dvd_mul_left h13
  have : 13 ^ j * m = a j := Nat.mul_div_cancel' h13
  have ha0 : a 0 = 12 ^ j * m := by simp [m, ← Nat.mul_div_assoc (12 ^ j) h13, hrel]
  exact ⟨m, ha0, this.symm⟩

/--
@isnad1 id=coprime.3h2v.s5.d6130bb8de6b from=translated src=- shape=f161c0c0 vocab=77beb901
-/
lemma coprime_ten {m l : ℕ} (hm : m = 6 * l) (h4 : ¬ 4 ∣ m) (h5 : ¬ 5 ∣ m) : l.Coprime 10 := by
  have h2l : ¬ 2 ∣ l := by grind
  have h5l : ¬ 5 ∣ l := by grind
  have hcop2 : l.Coprime 2 := Nat.coprime_comm.mpr (Nat.prime_two.coprime_iff_not_dvd.mpr h2l)
  have hcop5 : l.Coprime 5 := Nat.coprime_comm.mpr (Nat.prime_five.coprime_iff_not_dvd.mpr h5l)
  rw [show 10 = 2 * 5 by norm_num, Nat.coprime_mul_iff_right]
  exact ⟨hcop2, hcop5⟩

/--
@isnad1 id=ex.4h2v.s6.2839efe88f9a from=translated src=- shape=90a4b46b vocab=bb94a5b0
-/
lemma start_eq_pow_of_first_fixed_branch : ValidSequence a →  ∀ j, (∀ i < j, 4 ∣ a i) →
    ¬ 4 ∣ a j → ¬ 5 ∣ a j → ∃ l, a 0 = 12 ^ j * 6 * l ∧ l.Coprime 10 := by
  intro hvalid j hmin h4 h5
  have hmul := start_eq_pow_mul_of_first_fixed_branch hvalid j hmin
  obtain ⟨m, ha0, haj⟩ := hmul
  have h6 : 6 ∣ m := by
    have : 6 ∣ a j := six_dvd_of_ValidSequence hvalid j
    rw [haj] at this
    have hcop : Nat.Coprime 6 13 := by decide
    exact Nat.Coprime.dvd_of_dvd_mul_left (hcop.pow_right j) this
  obtain ⟨l, hl⟩ := h6
  simp [hl, ← mul_assoc] at ha0
  use l
  have h4m : ¬ 4 ∣ m := by grind only [Nat.dvd_mul_left_of_dvd]
  have h5m : ¬ 5 ∣ m := by grind only [Nat.dvd_mul_left_of_dvd]
  exact ⟨ha0, coprime_ten hl h4m h5m⟩

/--
@isnad1 id=mem.1h1v.s5.12819f5e6728 from=translated src=- shape=c336ac1b vocab=9a7fc887
-/
lemma answer_necessary : a₁ ∈ {a₁ | ∃ a : ℕ → ℕ, a 0 = a₁ ∧ ValidSequence a} → a₁ ∈ answer := by
  intro hseq
  obtain ⟨a, ha0, hvalid⟩ := hseq
  obtain ⟨j, hmin, h4, h5⟩ := exists_first_fixed_branch_of_ValidSequence hvalid
  obtain ⟨l, hl⟩ := start_eq_pow_of_first_fixed_branch hvalid j hmin h4 h5
  exact ⟨j, l, by simpa [ha0] using hl⟩

end Imo2025P4
