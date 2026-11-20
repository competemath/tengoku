/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.Seed.Tactic.GCongr
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.ProportionalTraceForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric form of the hypergeometric tail

This module turns the exact binomial-moment bound of `HypergeometricTail` into the
division-free geometric inequality consumed by the sampling schedule.  It also packages the
union-bound cancellation: after choosing a uniform denominator floor `D` and numerator ceiling
`Q`, the schedule need only prove `eventCount * Q < D`.

The fully uniform numerator `n^r s^r` is a diagnostic coarse bound and is generally too weak
when the proportional slack is `t < s`.  The active-trace wrapper removes traces (test sets)
with `hi ≥ s` (whose bad family is empty) and retains trace-size dependence on the genuinely
active family.
-/

open Finset

namespace RegularityLemmata

/-- Normalize the binomial-moment estimate without introducing division.
@isnad1 id=le.2h6v.s6.5c87b1dd0dad from=translated src=- shape=2bf1f5b0 vocab=005aed2a
-/
theorem normalize_binomial_moment
    {bad n s a K r : ℕ} (hrs : r ≤ s)
    (hmoment : bad * K.choose r ≤ a.choose r * (n - r).choose (s - r)) :
    bad * K.choose r * n.choose r ≤ n.choose s * a.choose r * s.choose r := by
  have h := Nat.mul_le_mul_right (n.choose r) hmoment
  calc
    bad * K.choose r * n.choose r ≤
        a.choose r * (n - r).choose (s - r) * n.choose r := by
      simpa [Nat.mul_assoc] using h
    _ = n.choose s * a.choose r * s.choose r := by
      have hchoose := Nat.choose_mul (n := n) hrs
      calc
        a.choose r * (n - r).choose (s - r) * n.choose r =
            a.choose r * (n.choose r * (n - r).choose (s - r)) := by ring
        _ = a.choose r * (n.choose s * s.choose r) := by rw [← hchoose]
        _ = n.choose s * a.choose r * s.choose r := by ring

/-- Division-free geometric consequence of the binomial-moment estimate.
@isnad1 id=le.2h6v.s7.a068c8d55bd2 from=translated src=- shape=5094cbef vocab=32545042
-/
theorem binomial_moment_geometric
    {bad n s a K r : ℕ} (hrs : r ≤ s)
    (hmoment : bad * K.choose r ≤ a.choose r * (n - r).choose (s - r)) :
    bad * (K + 1 - r) ^ r * (n + 1 - r) ^ r ≤
      n.choose s * a ^ r * s ^ r := by
  have hnorm := normalize_binomial_moment hrs hmoment
  have hscaled := Nat.mul_le_mul_right (r.factorial * r.factorial) hnorm
  have hdesc :
      bad * K.descFactorial r * n.descFactorial r ≤
        n.choose s * a.descFactorial r * s.descFactorial r := by
    calc
      bad * K.descFactorial r * n.descFactorial r =
          (bad * K.choose r * n.choose r) * (r.factorial * r.factorial) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose,
          Nat.descFactorial_eq_factorial_mul_choose]
        ring
      _ ≤ (n.choose s * a.choose r * s.choose r) *
          (r.factorial * r.factorial) := hscaled
      _ = n.choose s * a.descFactorial r * s.descFactorial r := by
        rw [Nat.descFactorial_eq_factorial_mul_choose,
          Nat.descFactorial_eq_factorial_mul_choose]
        ring
  calc
    bad * (K + 1 - r) ^ r * (n + 1 - r) ^ r ≤
        bad * K.descFactorial r * n.descFactorial r := by
      gcongr
      · exact Nat.pow_sub_le_descFactorial K r
      · exact Nat.pow_sub_le_descFactorial n r
    _ ≤ n.choose s * a.descFactorial r * s.descFactorial r := hdesc
    _ ≤ n.choose s * a ^ r * s ^ r := by
      gcongr <;> exact Nat.descFactorial_le_pow _ _

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The upper-violation family of the proportional route satisfies the division-free geometric
tail.  The threshold is `hi + 1`, hence the first denominator factor is `hi + 2 - r`.
@isnad1 id=le.1h5v.s7.15e0f12ebefe from=translated src=- shape=4c93bae9 vocab=1f0399cb
-/
theorem card_upperViolations_geometric (A : Finset α) {s hi r : ℕ} (hrs : r ≤ s) :
    (upperViolations A s hi).card * (hi + 2 - r) ^ r *
        (Fintype.card α + 1 - r) ^ r ≤
      (Fintype.card α).choose s * A.card ^ r * s ^ r := by
  have hmoment := card_filter_le_inter_card_mul_choose_le
    (Finset.univ : Finset α) A (Finset.subset_univ A)
    (s := s) (r := r) (K := hi + 1) hrs
  have hgeom := binomial_moment_geometric hrs hmoment
  simpa [upperViolations, Finset.card_univ, Nat.lt_iff_add_one_le] using hgeom

/-- Clearing-denominators union bound.  If every bad family has numerator `Q` and denominator
`D`, and the number of events times `Q` is below `D`, their total is below the sample-space
size `N`.
@isnad1 id=lt.4h7v.s6.0e1e820e9f54 from=translated src=- shape=63fc990b vocab=b2fdb46e
-/
theorem sum_bad_lt_of_mul_le_and_event_ratio
    {ι : Type*} [DecidableEq ι] (F : Finset ι) (bad : ι → ℕ)
    {m N Q D : ℕ} (hN : 0 < N) (hD : 0 < D)
    (htail : ∀ i ∈ F, bad i * D ≤ N * Q)
    (hratio : m * F.card * Q < D) :
    m * ∑ i ∈ F, bad i < N := by
  have hsum : (∑ i ∈ F, bad i) * D ≤ F.card * (N * Q) := by
    calc
      (∑ i ∈ F, bad i) * D = ∑ i ∈ F, bad i * D := by rw [Finset.sum_mul]
      _ ≤ ∑ _i ∈ F, N * Q := Finset.sum_le_sum htail
      _ = F.card * (N * Q) := by simp
  have hmul : (m * ∑ i ∈ F, bad i) * D < N * D := by
    calc
      (m * ∑ i ∈ F, bad i) * D = m * ((∑ i ∈ F, bad i) * D) := by ring
      _ ≤ m * (F.card * (N * Q)) := Nat.mul_le_mul_left m hsum
      _ = N * (m * F.card * Q) := by ring
      _ < N * D := (Nat.mul_lt_mul_left hN).mpr hratio
  exact (Nat.mul_lt_mul_right hD).mp (by simpa [mul_comm] using hmul)

/-- Schedule-ready simultaneous sampling.  The caller supplies only a uniform denominator
floor, numerator ceiling, positivity, and the strict event-ratio inequality.
@isnad1 id=ex.8h9v.s8.c00c62d415c5 from=translated src=- shape=a0db8bed vocab=aee8ea34
-/
theorem exists_equiv_forall_blocks_upper_of_geometric
    {n s m r D Q : ℕ} (hn : Fintype.card α = n) (hnm : n = m * s)
    (F : Finset (Finset α)) (hi : Finset α → ℕ) (hrs : r ≤ s)
    (hchoose : 0 < n.choose s) (hD : 0 < D)
    (hden : ∀ A ∈ F,
      D ≤ (hi A + 2 - r) ^ r * (n + 1 - r) ^ r)
    (hnum : ∀ A ∈ F, A.card ^ r * s ^ r ≤ Q)
    (hratio : m * F.card * Q < D) :
    ∃ e : Fin n ≃ α, ∀ A ∈ F, ∀ j, j < m →
      (A ∩ sampleBlock e s j).card ≤ hi A := by
  have htail : ∀ A ∈ F, (upperViolations A s (hi A)).card * D ≤ n.choose s * Q := by
    intro A hA
    have hgeom := card_upperViolations_geometric A (hi := hi A) (hrs := hrs)
    rw [hn] at hgeom
    calc
      (upperViolations A s (hi A)).card * D
          ≤ (upperViolations A s (hi A)).card *
              ((hi A + 2 - r) ^ r * (n + 1 - r) ^ r) :=
        Nat.mul_le_mul_left _ (hden A hA)
      _ = (upperViolations A s (hi A)).card * (hi A + 2 - r) ^ r *
          (n + 1 - r) ^ r := by ring
      _ ≤ n.choose s * A.card ^ r * s ^ r := hgeom
      _ = n.choose s * (A.card ^ r * s ^ r) := by ring
      _ ≤ n.choose s * Q := Nat.mul_le_mul_left _ (hnum A hA)
  have hsum : m * ∑ A ∈ F, (upperViolations A s (hi A)).card < n.choose s :=
    sum_bad_lt_of_mul_le_and_event_ratio F
      (fun A ↦ (upperViolations A s (hi A)).card) hchoose hD htail hratio
  exact exists_equiv_forall_blocks_upper hn hnm F hi hsum

/-- Proportional-window specialization of the geometric sampler.  Once `r ≤ t`, all trace
dependence disappears from the numerical hypothesis.
@isnad1 id=ex.7h7v.s8.47ec50d0c38c from=translated src=- shape=170894d8 vocab=a014cf9a
-/
theorem exists_equiv_forall_blocks_proportional_of_ratio
    {n s m t r : ℕ} (hn : Fintype.card α = n) (hnm : n = m * s)
    (F : Finset (Finset α)) (hrs : r ≤ s) (hrt : r ≤ t) (hrn : r ≤ n)
    (hchoose : 0 < n.choose s)
    (hratio : m * F.card * (n ^ r * s ^ r) <
      (t + 2 - r) ^ r * (n + 1 - r) ^ r) :
    ∃ e : Fin n ≃ α, ∀ A ∈ F, ∀ j, j < m →
      (A ∩ sampleBlock e s j).card ≤ A.card * s / n + t := by
  let D := (t + 2 - r) ^ r * (n + 1 - r) ^ r
  let Q := n ^ r * s ^ r
  have hD : 0 < D := by
    dsimp [D]
    apply Nat.mul_pos <;> apply pow_pos <;> omega
  apply exists_equiv_forall_blocks_upper_of_geometric hn hnm F
    (fun A ↦ A.card * s / n + t) hrs hchoose hD
  · intro A hA
    dsimp [D]
    have ht : t + 2 ≤ A.card * s / n + t + 2 :=
      Nat.add_le_add_right (Nat.le_add_left t _) 2
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.sub_le_sub_right ht r) r)
  · intro A hA
    have hAcard : A.card ≤ n := by rw [← hn]; exact Finset.card_le_univ A
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hAcard r)
  · simpa [D, Q] using hratio

omit [Fintype α] [DecidableEq α] in
/-- A simple geometric sufficient condition for the exact proportional-sampling ratio.  Under
the half-slack bounds on `r`, it exposes the factor `(4s/t)^r` directly.
@isnad1 id=lt.4h6v.s8.25b5338bf3d8 from=translated src=- shape=a045659c vocab=62399aff
-/
theorem proportional_ratio_of_four_mul
    {m F n s t r : ℕ} (hn : 0 < n)
    (hrt : 2 * r ≤ t + 4) (hrn : 2 * r ≤ n + 2)
    (hgeom : m * F * (4 * s) ^ r < t ^ r) :
    m * F * (n ^ r * s ^ r) <
      (t + 2 - r) ^ r * (n + 1 - r) ^ r := by
  let dt := t + 2 - r
  let dn := n + 1 - r
  have ht : t ≤ 2 * dt := by dsimp [dt]; omega
  have hn' : n ≤ 2 * dn := by dsimp [dn]; omega
  have ht_pow := Nat.pow_le_pow_left ht r
  have hn_pow := Nat.pow_le_pow_left hn' r
  have hscaled := (Nat.mul_lt_mul_right (pow_pos hn r)).mpr hgeom
  have hfour : 0 < 4 ^ r := pow_pos (by omega) r
  apply (Nat.mul_lt_mul_left hfour).mp
  calc
    4 ^ r * (m * F * (n ^ r * s ^ r)) = m * F * (4 * s) ^ r * n ^ r := by
      rw [mul_pow]
      ring
    _ < t ^ r * n ^ r := hscaled
    _ ≤ (2 * dt) ^ r * (2 * dn) ^ r := Nat.mul_le_mul ht_pow hn_pow
    _ = 4 ^ r * (dt ^ r * dn ^ r) := by
      rw [mul_pow, mul_pow, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
      ring
    _ = 4 ^ r * ((t + 2 - r) ^ r * (n + 1 - r) ^ r) := rfl

/-- A window already at least the sample size has no upper violations.
@isnad1 id=eq.1h4v.s5.38063e688528 from=translated src=- shape=9e3890da vocab=25180b3d
-/
theorem upperViolations_eq_empty_of_s_le_hi (A : Finset α) {s hi : ℕ} (h : s ≤ hi) :
    upperViolations A s hi = ∅ := by
  rw [upperViolations, Finset.filter_eq_empty_iff]
  intro S hS
  have hScard := (Finset.mem_powersetCard.mp hS).2
  exact not_lt_of_ge <| calc
    (A ∩ S).card ≤ S.card := Finset.card_le_card Finset.inter_subset_right
    _ = s := hScard
    _ ≤ hi := h

omit [Fintype α] [DecidableEq α] in
/-- The raw trace product is below `n` times one more than its proportional quotient.
@isnad1 id=lt.1h5v.s6.294a52b48082 from=translated src=- shape=268cd460 vocab=9b7302f0
-/
theorem card_mul_lt_mul_proportional_window_succ (A : Finset α) {n s t : ℕ}
    (hn : 0 < n) :
    A.card * s < n * (A.card * s / n + t + 1) := by
  calc
    A.card * s < n * (A.card * s / n + 1) := Nat.lt_mul_div_succ _ hn
    _ ≤ n * (A.card * s / n + t + 1) := by gcongr; omega

/-- Schedule-ready sampler asking tail estimates only for active traces `hi A < s`.  Every
inactive trace is discharged because its upper-violation family is empty.
@isnad1 id=ex.8h9v.s8.c3045abc9efa from=translated src=- shape=15e13d3e vocab=91698f0e
-/
theorem exists_equiv_forall_blocks_upper_of_active_geometric
    {n s m r D Q : ℕ} (hn : Fintype.card α = n) (hnm : n = m * s)
    (F : Finset (Finset α)) (hi : Finset α → ℕ) (hrs : r ≤ s)
    (hchoose : 0 < n.choose s) (hD : 0 < D)
    (hden : ∀ A ∈ F, hi A < s →
      D ≤ (hi A + 2 - r) ^ r * (n + 1 - r) ^ r)
    (hnum : ∀ A ∈ F, hi A < s → A.card ^ r * s ^ r ≤ Q)
    (hratio : m * (F.filter fun A ↦ hi A < s).card * Q < D) :
    ∃ e : Fin n ≃ α, ∀ A ∈ F, ∀ j, j < m →
      (A ∩ sampleBlock e s j).card ≤ hi A := by
  let active := F.filter fun A ↦ hi A < s
  obtain ⟨e, he⟩ := exists_equiv_forall_blocks_upper_of_geometric hn hnm active hi hrs
    hchoose hD
    (fun A hA ↦ hden A (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2)
    (fun A hA ↦ hnum A (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2)
    (by simpa [active] using hratio)
  refine ⟨e, fun A hA j hj ↦ ?_⟩
  by_cases hactive : hi A < s
  · exact he A (Finset.mem_filter.mpr ⟨hA, hactive⟩) j hj
  · have hjs : (j + 1) * s ≤ n := by
      calc
        (j + 1) * s ≤ m * s := Nat.mul_le_mul_right s hj
        _ = n := hnm.symm
    calc
      (A ∩ sampleBlock e s j).card ≤ (sampleBlock e s j).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = s := card_sampleBlock e hjs
      _ ≤ hi A := by omega

end RegularityLemmata
