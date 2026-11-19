import Tengoku.Erdos278.Erdos278.Density
import Tengoku.Seed.Data.Real.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

/-- Equation (8.1), over genuine integer residue and quotient variables.-/
def pairConstraint (d t q y : ℤ) : Prop :=
  1 - y ≤ t - d * q ∧ t - d * q ≤ (d - 1) * (1 - y)

theorem pair_constraint_exact (d t y : ℤ) (hd : 0 < d) (hy : y = 0 ∨ y = 1) :
    (∃ q : ℤ, pairConstraint d t q y) ↔ (y = 1 ↔ d ∣ t) := by
  rcases hy with rfl | rfl
  · simp only [zero_ne_one, false_iff]
    constructor
    · rintro ⟨q, hlo, hhi⟩ ht
      have hdiv : d ∣ t - d * q := dvd_sub ht (dvd_mul_right d q)
      have hpos : 0 < t - d * q := by omega
      have := Int.le_of_dvd hpos hdiv
      simp only [sub_zero, mul_one] at hhi
      omega
    · intro ht
      refine ⟨t / d, ?_⟩
      have hnonneg := Int.emod_nonneg t hd.ne'
      have hlt := Int.emod_lt_of_pos t hd
      have hne : t % d ≠ 0 := mt Int.dvd_of_emod_eq_zero ht
      have hrem := Int.emod_add_mul_ediv t d
      unfold pairConstraint
      simp only [sub_zero, mul_one]
      omega
  · simp only [true_iff]
    constructor
    · rintro ⟨q, hlo, hhi⟩
      refine ⟨q, ?_⟩
      simp only [sub_self, mul_zero] at hlo hhi
      omega
    · rintro ⟨q, rfl⟩
      exact ⟨q, by simp [pairConstraint]⟩

/-- Section 7: the nonedge remainder encoding, including negative differences.-/
theorem nonedge_remainder_exact (d t : ℤ) (hd : 0 < d) :
    (∃ q s : ℤ, t = d * q + s ∧ 1 ≤ s ∧ s ≤ d - 1) ↔ ¬d ∣ t := by
  have h := pair_constraint_exact d t 0 hd (Or.inl rfl)
  simp only [zero_ne_one, false_iff] at h
  rw [← h]
  constructor
  · rintro ⟨q, s, ht, hs, hs'⟩
    exact ⟨q, by simp only [pairConstraint, sub_zero, mul_one]; omega⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, t - d * q, by ring, by simpa [pairConstraint] using hq⟩

/-- Continuous AND constraints (8.3)-(8.4).-/
def andConstraints {α : Type*} [Fintype α] (y : α → ℝ) (z : ℝ) : Prop :=
  0 ≤ z ∧ z ≤ 1 ∧ (∀ e, z ≤ y e) ∧ 1 - ∑ e, (1 - y e) ≤ z

theorem continuous_clique_indicator {α : Type*} [Fintype α]
    (y : α → ℝ) (hy : ∀ e, y e = 0 ∨ y e = 1) (z : ℝ) :
    andConstraints y z ↔ z = if (∀ e, y e = 1) then 1 else 0 := by
  classical
  by_cases hall : ∀ e, y e = 1
  · have hsum : ∑ e, (1 - y e) = 0 := by simp [hall]
    simp only [ite_eq_left hall]
    constructor
    · rintro ⟨_, hz, _, hl⟩
      rw [hsum] at hl
      linarith
    · rintro rfl
      exact ⟨by norm_num, le_rfl, fun e => by rw [hall], by simp [hsum]⟩
  · obtain ⟨e, he⟩ := not_forall.mp hall
    have he0 : y e = 0 := (hy e).resolve_right he
    have hsum : 1 ≤ ∑ e, (1 - y e) := by
      calc
        1 = 1 - y e := by rw [he0]; norm_num
        _ ≤ ∑ e, (1 - y e) := Finset.single_le_sum (f := fun i => 1 - y i)
          (fun i _ => by rcases hy i with h | h <;> simp [h]) (mem_univ e)
    simp only [ite_eq_right hall]
    constructor
    · rintro ⟨hz, _, hu, _⟩
      have := hu e
      rw [he0] at this
      linarith
    · rintro rfl
      exact ⟨le_rfl, by norm_num,
        fun e => by rcases hy e with h | h <;> simp [h], by linarith⟩

end Erdos278
