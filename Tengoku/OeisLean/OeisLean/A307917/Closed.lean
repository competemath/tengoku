/-
OEIS A307917: pure algebra. Any `F` satisfying the boundary values `h0`, `hz` and the
three-term recurrence `hs` has a closed form in terms of `Closed.M`, and its diagonal sum
is `formula`.
-/
import Tengoku.OeisLean.OeisLean.A307917.Defs
import Tengoku.Seed.Algebra.BigOperators.Intervals
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms closed_form` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sum_eq_formula` (it only prints; the queue checks the axioms of every declaration). -/

namespace A307917

namespace Closed

/-- `M n q c = Sum_{j=0..c} (-1)^j C(c+1-j, j) (n-j)_(q-j)` (falling factorial).-/
def M (n q c : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (c + 1),
    (-1) ^ j * ((c + 1 - j).choose j : ℤ) * ((n - j).descFactorial (q - j) : ℤ)

/--
@isnad1 id=eq.0h2v.s4.a1a74974e8e5 from=translated src=- shape=c6f7e240 vocab=fe21d0a6
-/
theorem M_zero (n q : ℕ) : M n q 0 = n.descFactorial q := by
  simp [M]

/--
@isnad1 id=eq.0h2v.s6.27b55754a4b9 from=translated src=- shape=f0e678d1 vocab=3cdde0b6
-/
theorem M_one (n q : ℕ) :
    M (n + 1) (q + 1) 1 = ((n + 1).descFactorial (q + 1) : ℤ) - n.descFactorial q := by
  simp [M, Finset.sum_range_succ]
  ring

/-- Peel off the `j = 0` term and shift the index.
@isnad1 id=eq.0h3v.s7.626a7fc6231d from=translated src=- shape=f7c27cb9 vocab=efbcc5cf
-/
theorem M_shift (n q c : ℕ) :
    M (n + 1) (q + 1) (c + 1) = ((n + 1).descFactorial (q + 1) : ℤ) +
      ∑ j ∈ Finset.range (c + 1),
        (-1) ^ (j + 1) * ((c + 1 - j).choose (j + 1) : ℤ) *
          ((n - j).descFactorial (q - j) : ℤ) := by
  unfold M
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right, pow_zero, Nat.sub_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul]
  rw [add_comm]

/--
@isnad1 id=eq.0h3v.s6.9824cc2da815 from=translated src=- shape=80a0b724 vocab=5a9bd704
-/
theorem M_succ (n q c : ℕ) :
    M (n + 1) (q + 1) (c + 2) = M (n + 1) (q + 1) (c + 1) - M n q c := by
  show M (n + 1) (q + 1) (c + 1 + 1) = _
  rw [M_shift n q (c + 1), M_shift n q c, Finset.sum_range_succ]
  have hlast : (((c + 1 + 1 - (c + 1)).choose (c + 1 + 1) : ℕ) : ℤ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]; rfl
  rw [hlast]
  have key : ∑ j ∈ Finset.range (c + 1),
        (-1 : ℤ) ^ (j + 1) * ((c + 1 + 1 - j).choose (j + 1) : ℤ) *
          ((n - j).descFactorial (q - j) : ℤ)
      = ∑ j ∈ Finset.range (c + 1),
        (-1 : ℤ) ^ (j + 1) * ((c + 1 - j).choose (j + 1) : ℤ) *
          ((n - j).descFactorial (q - j) : ℤ) - M n q c := by
    unfold M
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < c + 1 := Finset.mem_range.mp hj
    have e : c + 1 + 1 - j = (c + 1 - j) + 1 := by omega
    rw [e, Nat.choose_succ_succ']
    push_cast
    ring
  rw [key]
  ring

/--
@isnad1 id=eq.0h2v.s7.945d0024e65e from=translated src=- shape=68d39647 vocab=9cf6b19e
-/
theorem sum_parity (g : ℕ → ℤ) (n : ℕ) :
    ∑ L ∈ Finset.Icc 2 (2 * n), g L
      = ∑ k ∈ Finset.Icc 1 n, g (2 * k) + ∑ k ∈ Finset.Icc 1 (n - 1), g (2 * k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      have e : 2 * (m + 1 + 1) = 2 * (m + 1) + 1 + 1 := by ring
      rw [e, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      rw [Finset.sum_Icc_succ_top (a := 1) (b := m + 1) (by omega) (fun k => g (2 * k)),
        Finset.sum_Icc_succ_top (a := 1) (b := m) (by omega) (fun k => g (2 * k + 1)), e]
      ring

/--
@isnad1 id=eq.1h2v.s7.982f67479fa7 from=translated src=- shape=3c186aff vocab=2e36909c
-/
theorem M_even (n k : ℕ) (hk : 1 ≤ k) :
    M n k (2 * k - 1) = ∑ j ∈ Finset.range (k + 1),
      (-1) ^ j * ((2 * k - j).choose j : ℤ) * ((n - j).descFactorial (k - j) : ℤ) := by
  unfold M
  have e : 2 * k - 1 + 1 = 2 * k := by omega
  rw [e]
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at *
    omega
  · intro j hj hj'
    simp only [Finset.mem_range] at hj hj'
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/--
@isnad1 id=eq.0h2v.s7.99f55fb87af0 from=translated src=- shape=12fc6ccf vocab=efbcc5cf
-/
theorem M_odd (n k : ℕ) :
    M n k (2 * k) = ∑ j ∈ Finset.range (k + 1),
      (-1) ^ j * ((2 * k + 1 - j).choose j : ℤ) * ((n - j).descFactorial (k - j) : ℤ) := by
  unfold M
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at *
    omega
  · intro j hj hj'
    simp only [Finset.mem_range] at hj hj'
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/--
@isnad1 id=eq.0h2v.s6.3c4ef3e710b5 from=translated src=- shape=0b4059f2 vocab=f218fa49
-/
theorem cast_desc_succ (n p : ℕ) :
    ((n + 1).descFactorial (p + 1) : ℤ) = (n + 1) * (n.descFactorial p : ℤ) := by
  rw [Nat.succ_descFactorial_succ]
  push_cast
  ring

end Closed

/--
@isnad1 id=eq.4h4v.s8.664bc1d48a43 from=translated src=- shape=51dda1fa vocab=128719ed
-/
theorem closed_form (F : ℕ → ℕ → ℕ → ℕ)
    (h0 : ∀ n L, F n L 0 = n.descFactorial ((L + 1) / 2) * n.descFactorial (L / 2))
    (hz : ∀ L c, 1 ≤ L → F 0 L c = 0)
    (hs : ∀ n L c, c ≤ L →
      F (n + 1) (L + 2) (c + 1) + (n + 1) * F n L (c - 1) = F (n + 1) (L + 2) c) :
    ∀ c n L, c + 1 ≤ L →
      (F n L c : ℤ) = (n.descFactorial ((L + 1) / 2) : ℤ) * Closed.M n (L / 2) c := by
  intro c
  induction c using Nat.twoStepInduction with
  | zero =>
    intro n L _
    rw [h0, Closed.M_zero, Nat.cast_mul]
  | one =>
    intro n L hL
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 2 := ⟨L - 2, by omega⟩
    have e1 : (L' + 2 + 1) / 2 = (L' + 1) / 2 + 1 := by omega
    have e2 : (L' + 2) / 2 = L' / 2 + 1 := by omega
    rw [e1, e2]
    cases n with
    | zero => rw [hz _ _ (by omega), Nat.zero_descFactorial_succ]; simp
    | succ n =>
      have h := hs n L' 0 (by omega)
      simp only [Nat.zero_sub, zero_add] at h
      rw [h0, h0, e1, e2] at h
      have h' : (F (n + 1) (L' + 2) 1 : ℤ) +
          (n + 1) * ((n.descFactorial ((L' + 1) / 2) : ℤ) * (n.descFactorial (L' / 2) : ℤ))
          = ((n + 1).descFactorial ((L' + 1) / 2 + 1) : ℤ) *
            ((n + 1).descFactorial (L' / 2 + 1) : ℤ) := by
        exact_mod_cast h
      rw [Closed.M_one]
      rw [Closed.cast_desc_succ n ((L' + 1) / 2)] at h' ⊢
      linear_combination h'
  | more c ih0 ih1 =>
    intro n L hL
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 2 := ⟨L - 2, by omega⟩
    have e1 : (L' + 2 + 1) / 2 = (L' + 1) / 2 + 1 := by omega
    have e2 : (L' + 2) / 2 = L' / 2 + 1 := by omega
    rw [e1, e2]
    cases n with
    | zero => rw [hz _ _ (by omega), Nat.zero_descFactorial_succ]; simp
    | succ n =>
      have h := hs n L' (c + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h
      have h' : (F (n + 1) (L' + 2) (c + 2) : ℤ) + (n + 1) * (F n L' c : ℤ)
          = (F (n + 1) (L' + 2) (c + 1) : ℤ) := by
        exact_mod_cast h
      rw [ih1 (n + 1) (L' + 2) (by omega), ih0 n L' (by omega), e1, e2] at h'
      rw [Closed.M_succ]
      rw [Closed.cast_desc_succ n ((L' + 1) / 2)] at h' ⊢
      linear_combination h'

/--
@isnad1 id=eq.3h2v.s8.be93b8bac2d6 from=translated src=- shape=db4de6f0 vocab=8064583d
-/
theorem sum_eq_formula (F : ℕ → ℕ → ℕ → ℕ)
    (h0 : ∀ n L, F n L 0 = n.descFactorial ((L + 1) / 2) * n.descFactorial (L / 2))
    (hz : ∀ L c, 1 ≤ L → F 0 L c = 0)
    (hs : ∀ n L c, c ≤ L →
      F (n + 1) (L + 2) (c + 1) + (n + 1) * F n L (c - 1) = F (n + 1) (L + 2) c)
    (n : ℕ) :
    ∑ L ∈ Finset.Icc 2 (2 * n), (F n L (L - 1) : ℤ) = formula n := by
  rw [Closed.sum_parity (fun L => (F n L (L - 1) : ℤ)), formula]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have e1 : (2 * k + 1) / 2 = k := by omega
    have e2 : 2 * k / 2 = k := by omega
    rw [closed_form F h0 hz hs (2 * k - 1) n (2 * k) (by omega), e1, e2,
      Closed.M_even n k hk1]
  · apply Finset.sum_congr rfl
    intro k _
    have e1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have e2 : (2 * k + 1) / 2 = k := by omega
    rw [Nat.add_sub_cancel, closed_form F h0 hz hs (2 * k) n (2 * k + 1) (by omega), e1, e2,
      Closed.M_odd n k]

end A307917
