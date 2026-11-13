import Tengoku.Seed.Data.Int.CardIntervalMod
import Tengoku.Rankamplificationtotient.RankAmplification.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Coprimality in shifted divisor systems The elementary CRT compatibility step used in the shifted divisor convolution (Lemma 2.4). -/

namespace RankAmplification

/-- The exact set counted by `N_h(d₁,d₂)` in Lemma 2.4.-/
def shiftedDivisibilitySet (x h d₁ d₂ : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ d₁ ∣ n ∧ d₂ ∣ n + h

@[simp]
theorem mem_shiftedDivisibilitySet {x h d₁ d₂ n : ℕ} :
    n ∈ shiftedDivisibilitySet x h d₁ d₂ ↔
      1 ≤ n ∧ n ≤ x ∧ d₁ ∣ n ∧ d₂ ∣ n + h := by
  simp [shiftedDivisibilitySet, and_assoc]

theorem prime_not_dvd_both_shifted {p n h : ℕ} (_hp : p.Prime) (hh : 0 < h)
    (hph : h < p) (hpn : p ∣ n) : ¬p ∣ n + h := by
  intro hpnh
  have hpd : p ∣ h := (Nat.dvd_add_iff_right hpn).mpr hpnh
  have hple : p ≤ h := Nat.le_of_dvd hh hpd
  exact (Nat.not_lt_of_ge hple) hph

theorem shifted_divisors_coprime {d₁ d₂ n h : ℕ} (hh : 0 < h)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ d₁ → h < p)
    (hd₁ : d₁ ∣ n) (hd₂ : d₂ ∣ n + h) : Nat.Coprime d₁ d₂ := by
  apply Nat.coprime_of_dvd
  intro p hp hpd₁
  exact prime_not_dvd_both_shifted hp hh (hlarge p hp hpd₁) (hpd₁.trans hd₁) ∘
    (·.trans hd₂)

theorem divisors_modEq {d a b : ℕ} (ha : d ∣ a) (hb : d ∣ b) : a ≡ b [MOD d] :=
  ha.modEq_zero_nat.trans hb.zero_modEq_nat

theorem shifted_divisors_modEq {d a b h : ℕ} (ha : d ∣ a + h) (hb : d ∣ b + h) :
    a ≡ b [MOD d] := by
  have hab : a + h ≡ b + h [MOD d] := divisors_modEq ha hb
  exact Nat.ModEq.rfl.add_right_cancel hab

theorem shifted_residue_modEq_product {d₁ d₂ a b h : ℕ} (hcop : Nat.Coprime d₁ d₂)
    (ha₁ : d₁ ∣ a) (ha₂ : d₂ ∣ a + h) (hb₁ : d₁ ∣ b) (hb₂ : d₂ ∣ b + h) :
    a ≡ b [MOD d₁ * d₂] := by
  apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
  exact ⟨divisors_modEq ha₁ hb₁, shifted_divisors_modEq ha₂ hb₂⟩

theorem shifted_residue_sub_dvd_product {d₁ d₂ a b h : ℕ} (hab : a ≤ b)
    (hcop : Nat.Coprime d₁ d₂) (ha₁ : d₁ ∣ a) (ha₂ : d₂ ∣ a + h)
    (hb₁ : d₁ ∣ b) (hb₂ : d₂ ∣ b + h) : d₁ * d₂ ∣ b - a := by
  exact (Nat.modEq_iff_dvd' hab).mp
    (shifted_residue_modEq_product hcop ha₁ ha₂ hb₁ hb₂)

theorem count_modEq_le_div_add_one (x v m : ℕ) (hm : 0 < m) :
    Nat.count (· ≡ v [MOD m]) (x + 1) ≤ x / m + 1 := by
  rw [Nat.count_modEq_card (b := x + 1) (r := m) hm v, Nat.succ_div]
  by_cases hdvd : m ∣ x + 1
  · have hmod : (x + 1) % m = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
    simp [hdvd, hmod]
  · simp only [hdvd, ↓reduceIte, add_zero, add_le_add_iff_left]
    split_ifs <;> omega

/-- A compatible shifted pair occupies one residue class modulo `d₁d₂`, giving the paper's `x/(d₁d₂)+1` bound.-/
theorem shiftedDivisibilitySet_card_le {x h d₁ d₂ : ℕ} (hh : 0 < h)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ d₁ → h < p) :
    (shiftedDivisibilitySet x h d₁ d₂).card ≤ x / (d₁ * d₂) + 1 := by
  by_cases hempty : shiftedDivisibilitySet x h d₁ d₂ = ∅
  · simp [hempty]
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hcop : Nat.Coprime d₁ d₂ :=
      shifted_divisors_coprime hh hlarge
        (mem_shiftedDivisibilitySet.mp ha).2.2.1
        (mem_shiftedDivisibilitySet.mp ha).2.2.2
    have hmul : 0 < d₁ * d₂ := Nat.mul_pos hd₁ hd₂
    calc
      (shiftedDivisibilitySet x h d₁ d₂).card ≤
          ((Finset.range (x + 1)).filter fun n ↦ n ≡ a [MOD d₁ * d₂]).card := by
        apply Finset.card_le_card
        intro b hb
        have hbm := mem_shiftedDivisibilitySet.mp hb
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.lt_succ_of_le hbm.2.1, ?_⟩
        exact shifted_residue_modEq_product hcop
          hbm.2.2.1
          hbm.2.2.2
          (mem_shiftedDivisibilitySet.mp ha).2.2.1
          (mem_shiftedDivisibilitySet.mp ha).2.2.2
      _ = Nat.count (· ≡ a [MOD d₁ * d₂]) (x + 1) := by
        rw [Nat.count_eq_card_filter_range]
      _ ≤ x / (d₁ * d₂) + 1 := count_modEq_le_div_add_one x a (d₁ * d₂) hmul

end RankAmplification
