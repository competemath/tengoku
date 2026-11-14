import Tengoku.Piirrationalitymeasure.Formalization.PrimeSaving

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The fractional-part condition of Section 3.1 on each cell of the 3714-grid.
-/

namespace PiIrrationality

def primeSavingCondition (u : ℝ) : Prop :=
  Int.fract (1857 * u + 1 / 2) + 2 * Int.fract (3714 * u) < Int.fract (5570 * u)

def primeSavingSet : Set ℝ := {u | 0 ≤ u ∧ u < 1 ∧ primeSavingCondition u}

def SavingCell (j : ℕ) (u : ℝ) : Prop :=
  (j : ℝ) ≤ 3714 * u ∧ 3714 * u < (j : ℝ) + 1

theorem savingCell_floor_b {j : ℕ} {u : ℝ} (hu : SavingCell j u) :
    ⌊3714 * u⌋ = (j : ℤ) := by
  apply Int.floor_eq_iff.mpr
  simpa only [Int.cast_natCast, SavingCell] using hu

theorem savingCell_floor_a {j : ℕ} {u : ℝ} (hu : SavingCell j u) :
    ⌊1857 * u + 1 / 2⌋ = (((j + 1) / 2 : ℕ) : ℤ) := by
  have h₁ : 2 * ((j + 1) / 2) ≤ j + 1 := by omega
  have h₂ : j ≤ 2 * ((j + 1) / 2) := by omega
  have h₁' : 2 * (((j + 1) / 2 : ℕ) : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast h₁
  have h₂' : (j : ℝ) ≤ 2 * (((j + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h₂
  apply Int.floor_eq_iff.mpr
  simp only [Int.cast_natCast]
  constructor <;> dsimp [SavingCell] at hu <;> linarith [hu.1, hu.2]

theorem savingCell_condition_floor {j : ℕ} {u : ℝ} (hu : SavingCell j u) :
    primeSavingCondition u ↔
      3715 * u + 1 / 2 < (((j + 1) / 2 : ℕ) : ℝ) +
        2 * (j : ℝ) - (⌊5570 * u⌋ : ℝ) := by
  unfold primeSavingCondition Int.fract
  rw [savingCell_floor_a hu, savingCell_floor_b hu]
  simp only [Int.cast_natCast]
  constructor <;> intro h <;> linarith

/-- A first jump of the c-grid already exhausts the initial gap.-/
theorem savingCell_condition_iff {j : ℕ} {u : ℝ} {q : ℤ}
    (hu : SavingCell j u) (hq : ⌊5570 * (j : ℝ) / 3714⌋ = q) :
    primeSavingCondition u ↔
      5570 * u < (q : ℝ) + 1 ∧
        3715 * u + 1 / 2 < (((j + 1) / 2 : ℕ) : ℝ) + 2 * (j : ℝ) - q := by
  have hqbounds := Int.floor_eq_iff.mp hq
  have hqcu : (q : ℝ) ≤ 5570 * u := by
    dsimp [SavingCell] at hu
    linarith [hqbounds.1, hu.1]
  have hqfloor : q ≤ ⌊5570 * u⌋ := Int.le_floor.mpr hqcu
  have hceil : 2 * (((j + 1) / 2 : ℕ) : ℝ) ≤ (j : ℝ) + 1 := by
    exact_mod_cast (show 2 * ((j + 1) / 2) ≤ j + 1 by omega)
  rw [savingCell_condition_floor hu]
  constructor
  · intro h
    have heq : ⌊5570 * u⌋ = q := by
      by_contra hne
      have hz : q + 1 ≤ ⌊5570 * u⌋ := by omega
      have hz' : (q : ℝ) + 1 ≤ (⌊5570 * u⌋ : ℝ) := by exact_mod_cast hz
      dsimp [SavingCell] at hu
      linarith [hqbounds.2, hu.1]
    rw [heq] at h
    exact ⟨by simpa only [heq] using Int.lt_floor_add_one (5570 * u), h⟩
  · rintro ⟨hc, hd⟩
    have heq : ⌊5570 * u⌋ = q := Int.floor_eq_iff.mpr ⟨hqcu, hc⟩
    simpa only [heq] using hd

theorem savingCell_condition_even {j : ℕ} {u : ℝ}
    (hj : 1 ≤ j) (hj' : j ≤ 3713) (he : j % 2 = 0) (hu : SavingCell j u) :
    primeSavingCondition u ↔
      u < 3 * (j : ℝ) / 11140 ∧ u < (2 * (j : ℝ) + 1) / 7430 := by
  have hdiv : 2 * (j / 2) = j := by omega
  have hdiv' : 2 * ((j / 2 : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast hdiv
  have hceil : (j + 1) / 2 = j / 2 := by omega
  have hq : ⌊5570 * (j : ℝ) / 3714⌋ = 3 * ((j / 2 : ℕ) : ℤ) - 1 := by
    apply Int.floor_eq_iff.mpr
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    have hlow : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hhigh : (j : ℝ) ≤ 3713 := by exact_mod_cast hj'
    constructor <;> linarith
  rw [savingCell_condition_iff hu hq, hceil]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem savingCell_condition_lower_odd {j : ℕ} {u : ℝ}
    (hj : j ≤ 1857) (he : j % 2 = 1) (hu : SavingCell j u) :
    primeSavingCondition u ↔
      u < (3 * (j : ℝ) + 1) / 11140 ∧ u < (2 * (j : ℝ) + 1) / 7430 := by
  have hdiv : 2 * (j / 2) + 1 = j := by omega
  have hdiv' : 2 * ((j / 2 : ℕ) : ℝ) + 1 = (j : ℝ) := by exact_mod_cast hdiv
  have hceil : (j + 1) / 2 = j / 2 + 1 := by omega
  have hq : ⌊5570 * (j : ℝ) / 3714⌋ = 3 * ((j / 2 : ℕ) : ℤ) + 1 := by
    apply Int.floor_eq_iff.mpr
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    have hlow : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    have hhigh : (j : ℝ) ≤ 1857 := by exact_mod_cast hj
    constructor <;> linarith
  rw [savingCell_condition_iff hu hq, hceil]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    Nat.cast_add, Nat.cast_one]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem savingCell_condition_upper_odd {j : ℕ} {u : ℝ}
    (hj : 1859 ≤ j) (hj' : j ≤ 3713) (he : j % 2 = 1) (hu : SavingCell j u) :
    primeSavingCondition u ↔ u < (3 * (j : ℝ) - 1) / 11140 := by
  have hdiv : 2 * (j / 2) + 1 = j := by omega
  have hdiv' : 2 * ((j / 2 : ℕ) : ℝ) + 1 = (j : ℝ) := by exact_mod_cast hdiv
  have hceil : (j + 1) / 2 = j / 2 + 1 := by omega
  have hlow : (1859 : ℝ) ≤ j := by exact_mod_cast hj
  have hhigh : (j : ℝ) ≤ 3713 := by exact_mod_cast hj'
  have hq : ⌊5570 * (j : ℝ) / 3714⌋ = 3 * ((j / 2 : ℕ) : ℤ) := by
    apply Int.floor_eq_iff.mpr
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    constructor <;> linarith
  rw [savingCell_condition_iff hu hq, hceil]
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
  constructor
  · rintro ⟨h₁, h₂⟩
    linarith
  · intro h
    constructor <;> linarith

theorem savingCell_zero {u : ℝ} (hu : SavingCell 0 u) : ¬primeSavingCondition u := by
  dsimp [SavingCell] at hu
  norm_num at hu
  intro h
  have hf := (savingCell_condition_floor (j := 0) (by simpa [SavingCell] using hu)).mp h
  have hz : (0 : ℤ) ≤ ⌊5570 * u⌋ := Int.le_floor.mpr (by norm_num; linarith [hu.1])
  have hz' : (0 : ℝ) ≤ (⌊5570 * u⌋ : ℝ) := by exact_mod_cast hz
  norm_num at hf
  linarith [hu.1]

end PiIrrationality
