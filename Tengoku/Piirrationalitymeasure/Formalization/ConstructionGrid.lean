import Tengoku.Piirrationalitymeasure.Formalization.ConstructionSavingFloor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Grid lemmas for the finite endpoint partition of a general integer triple. -/

namespace PiIrrationality

open Set

def constructionGridDenominator (a b c : ℕ) : ℕ := 2 * a * b * c

/--
@isnad1 id=and.3h3v.s6.1fa3e734e0c6 from=translated src=- shape=24fe72a8 vocab=a1ad7c72
-/
theorem constructionGridDenominator_properties {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < constructionGridDenominator a b c ∧
      2 * a ∣ constructionGridDenominator a b c ∧
      b ∣ constructionGridDenominator a b c ∧
      c ∣ constructionGridDenominator a b c := by
  unfold constructionGridDenominator
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · exact ⟨b * c, by simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]⟩
  · exact ⟨2 * a * c, by simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]⟩
  · exact ⟨2 * a * b, by simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]⟩

/--
@isnad1 id=disjoint.4h3v.s7.8fce3b62bf3d from=translated src=- shape=0fc14be7 vocab=9ca265c1
-/
theorem constructionGridCell_pairwiseDisjoint {K i j : ℕ}
    (hK : 0 < K) (hi : i < K) (hj : j < K) (hne : i ≠ j) :
    Disjoint (Ioo ((i : ℝ) / K) (((i + 1 : ℕ) : ℝ) / K))
      (Ioo ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) := by
  apply Set.disjoint_left.mpr
  intro u hui huj
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hlefti : (i : ℝ) < (K : ℝ) * u := by
    simpa [mul_comm] using (div_lt_iff₀ hK').mp hui.1
  have hrighti : (K : ℝ) * u < (i + 1 : ℕ) := by
    simpa [mul_comm] using (lt_div_iff₀ hK').mp hui.2
  have hleftj : (j : ℝ) < (K : ℝ) * u := by
    simpa [mul_comm] using (div_lt_iff₀ hK').mp huj.1
  have hrightj : (K : ℝ) * u < (j + 1 : ℕ) := by
    simpa [mul_comm] using (lt_div_iff₀ hK').mp huj.2
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hstep : i + 1 ≤ j := by omega
    have hstep' : (i + 1 : ℕ) ≤ (j : ℝ) := by exact_mod_cast hstep
    linarith
  · have hstep : j + 1 ≤ i := by omega
    have hstep' : (j + 1 : ℕ) ≤ (i : ℝ) := by exact_mod_cast hstep
    linarith

/--
@isnad1 id=disjoint.4h3v.s7.4091b30b7d8e from=translated src=- shape=0fc14be7 vocab=f15f93bc
-/
theorem constructionGridCell_Ico_pairwiseDisjoint {K i j : ℕ}
    (hK : 0 < K) (hi : i < K) (hj : j < K) (hne : i ≠ j) :
    Disjoint (Ico ((i : ℝ) / K) (((i + 1 : ℕ) : ℝ) / K))
      (Ico ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) := by
  apply Set.disjoint_left.mpr
  intro u hui huj
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hrighti : (K : ℝ) * u < (i + 1 : ℕ) := by
    simpa [mul_comm] using (lt_div_iff₀ hK').mp hui.2
  have hleftj : (j : ℕ) ≤ (K : ℝ) * u := by
    simpa [mul_comm] using (div_le_iff₀ hK').mp huj.1
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hstep : i + 1 ≤ j := by omega
    have hstep' : (i + 1 : ℕ) ≤ (j : ℝ) := by exact_mod_cast hstep
    linarith
  · have hstep : j + 1 ≤ i := by omega
    have hrightj : (K : ℝ) * u < (j + 1 : ℕ) := by
      simpa [mul_comm] using (lt_div_iff₀ hK').mp huj.2
    have hlefti : (i : ℕ) ≤ (K : ℝ) * u := by
      simpa [mul_comm] using (div_le_iff₀ hK').mp hui.1
    have hstep' : (j + 1 : ℕ) ≤ (i : ℝ) := by exact_mod_cast hstep
    linarith

/--
@isnad1 id=iff.3h7v.s7.4ead739954f5 from=translated src=- shape=df84aa7e vocab=59422848
-/
theorem constructionSavingCondition_of_floor_data
    {a b c : ℕ} {u : ℝ} {A B C : ℤ}
    (hA : ⌊(a : ℝ) * u + 1 / 2⌋ = A)
    (hB : ⌊(b : ℝ) * u⌋ = B)
    (hC : ⌊(c : ℝ) * u⌋ = C) :
    constructionSavingCondition a b c u ↔
      ((a : ℝ) + 2 * b - c) * u + 1 / 2 <
        (A : ℝ) + 2 * (B : ℝ) - (C : ℝ) := by
  rw [constructionSavingCondition_floor]
  simp only [hA, hB, hC]
/--
@isnad1 id=eq.4h4v.s7.2014be88648e from=translated src=- shape=e54ea396 vocab=3a429b95
-/
theorem floor_nat_mul_on_grid {k K j : ℕ}
    (hk : 0 < k) (hK : 0 < K) (hdiv : k ∣ K) {u : ℝ}
    (hu : u ∈ Ioo ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) :
    ⌊(k : ℝ) * u⌋ = ((j / (K / k) : ℕ) : ℤ) := by
  obtain ⟨d, hd⟩ := hdiv
  have hkd : K / k = d := by
    rw [hd, Nat.mul_comm k d, Nat.mul_div_left d hk]
  have hdpos : 0 < d := by
    have : 0 < k * d := by simpa [hd] using hK
    exact Nat.pos_of_mul_pos_left this
  have hKreal : (K : ℝ) = (k : ℝ) * d := by
    exact_mod_cast hd
  have hleft : (j : ℝ) < (K : ℝ) * u := by
    simpa [mul_comm] using (div_lt_iff₀ (show (0 : ℝ) < K by exact_mod_cast hK)).mp hu.1
  have hright : (K : ℝ) * u < (j + 1 : ℕ) := by
    simpa [mul_comm] using (lt_div_iff₀ (show (0 : ℝ) < K by exact_mod_cast hK)).mp hu.2
  let q : ℕ := j / d
  have hmod : j % d < d := Nat.mod_lt _ hdpos
  have hdecomp : j % d + d * (j / d) = j := Nat.mod_add_div j d
  have hqlo : q * d ≤ j := by
    dsimp [q]
    exact Nat.div_mul_le_self j d
  have hqhi : j < (q + 1) * d := by
    dsimp [q]
    exact (Nat.div_lt_iff_lt_mul hdpos).mp (Nat.lt_succ_self (j / d))
  have hqlo' : (q : ℝ) ≤ (j : ℝ) / d := by
    apply (le_div_iff₀ (by exact_mod_cast hdpos)).mpr
    exact_mod_cast hqlo
  have hqhi' : (j : ℝ) / d < (q : ℝ) + 1 := by
    apply (div_lt_iff₀ (by exact_mod_cast hdpos)).mpr
    exact_mod_cast hqhi
  have hku_lo : (j : ℝ) / d < (k : ℝ) * u := by
    apply (div_lt_iff₀ (by exact_mod_cast hdpos)).mpr
    simpa [hKreal, mul_assoc, mul_comm, mul_left_comm] using hleft
  have hku_hi : (k : ℝ) * u < ((j + 1 : ℕ) : ℝ) / d := by
    apply (lt_div_iff₀ (by exact_mod_cast hdpos)).mpr
    simpa [hKreal, mul_assoc, mul_comm, mul_left_comm] using hright
  have hfloor : (q : ℝ) ≤ (k : ℝ) * u ∧ (k : ℝ) * u < (q : ℝ) + 1 :=
    ⟨le_trans hqlo' hku_lo.le, lt_of_lt_of_le hku_hi (by
      apply (div_le_iff₀ (by exact_mod_cast hdpos)).mpr
      exact_mod_cast (Nat.succ_le_of_lt hqhi))⟩
  rw [hkd]
  change ⌊(k : ℝ) * u⌋ = (q : ℤ)
  apply Int.floor_eq_iff.mpr
  simpa only [Int.cast_natCast, hkd] using hfloor

/--
@isnad1 id=eq.4h4v.s7.da32da14a7cb from=translated src=- shape=e54ea396 vocab=b162e838
-/
theorem floor_nat_mul_on_grid_Ico {k K j : ℕ}
    (hk : 0 < k) (hK : 0 < K) (hdiv : k ∣ K) {u : ℝ}
    (hu : u ∈ Ico ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) :
    ⌊(k : ℝ) * u⌋ = ((j / (K / k) : ℕ) : ℤ) := by
  obtain ⟨d, hd⟩ := hdiv
  have hkd : K / k = d := by
    rw [hd, Nat.mul_comm k d, Nat.mul_div_left d hk]
  have hdpos : 0 < d := by
    have : 0 < k * d := by simpa [hd] using hK
    exact Nat.pos_of_mul_pos_left this
  have hKreal : (K : ℝ) = (k : ℝ) * d := by exact_mod_cast hd
  have hleft : (j : ℝ) ≤ (K : ℝ) * u := by
    simpa [mul_comm] using (div_le_iff₀ (show (0 : ℝ) < K by exact_mod_cast hK)).mp hu.1
  have hright : (K : ℝ) * u < (j + 1 : ℕ) := by
    simpa [mul_comm] using (lt_div_iff₀ (show (0 : ℝ) < K by exact_mod_cast hK)).mp hu.2
  let q : ℕ := j / d
  have hqlo : q * d ≤ j := by
    dsimp [q]
    exact Nat.div_mul_le_self j d
  have hqhi : j < (q + 1) * d := by
    dsimp [q]
    exact (Nat.div_lt_iff_lt_mul hdpos).mp (Nat.lt_succ_self (j / d))
  have hqlo' : (q : ℝ) ≤ (j : ℝ) / d := by
    apply (le_div_iff₀ (by exact_mod_cast hdpos)).mpr
    exact_mod_cast hqlo
  have hku_lo : (j : ℝ) / d ≤ (k : ℝ) * u := by
    apply (div_le_iff₀ (by exact_mod_cast hdpos)).mpr
    simpa [hKreal, mul_assoc, mul_comm, mul_left_comm] using hleft
  have hku_hi : (k : ℝ) * u < ((j + 1 : ℕ) : ℝ) / d := by
    apply (lt_div_iff₀ (by exact_mod_cast hdpos)).mpr
    simpa [hKreal, mul_assoc, mul_comm, mul_left_comm] using hright
  rw [hkd]
  change ⌊(k : ℝ) * u⌋ = (q : ℤ)
  apply Int.floor_eq_iff.mpr
  refine ⟨le_trans hqlo' hku_lo, lt_of_lt_of_le hku_hi ?_⟩
  apply (div_le_iff₀ (by exact_mod_cast hdpos)).mpr
  exact_mod_cast (Nat.succ_le_of_lt hqhi)

/--
@isnad1 id=eq.4h4v.s7.916deceee59b from=translated src=- shape=5f1feaa0 vocab=b162e838
-/
theorem floor_half_nat_mul_on_grid_Ico {m K j : ℕ}
    (hm : 0 < m) (hK : 0 < K) (hdiv : 2 * m ∣ K) {u : ℝ}
    (hu : u ∈ Ico ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) :
    ⌊(m : ℝ) * u + 1 / 2⌋ =
      ((((j / (K / (2 * m))) + 1) / 2 : ℕ) : ℤ) := by
  let q : ℕ := j / (K / (2 * m))
  have hq : ⌊(2 * (m : ℝ)) * u⌋ = (q : ℤ) := by
    simpa [q, Nat.cast_mul, mul_comm] using
      (floor_nat_mul_on_grid_Ico (k := 2 * m) (K := K) (j := j)
        (by omega) hK hdiv hu)
  have hbounds := Int.floor_eq_iff.mp hq
  have hbounds' : (q : ℝ) ≤ 2 * ((m : ℝ) * u) ∧
      2 * ((m : ℝ) * u) < (q : ℝ) + 1 := by
    simpa [mul_assoc] using hbounds
  have hpar : q % 2 = 0 ∨ q % 2 = 1 := by omega
  apply Int.floor_eq_iff.mpr
  rcases hpar with hpar | hpar
  · have hqcast : (q : ℝ) = 2 * (q / 2 : ℕ) := by
      exact_mod_cast (show q = 2 * (q / 2) by omega)
    have hrcast : ((((q + 1) / 2 : ℕ) : ℝ)) = (q / 2 : ℕ) := by
      exact_mod_cast (show (q + 1) / 2 = q / 2 by omega)
    simp only [Int.cast_natCast]
    rw [hrcast]
    constructor <;> linarith [hbounds'.1, hbounds'.2, hqcast]
  · have hqcast : (q : ℝ) = 2 * (q / 2 : ℕ) + 1 := by
      exact_mod_cast (show q = 2 * (q / 2) + 1 by omega)
    have hrcast : ((((q + 1) / 2 : ℕ) : ℝ)) = (q / 2 : ℕ) + 1 := by
      exact_mod_cast (show (q + 1) / 2 = q / 2 + 1 by omega)
    simp only [Int.cast_natCast]
    rw [hrcast]
    constructor <;> linarith [hbounds'.1, hbounds'.2, hqcast]

/--
@isnad1 id=iff.8h6v.s8.816b6eb9f07e from=translated src=- shape=86ef36d7 vocab=419d4795
-/
theorem constructionSavingCondition_on_grid_Ico {a b c K j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (hdivA : 2 * a ∣ K) (hdivB : b ∣ K) (hdivC : c ∣ K) {u : ℝ}
    (hu : u ∈ Ico ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) :
    constructionSavingCondition a b c u ↔
      ((a : ℝ) + 2 * b - c) * u + 1 / 2 <
        (((j / (K / (2 * a)) + 1) / 2 : ℕ) : ℝ) +
          2 * ((j / (K / b) : ℕ) : ℝ) - ((j / (K / c) : ℕ) : ℝ) := by
  rw [constructionSavingCondition_floor]
  simp only [floor_half_nat_mul_on_grid_Ico ha hK hdivA hu,
    floor_nat_mul_on_grid_Ico hb hK hdivB hu,
    floor_nat_mul_on_grid_Ico hc hK hdivC hu]
  simp only [Int.cast_natCast]

/--
@isnad1 id=iff.9h6v.s8.283ce0c6573a from=translated src=- shape=eaef5233 vocab=419d4795
-/
theorem constructionSavingCondition_threshold_on_grid_Ico {a b c K j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (hdivA : 2 * a ∣ K) (hdivB : b ∣ K) (hdivC : c ∣ K)
    (hq : 0 < (a : ℝ) + 2 * b - c) {u : ℝ}
    (hu : u ∈ Ico ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) :
    constructionSavingCondition a b c u ↔
      u <
        (((((j / (K / (2 * a)) + 1) / 2 : ℕ) : ℝ) +
          2 * ((j / (K / b) : ℕ) : ℝ) - ((j / (K / c) : ℕ) : ℝ)) - 1 / 2) /
          ((a : ℝ) + 2 * b - c) := by
  rw [constructionSavingCondition_on_grid_Ico ha hb hc hK hdivA hdivB hdivC hu]
  constructor <;> intro h
  · apply (lt_div_iff₀ hq).mpr
    nlinarith [h]
  · have h' := (lt_div_iff₀ hq).mp h
    nlinarith [h']

/--
@isnad1 id=eq.4h4v.s7.0d4f513b0b23 from=translated src=- shape=5f1feaa0 vocab=3a429b95
-/
theorem floor_half_nat_mul_on_grid {m K j : ℕ}
    (hm : 0 < m) (hK : 0 < K) (hdiv : 2 * m ∣ K) {u : ℝ}
    (hu : u ∈ Ioo ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) :
    ⌊(m : ℝ) * u + 1 / 2⌋ =
      ((((j / (K / (2 * m))) + 1) / 2 : ℕ) : ℤ) := by
  let q : ℕ := j / (K / (2 * m))
  have hq : ⌊(2 * (m : ℝ)) * u⌋ = (q : ℤ) := by
    simpa [q, Nat.cast_mul, mul_comm] using
      (floor_nat_mul_on_grid (k := 2 * m) (K := K) (j := j)
        (by omega) hK hdiv hu)
  have hbounds := Int.floor_eq_iff.mp hq
  have hbounds' : (q : ℝ) ≤ 2 * ((m : ℝ) * u) ∧
      2 * ((m : ℝ) * u) < (q : ℝ) + 1 := by
    simpa [mul_assoc] using hbounds
  have hpar : q % 2 = 0 ∨ q % 2 = 1 := by omega
  apply Int.floor_eq_iff.mpr
  rcases hpar with hpar | hpar
  · have hqcast : (q : ℝ) = 2 * (q / 2 : ℕ) := by
      exact_mod_cast (show q = 2 * (q / 2) by omega)
    have hrcast : ((((q + 1) / 2 : ℕ) : ℝ)) = (q / 2 : ℕ) := by
      exact_mod_cast (show (q + 1) / 2 = q / 2 by omega)
    simp only [Int.cast_natCast]
    rw [hrcast]
    constructor <;> linarith [hbounds'.1, hbounds'.2, hqcast]
  · have hqcast : (q : ℝ) = 2 * (q / 2 : ℕ) + 1 := by
      exact_mod_cast (show q = 2 * (q / 2) + 1 by omega)
    have hrcast : ((((q + 1) / 2 : ℕ) : ℝ)) = (q / 2 : ℕ) + 1 := by
      exact_mod_cast (show (q + 1) / 2 = q / 2 + 1 by omega)
    simp only [Int.cast_natCast]
    rw [hrcast]
    constructor <;> linarith [hbounds'.1, hbounds'.2, hqcast]

/--
@isnad1 id=iff.8h6v.s8.fb161ca30ce9 from=translated src=- shape=86ef36d7 vocab=5cfcadf3
-/
theorem constructionSavingCondition_on_grid {a b c K j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (hdivA : 2 * a ∣ K) (hdivB : b ∣ K) (hdivC : c ∣ K) {u : ℝ}
    (hu : u ∈ Ioo ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) :
    constructionSavingCondition a b c u ↔
      ((a : ℝ) + 2 * b - c) * u + 1 / 2 <
        (((j / (K / (2 * a)) + 1) / 2 : ℕ) : ℝ) +
          2 * ((j / (K / b) : ℕ) : ℝ) - ((j / (K / c) : ℕ) : ℝ) := by
  apply constructionSavingCondition_of_floor_data
  · exact floor_half_nat_mul_on_grid ha hK hdivA hu
  · exact floor_nat_mul_on_grid hb hK hdivB hu
  · exact floor_nat_mul_on_grid hc hK hdivC hu

/--
@isnad1 id=iff.9h6v.s8.29879f10a1c0 from=translated src=- shape=eaef5233 vocab=5cfcadf3
-/
theorem constructionSavingCondition_threshold_on_grid {a b c K j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (hdivA : 2 * a ∣ K) (hdivB : b ∣ K) (hdivC : c ∣ K)
    (hq : 0 < (a : ℝ) + 2 * b - c) {u : ℝ}
    (hu : u ∈ Ioo ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) :
    constructionSavingCondition a b c u ↔
      u <
        (((((j / (K / (2 * a)) + 1) / 2 : ℕ) : ℝ) +
          2 * ((j / (K / b) : ℕ) : ℝ) - ((j / (K / c) : ℕ) : ℝ)) - 1 / 2) /
          ((a : ℝ) + 2 * b - c) := by
  rw [constructionSavingCondition_on_grid ha hb hc hK hdivA hdivB hdivC hu]
  constructor <;> intro h
  · apply (lt_div_iff₀ hq).mpr
    nlinarith [h]
  · have h' := (lt_div_iff₀ hq).mp h
    nlinarith [h']

/--
@isnad1 id=iff.9h6v.s8.407050b07120 from=translated src=- shape=7594713b vocab=58bb7f55
-/
theorem constructionSavingSet_inter_grid_open {a b c K j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (hj : j < K) (hdivA : 2 * a ∣ K) (hdivB : b ∣ K) (hdivC : c ∣ K)
    (hq : 0 < (a : ℝ) + 2 * b - c) {u : ℝ} :
    u ∈ constructionSavingSet a b c ∧
        u ∈ Ioo ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K) ↔
      u ∈ Ioo ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K) ∧
        u <
          (((((j / (K / (2 * a)) + 1) / 2 : ℕ) : ℝ) +
            2 * ((j / (K / b) : ℕ) : ℝ) - ((j / (K / c) : ℕ) : ℝ)) - 1 / 2) /
            ((a : ℝ) + 2 * b - c) := by
  constructor
  · rintro ⟨⟨hu0, hu1, hcond⟩, hu⟩
    exact ⟨hu, (constructionSavingCondition_threshold_on_grid ha hb hc hK
      hdivA hdivB hdivC hq hu).mp hcond⟩
  · rintro ⟨hu, hthr⟩
    have hu0 : 0 ≤ u := by
      have hj0 : (0 : ℝ) ≤ j := by positivity
      have hK' : (0 : ℝ) < K := by exact_mod_cast hK
      exact le_trans (div_nonneg hj0 hK'.le) hu.1.le
    have hu1 : u < 1 := by
      have hK' : (0 : ℝ) < K := by exact_mod_cast hK
      have hj' : (j + 1 : ℕ) ≤ K := by omega
      have hj'' : ((j + 1 : ℕ) : ℝ) / K ≤ 1 := by
        apply (div_le_iff₀ hK').mpr
        simpa using (show ((j + 1 : ℕ) : ℝ) ≤ (K : ℝ) by exact_mod_cast hj')
      exact lt_of_lt_of_le hu.2 hj''
    exact ⟨⟨hu0, hu1, (constructionSavingCondition_threshold_on_grid ha hb hc hK
      hdivA hdivB hdivC hq hu).mpr hthr⟩, hu⟩

/--
@isnad1 id=ne.4h5v.s7.bedf78cb48a2 from=translated src=- shape=810f8f7b vocab=14f684aa
-/
theorem no_half_endpoint_inside_grid {m K j : ℕ}
    (hm : 0 < m) (hK : 0 < K) (hdiv : 2 * m ∣ K) {u : ℝ}
    (hu : u ∈ Ioo ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) :
    ∀ z : ℤ, (m : ℝ) * u + 1 / 2 ≠ (z : ℝ) := by
  intro z hz
  obtain ⟨d, hd⟩ := hdiv
  have hKd : (K : ℝ) = (2 * m * d : ℕ) := by
    exact_mod_cast hd
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hleft : (j : ℝ) < (K : ℝ) * u := by
    simpa [mul_comm] using (div_lt_iff₀ hKpos).mp hu.1
  have hright : (K : ℝ) * u < (j + 1 : ℕ) := by
    simpa [mul_comm] using (lt_div_iff₀ hKpos).mp hu.2
  have hku : (K : ℝ) * u =
      ((d : ℝ) * (2 * (z : ℝ) - 1)) := by
    rw [hKd]
    push_cast
    calc
      (2 * (m : ℝ) * (d : ℝ)) * u =
          (d : ℝ) * (2 * ((m : ℝ) * u)) := by ring
      _ = (d : ℝ) * (2 * (z : ℝ) - 1) := by
        rw [show 2 * ((m : ℝ) * u) = 2 * (z : ℝ) - 1 by linarith]
  have hleft' : (j : ℤ) < (d * (2 * z - 1) : ℤ) := by
    exact_mod_cast hleft.trans_eq hku
  have hright' : (d * (2 * z - 1) : ℤ) < (j + 1 : ℕ) := by
    exact_mod_cast hku ▸ hright
  omega

/--
@isnad1 id=ne.4h5v.s6.05fc8e4a3035 from=translated src=- shape=f85d858f vocab=14f684aa
-/
theorem no_integer_endpoint_inside_grid {m K j : ℕ}
    (hm : 0 < m) (hK : 0 < K) (hdiv : m ∣ K) {u : ℝ}
    (hu : u ∈ Ioo ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) :
    ∀ z : ℤ, (m : ℝ) * u ≠ (z : ℝ) := by
  intro z hz
  obtain ⟨d, hd⟩ := hdiv
  have hKd : (K : ℝ) = (m * d : ℕ) := by
    exact_mod_cast hd
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hleft : (j : ℝ) < (K : ℝ) * u := by
    simpa [mul_comm] using (div_lt_iff₀ hKpos).mp hu.1
  have hright : (K : ℝ) * u < (j + 1 : ℕ) := by
    simpa [mul_comm] using (lt_div_iff₀ hKpos).mp hu.2
  have hku : (K : ℝ) * u = (d : ℝ) * (z : ℝ) := by
    rw [hKd]
    push_cast
    calc
      ((m : ℝ) * (d : ℝ)) * u = (d : ℝ) * ((m : ℝ) * u) := by ring
      _ = (d : ℝ) * (z : ℝ) := by rw [hz]
  have hleft' : (j : ℤ) < (d * z : ℤ) := by
    exact_mod_cast hleft.trans_eq hku
  have hright' : (d * z : ℤ) < (j + 1 : ℕ) := by
    exact_mod_cast hku ▸ hright
  omega

end PiIrrationality
