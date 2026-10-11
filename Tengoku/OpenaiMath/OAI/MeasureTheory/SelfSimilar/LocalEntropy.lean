import Tengoku.OpenaiMath.OAI.MeasureTheory.SelfSimilar.DigitSumset

namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FiniteEntropy

theorem entropy_le_mass_log_card {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    entropy s p ≤ Real.negMulLog (∑ a ∈ s, p a)+
      (∑ a ∈ s, p a)*Real.log (max 1 (s.card : ℝ)) := by
  let P := ∑ a ∈ s, p a
  have hP : 0 ≤ P := Finset.sum_nonneg hp
  rw [entropy_normalize s p hp]
  change Real.negMulLog P+P*entropy s (fun a => p a/P) ≤
    Real.negMulLog P+P*Real.log (max 1 (s.card : ℝ))
  rcases eq_or_lt_of_le hP with he | he
  · simp only [← he,zero_mul,add_zero,le_refl]
  have hs : 0 < s.card := Finset.card_pos.mpr (by
    by_contra h
    have hse : s=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [P,hse,Finset.sum_empty] at he
    exact lt_irrefl _ he)
  have hh := entropy_le_log_card s (fun a => p a/P)
    (fun a ha => div_nonneg (hp a ha) hP) (by rw [← Finset.sum_div]; exact div_self he.ne')
  have hcard : max 1 (s.card : ℝ)=(s.card : ℝ) := max_eq_right (by exact_mod_cast hs)
  rw [hcard]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hh hP) _

theorem entropy_split_bound {α : Type uα} [DecidableEq α] (s a : Finset α)
    (p : α → ℝ) (ha : a ⊆ s) (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i=1) :
    entropy s p ≤ Real.log 2+Real.log (max 1 (a.card : ℝ))+
      (∑ i ∈ s\a, p i)*Real.log (max 1 (s.card : ℝ)) := by
  classical
  let P := ∑ i ∈ a, p i
  let Q := ∑ i ∈ s\a, p i
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i hi => hp i (ha hi))
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i hi => hp i (Finset.mem_sdiff.mp hi).1)
  have hPQ : P+Q=1 := by
    change (∑ i ∈ a, p i)+(∑ i ∈ s\a, p i)=1
    rw [add_comm,Finset.sum_sdiff ha,hp1]
  have hPa := entropy_le_mass_log_card a p (fun i hi => hp i (ha hi))
  have hQb := entropy_le_mass_log_card (s\a) p (fun i hi => hp i (Finset.mem_sdiff.mp hi).1)
  have hnum := entropy_le_log_card (Finset.univ : Finset (Fin 2))
    (fun i => if i=0 then P else Q) (by intro i _; split <;> assumption)
    (by simpa [Fin.sum_univ_two] using hPQ)
  have hn : Real.negMulLog P+Real.negMulLog Q ≤ Real.log 2 := by
    simpa [entropy,Fin.sum_univ_two] using hnum
  have hlogA : 0 ≤ Real.log (max 1 (a.card : ℝ)) := Real.log_nonneg (le_max_left _ _)
  have hlogB : Real.log (max 1 ((s\a).card : ℝ)) ≤ Real.log (max 1 (s.card : ℝ)) := by
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    exact max_le_max_left 1 (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := s) (t := a)))
  have he : entropy s p=entropy a p+entropy (s\a) p := by
    unfold entropy
    rw [add_comm,Finset.sum_sdiff ha]
  rw [he]
  change entropy a p ≤ Real.negMulLog P+P*_ at hPa
  change entropy (s\a) p ≤ Real.negMulLog Q+Q*_ at hQb
  change _ ≤ Real.log 2+_+Q*_
  nlinarith [mul_le_mul_of_nonneg_left hlogB hQ,mul_nonneg hQ hlogA]

end FiniteEntropy

namespace MeasureEntropy

theorem card_mul_mass_le_one {α : Type uα} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Finset α) (x : α → ℝ) {r q : ℝ}
    (hd : (↑s : Set α).PairwiseDisjoint (fun i => Metric.ball (x i) r))
    (hq : ∀ i ∈ s, q ≤ μ.real (Metric.ball (x i) r)) :
    (s.card : ℝ)*q ≤ 1 := by
  calc
    (s.card : ℝ)*q = ∑ i ∈ s, q := by simp
    _ ≤ ∑ i ∈ s, μ.real (Metric.ball (x i) r) := Finset.sum_le_sum hq
    _ = μ.real (⋃ i ∈ s, Metric.ball (x i) r) :=
      (measureReal_biUnion_finset hd (fun _ _ => measurableSet_ball)).symm
    _ ≤ 1 := (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)

theorem label_ball_disjoint {s u x y : ℝ} (hs : 0 < s)
    (hne : label s u x ≠ label s u y) (hmod : label s u x % 3=label s u y % 3) :
    Disjoint (Metric.ball x (s/2)) (Metric.ball y (s/2)) := by
  have hd : s ≤ dist x y := by
    rw [Real.dist_eq]
    have hx1 := Int.floor_le (x/s+u)
    have hx2 := Int.lt_floor_add_one (x/s+u)
    have hy1 := Int.floor_le (y/s+u)
    have hy2 := Int.lt_floor_add_one (y/s+u)
    have hdiff : label s u x+3 ≤ label s u y ∨ label s u y+3 ≤ label s u x := by omega
    rcases hdiff with h | h
    · have h' : (label s u x : ℝ)+3 ≤ (label s u y : ℝ) := by exact_mod_cast h
      change (⌊x/s+u⌋ : ℝ)+3 ≤ (⌊y/s+u⌋ : ℝ) at h'
      have hxy : 2 < y/s-x/s := by linarith
      have hmul := (lt_div_iff₀ hs).mp (by simpa only [← sub_div] using hxy)
      rw [abs_of_nonpos (by linarith : x-y ≤ 0)]
      linarith
    · have h' : (label s u y : ℝ)+3 ≤ (label s u x : ℝ) := by exact_mod_cast h
      change (⌊y/s+u⌋ : ℝ)+3 ≤ (⌊x/s+u⌋ : ℝ) at h'
      have hxy : 2 < x/s-y/s := by linarith
      have hmul := (lt_div_iff₀ hs).mp (by simpa only [← sub_div] using hxy)
      rw [abs_of_nonneg (by linarith : 0 ≤ x-y)]
      linarith
  apply Set.disjoint_left.mpr
  intro z hz hzy
  have hz1 := Metric.mem_ball.mp hz
  have hz2 := Metric.mem_ball.mp hzy
  have ht := dist_triangle_left x y z
  linarith

theorem good_labels_card_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s u q : ℝ} (hs : 0 < s) (a : Finset ℤ) (x : ℤ → ℝ)
    (hx : ∀ i ∈ a, label s u (x i)=i)
    (hq : ∀ i ∈ a, q ≤ μ.real (Metric.ball (x i) (s/2))) :
    (a.card : ℝ)*q ≤ 3 := by
  let color : ℤ → Fin 3 := fun i => ⟨(i%3).toNat, by omega⟩
  have hc : ∀ c : Fin 3,
      (((a.filter (fun i => color i=c)).card : ℕ) : ℝ)*q ≤ 1 := by
    intro c
    apply card_mul_mass_le_one μ _ x
    · intro i hi j hj hij
      have hia := (Finset.mem_filter.mp hi).1
      have hja := (Finset.mem_filter.mp hj).1
      apply label_ball_disjoint hs
      · rwa [hx i hia,hx j hja]
      · rw [hx i hia,hx j hja]
        have he := congrArg Fin.val ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
        dsimp [color] at he
        omega
    · intro i hi
      exact hq i (Finset.mem_filter.mp hi).1
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hc c)
  have he : ∑ c : Fin 3, (((a.filter (fun i => color i=c)).card : ℕ) : ℝ) = (a.card : ℝ) := by
    simp only [← Nat.cast_sum]
    congr 1
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
      (Finset.sum_fiberwise a color (fun _ => (1 : ℕ)))
  rw [← Finset.sum_mul,he] at hsum
  simpa using hsum

end MeasureEntropy
end EntropyRateDimension

end OAI
