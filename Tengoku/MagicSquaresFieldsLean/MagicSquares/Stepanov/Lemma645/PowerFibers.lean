import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma645.Sets
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.FirstBlockIndependence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The concrete power-fiber count in Lemma 6.45

For `m | q-1`, a nonzero `a` is an `m`-th power exactly when
`a^((q-1)/m)=1`, and then it has exactly `m` distinct `m`-th roots.
Summing these fibers counts the actual pairs `(x,y)` satisfying `y^m=f(x)`.
-/

omit [DecidableEq F] in
theorem stepanovPowerExponent_pos {m : ℕ} (hmq : m ∣ Fintype.card F - 1) :
    0 < (Fintype.card F - 1) / m := by
  have hq := Fintype.one_lt_card (α := F)
  have hm : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hz
    subst m
    simp only [zero_dvd_iff] at hmq
    omega
  exact Nat.div_pos (Nat.le_of_dvd (by omega) hmq) hm

omit [DecidableEq F] in
theorem exists_pow_eq_iff_stepanovPower
    {m : ℕ} (hm : 0 < m) (hmq : m ∣ Fintype.card F - 1)
    {a : F} (ha : a ≠ 0) :
    (∃ y : F, y ^ m = a) ↔ a ^ ((Fintype.card F - 1) / m) = 1 := by
  let s := (Fintype.card F - 1) / m
  have hs : 0 < s := stepanovPowerExponent_pos hmq
  have hms : m * s = Fintype.card F - 1 := Nat.mul_div_cancel' hmq
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by intro h; simp [h, hm.ne'] at ha
    rw [← pow_mul, hms]
    exact FiniteField.pow_card_sub_one_eq_one y hy
  · intro hapow
    have hq : 0 < Fintype.card F - 1 := by have := Fintype.one_lt_card (α := F); omega
    letI : NeZero (Fintype.card F - 1) := ⟨hq.ne'⟩
    obtain ⟨zeta, hzeta⟩ := exists_primitiveRoot_of_dvd_card_sub_one hq (dvd_refl _)
    obtain ⟨j, hj, hja⟩ := hzeta.eq_pow_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one a ha)
    have hjdiv : m ∣ j := by
      have hd : Fintype.card F - 1 ∣ j * s :=
        (hzeta.pow_eq_one_iff_dvd _).mp (by rw [pow_mul, hja]; exact hapow)
      rw [← hms] at hd
      exact Nat.dvd_of_mul_dvd_mul_right hs hd
    refine ⟨zeta ^ (j / m), ?_⟩
    rw [← pow_mul, Nat.div_mul_cancel hjdiv, hja]

theorem card_power_fiber_of_exists
    {m : ℕ} (hm : 0 < m) {zeta : F} (hzeta : IsPrimitiveRoot zeta m)
    {a : F} (ha : a ≠ 0) (hex : ∃ y : F, y ^ m = a) :
    (Finset.univ.filter (fun y : F => y ^ m = a)).card = m := by
  obtain ⟨alpha, halpha⟩ := hex
  have halpha0 : alpha ≠ 0 := by intro h; simp [h, hm.ne'] at halpha; exact ha halpha.symm
  have hset : Finset.univ.filter (fun y : F => y ^ m = a) =
      (Finset.range m).image (fun i => zeta ^ i * alpha) := by
    ext y
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [← Polynomial.mem_nthRoots hm, hzeta.nthRoots_eq halpha]
    simp
  rw [hset, Finset.card_image_of_injOn, Finset.card_range]
  exact hzeta.injOn_pow_mul halpha0

theorem card_power_fiber
    {m : ℕ} (hm : 0 < m) (hmq : m ∣ Fintype.card F - 1) (a : F) :
    (Finset.univ.filter (fun y : F => y ^ m = a)).card =
      (if a = 0 then 1 else 0) +
        (if a ^ ((Fintype.card F - 1) / m) = 1 then m else 0) := by
  have hs := stepanovPowerExponent_pos hmq
  by_cases ha : a = 0
  · simp [ha, pow_eq_zero_iff hm.ne', zero_pow hs.ne', Finset.filter_eq']
  · by_cases hp : a ^ ((Fintype.card F - 1) / m) = 1
    · obtain ⟨zeta, hzeta⟩ := exists_primitiveRoot_of_dvd_card_sub_one hm hmq
      simpa [ha, hp] using card_power_fiber_of_exists hm hzeta ha
        ((exists_pow_eq_iff_stepanovPower hm hmq ha).mpr hp)
    · have hnone : ¬ ∃ y : F, y ^ m = a :=
        fun h => hp ((exists_pow_eq_iff_stepanovPower hm hmq ha).mp h)
      have hzero : Finset.univ.filter (fun y : F => y ^ m = a) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact hnone ⟨y, (Finset.mem_filter.mp hy).2⟩
      simp [hzero, ha, hp]

/-- The number of pairs `(x,y)` over `F` with `y^m=f(x)`.-/
noncomputable def stepanovSolutionCount (m : ℕ) (f : Polynomial F) : ℕ :=
  (Finset.univ.filter (fun xy : F × F => xy.2 ^ m = eval xy.1 f)).card

theorem stepanovSolutionCount_eq_sum (m : ℕ) (f : Polynomial F) :
    stepanovSolutionCount m f =
      ∑ x : F, (Finset.univ.filter (fun y : F => y ^ m = eval x f)).card := by
  simp only [stepanovSolutionCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- The solution-count identity in Lemma 6.45, with no assumed fiber count.-/
theorem ln97_6_45_solutions {m : ℕ} (hm : 0 < m)
    (hmq : m ∣ Fintype.card F - 1) (f : Polynomial F) :
    stepanovSolutionCount m f = (stepanovT0 f).card + m * (stepanovT1 m f).card := by
  rw [stepanovSolutionCount_eq_sum]
  simp_rw [card_power_fiber hm hmq]
  simp [stepanovT0, stepanovT1, stepanovG, stepanovPowerExponent,
    Finset.sum_add_distrib, ← Finset.sum_filter, Nat.mul_comm]

end LN97
end MagicSquares
