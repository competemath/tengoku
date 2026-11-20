import Tengoku.Seed.Analysis.Convex.SpecificFunctions.Basic
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite majorization and the exponential case of Karamata's inequality

This file proves exactly the finite Karamata step used in the paper.  The
proof starts from decreasing rearrangements and their prefix-sum inequalities.
For the exponential function, its tangent inequality is summed and Abel's
summation-by-parts identity turns the majorization hypotheses into the desired
sum inequality.
-/

namespace HiaiLimPowerMeans

open Finset
open scoped BigOperators

/-- Extend a vector on `Fin n` by zero to a function on the natural numbers.-/
private def natAt {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then x ⟨i, hi⟩ else 0

/-- Sum of the first `k` entries of a finite vector.  Only values `k ≤ n`
occur in the definition of majorization.-/
def prefixSum {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, natAt x i

lemma prefixSum_card {n : ℕ} (x : Fin n → ℝ) :
    prefixSum x n = ∑ i, x i := by
  simpa [prefixSum, natAt] using (Finset.sum_fin_eq_sum_range x).symm

/-- When `k ≤ n`, the zero-extended prefix sum is the ordinary sum over
`Fin k`.-/
lemma prefixSum_eq_sum_fin {n : ℕ} (x : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) :
    prefixSum x k = ∑ i : Fin k, x (Fin.castLE hk i) := by
  rw [Finset.sum_fin_eq_sum_range]
  unfold prefixSum
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have hin : i < n := lt_of_lt_of_le hik hk
  simp [natAt, hik, hin]

/-- Finite vector majorization, expressed through decreasing rearrangements,
prefix-sum inequalities, and equality of the total sums.-/
def Majorized {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∃ leftPerm rightPerm : Equiv.Perm (Fin n),
    Antitone (fun i ↦ x (leftPerm i)) ∧
    Antitone (fun i ↦ y (rightPerm i)) ∧
    (∀ k, k ≤ n →
      prefixSum (fun i ↦ x (leftPerm i)) k ≤
        prefixSum (fun i ↦ y (rightPerm i)) k) ∧
    prefixSum (fun i ↦ x (leftPerm i)) n =
      prefixSum (fun i ↦ y (rightPerm i)) n

/-- Abel summation: decreasing coefficients paired with a sequence having
nonpositive prefix sums and total sum zero have nonpositive scalar product.-/
private lemma sum_range_mul_nonpos
    (n : ℕ) (c d : ℕ → ℝ)
    (hc : ∀ i, i + 1 < n → c (i + 1) ≤ c i)
    (hd : ∀ k, k ≤ n → ∑ i ∈ Finset.range k, d i ≤ 0)
    (htotal : ∑ i ∈ Finset.range n, d i = 0) :
    ∑ i ∈ Finset.range n, c i * d i ≤ 0 := by
  have hparts := Finset.sum_range_by_parts c d n
  have hnonneg :
      0 ≤ ∑ i ∈ Finset.range (n - 1),
        (c (i + 1) - c i) * ∑ j ∈ Finset.range (i + 1), d j := by
    apply Finset.sum_nonneg
    intro i hi
    have hin : i + 1 < n := by
      have hi' : i < n - 1 := Finset.mem_range.mp hi
      omega
    exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (hc i hin)) (hd (i + 1) (by omega))
  rw [show (∑ i ∈ Finset.range n, c i * d i) =
      ∑ i ∈ Finset.range n, c i • d i by simp [smul_eq_mul],
    hparts, htotal]
  simpa using neg_nonpos.mpr hnonneg

/-- Abel summation with only nonpositive prefix sums.  The extra
nonnegativity of the decreasing coefficients replaces the equality of the
total sums used in the majorization version above.-/
private lemma sum_range_mul_nonpos_weak
    (n : ℕ) (c d : ℕ → ℝ)
    (hc0 : ∀ i, i < n → 0 ≤ c i)
    (hc : ∀ i, i + 1 < n → c (i + 1) ≤ c i)
    (hd : ∀ k, k ≤ n → ∑ i ∈ Finset.range k, d i ≤ 0) :
    ∑ i ∈ Finset.range n, c i * d i ≤ 0 := by
  by_cases hn : n = 0
  · simp [hn]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hparts := Finset.sum_range_by_parts c d n
  have hnonneg :
      0 ≤ ∑ i ∈ Finset.range (n - 1),
        (c (i + 1) - c i) * ∑ j ∈ Finset.range (i + 1), d j := by
    apply Finset.sum_nonneg
    intro i hi
    have hin : i + 1 < n := by
      have hi' : i < n - 1 := Finset.mem_range.mp hi
      omega
    exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (hc i hin)) (hd (i + 1) (by omega))
  have hfirst :
      c (n - 1) * ∑ i ∈ Finset.range n, d i ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (hc0 (n - 1) (by omega)) (hd n le_rfl)
  rw [show (∑ i ∈ Finset.range n, c i * d i) =
      ∑ i ∈ Finset.range n, c i • d i by simp [smul_eq_mul], hparts]
  simp only [smul_eq_mul]
  linarith

/-- The tangent inequality for the exponential function in the form used by
the finite Karamata proof.-/
private lemma exp_sub_exp_le_tangent (t a b : ℝ) :
    Real.exp (t * a) - Real.exp (t * b) ≤
      (t * Real.exp (t * a)) * (a - b) := by
  have hmul :
      Real.exp (t * a) * (t * (b - a) + 1) ≤ Real.exp (t * b) := by
    calc
      Real.exp (t * a) * (t * (b - a) + 1) ≤
          Real.exp (t * a) * Real.exp (t * (b - a)) :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
      _ = Real.exp (t * b) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    Real.exp (t * a) - Real.exp (t * b) ≤
        Real.exp (t * a) -
          Real.exp (t * a) * (t * (b - a) + 1) :=
      sub_le_sub_left hmul _
    _ = (t * Real.exp (t * a)) * (a - b) := by ring

/-- Karamata's inequality for the exponential function, proved directly from
the finite prefix-sum definition for vectors already in decreasing order.-/
theorem sum_exp_le_sum_exp_of_antitone
    {n : ℕ} {x y : Fin n → ℝ}
    (hx : Antitone x) (_hy : Antitone y)
    (hprefix : ∀ k, k ≤ n → prefixSum x k ≤ prefixSum y k)
    (htotal : prefixSum x n = prefixSum y n)
    {t : ℝ} (ht : 0 < t) :
    (∑ i, Real.exp (t * x i)) ≤ ∑ i, Real.exp (t * y i) := by
  let c : ℕ → ℝ := fun i ↦ t * Real.exp (t * natAt x i)
  let d : ℕ → ℝ := fun i ↦ natAt x i - natAt y i
  have hc : ∀ i, i + 1 < n → c (i + 1) ≤ c i := by
    intro i hi
    have hxi : x ⟨i + 1, hi⟩ ≤ x ⟨i, by omega⟩ :=
      hx (by simp only [Fin.mk_le_mk]; omega)
    have hexp : Real.exp (t * x ⟨i + 1, hi⟩) ≤
        Real.exp (t * x ⟨i, by omega⟩) :=
      Real.exp_monotone (mul_le_mul_of_nonneg_left hxi ht.le)
    simpa [c, natAt, hi, show i < n by omega] using
      mul_le_mul_of_nonneg_left hexp ht.le
  have hd : ∀ k, k ≤ n → ∑ i ∈ Finset.range k, d i ≤ 0 := by
    intro k hk
    have hle := hprefix k hk
    rw [prefixSum, prefixSum] at hle
    simpa [d, Finset.sum_sub_distrib] using sub_nonpos.mpr hle
  have hdtotal : ∑ i ∈ Finset.range n, d i = 0 := by
    rw [show (∑ i ∈ Finset.range n, d i) = prefixSum x n - prefixSum y n by
      simp [d, prefixSum, Finset.sum_sub_distrib]]
    exact sub_eq_zero.mpr htotal
  have hweighted : ∑ i ∈ Finset.range n, c i * d i ≤ 0 :=
    sum_range_mul_nonpos n c d hc hd hdtotal
  have hpoint : ∀ i : Fin n,
      Real.exp (t * x i) - Real.exp (t * y i) ≤
        (t * Real.exp (t * x i)) * (x i - y i) :=
    fun i ↦ exp_sub_exp_le_tangent t (x i) (y i)
  have hsum :
      (∑ i, (Real.exp (t * x i) - Real.exp (t * y i))) ≤
        ∑ i, (t * Real.exp (t * x i)) * (x i - y i) :=
    Finset.sum_le_sum fun i _ ↦ hpoint i
  have hright :
      (∑ i, (t * Real.exp (t * x i)) * (x i - y i)) =
        ∑ i ∈ Finset.range n, c i * d i := by
    calc
      (∑ i, (t * Real.exp (t * x i)) * (x i - y i)) =
          ∑ i ∈ Finset.range n, if hi : i < n then
            (t * Real.exp (t * x ⟨i, hi⟩)) * (x ⟨i, hi⟩ - y ⟨i, hi⟩)
          else 0 := Finset.sum_fin_eq_sum_range _
      _ = ∑ i ∈ Finset.range n, c i * d i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        simp [c, d, natAt, hin]
  rw [hright] at hsum
  have hdiff :
      (∑ i, Real.exp (t * x i)) - (∑ i, Real.exp (t * y i)) ≤ 0 := by
    rw [← Finset.sum_sub_distrib]
    exact hsum.trans hweighted
  exact sub_nonpos.mp hdiff

/-- The increasing-convex exponential consequence of weak majorization for
vectors already in decreasing order.-/
theorem sum_exp_le_sum_exp_of_antitone_weak
    {n : ℕ} {x y : Fin n → ℝ}
    (hx : Antitone x) (_hy : Antitone y)
    (hprefix : ∀ k, k ≤ n → prefixSum x k ≤ prefixSum y k)
    {t : ℝ} (ht : 0 < t) :
    (∑ i, Real.exp (t * x i)) ≤ ∑ i, Real.exp (t * y i) := by
  let c : ℕ → ℝ := fun i ↦ t * Real.exp (t * natAt x i)
  let d : ℕ → ℝ := fun i ↦ natAt x i - natAt y i
  have hc0 : ∀ i, i < n → 0 ≤ c i := by
    intro i hi
    exact mul_nonneg ht.le (Real.exp_pos _).le
  have hc : ∀ i, i + 1 < n → c (i + 1) ≤ c i := by
    intro i hi
    have hxi : x ⟨i + 1, hi⟩ ≤ x ⟨i, by omega⟩ :=
      hx (by simp only [Fin.mk_le_mk]; omega)
    have hexp : Real.exp (t * x ⟨i + 1, hi⟩) ≤
        Real.exp (t * x ⟨i, by omega⟩) :=
      Real.exp_monotone (mul_le_mul_of_nonneg_left hxi ht.le)
    simpa [c, natAt, hi, show i < n by omega] using
      mul_le_mul_of_nonneg_left hexp ht.le
  have hd : ∀ k, k ≤ n → ∑ i ∈ Finset.range k, d i ≤ 0 := by
    intro k hk
    have hle := hprefix k hk
    rw [prefixSum, prefixSum] at hle
    simpa [d, Finset.sum_sub_distrib] using sub_nonpos.mpr hle
  have hweighted : ∑ i ∈ Finset.range n, c i * d i ≤ 0 :=
    sum_range_mul_nonpos_weak n c d hc0 hc hd
  have hpoint : ∀ i : Fin n,
      Real.exp (t * x i) - Real.exp (t * y i) ≤
        (t * Real.exp (t * x i)) * (x i - y i) :=
    fun i ↦ exp_sub_exp_le_tangent t (x i) (y i)
  have hsum :
      (∑ i, (Real.exp (t * x i) - Real.exp (t * y i))) ≤
        ∑ i, (t * Real.exp (t * x i)) * (x i - y i) :=
    Finset.sum_le_sum fun i _ ↦ hpoint i
  have hright :
      (∑ i, (t * Real.exp (t * x i)) * (x i - y i)) =
        ∑ i ∈ Finset.range n, c i * d i := by
    calc
      (∑ i, (t * Real.exp (t * x i)) * (x i - y i)) =
          ∑ i ∈ Finset.range n, if hi : i < n then
            (t * Real.exp (t * x ⟨i, hi⟩)) * (x ⟨i, hi⟩ - y ⟨i, hi⟩)
          else 0 := Finset.sum_fin_eq_sum_range _
      _ = ∑ i ∈ Finset.range n, c i * d i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        simp [c, d, natAt, hin]
  rw [hright] at hsum
  have hdiff :
      (∑ i, Real.exp (t * x i)) - (∑ i, Real.exp (t * y i)) ≤ 0 := by
    rw [← Finset.sum_sub_distrib]
    exact hsum.trans hweighted
  exact sub_nonpos.mp hdiff

/-- A version of the preceding theorem whose prefix hypotheses are stated as
sums over the corresponding `Fin k`.-/
theorem sum_exp_le_sum_exp_of_fin_prefix
    {n : ℕ} {x y : Fin n → ℝ}
    (hx : Antitone x) (hy : Antitone y)
    (hprefix : ∀ (k : ℕ) (hk : k ≤ n),
      (∑ i : Fin k, x (Fin.castLE hk i)) ≤
        ∑ i : Fin k, y (Fin.castLE hk i))
    {t : ℝ} (ht : 0 < t) :
    (∑ i, Real.exp (t * x i)) ≤ ∑ i, Real.exp (t * y i) := by
  apply sum_exp_le_sum_exp_of_antitone_weak hx hy _ ht
  intro k hk
  rw [prefixSum_eq_sum_fin x k hk, prefixSum_eq_sum_fin y k hk]
  exact hprefix k hk

/-- The exponential instance of finite Karamata's inequality.-/
theorem Majorized.sum_exp_le_sum_exp
    {n : ℕ} {x y : Fin n → ℝ} (h : Majorized x y)
    {t : ℝ} (ht : 0 < t) :
    (∑ i, Real.exp (t * x i)) ≤ ∑ i, Real.exp (t * y i) := by
  obtain ⟨leftPerm, rightPerm, hleft, hright, hprefix, htotal⟩ := h
  have hs := sum_exp_le_sum_exp_of_antitone
    hleft hright hprefix htotal ht
  calc
    (∑ i, Real.exp (t * x i)) =
        ∑ i, Real.exp (t * x (leftPerm i)) :=
      (Equiv.sum_comp leftPerm (fun a ↦ Real.exp (t * x a))).symm
    _ ≤ ∑ i, Real.exp (t * y (rightPerm i)) := hs
    _ = ∑ i, Real.exp (t * y i) :=
      Equiv.sum_comp rightPerm (fun a ↦ Real.exp (t * y a))

end HiaiLimPowerMeans
