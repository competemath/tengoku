/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.RingTheory.PowerSeries.Restricted

/-!
# The Gauss norm of restricted power series

A restricted power series has finite Gauss norm. At a positive radius, a nonzero restricted
series has a last coefficient attaining that norm; the degree of that coefficient is the
*distinguished degree* of the series, and `IsDistinguished` names the property. Over a
nonarchimedean normed ring with multiplicative norm, a pair of distinguished degrees produces a
dominant coefficient in a product, and the Gauss norm is therefore multiplicative on restricted
series.

The distinguished degree is the datum Weierstrass division and preparation for Tate algebras are
organised around. No completeness hypothesis is needed for the norm identities here. The radius is
any positive real number, including the unit radius of the usual Tate algebra.

Completeness enters only at the end of the file, where a family of restricted series with
summable Gauss norms is summed coefficientwise. This is the convergence statement that
successive-approximation arguments over a complete nonarchimedean ring run on, and it takes the
place of completeness of the Tate algebra for the Gauss norm.

## Main definitions

* `TauCeti.PowerSeries.IsDistinguished`: the Gauss norm is attained in degree `s` and every later
  coefficient is strictly smaller.

## Main results

* `TauCeti.PowerSeries.gaussNorm_eq_of_forall_le`: the Gauss norm is attained at a degree whose
  weighted coefficient dominates.
* `TauCeti.PowerSeries.exists_isDistinguished`: at a positive radius, every nonzero restricted
  series is distinguished of some degree.
* `TauCeti.PowerSeries.IsDistinguished.unique`: of no more than one degree.
* `TauCeti.PowerSeries.IsDistinguished.trunc`,
  `TauCeti.PowerSeries.IsDistinguished.gaussNorm_trunc` and
  `TauCeti.PowerSeries.IsDistinguished.gaussNorm_sub_trunc_lt`: the polynomial part of a
  distinguished series is distinguished of the same degree and the same Gauss norm, and the
  tail it leaves is strictly smaller.
* `TauCeti.PowerSeries.IsDistinguished.norm_coeff_mul_mul_pow_eq_gaussNorm_mul`: the dominant
  coefficient of a product of distinguished series.
* `TauCeti.PowerSeries.gaussNorm_mul_of_isRestricted`: multiplicativity of the Gauss norm.
* `TauCeti.PowerSeries.summable_coeff_of_summable_gaussNorm` and
  `TauCeti.PowerSeries.isRestricted_mk_tsum_coeff`: over a complete ring, a family of restricted
  series with summable Gauss norms has summable coefficients, and its coefficientwise sum is
  again restricted.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.

The dominant-coefficient argument follows Mathlib's proof of `Polynomial.gaussNorm_mul`;
restrictedness replaces the finite-support argument for attaining the maximum. We use Mathlib's
`PowerSeries.IsRestricted` and `PowerSeries.gaussNorm` throughout.
-/

public section

namespace TauCeti.PowerSeries

open Filter
open scoped Topology

variable {R : Type*} [NormedRing R] {c : ℝ} {i j s t : ℕ} {f g : PowerSeries R}

/-- A restricted power series has bounded weighted coefficient norms. -/
theorem hasGaussNorm_of_isRestricted (hf : f.IsRestricted c) :
    f.HasGaussNorm norm c :=
  ((PowerSeries.isRestricted_iff c f).mp hf).bddAbove_range_of_cofinite

/-- If the weighted coefficient in degree `s` dominates every other one, the Gauss norm is the
value it takes there. -/
theorem gaussNorm_eq_of_forall_le {S : Type*} [Semiring S] {v : S → ℝ} {a : PowerSeries S}
    (h : ∀ m, v (a.coeff m) * c ^ m ≤ v (a.coeff s) * c ^ s) :
    a.gaussNorm v c = v (a.coeff s) * c ^ s :=
  le_antisymm ((PowerSeries.gaussNorm_eq v c a).trans_le (ciSup_le h))
    (PowerSeries.le_gaussNorm v c a ⟨_, Set.forall_mem_range.mpr h⟩ s)

section

variable (c) (s) (f)

/-- `f` is **distinguished of degree `s`** at the radius `c` when its Gauss norm at `c` is attained
in degree `s` and every later coefficient is strictly smaller.

At the unit radius this is a norm-theoretic analogue of the classical condition that the leading
coefficient of `f` dominates, in the sense of Bosch–Güntzer–Remmert §5.2. At a positive radius, a
nonzero restricted series is distinguished of exactly one degree
(`TauCeti.PowerSeries.exists_isDistinguished` and
`TauCeti.PowerSeries.IsDistinguished.unique`), so this is a genuine invariant of `f` and `c` rather
than extra data.

The first field is the univariate reading of Mathlib's `MvPowerSeries.AchievesGaussNorm`; the
second is what makes the degree unique and pins down the dominant coefficient of a product.

This is unrelated to `Polynomial.IsDistinguishedAt`, which asks a polynomial to be monic with its
remaining coefficients in an ideal. -/
structure IsDistinguished : Prop where
  /-- The Gauss norm is attained in degree `s`. -/
  norm_coeff_mul_pow_eq : ‖f.coeff s‖ * c ^ s = f.gaussNorm norm c
  /-- Every coefficient in a degree past `s` is strictly smaller. -/
  norm_coeff_mul_pow_lt : ∀ m, s < m → ‖f.coeff m‖ * c ^ m < f.gaussNorm norm c

end

/-- A distinguished series has positive Gauss norm, without any sign assumption on the radius. -/
theorem IsDistinguished.gaussNorm_pos (hf : IsDistinguished c s f) :
    0 < f.gaussNorm norm c := by
  have hpow : 0 ≤ c ^ (2 * (s + 1)) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg c) _
  exact lt_of_le_of_lt (mul_nonneg (norm_nonneg _) hpow)
    (hf.norm_coeff_mul_pow_lt (2 * (s + 1)) (by omega))

/-- A distinguished series is nonzero. -/
theorem IsDistinguished.ne_zero (hf : IsDistinguished c s f) : f ≠ 0 := by
  rintro rfl
  have h := hf.gaussNorm_pos
  rw [PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)] at h
  exact absurd h (lt_irrefl 0)

/-- The coefficient of a distinguished series in its distinguished degree is nonzero. -/
theorem IsDistinguished.coeff_ne_zero (hf : IsDistinguished c s f) : f.coeff s ≠ 0 := by
  intro h
  have hpos := hf.gaussNorm_pos
  rw [← hf.norm_coeff_mul_pow_eq, h] at hpos
  simp at hpos

/-- The weighted coefficient norms of a distinguished series are bounded above. -/
theorem IsDistinguished.hasGaussNorm (hf : IsDistinguished c s f) :
    f.HasGaussNorm norm c := by
  let a : ℕ → ℝ := fun n ↦ ‖f.coeff n‖ * c ^ n
  have hfinite : Set.Finite (a '' {n | n ≤ s}) := (Set.finite_le_nat s).image a
  obtain ⟨b, hb⟩ := hfinite.bddAbove
  refine ⟨max b (f.gaussNorm norm c), ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n ≤ s
  · exact (hb ⟨n, hn, rfl⟩).trans (le_max_left _ _)
  · exact (hf.norm_coeff_mul_pow_lt n (Nat.lt_of_not_ge hn)).le.trans (le_max_right _ _)

/-- The distinguished degree is unique: a series cannot be distinguished of two degrees at the
same radius. -/
theorem IsDistinguished.unique (hf : IsDistinguished c s f) (hf' : IsDistinguished c t f) :
    s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact absurd hf'.norm_coeff_mul_pow_eq (hf.norm_coeff_mul_pow_lt t h).ne
  · exact h
  · exact absurd hf.norm_coeff_mul_pow_eq (hf'.norm_coeff_mul_pow_lt s h).ne

/-- Every nonzero restricted series is distinguished of some degree: its last coefficient
attaining the Gauss norm supplies that degree. -/
theorem exists_isDistinguished (hc : 0 < c) (hf : f.IsRestricted c) (hf0 : f ≠ 0) :
    ∃ s : ℕ, IsDistinguished c s f := by
  classical
  have hex : ∃ i, f.coeff i ≠ 0 := by
    simpa only [not_forall] using (PowerSeries.forall_coeff_eq_zero f).not.mpr hf0
  obtain ⟨i, hi⟩ := hex
  let a : ℕ → ℝ := fun n ↦ ‖f.coeff n‖ * c ^ n
  have hi_pos : 0 < a i := mul_pos (norm_pos_iff.mpr hi) (pow_pos hc _)
  have hfinite : {n | a i ≤ a n}.Finite := by
    have h : ∀ᶠ n in cofinite, a n < a i :=
      ((PowerSeries.isRestricted_iff c f).mp hf).eventually (gt_mem_nhds hi_pos)
    simpa only [eventually_cofinite, not_lt] using h
  let S := hfinite.toFinset
  have hi_mem : i ∈ S := by simp [S]
  obtain ⟨k, hk, hmax⟩ := S.exists_max_image a ⟨i, hi_mem⟩
  have hbound (m : ℕ) : a m ≤ a k := by
    by_cases hm : m ∈ S
    · exact hmax m hm
    · have hm' : a m < a i := by simpa [S] using hm
      exact hm'.le.trans (hmax i hi_mem)
  have heq : a k = f.gaussNorm norm c := by
    rw [PowerSeries.gaussNorm_eq]
    exact (ciSup_eq_of_forall_le_of_forall_lt_exists_gt hbound fun _ h ↦ ⟨k, h⟩).symm
  let T := S.filter fun n ↦ a n = a k
  have hk_mem : k ∈ T := by simp [T, hk]
  obtain ⟨n, hn, hnmax⟩ := T.exists_max_image id ⟨k, hk_mem⟩
  have hn_eq : a n = a k := (Finset.mem_filter.mp hn).2
  refine ⟨n, hn_eq.trans heq, fun m hm ↦ ?_⟩
  rw [← heq]
  refine lt_of_le_of_ne (hbound m) fun h ↦ ?_
  have hm_mem : m ∈ T := by
    simp only [T, Finset.mem_filter]
    exact ⟨by simpa [S] using (hmax i hi_mem).trans_eq h.symm, h⟩
  exact (not_le_of_gt hm) (hnmax m hm_mem)

section Truncation

/-- Truncating a series just past a degree in which its Gauss norm is attained leaves that norm
unchanged. -/
@[simp] theorem IsDistinguished.gaussNorm_trunc (hf : IsDistinguished c s f) :
    ((f.trunc (s + 1) : Polynomial R) : PowerSeries R).gaussNorm norm c
      = f.gaussNorm norm c := by
  have hcoeff (m : ℕ) : ((f.trunc (s + 1) : Polynomial R) : PowerSeries R).coeff m =
      if m < s + 1 then f.coeff m else 0 := by
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  refine le_antisymm ?_ ?_
  · rw [PowerSeries.gaussNorm_eq]
    refine ciSup_le fun m ↦ ?_
    rw [hcoeff m]
    split_ifs
    · exact PowerSeries.le_gaussNorm norm c f hf.hasGaussNorm m
    · simpa using PowerSeries.gaussNorm_nonneg norm c f norm_nonneg
  · have hbdd : ((f.trunc (s + 1) : Polynomial R) : PowerSeries R).HasGaussNorm norm c :=
      hasGaussNorm_of_isRestricted (isRestricted_of_forall_coeff_eq_zero (n := s + 1)
        fun m hm ↦ by rw [hcoeff m, ite_eq_right (by omega)])
    have h := PowerSeries.le_gaussNorm norm c _ hbdd s
    rw [hcoeff s, ite_eq_left (Nat.lt_succ_self s)] at h
    exact le_of_eq_of_le hf.norm_coeff_mul_pow_eq.symm h

/-- The truncation of a distinguished series just past its distinguished degree is again
distinguished of that degree. It is the polynomial part `f⁻` a Weierstrass division divides by. -/
theorem IsDistinguished.trunc (hf : IsDistinguished c s f) :
    IsDistinguished c s ((f.trunc (s + 1) : Polynomial R) : PowerSeries R) := by
  have hcoeff (m : ℕ) : ((f.trunc (s + 1) : Polynomial R) : PowerSeries R).coeff m =
      if m < s + 1 then f.coeff m else 0 := by
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  refine ⟨?_, fun m hm ↦ ?_⟩
  · rw [hcoeff s, ite_eq_left (Nat.lt_succ_self s), hf.gaussNorm_trunc]
    exact hf.norm_coeff_mul_pow_eq
  · rw [hcoeff m, ite_eq_right (by omega), hf.gaussNorm_trunc]
    simpa using hf.gaussNorm_pos

/-- The tail `f⁺` left by truncating a restricted distinguished series just past its
distinguished degree has strictly smaller Gauss norm than the series itself. This is the
contraction factor of the Weierstrass division algorithm. -/
theorem IsDistinguished.gaussNorm_sub_trunc_lt (hf : IsDistinguished c s f) (hc : 0 < c)
    (hfr : f.IsRestricted c) :
    (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)).gaussNorm norm c
      < f.gaussNorm norm c := by
  have hcoeff (m : ℕ) : (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)).coeff m =
      if m < s + 1 then 0 else f.coeff m := by
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs <;> simp
  have htr : (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)).IsRestricted c := by
    rw [sub_eq_add_neg]
    exact PowerSeries.isRestricted.add c hfr (PowerSeries.isRestricted.neg c
      (isRestricted_of_forall_coeff_eq_zero (n := s + 1) fun m hm ↦ by
        rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_right (by omega)]))
  rcases eq_or_ne (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)) 0 with h0 | h0
  · rw [h0, PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
    exact hf.gaussNorm_pos
  · obtain ⟨n, hn⟩ := exists_isDistinguished hc htr h0
    have hns : s < n := by
      by_contra hcon
      exact hn.coeff_ne_zero (by rw [hcoeff n, ite_eq_left (by omega)])
    rw [← hn.norm_coeff_mul_pow_eq, hcoeff n, ite_eq_right (by omega)]
    exact hf.norm_coeff_mul_pow_lt n hns

end Truncation

variable [IsUltrametricDist R]

/-- The sum of two power series with bounded weighted coefficient norms again has bounded weighted
coefficient norms at a nonnegative radius. -/
theorem hasGaussNorm_add (hc : 0 ≤ c) (hf : f.HasGaussNorm norm c)
    (hg : g.HasGaussNorm norm c) : (f + g).HasGaussNorm norm c := by
  have key (m : ℕ) :
      ‖(f + g).coeff m‖ * c ^ m ≤ max (f.gaussNorm norm c) (g.gaussNorm norm c) := by
    rw [map_add]
    calc
      ‖f.coeff m + g.coeff m‖ * c ^ m ≤ max ‖f.coeff m‖ ‖g.coeff m‖ * c ^ m :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.isNonarchimedean_norm _ _) (pow_nonneg hc m)
      _ = max (‖f.coeff m‖ * c ^ m) (‖g.coeff m‖ * c ^ m) :=
        max_mul_of_nonneg _ _ (pow_nonneg hc m)
      _ ≤ max (f.gaussNorm norm c) (g.gaussNorm norm c) :=
        max_le_max (PowerSeries.le_gaussNorm norm c _ hf m)
          (PowerSeries.le_gaussNorm norm c _ hg m)
  exact ⟨_, Set.forall_mem_range.mpr key⟩

section Summation

variable [CompleteSpace R] {ι : Type*} {a : ι → PowerSeries R}

omit [IsUltrametricDist R] in
/-- Over a complete ring, a family of power series with summable Gauss norms has summable
coefficients in every degree. -/
theorem summable_coeff_of_summable_gaussNorm (hc : 0 < c)
    (ha : ∀ k, (a k).HasGaussNorm norm c)
    (hs : Summable fun k ↦ (a k).gaussNorm norm c) (i : ℕ) :
    Summable fun k ↦ (a k).coeff i := by
  refine Summable.of_norm_bounded (hs.mul_right (c ^ i)⁻¹) fun k ↦ ?_
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hc i)]
  exact PowerSeries.le_gaussNorm norm c _ (ha k) i

/-- **Coefficientwise summation of restricted power series.** Over a complete nonarchimedean
ring, the degreewise sums of a family of restricted power series with summable Gauss norms
assemble into a restricted power series.

This is the convergence statement behind successive-approximation arguments such as Weierstrass
division: it plays the role of completeness of the Tate algebra for the Gauss norm. -/
theorem isRestricted_mk_tsum_coeff (hc : 0 < c) (ha : ∀ k, (a k).IsRestricted c)
    (hs : Summable fun k ↦ (a k).gaussNorm norm c) :
    (PowerSeries.mk fun i ↦ ∑' k, (a k).coeff i).IsRestricted c := by
  classical
  have hsum := summable_coeff_of_summable_gaussNorm hc
    (fun k ↦ hasGaussNorm_of_isRestricted (ha k)) hs
  rw [PowerSeries.isRestricted_iff']
  refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun i ↦
    hb.trans_le (by positivity), fun ε hε ↦ ?_⟩
  have hsmall : {k | ¬(a k).gaussNorm norm c < ε / 2}.Finite :=
    Filter.eventually_cofinite.mp
      (hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (half_pos hε)))
  let S := hsmall.toFinset
  have hpartial : (∑ k ∈ S, a k).IsRestricted c :=
    sum_mem (S := PowerSeries.IsRestricted.addSubgroup c) fun k _ ↦ ha k
  filter_upwards [((PowerSeries.isRestricted_iff' c
    (∑ k ∈ S, a k)).mp hpartial).eventually
      (gt_mem_nhds (half_pos hε))] with i hi
  have hsplit : (PowerSeries.mk fun i ↦ ∑' k, (a k).coeff i).coeff i =
      (∑ k ∈ S, a k).coeff i + ∑' k : {k // k ∉ S}, (a k).coeff i := by
    rw [PowerSeries.coeff_mk, ← (hsum i).sum_add_tsum_subtype_compl S, map_sum]
  have htail : ‖∑' k : {k // k ∉ S}, (a k).coeff i‖ * c ^ i ≤ ε / 2 := by
    rw [← le_div_iff₀ (pow_pos hc i)]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
      (by positivity) fun k ↦ ?_
    rw [le_div_iff₀ (pow_pos hc i)]
    have hk : (a k).gaussNorm norm c < ε / 2 := by simpa [S] using k.property
    exact (PowerSeries.le_gaussNorm norm c _
      (hasGaussNorm_of_isRestricted (ha k)) i).trans hk.le
  rw [hsplit]
  calc ‖(∑ k ∈ S, a k).coeff i + ∑' k : {k // k ∉ S}, (a k).coeff i‖ * c ^ i
      ≤ max ‖(∑ k ∈ S, a k).coeff i‖ ‖∑' k : {k // k ∉ S}, (a k).coeff i‖ * c ^ i :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.isNonarchimedean_norm _ _)
          (pow_nonneg hc.le i)
    _ = max (‖(∑ k ∈ S, a k).coeff i‖ * c ^ i)
          (‖∑' k : {k // k ∉ S}, (a k).coeff i‖ * c ^ i) :=
        max_mul_of_nonneg _ _ (pow_nonneg hc.le i)
    _ < ε := max_lt (hi.trans (half_lt_self hε)) (htail.trans_lt (half_lt_self hε))

end Summation

variable [NormMulClass R]

end TauCeti.PowerSeries
