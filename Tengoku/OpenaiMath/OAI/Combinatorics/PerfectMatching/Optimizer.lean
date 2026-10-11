import Tengoku.OpenaiMath.OAI.Combinatorics.PerfectMatching.Entropy

namespace OAI

/-!
Support and first-order identities for entropy-maximizing matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Concavity of actual finite-law Shannon entropy. -/
theorem entropy_mix_ge {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  unfold entropy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
    (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)

/-- A zero probability gains a strict logarithmic bonus under mixing.
This is the boundary argument needed to obtain a positive entropy optimizer
on the entire face, not an assumed regularity of H. -/
theorem entropy_mix_zero_bonus {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) {j : ι} (hj : p j = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q + q j * Real.negMulLog t ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  classical
  have hterm : ∀ i, (1-t) * Real.negMulLog (p i) + t * Real.negMulLog (q i) +
      (if i=j then q j * Real.negMulLog t else 0) ≤
        Real.negMulLog ((1-t)*p i+t*q i) := by
    intro i
    by_cases hi : i=j
    · subst i
      simp only [hj, Real.negMulLog_zero, mul_zero, zero_add, ite_true,
        Real.negMulLog_mul]
      linarith
    · simp only [hi, ↓reduceIte, add_zero]
      simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
        (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, entropy] using hh

/-- Every entropy maximizer on a convex feasible set has maximal support. -/
theorem entropy_maximizer_support {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      entropy (fun i => (1-t)*p i+t*q i) ≤ entropy p) {j : ι} (hjq : 0 < q j) :
    0 < p j := by
  by_contra hj
  have hj0 : p j = 0 := le_antisymm (le_of_not_gt hj) (hp j)
  have hqp : entropy q ≤ entropy p := by simpa using hmax 1 (by constructor <;> norm_num)
  let c := (entropy p-entropy q)/(q j)+1
  have hc : 0 < c := by dsimp [c]; positivity
  let t := Real.exp (-c)
  have htp : 0 < t := Real.exp_pos _
  have ht : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨htp.le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hc.le)⟩
  have hbonus := (entropy_mix_zero_bonus hp hq hj0 ht).trans (hmax t ht)
  have hlog : Real.log t = -c := Real.log_exp _
  rw [Real.negMulLog, hlog] at hbonus
  have he : q j * c = entropy p-entropy q+q j := by
    dsimp [c]
    field_simp
  nlinarith

/-- Supporting-line inequality for -x log x, with no positivity assumption
on the comparison probability x. -/
theorem negMulLog_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x ≤ -x * Real.log y + y-x := by
  have h := mul_le_mul_of_nonneg_left
    (Real.negMulLog_le_one_sub_self (div_nonneg hx hy.le)) hy.le
  have he : Real.negMulLog x = -x * Real.log y + y * Real.negMulLog (x/y) := by
    calc
      Real.negMulLog x = Real.negMulLog (y * (x/y)) := by congr 1; field_simp
      _ = (x/y) * Real.negMulLog y + y * Real.negMulLog (x/y) := Real.negMulLog_mul _ _
      _ = _ := by unfold Real.negMulLog; field_simp
  rw [he]
  have hdiv : y * (x/y) = x := by field_simp
  nlinarith

/-- Gibbs' inequality on a finite set, with the exact support condition
needed on boundary faces. -/
theorem entropy_le_crossEntropy {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) :
    entropy q ≤ -∑ i, q i * Real.log (p i) := by
  have hterm : ∀ i, Real.negMulLog (q i) ≤
      -(q i * Real.log (p i)) + p i-q i := by
    intro i
    by_cases hi : p i = 0
    · simp [hi, hsupp i hi]
    · simpa only [neg_mul] using negMulLog_tangent (hq.1 i)
        (lt_of_le_of_ne (hp.1 i) (Ne.symm hi))
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, hp.2, hq.2, add_sub_cancel_right, entropy] using hh

/-- A finite nonnegative vector permits small positive motion in any direction
which does not point outwards at its zero coordinates. -/
theorem exists_pos_nonneg_perturb {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, p i = 0 → 0 ≤ v i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ p i+t*v i := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, p i ≠ 0 → 0 ≤ p i+t*v i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : p i = 0
    · exact Filter.Eventually.of_forall (fun _ h => (h hi).elim)
    · have hc : Continuous (fun t : ℝ => p i+t*v i) := by fun_prop
      have hh : {t : ℝ | 0 < p i+t*v i} ∈ 𝓝 0 :=
        (isOpen_lt continuous_const hc).mem_nhds
          (by simpa using lt_of_le_of_ne (hp i) (Ne.symm hi))
      exact Filter.Eventually.mono hh (fun t ht _ => ht.le)
  have he' := (hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioi 0)
  obtain ⟨t, ht, htp⟩ := he'.exists
  refine ⟨t, htp, fun i => ?_⟩
  by_cases hi : p i = 0
  · rw [hi, zero_add]
    exact mul_nonneg htp.le (hz i hi)
  · exact ht i hi

end MatchingEntropy

end

end OAI
