/-
Generic finite weighted-counting transfer.
STATUS: PATCHED AFTER USER COMPILER FEEDBACK; NOT RECOMPILED HERE.
No arithmetic/sieve assumptions are hidden in this general finite-set lemma.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

private theorem card_filter_eq_indicator_sum {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    ((s.filter P).card : ℝ) = ∑ a ∈ s, if P a then (1 : ℝ) else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp

/-- Count good points by an exceptional set plus a nonnegative weighted majorant.
@isnad1 id=le.3h6v.s7.d91ad2430c62 from=translated src=- shape=b39eb401 vocab=1e8548c6
-/
theorem count_le_exceptions_add_weight {α : Type*}
    (s e : Finset α) (P : α → Prop) [DecidablePred P] (w : α → ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hcover : ∀ a ∈ s, P a → a ∉ e → 1 ≤ K * w a) :
    ((s.filter P).card : ℝ) ≤ (e.card : ℝ) + K * ∑ a ∈ s, w a := by
  classical
  have hp : ∀ a ∈ s, (if P a then (1 : ℝ) else 0) ≤
      (if a ∈ e then (1 : ℝ) else 0) + K * w a := by
    intro a ha
    have hwK : 0 ≤ K * w a := mul_nonneg hK (hw a ha)
    by_cases hP : P a
    · by_cases he : a ∈ e
      · simp only [ite_eq_left hP, ite_eq_left he]
        linarith
      · simpa only [ite_eq_left hP, ite_eq_right he, zero_add] using hcover a ha hP he
    · by_cases he : a ∈ e
      · simp only [ite_eq_right hP, ite_eq_left he]
        linarith
      · simpa only [ite_eq_right hP, ite_eq_right he, zero_add] using hwK
  have hsub : s.filter (fun a => a ∈ e) ⊆ e := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hc : ((s.filter (fun a => a ∈ e)).card : ℝ) ≤ (e.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    ((s.filter P).card : ℝ) = ∑ a ∈ s, if P a then (1 : ℝ) else 0 :=
      card_filter_eq_indicator_sum s P
    _ ≤ ∑ a ∈ s, ((if a ∈ e then (1 : ℝ) else 0) + K * w a) :=
      Finset.sum_le_sum hp
    _ = ((s.filter (fun a => a ∈ e)).card : ℝ) + K * ∑ a ∈ s, w a := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← card_filter_eq_indicator_sum]
    _ ≤ (e.card : ℝ) + K * ∑ a ∈ s, w a := add_le_add hc le_rfl

/-- The exact exponential weight paid for a signed integral hit budget.
@isnad1 id=le.3h3v.s6.7698b5c3ac6d from=translated src=- shape=8ccf9529 vocab=5cdc8e5d
-/
theorem one_le_budget_weight (z : ℝ) (hz : 0 < z) (hz1 : z < 1)
    (B : ℤ) (k : ℕ) (hk : (k : ℤ) ≤ B) :
    1 ≤ Real.exp ((-Real.log z) * (B : ℝ)) * z ^ k := by
  have hp : ∀ q : ℕ, Real.exp ((q : ℝ) * Real.log z) = z ^ q := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.cast_add, Nat.cast_one, add_mul, Real.exp_add, ih, one_mul,
          Real.exp_log hz]
        rw [pow_succ]
  have hlog : Real.log z ≤ 0 := Real.log_nonpos hz.le hz1.le
  have hkR : (k : ℝ) ≤ (B : ℝ) := by exact_mod_cast hk
  have hnonneg : 0 ≤ (-Real.log z) * (B : ℝ) + (k : ℝ) * Real.log z := by
    have hmul := mul_le_mul_of_nonpos_right hkR hlog
    linarith
  rw [← hp k, ← Real.exp_add]
  simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hnonneg

end Erdos647Sieve
end
