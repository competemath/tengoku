import Tengoku.Seed.Probability.Distributions.Uniform
import Tengoku.Seed.Probability.ProbabilityMassFunction.Integrals
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Oscillation
noncomputable section
open Finset MeasureTheory
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The normalized average on a finite set.-/
def finAvg (f : α → ℝ) : ℝ := (∑ x, f x) / Fintype.card α

/--
@isnad1 id=eq.1h3v.s5.c9c492f0f8f2 from=translated src=- shape=6f600fa3 vocab=f6e9f9fc
-/
lemma finAvg_congr {f g : α → ℝ} (h : ∀ x, f x = g x) : finAvg f = finAvg g := by
  unfold finAvg
  congr 1
  exact Finset.sum_congr rfl (fun x _ ↦ h x)

/--
@isnad1 id=eq.0h2v.s4.eaf4b0831db5 from=translated src=- shape=5addde91 vocab=9e429e05
-/
@[simp] lemma finAvg_const [Nonempty α] (c : ℝ) : finAvg (fun _ : α ↦ c) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finAvg, hc]

/--
@isnad1 id=eq.0h3v.s5.36600a631140 from=translated src=- shape=f9e647ab vocab=8d86f43b
-/
lemma finAvg_add (f g : α → ℝ) : finAvg (fun x ↦ f x + g x) = finAvg f + finAvg g := by
  simp [finAvg, Finset.sum_add_distrib, add_div]

/--
@isnad1 id=eq.0h3v.s5.334dadb2a52f from=translated src=- shape=f9e647ab vocab=9022c28a
-/
lemma finAvg_sub (f g : α → ℝ) : finAvg (fun x ↦ f x - g x) = finAvg f - finAvg g := by
  simp [finAvg, Finset.sum_sub_distrib, sub_div]

/--
@isnad1 id=eq.0h3v.s5.4922f39f8be5 from=translated src=- shape=d1a0213d vocab=d926da1e
-/
lemma finAvg_mul_const (f : α → ℝ) (c : ℝ) : finAvg (fun x ↦ f x * c) = finAvg f * c := by
  simp only [finAvg, ← Finset.sum_mul]
  ring

/--
@isnad1 id=eq.0h3v.s5.06b66861e268 from=translated src=- shape=adf02c15 vocab=d926da1e
-/
lemma finAvg_const_mul (c : ℝ) (f : α → ℝ) : finAvg (fun x ↦ c * f x) = c * finAvg f := by
  simp only [finAvg, ← Finset.mul_sum]
  ring

/--
@isnad1 id=le.1h3v.s5.7ea9d8bc09bc from=translated src=- shape=6f600fa3 vocab=a76fed6e
-/
lemma finAvg_mono {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : finAvg f ≤ finAvg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ ↦ h x)) (Nat.cast_nonneg _)

/--
@isnad1 id=le.1h2v.s5.29ddd6b2afdc from=translated src=- shape=92c325ac vocab=a76fed6e
-/
lemma finAvg_nonneg {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ finAvg f := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ ↦ h x)) (Nat.cast_nonneg _)

/--
@isnad1 id=le.0h2v.s5.44d3c65dc87e from=translated src=- shape=65f7e77c vocab=2db542f7
-/
lemma abs_finAvg_le (f : α → ℝ) : |finAvg f| ≤ finAvg (fun x ↦ |f x|) := by
  unfold finAvg
  have hc : |(Fintype.card α : ℝ)| = (Fintype.card α : ℝ) := abs_of_nonneg (by positivity)
  rw [abs_div, hc]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/--
@isnad1 id=le.1h4v.s6.407a0ae050e5 from=translated src=- shape=5f98d0bc vocab=479a315a
-/
lemma abs_finAvg_sub_le [Nonempty α] (f g : α → ℝ) {d : ℝ}
    (h : ∀ x, |f x - g x| ≤ d) : |finAvg f - finAvg g| ≤ d := by
  rw [← finAvg_sub]
  exact (abs_finAvg_le _).trans ((finAvg_mono h).trans_eq (finAvg_const d))

/--
@isnad1 id=eq.0h4v.s5.088128acdabe from=translated src=- shape=03577e2f vocab=ac75ab14
-/
lemma finAvg_equiv (e : α ≃ β) (f : β → ℝ) : finAvg (fun x ↦ f (e x)) = finAvg f := by
  rw [finAvg, finAvg, Fintype.card_congr e, e.sum_comp]

/--
@isnad1 id=eq.0h3v.s5.79f682db2dce from=translated src=- shape=fbfa7000 vocab=dde72c9d
-/
lemma finAvg_prod (f : α × β → ℝ) :
    finAvg f = finAvg (fun x : α ↦ finAvg (fun y : β ↦ f (x,y))) := by
  simp only [finAvg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

/--
@isnad1 id=eq.0h3v.s7.36b209f2f0b8 from=translated src=- shape=cbafc1c9 vocab=e8142db9
-/
lemma finAvg_pi_succ {n : ℕ} (f : (Fin (n + 1) → α) → ℝ) :
    finAvg f = finAvg (fun x : Fin n → α ↦ finAvg (fun y : α ↦ f (Fin.snoc x y))) := by
  let e : ((Fin n → α) × α) ≃ (Fin (n + 1) → α) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ α))
  rw [← finAvg_equiv e f, finAvg_prod]
  rfl

/--
@isnad1 id=eq.0h2v.s5.44228ca2d1e0 from=translated src=- shape=78f2c463 vocab=e6065dfa
-/
lemma integral_uniform_eq_finAvg [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → ℝ) : (∫ x, f x ∂(PMF.uniformOfFintype α).toMeasure) = finAvg f := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, finAvg]
  ring

/--
@isnad1 id=eq.0h4v.s5.aee193e7240a from=translated src=- shape=954eec4f vocab=89fe5d29
-/
lemma finAvg_sum {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) :
    finAvg (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, finAvg (f i) := by
  simp only [finAvg, ← Finset.sum_div]
  rw [Finset.sum_comm]

/--
@isnad1 id=eq.0h3v.s5.993d82727d1f from=translated src=- shape=d1a0213d vocab=1c5e99c7
-/
lemma finAvg_div_const (f : α → ℝ) (c : ℝ) :
    finAvg (fun x ↦ f x / c) = finAvg f / c := by
  simp only [finAvg, ← Finset.sum_div]
  ring

/--
@isnad1 id=eq.0h3v.s5.bdfc7512e7e4 from=translated src=- shape=503324de vocab=f6e9f9fc
-/
lemma finAvg_finAvg_comm (f : α → β → ℝ) :
    finAvg (fun x ↦ finAvg (f x)) = finAvg (fun y ↦ finAvg (fun x ↦ f x y)) := by
  simp only [finAvg, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

end
end Oscillation
