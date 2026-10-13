/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Local

/-!
# Expected counts for the Gaussian layout

Adjacent kernel rows have correlation at least `ρ₀`, so a threshold separates the scores
of an edge's endpoints with probability at most `crossBound ρ₀`. A unit score lies in a
window of width `δ` with probability at most `δ / √(2π)`, and beyond `±T` with
probability at most `1 / T²`. Counts of events are written as sums of indicators.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory

/-- The crossing-probability bound for edges whose kernel correlation is at least `ρ₀`. -/
noncomputable def crossBound (ρ₀ : ℝ) : ℝ :=
  2 / Real.pi * (Real.sqrt (1 - ρ₀) / Real.sqrt (1 + ρ₀))

/--
@isnad1 id=eq.0h3v.s7.733d6b961edb from=translated src=- shape=e2c87bb4 vocab=e27ceb7c
-/
theorem sum_add_sq {ι : Type} [Fintype ι] (α β : ι → ℝ) :
    ∑ i, (α i + β i) ^ 2 = ∑ i, α i ^ 2 + 2 * ∑ i, α i * β i + ∑ i, β i ^ 2 := by
  simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/--
@isnad1 id=eq.0h3v.s7.ddcb2f09cf23 from=translated src=- shape=0d4d62ab vocab=0f15ecb8
-/
theorem sum_sub_sq {ι : Type} [Fintype ι] (α β : ι → ℝ) :
    ∑ i, (β i - α i) ^ 2 = ∑ i, α i ^ 2 - 2 * ∑ i, α i * β i + ∑ i, β i ^ 2 := by
  have : ∀ i, (β i - α i) ^ 2 = α i ^ 2 - 2 * (α i * β i) + β i ^ 2 := fun i => by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Two unit coefficient vectors with correlation at least `ρ₀ > -1` cross a threshold
with probability at most `crossBound ρ₀`.
@isnad1 id=le.4h5v.s7.7a3186709e06 from=translated src=- shape=03c41686 vocab=1f63aab4
-/
theorem gaussPi_between_le_crossBound {ι : Type} [Fintype ι] {α β : ι → ℝ}
    (hα : ∑ i, α i ^ 2 = 1) (hβ : ∑ i, β i ^ 2 = 1) {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀)
    (hρ : ρ₀ ≤ ∑ i, α i * β i) (t : ℝ) :
    (gaussPi ι).real {ω | Between t (form α ω) (form β ω)} ≤ crossBound ρ₀ := by
  set ρ := ∑ i, α i * β i
  have hplus : ∑ i, (α i + β i) ^ 2 = 2 * (1 + ρ) := by rw [sum_add_sq, hα, hβ]; ring
  have hminus : ∑ i, (β i - α i) ^ 2 = 2 * (1 - ρ) := by rw [sum_sub_sq, hα, hβ]; ring
  have hpos : 0 < 1 + ρ := by linarith
  refine (gaussPi_between_le α β (by rw [hα, hβ]) (by rw [hplus]; positivity) t).trans ?_
  rw [hplus, hminus, Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num),
    mul_div_mul_left _ _ (by positivity)]
  unfold crossBound
  gcongr
  all_goals exact Real.sqrt_pos.mpr (by linarith)

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

omit [DecidableEq W] in
/--
@isnad1 id=le.5h7v.s8.a050c0038408 from=translated src=- shape=7717e07b vocab=30ece1ae
-/
theorem measureReal_crossEvent_le (degree : ∀ v, H.degree v ≤ 3) {q : ℝ} (hq0 : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) {e : Sym2 W}
    (he : e ∈ H.edgeFinset) : (gaussPi W).real (crossEvent H q R t e) ≤ crossBound ρ₀ := by
  induction e using Sym2.ind with
  | _ u v =>
  have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
  exact gaussPi_between_le_crossBound (sum_unitKernel_sq H q R u) (sum_unitKernel_sq H q R v)
    hρ₀ (hρ.trans (sum_unitKernel_mul_ge H degree hq0 R huv)) t

/-- The event that a score lies in the window `[s, s + δ)`. -/
def windowEvent (q : ℝ) (R : ℕ) (s δ : ℝ) (v : W) : Set (W → ℝ) :=
  scoreEvent H q R (fun x => s ≤ x ∧ x < s + δ) v

omit [DecidableEq W] [DecidableRel H.Adj] in
/--
@isnad1 id=le.1h7v.s6.cb093b065705 from=translated src=- shape=86dc649d vocab=1dfe887f
-/
theorem measureReal_windowEvent_le (q : ℝ) (R : ℕ) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (v : W) :
    (gaussPi W).real (windowEvent H q R s δ v) ≤ δ / Real.sqrt (2 * Real.pi) :=
  gaussPi_window_le _ (sum_unitKernel_sq H q R v) s hδ

omit [DecidableEq W] [DecidableRel H.Adj] in
/--
@isnad1 id=le.1h6v.s6.9d385a0e0c72 from=translated src=- shape=75295fad vocab=c8933e55
-/
theorem measureReal_lowEvent_le (q : ℝ) (R : ℕ) {T : ℝ} (hT : 0 < T) (v : W) :
    (gaussPi W).real (scoreEvent H q R (fun x => x < -T) v) ≤ 1 / T ^ 2 := by
  refine (measureReal_mono ?_).trans (gaussPi_tail_le _ (sum_unitKernel_sq H q R v) hT)
  intro ω hω
  simp only [scoreEvent, score, Set.mem_ofPred_eq] at hω ⊢
  rw [abs_of_neg (by linarith)]
  linarith

omit [DecidableEq W] [DecidableRel H.Adj] in
/--
@isnad1 id=le.1h6v.s6.336fde99cdd8 from=translated src=- shape=52949545 vocab=16ebb3ad
-/
theorem measureReal_highEvent_le (q : ℝ) (R : ℕ) {T : ℝ} (hT : 0 < T) (v : W) :
    (gaussPi W).real (scoreEvent H q R (fun x => T ≤ x) v) ≤ 1 / T ^ 2 := by
  refine (measureReal_mono ?_).trans (gaussPi_tail_le _ (sum_unitKernel_sq H q R v) hT)
  intro ω hω
  simp only [scoreEvent, score, Set.mem_ofPred_eq] at hω ⊢
  exact hω.trans (le_abs_self _)

omit [DecidableRel H.Adj] [DecidableEq W] in
/-- The cut of a threshold set counts the crossing events of the edges.
@isnad1 id=eq.0h6v.s6.898b9a27a876 from=translated src=- shape=50a77ac9 vocab=494afd44
-/
theorem card_cutFinset_eq_sum_indicator (q : ℝ) (R : ℕ) (t : ℝ) (ω : W → ℝ)
    [Fintype H.edgeSet] :
    ((H.cutFinset (Finset.univ.filter fun v => score H q R ω v < t)).card : ℝ) =
      ∑ e ∈ H.edgeFinset, (crossEvent H q R t e).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  have hset : H.cutFinset (Finset.univ.filter fun v => score H q R ω v < t) =
      H.edgeFinset.filter fun e => ω ∈ crossEvent H q R t e := by
    ext e
    rw [mem_cutFinset_filter_lt_iff, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    rfl
  rw [hset, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : ω ∈ crossEvent H q R t e <;> simp [h]

omit [DecidableEq W] [DecidableRel H.Adj] in
/-- A count of score events is the sum of their indicators.
@isnad1 id=eq.0h6v.s6.bba52a25e6d8 from=translated src=- shape=01a80603 vocab=7cfa5e0e
-/
theorem card_filter_eq_sum_indicator (q : ℝ) (R : ℕ) (p : ℝ → Prop) [DecidablePred p]
    (ω : W → ℝ) :
    ((Finset.univ.filter fun v => p (score H q R ω v)).card : ℝ) =
      ∑ v, (scoreEvent H q R p v).indicator (fun _ => (1 : ℝ)) ω := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : p (score H q R ω v) <;> simp [scoreEvent, h]

end Algebraic.Cutwidth.Gaussian.Internal
