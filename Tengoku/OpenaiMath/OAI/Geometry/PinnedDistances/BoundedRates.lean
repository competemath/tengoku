import Tengoku.OpenaiMath.OAI.Geometry.PinnedDistances.NormalizedGraphs

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace WeakPinned.Bounded
open Hierarchy Global Variance NumberField

lemma bounded_denominator_rate (x w : ℕ → ℝ) (C : ℝ)
    (hx : ∀ n,0≤x n) (hw : ∀ n,0≤w n) (hC : ∀ n,w n≤C)
    (ht : Tendsto (fun n => x n/(w n+1)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  apply squeeze_zero hx _ (by simpa only [mul_zero] using tendsto_const_nhds.mul ht (a:=C+1))
  intro n
  have hp : 0<w n+1 := by linarith [hw n]
  calc
    x n = (w n+1)*(x n/(w n+1)) := by field_simp
    _ ≤ (C+1)*(x n/(w n+1)) :=
      mul_le_mul_of_nonneg_right (by linarith [hC n]) (div_nonneg (hx n) hp.le)

variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]

lemma massEval_add (q r : Finset P → ℝ) (d d' : Depth P) :
    massEval (fun C => q C+r C) d d'=massEval q d d'+massEval r d d' := by
  simp only [massEval,weightedIntegral,mul_add,Finset.sum_add_distrib]
  ring

omit [NumberField K] in
lemma archMean_mass_swap (Z₁ Z₂ : P → K) (q : Finset P → ℝ) (v : InfinitePlace K) :
    archMean Z₂ Z₁ (massEval q) v=archMean Z₁ Z₂ (massEval q) v := by
  unfold archMean
  congr 1
  funext ω
  exact add_comm _ _

omit [NumberField K] in
lemma archMean_scale_swap (Z₁ Z₂ : P → K) (v : InfinitePlace K) :
    archMean Z₂ Z₁ scaleEval v=archMean Z₁ Z₂ scaleEval v := by
  unfold archMean
  congr 1
  funext ω
  simp only [scaleEval,massEval,potentialEval]
  congr 1
  · exact add_comm _ _
  · apply Finset.sum_congr rfl
    intro x _
    rw [add_comm ((arch Z₂ v ω).potential x)]

omit [DecidableEq P] in
lemma weightedIntegral_add (m q r : Finset P → ℝ) :
    weightedIntegral m (fun C => q C+r C)=weightedIntegral m q+weightedIntegral m r := by
  simp only [weightedIntegral,mul_add,Finset.sum_add_distrib]

variable {V : ℕ → Type u3} {L : ℕ → Type u4} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)]
  [∀ n,Field (L n)] [∀ n,NumberField (L n)]

lemma power_fraction_rate (n : ℕ → ℝ) (hn : ∀ j,0<n j)
    (ht : Tendsto n atTop atTop) (c : ℝ) (hc : 0<c) :
    Tendsto (fun j => (n j)^(1-c)/n j) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop hc).comp ht
  convert hh using 1
  funext j
  rw [show 1-c=1+(-c) by ring,Real.rpow_add (hn j),Real.rpow_one]
  simp only [Function.comp_apply]
  exact mul_div_cancel_left₀ _ (hn j).ne'

end WeakPinned.Bounded

end
end

end OAI
