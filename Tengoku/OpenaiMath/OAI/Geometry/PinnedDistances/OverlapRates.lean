import Tengoku.OpenaiMath.OAI.Geometry.PinnedDistances.ArithmeticGraphs

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology

namespace WeakPinned

/-- The scalar limiting step for small overlap, with fixed positive τ and H. -/

theorem small_overlap_rate (n η U A D : ℕ → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hn : Tendsto n atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    (hη0 : ∀ j, 0 ≤ η j) (hU : ∀ j, 0 ≤ U j) (hA : ∀ j, 0 ≤ A j) (hD : ∀ j, 0 ≤ D j)
    (hbound : ∀ τ H : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ H → ∀ᶠ j in atTop,
      D j ≤ (2*(1/Real.log (n j))/τ^2+2*(1/Real.log (n j))/(θ-η j)+((θ+η j)/(θ-η j)-1))*U j +
        (2*τ/(θ-η j)+(2-2*((θ-η j)/(θ+η j/8))))*A j +
        4*(1/Real.log (n j))*H + 32*Real.exp (-H/2)) :
    Tendsto (fun j => D j/(U j+A j+1)) atTop (𝓝 0) := by
  have hlamT : Tendsto (fun j => 1/Real.log (n j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hn)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun j => ha.trans_le (div_nonneg (hD j) (by linarith [hU j,hA j]))
  · intro ε hε
    let τ := min 1 (ε*θ/16)
    have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
    have hτ1 : τ ≤ 1 := min_le_left _ _
    have hτb : 2*τ/θ ≤ ε/8 := by
      apply (div_le_iff₀ hθ).mpr
      have := min_le_right (1:ℝ) (ε*θ/16)
      dsimp [τ] at ⊢
      linarith
    have htExp : Tendsto (fun H : ℝ => 32*Real.exp (-H/2)) atTop (𝓝 0) := by
      have hd : Tendsto (fun H : ℝ => H/2) atTop atTop := by
        simpa only [div_eq_mul_inv, mul_comm, id_eq, one_mul] using
          (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<1/2)).mpr tendsto_id
      simpa only [Function.comp_def,neg_div,mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp hd).const_mul 32
    obtain ⟨H,hH,hHb⟩ := (eventually_ge_atTop (0:ℝ) |>.and (htExp.eventually (eventually_lt_nhds (show (0:ℝ)<ε/8 by linarith)))).exists
    let a := fun j => 2*(1/Real.log (n j))/τ^2+2*(1/Real.log (n j))/(θ-η j)+((θ+η j)/(θ-η j)-1)
    let b := fun j => 2*τ/(θ-η j)+(2-2*((θ-η j)/(θ+η j/8)))
    let e := fun j => 4*(1/Real.log (n j))*H+32*Real.exp (-H/2)
    have hθm : Tendsto (fun j => θ-η j) atTop (𝓝 θ) := by
      simpa using (tendsto_const_nhds (x:=θ)).sub hη
    have hθp : Tendsto (fun j => θ+η j) atTop (𝓝 θ) := by
      simpa using (tendsto_const_nhds (x:=θ)).add hη
    have hθp8 : Tendsto (fun j => θ+η j/8) atTop (𝓝 θ) := by
      simpa using (tendsto_const_nhds (x:=θ)).add (hη.div_const 8)
    have ha : Tendsto a atTop (𝓝 0) := by
      have ha1 : Tendsto (fun j => 2*(1/Real.log (n j))/τ^2) atTop (𝓝 0) := by
        simpa using (hlamT.const_mul 2).div_const (τ^2)
      have ha2 : Tendsto (fun j => 2*(1/Real.log (n j))/(θ-η j)) atTop (𝓝 0) := by
        convert (hlamT.const_mul 2).div hθm hθ.ne' using 1
        simp
        first
          | (all_goals grind; done)
          | (all_goals simp_all; done)
          | (all_goals aesop; done)
          | (all_goals omega; done)
          | (all_goals norm_num; done)
          | (all_goals positivity; done)
          | (all_goals linarith; done)
          | (all_goals decide; done)
          | (all_goals tauto; done)
      have ha3 : Tendsto (fun j => (θ+η j)/(θ-η j)-1) atTop (𝓝 0) := by
        simpa [hθ.ne',Pi.div_apply] using (hθp.div hθm hθ.ne').sub (tendsto_const_nhds (x:=1))
      simpa [a] using (ha1.add ha2).add ha3
    have hb : Tendsto b atTop (𝓝 (2*τ/θ)) := by
      have hb1 := (tendsto_const_nhds (x:=2*τ)).div hθm hθ.ne'
      have hb2 : Tendsto (fun j => 2-2*((θ-η j)/(θ+η j/8))) atTop (𝓝 0) := by
        simpa [hθ.ne',Pi.div_apply] using (tendsto_const_nhds (x:= (2:ℝ))).sub ((hθm.div hθp8 hθ.ne').const_mul 2)
      simpa [b,Pi.div_apply] using hb1.add hb2
    have he : Tendsto e atTop (𝓝 (32*Real.exp (-H/2))) := by
      simpa [e] using ((hlamT.const_mul 4).mul_const H).add (tendsto_const_nhds (x:=32*Real.exp (-H/2)))
    have hlt : 2*τ/θ+32*Real.exp (-H/2)<ε := by linarith
    have hsum := (ha.add hb |>.add he).eventually (eventually_lt_nhds (by simpa using hlt))
    filter_upwards [hbound τ H hτ hτ1 hH,hsum,hη.eventually (eventually_lt_nhds hθ),
      (Real.tendsto_log_atTop.comp hn).eventually (eventually_gt_atTop (0:ℝ))] with j hj hjlt hjη hjlog
    have ha0 : 0 ≤ a j := by
      have hr : 1 ≤ (θ+η j)/(θ-η j) := (one_le_div (sub_pos.mpr hjη)).mpr (by linarith [hη0 j])
      dsimp [a]
      positivity
    have hb0 : 0 ≤ b j := by
      have hr : (θ-η j)/(θ+η j/8) ≤ 1 := (div_le_one (by linarith [hη0 j] : 0<θ+η j/8)).mpr (by linarith [hη0 j])
      have hr0 : 0 ≤ 2-2*((θ-η j)/(θ+η j/8)) := by linarith
      dsimp [b]
      positivity
    have he0 : 0 ≤ e j := by dsimp [e]; positivity
    have hden : 0 < U j+A j+1 := by linarith [hU j,hA j]
    have hupper : D j ≤ (a j+b j+e j)*(U j+A j+1) := by
      have hj' : D j ≤ a j*U j+b j*A j+e j := by
        simpa only [a,b,e,add_assoc] using hj
      nlinarith only [hj',hU j,hA j,ha0,hb0,he0,mul_nonneg ha0 (hA j),mul_nonneg hb0 (hU j),mul_nonneg he0 (hU j),mul_nonneg he0 (hA j)]
    exact (div_le_iff₀ hden).mpr hupper |>.trans_lt hjlt
end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology
open Global
variable (V : ℕ → Type u1) (I : ℕ → Type u2) (K : ℕ → Type u3) [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

end WeakPinned

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance
variable {V : Type u4} {I : Type u5} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

def retainedWeight (T : ℝ) (y : V) : ℝ := if T≤((G.incoming y).card:ℝ) then G.incomingWeight y else 0

def retainedSet (T : ℝ) (y : V) : Finset V := if T≤((G.incoming y).card:ℝ) then G.incoming y else Finset.univ

omit [Fintype I] in
lemma retainedWeight_nonneg (T : ℝ) (y : V) : 0≤G.retainedWeight T y := by
  unfold retainedWeight incomingWeight edgeCount
  split_ifs <;> positivity

omit [Fintype I] in
lemma retainedWeight_le (T : ℝ) (y : V) : G.retainedWeight T y≤G.incomingWeight y := by
  unfold retainedWeight
  split_ifs
  · exact le_rfl
  · unfold incomingWeight edgeCount; positivity

omit [Fintype I] in
lemma sum_retainedWeight (T : ℝ) (hG : 0<G.edgeCount) : (∑ y, G.retainedWeight T y)≤1 := by
  rw [← G.sum_incomingWeight hG]
  exact Finset.sum_le_sum (fun y _ => G.retainedWeight_le T y)

omit [Fintype I] in
lemma retainedSet_size (T : ℝ) (hT : T≤Fintype.card V) (y : V) : T≤((G.retainedSet T y).card:ℝ) := by
  unfold retainedSet
  split_ifs with h
  · exact h
  · simpa using hT

omit [Fintype I] in
lemma retained_domination (T M : ℝ) (hdom : ∀ x y, G.edgeLaw x y≤M*pairProb Finset.univ x y)
    (hn : 2≤Fintype.card V) (x : V) :
    (∑ y, G.retainedWeight T y*prob (G.retainedSet T y) x)≤M*prob Finset.univ x := by
  refine le_trans (Finset.sum_le_sum (fun y _ => ?_)) (G.incoming_domination M hdom hn x)
  unfold retainedWeight retainedSet
  split_ifs
  · exact le_rfl
  · simp only [zero_mul]
    unfold incomingWeight edgeCount prob
    split_ifs <;> positivity
end WeakPinned.Core.Fibers

namespace WeakPinned
open Filter Variance Global
open scoped Topology BigOperators
variable {V : ℕ → Type u6} {I : ℕ → Type u7} {K : ℕ → Type u8} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

lemma PreparedGraph.uniform_domination {V : Type u9} {I : Type u10} [Fintype V] [Fintype I] [DecidableEq V]
    {G : Core.Fibers V I} {θ γ c η : ℝ} (h : PreparedGraph V I G θ γ c η) (hθ : 0<θ)
    (hη : η≤θ/2) (x y : V) : G.edgeLaw x y≤(2/θ)*pairProb Finset.univ x y := by
  have hh : η<θ := by linarith
  refine (h.edge_domination hh x y).trans (mul_le_mul_of_nonneg_right ?_ (by
    unfold pairProb
    split_ifs
    · have hn : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
      simp only [Finset.card_univ]
      exact div_nonneg (by norm_num) (mul_nonneg (by positivity) (by linarith))
    · exact le_rfl))
  apply (div_le_div_iff₀ (by linarith : 0<θ-η) hθ).mpr
  linarith

def fiberVariance (j : ℕ) : ℝ := weightedIntegral (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
  (varianceCell (G j).fiberWeight (G j).targets ((Fintype.card (V j):ℝ)^(1-c)))

def incomingVariance (j : ℕ) : ℝ := weightedIntegral (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
  (varianceCell ((G j).retainedWeight ((Fintype.card (V j):ℝ)^γ))
    ((G j).retainedSet ((Fintype.card (V j):ℝ)^γ)) ((Fintype.card (V j):ℝ)^(1-c)))

end WeakPinned

end
end
end
end
end
end
end
end
end

end OAI
