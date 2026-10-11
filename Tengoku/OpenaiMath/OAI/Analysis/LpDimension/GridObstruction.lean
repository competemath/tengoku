import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.Parallelogram

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
universe u uA uE uI uJ

namespace SubpolynomialLp

section Grid
variable {I : Type uI} [Fintype I] [DecidableEq I]

def rowVector (i : I) : I × I → ℝ := fun ab => if ab.1 = i then 1 else 0
def colVector (j : I) : I × I → ℝ := fun ab => if ab.2 = j then 1 else 0
abbrev GridIndex (I : Type uI) := Option ((I ⊕ I) × Bool)
def gridVector : GridIndex I → I × I → ℝ
  | none => 0
  | some (Sum.inl i, false) => rowVector i
  | some (Sum.inl i, true) => -rowVector i
  | some (Sum.inr j, false) => colVector j
  | some (Sum.inr j, true) => -colVector j

omit [Fintype I] in
lemma row_disjoint (i i' : I) (hne : i ≠ i') (ab : I × I) :
    rowVector i ab = 0 ∨ rowVector i' ab = 0 := by
  by_cases h : ab.1 = i
  · right
    simp [rowVector, h, hne]
  · left; simp [rowVector, h]

omit [Fintype I] in
lemma col_disjoint (j j' : I) (hne : j ≠ j') (ab : I × I) :
    colVector j ab = 0 ∨ colVector j' ab = 0 := by
  by_cases h : ab.2 = j
  · right
    simp [colVector, h, hne]
  · left; simp [colVector, h]

omit [Fintype I] in
lemma row_col_not_disjoint (i j : I) :
    ¬ (∀ ab, rowVector i ab = 0 ∨ colVector j ab = 0) := by
  intro h
  simpa [rowVector, colVector] using h (i,j)

lemma grid_dimension_obstruction {E : Type uE} [Fintype E] (p : ℝ)
    (hp : 1 < p) (hp2 : p ≠ 2) (f : GridIndex I → E → ℝ)
    (hf0 : f none = 0)
    (hf : ∀ i j, lpPower p (f i-f j) = lpPower p (gridVector i-gridVector j)) :
    (Fintype.card I)^2 ≤ Fintype.card E := by
  let r : I → E → ℝ := fun i => f (some (Sum.inl i, false))
  let c : I → E → ℝ := fun j => f (some (Sum.inr j, false))
  have hn (i : GridIndex I) : lpPower p (f i) = lpPower p (gridVector i) := by
    simpa only [hf0, gridVector, sub_zero] using hf i none
  have hneg (i : I ⊕ I) : gridVector (some (i,true)) = -gridVector (some (i,false)) := by
    cases i <;> rfl
  have hant (i : I ⊕ I) : f (some (i,true)) = -f (some (i,false)) := by
    apply antipodes_of_lpPower p hp
    · rw [hn, hn, hneg, lpPower_neg]
    · have hh := hf (some (i,false)) (some (i,true))
      have he : gridVector (some (i,false)) - gridVector (some (i,true)) =
          (2:ℝ) • gridVector (some (i,false)) := by
        rw [hneg]
        module
      rw [he, lpPower_smul, abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
      rw [hn]
      exact hh
  have hd (i j : I ⊕ I) :
      (∀ a, f (some (i,false)) a = 0 ∨ f (some (j,false)) a = 0) ↔
      (∀ a, gridVector (some (i,false)) a = 0 ∨ gridVector (some (j,false)) a = 0) := by
    rw [← lpPower_disjointness p (by linarith) hp2, ← lpPower_disjointness p (by linarith) hp2]
    have he : gridVector (some (j,true)) = -gridVector (some (j,false)) := by
      cases j <;> rfl
    have hs : lpPower p (f (some (i,false)) + f (some (j,false))) =
        lpPower p (gridVector (some (i,false)) + gridVector (some (j,false))) := by
      have hh := hf (some (i,false)) (some (j,true))
      simpa only [hant, he, sub_neg_eq_add] using hh
    rw [hs, hf, hn, hn]
  apply le_trans _ (disjoint_rows_columns_card r c ?_ ?_ ?_)
  · simp [sq]
  · intro i i' hh
    exact (hd (Sum.inl i) (Sum.inl i')).mpr (row_disjoint i i' hh)
  · intro j j' hh
    exact (hd (Sum.inr j) (Sum.inr j')).mpr (col_disjoint j j' hh)
  · intro i j
    have hh : ¬ (∀ a, r i a = 0 ∨ c j a = 0) := by
      intro ha
      exact row_col_not_disjoint i j ((hd (Sum.inl i) (Sum.inr j)).mp ha)
    push Not at hh
    exact hh

end Grid

section FiniteLp
variable {I : Type uI} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma finite_extend_card {A : Type uA} [Infinite A] (t : Finset A) (n : ℕ) (h : t.card ≤ n) :
    ∃ s : Finset A, t ⊆ s ∧ s.card = n := by
  classical
  obtain ⟨u, hu⟩ := Finset.exists_card_eq (α := A) n
  have hn : n ≤ (t ∪ u).card := hu.symm.trans_le (Finset.card_le_card Finset.subset_union_right)
  obtain ⟨s, hts, _, hs⟩ := Finset.exists_subsuperset_card_eq Finset.subset_union_left h hn
  exact ⟨s, hts, hs⟩

end FiniteLp

lemma GoodDimension.finite_family {p D : ℝ} {n d : ℕ} (h : GoodDimension.{u} p n D d)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [Infinite (Lp ℝ (ENNReal.ofReal p) μ)] {J : Type uJ} [Fintype J]
    (x : J → Lp ℝ (ENNReal.ofReal p) μ) (hJ : Fintype.card J ≤ n) :
    ∃ (y : J → Fin d → ℝ) (s : ℝ), 0 < s ∧
      ∀ i j, s * ‖x i-x j‖ ≤ coordinateDistance p (y i) (y j) ∧
        coordinateDistance p (y i) (y j) ≤ D*s*‖x i-x j‖ := by
  classical
  let t := Finset.univ.image x
  have ht : t.card ≤ n := (Finset.card_image_le).trans (by simpa using hJ)
  obtain ⟨S, hS, hc⟩ := finite_extend_card t n ht
  let e : S ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hc)
  let z : Fin n → Lp ℝ (ENNReal.ofReal p) μ := fun i => (e.symm i).val
  have hz : Function.Injective z := Subtype.val_injective.comp e.symm.injective
  obtain ⟨y, s, hs, hy⟩ := h Ω inferInstance μ z hz
  let j : J → S := fun i => ⟨x i, hS (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
  refine ⟨fun i => y (e (j i)), s, hs, ?_⟩
  intro a b
  simpa only [z, Equiv.symm_apply_apply, j] using hy (e (j a)) (e (j b))

lemma coordinateDistance_rpow (p : ℝ) (hp : 0 < p) {d : ℕ} (x y : Fin d → ℝ) :
    coordinateDistance p x y ^ p = lpPower p (x-y) := by
  unfold coordinateDistance
  rw [one_div, Real.rpow_inv_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)) hp.ne']
  rfl

end SubpolynomialLp

end

end OAI
