import Tengoku.ErdosLean.ErdosLean.Erdos956.Statement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #956 — Part 14: padding with far-away translates (note, end of §4)

A compact `C` is bounded; a new point at distance `> 2 sup ‖c‖` from all existing points gives a
disjoint translate.  Adding points never removes unit pairs.
-/

namespace Erdos956

/--
@isnad1 id=le.1h3v.s5.575c013eed45 from=translated src=- shape=c6e1ef6f vocab=093893e1
-/
lemma unitPairs_mono {C : Set E} {X Y : Finset E} (h : X ⊆ Y) :
    unitPairs C X ⊆ unitPairs C Y := by
  classical
  unfold unitPairs
  exact Finset.filter_subset_filter _ (Finset.sym2_mono h)

/--
@isnad1 id=ex.1h2v.s7.bb5fe73da921 from=translated src=- shape=98dba540 vocab=1c758ed8
-/
lemma altPadding_exists_far {C : Set E} {X : Finset E} (hX : Admissible C X) :
    ∃ y, y ∉ X ∧ Admissible C (insert y X) := by
  obtain ⟨hc, hconv, hne, hpw⟩ := hX
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).1 hc.isBounded
  have hS0 : 0 ≤ ∑ x ∈ X, ‖x‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set M : ℝ := ∑ x ∈ X, ‖x‖ + 2 * |R| + 1 with hMdef
  have hM0 : 0 ≤ M := by have := abs_nonneg R; linarith
  set y : E := EuclideanSpace.single 0 M with hydef
  have hy : ‖y‖ = M := by
    rw [hydef, PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg hM0]
  have hCn : ∀ c ∈ C, ‖c‖ ≤ |R| := by
    intro c hc'
    have := hR hc'
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_abs_self R)
  have hfar : ∀ x ∈ X, 2 * |R| < ‖y - x‖ := by
    intro x hx
    have h1 := norm_sub_norm_le y x
    have h2 : ‖x‖ ≤ ∑ x ∈ X, ‖x‖ :=
      Finset.single_le_sum (f := fun x => ‖x‖) (fun _ _ => norm_nonneg _) hx
    linarith
  have hdisj : ∀ x ∈ X, Disjoint (translate C y) (translate C x) := by
    intro x hx
    rw [Set.disjoint_left]
    rintro _ ⟨c, hc', rfl⟩ ⟨c', hc'', hEq⟩
    have hEq' : c' + x = c + y := hEq
    have hyx : y - x = c' - c := by
      calc y - x = (c + y) - (c + x) := by abel
        _ = (c' + x) - (c + x) := by rw [← hEq']
        _ = c' - c := by abel
    have h1 := norm_sub_le c' c
    have h2 := hCn c hc'
    have h3 := hCn c' hc''
    have h4 := hfar x hx
    rw [hyx] at h4
    linarith
  refine ⟨y, fun hyX => ?_, hc, hconv, hne, ?_⟩
  · have := hfar y hyX
    rw [sub_self, norm_zero] at this
    linarith [abs_nonneg R]
  · rw [Finset.coe_insert, Set.pairwise_insert]
    exact ⟨hpw, fun x hx _ => ⟨hdisj x hx, (hdisj x hx).symm⟩⟩

/--
@isnad1 id=ex.2h3v.s5.a5618647d08c from=translated src=- shape=94dd11d3 vocab=566f1923
-/
theorem exists_padding {C : Set E} {X : Finset E} (hX : Admissible C X) {n : ℕ}
    (hn : X.card ≤ n) : ∃ Y : Finset E, X ⊆ Y ∧ Y.card = n ∧ Admissible C Y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction d with
  | zero => exact ⟨X, subset_rfl, by simp, hX⟩
  | succ d ih =>
    obtain ⟨Y, hXY, hcard, hY⟩ := ih
    obtain ⟨y, hy, hY'⟩ := altPadding_exists_far hY
    refine ⟨insert y Y, hXY.trans (Finset.subset_insert _ _), ?_, hY'⟩
    rw [Finset.card_insert_of_notMem hy, hcard, Nat.add_assoc]

end Erdos956
