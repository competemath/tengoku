/-
Vendored from `google-deepmind/debate` (Apache-2.0) via the Lean v4.31.0 port
`LukaHobor/debate` @ `dafe25d`, and migrated in place to Lean v4.33.0. Changed at
the header only; ledger and rationale: `vendor/debate/PROVENANCE.md`.
-/

module

public import Tengoku.Seed.Topology.Algebra.InfiniteSum.Basic
public import Tengoku.Seed.Topology.Instances.ENNReal.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/mbrcic/ai-safety-formalization-atlas@a65e32f80475, `AISafetyAtlas/Upstream/Debate/Misc/Finset.lean`: removed 7 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

@[expose] public section

-- Linters off per `vendor/debate/PROVENANCE.md`; no correctness linter is
-- touched and incomplete proofs stay errors.

/-!
`Finset` facts
-/

open Classical
open Option (some none)
open scoped Real NNReal
noncomputable section

variable {α β : Type}

/-- We can swap one set for another in `Finset.sum` if the function is zero off the intersection
@isnad1 id=eq.1h4v.s6.543fd3fa4aa6 from=translated src=- shape=72512049 vocab=fa4b94c3
-/
lemma Finset.sum_eq_sum_zero_off_inter {s0 s1 : Finset α} {g : α → ℝ}
    (h : ∀ x, x ∉ s0 ∨ x ∉ s1 → g x = 0) : s0.sum g = s1.sum g := by
  have e0 : s0.sum g = (s0 ∪ s1).sum g := by
    apply Finset.sum_subset_zero_on_sdiff (Finset.subset_union_left)
    · intro x m; apply h; left; rw [Finset.mem_sdiff] at m; exact m.2
    · simp only [Prod.mk.eta, implies_true, Prod.forall, forall_const]
  have e1 : s1.sum g = (s0 ∪ s1).sum g := by
    apply Finset.sum_subset_zero_on_sdiff (Finset.subset_union_right)
    · intro x m; apply h; right; rw [Finset.mem_sdiff] at m; exact m.2
    · simp only [Prod.mk.eta, implies_true, Prod.forall, forall_const]
  rw [e0, e1]

/-- Bound one `Finset.sum` by another on a different space, but injecting between the spaces
@isnad1 id=le.4h7v.s7.b6690bed9b37 from=translated src=- shape=e25b2d22 vocab=6f032d58
-/
lemma Finset.sum_le_sum_of_map {s : Finset α} {t : Finset β} {u : α → ℝ} {v : β → ℝ} (i : α → β)
    (inj : ∀ x0 x1, u x0 ≠ 0 → u x1 ≠ 0 → i x0 = i x1 → x0 = x1)
    (le : ∀ x, u x ≠ 0 → u x ≤ v (i x))
    (tv : ∀ y, y ∉ t → v y = 0)
    (v0 : ∀ y, y ∈ t → 0 ≤ v y) :
    s.sum u ≤ t.sum v := by
  rw [←Finset.sum_filter_ne_zero]
  set s' := s.filter (λ x ↦ u x ≠ 0)
  have e : t.sum v = (s'.image i).sum v + (t \ s'.image i).sum v := by
    rw [←Finset.sum_union disjoint_sdiff]; apply Finset.sum_subset_zero_on_sdiff
    · simp only [union_sdiff_self_eq_union, Finset.subset_union_right]
    · intro y m; simp only [union_sdiff_self_eq_union, mem_sdiff, mem_union] at m
      exact tv _ m.2
    · intro _ _; rfl
  rw [e]; clear e
  refine le_trans ?_ (le_add_of_nonneg_right ?_)
  · rw [Finset.sum_image]
    · apply Finset.sum_le_sum; intro x m; simp only [mem_filter, s'] at m; exact le _ m.2
    · intro x m y n; simp only [mem_coe, mem_filter, s'] at m n; apply inj _ _ m.2 n.2
  · apply Finset.sum_nonneg; intro y m
    simp only [mem_sdiff, not_exists, not_and] at m; exact v0 _ m.1

/-- `ENNReal.ofReal` commutes with `Finset.sum` for nonnegative maps
@isnad1 id=eq.1h3v.s5.914d053b0b23 from=translated src=- shape=36bce575 vocab=ed1b8848
-/
lemma Finset.sum_ofReal {s : Finset α} {f : α → ℝ} (f0 : ∀ x, 0 ≤ f x) :
    s.sum (fun x => ENNReal.ofReal (f x)) = .ofReal (s.sum f) := by
  lift f to α → ℝ≥0 using f0
  simp only [ENNReal.ofReal_coe_nnreal, ←ENNReal.coe_finset_sum, ←NNReal.coe_sum]

/-- `Finset.sum` of finite `ENNReals` is finite
@isnad1 id=ne.1h3v.s4.2dca6bc130fc from=translated src=- shape=99cc7c03 vocab=b2ce7be8
-/
lemma Finset.sum_ne_top {s : Finset α} {f : α → ENNReal} (ft : ∀ x, f x ≠ ⊤) : s.sum f ≠ ⊤ := by
  lift f to α → ℝ≥0 using ft
  simpa only [←ENNReal.coe_finset_sum] using ENNReal.coe_ne_top

/-- `ENNReal.ofReal` commutes with `Finset.sum` for finite maps
@isnad1 id=eq.1h3v.s5.5e4978eb8214 from=translated src=- shape=57c72645 vocab=6bf40094
-/
lemma Finset.sum_toReal {s : Finset α} {f : α → ENNReal} (ft : ∀ x, f x ≠ ⊤) :
    s.sum (fun x => ENNReal.toReal (f x)) = ENNReal.toReal (s.sum f) := by
  lift f to α → ℝ≥0 using ft
  simp only [←ENNReal.coe_finset_sum, ←NNReal.coe_sum, ENNReal.coe_toReal]

/-- `Finset` sums are the same as `HasSum` if the support is in the set
@isnad1 id=hassum.1h4v.s6.d4bb7ba3c045 from=translated src=- shape=a6a42bba vocab=775876c6
-/
lemma Finset.hasSum_sum [AddCommMonoid β] [TopologicalSpace β] {s : Finset α} {f : α → β}
    (h : ∀ x, x ∉ s → f x = 0) : HasSum f (s.sum f) := by
  exact hasSum_sum_of_ne_finset_zero h
