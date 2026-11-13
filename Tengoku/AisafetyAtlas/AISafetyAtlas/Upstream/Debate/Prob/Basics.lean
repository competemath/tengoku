/-
Vendored from `google-deepmind/debate` (Apache-2.0) via the Lean v4.31.0 port
`LukaHobor/debate` @ `dafe25d`, and migrated in place to Lean v4.33.0. Changed at
the header only; ledger and rationale: `vendor/debate/PROVENANCE.md`.
-/

module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.Debate.Prob.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/mbrcic/ai-safety-formalization-atlas@a65e32f80475, `AISafetyAtlas/Upstream/Debate/Prob/Basics.lean`: removed 7 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

@[expose] public section
namespace Tengoku.AisafetyAtlas end Tengoku.AisafetyAtlas open Tengoku.AisafetyAtlas 
-- Linters off per `vendor/debate/PROVENANCE.md`; no correctness linter is
-- touched and incomplete proofs stay errors.

/-!
## Basic properties of `Prob`
-/

open Classical
open Tengoku.AisafetyAtlas.Prob
open Set
open scoped Real
noncomputable section

variable {α β γ : Type}

namespace Tengoku.AisafetyAtlas.Prob

-- Monad details
/--
@isnad1 id=eq.0h2v.s4.c80f2a1ce716 from=translated src=- shape=6c2d59f2 vocab=951227a4
-/
lemma prob_pure' (x : α) : (pure x : Prob α).prob = Finsupp.single x 1 := rfl
/--
@isnad1 id=eq.0h4v.s6.b9f8073e64c8 from=translated src=- shape=e4884bcf vocab=55493400
-/
lemma prob_bind' (f : Prob α) (g : α → Prob β) :
    (f >>= g).prob = f.prob.sum (λ x p ↦ p • (g x).prob) := rfl

/-- (pure x).prob is the indicator function on {x}
@isnad1 id=eq.0h3v.s5.fc51a658a6da from=translated src=- shape=c6b76224 vocab=30114f87
-/
lemma prob_pure (x y : α) : (pure x : Prob α).prob y = if y = x then 1 else 0 := by
  simp only [Prob.prob, prob_pure', Finsupp.single_apply, eq_comm]

/-- pure.exp is function application
@isnad1 id=eq.0h3v.s4.eca14cd9d6b6 from=translated src=- shape=eb4cb607 vocab=da0107bc
-/
@[simp] lemma exp_pure (x : α) (f : α → ℝ) : (pure x : Prob α).exp f = f x := by
  simp only [exp, prob_pure', zero_mul, Finsupp.sum_single_index, one_mul]

-- Basic definitions
/--
@isnad1 id=eq.0h4v.s5.4fac9d1bf1dd from=translated src=- shape=028b0ccb vocab=fc4559f1
-/
lemma map_eq (f : α → β) (x : Prob α) : f <$> x = x >>= (λ x ↦ pure (f x)) := rfl
/--
@isnad1 id=eq.0h4v.s5.5646441dd167 from=translated src=- shape=0eabc8c1 vocab=7e7f41de
-/
lemma seq_eq (f : Prob (α → β)) (x : Prob α) : f <*> x = f >>= (λ f ↦ f <$> x) := rfl
/--
@isnad1 id=eq.0h4v.s5.5a069e048b7c from=translated src=- shape=d4a353c6 vocab=ba6a4ae6
-/
lemma seqLeft_eq (x : Prob α) (y : Prob β) : x <* y = x >>= (λ x ↦ y >>= λ _ ↦ pure x) := rfl
/--
@isnad1 id=eq.0h4v.s5.2a49d855dfc0 from=translated src=- shape=c77ad679 vocab=02102aad
-/
lemma seqRight_eq (x : Prob α) (y : Prob β) : x *> y = x >>= (λ _ ↦ y) := rfl

/-- (f >>= g).prob as an exp
@isnad1 id=eq.0h5v.s6.8ee546bb9275 from=translated src=- shape=251ddb48 vocab=303d74be
-/
lemma prob_bind (f : Prob α) (g : α → Prob β) (y : β) :
    (f >>= g).prob y = f.exp (λ x ↦ (g x).prob y) := by
  simp only [Prob.prob, prob_bind', Prob.exp, Finsupp.sum_apply]
  apply Finsupp.sum_congr; intro x _; rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]

/-- bind.exp is iterated exp
@isnad1 id=eq.0h5v.s5.1e9821c59157 from=translated src=- shape=0b292301 vocab=82d52a7d
-/
lemma exp_bind (f : Prob α) (g : α → Prob β) (h : β → ℝ) :
    (f >>= g).exp h = f.exp (λ x ↦ (g x).exp h) := by
  simp only [exp, prob_bind']; rw [Finsupp.sum_sum_index]
  · apply Finsupp.sum_congr; intro x _; rw [Finsupp.sum_smul_index]
    · simp only [mul_assoc, ←Finsupp.mul_sum]
    · intro _; simp only [zero_mul]
  · intro _; simp only [zero_mul]
  · intro _ _ _; simp only [add_mul]

-- Monad laws for Prob
/--
@isnad1 id=eq.0h2v.s4.4f572a8ffecb from=translated src=- shape=fce829fa vocab=65763526
-/
lemma left_id (f : Prob α) : f >>= pure = f := by
  ext x; simp only [prob_bind, prob_pure, exp, mul_ite, mul_one, mul_zero, Finsupp.sum_ite_eq,
    Finsupp.mem_support_iff, ne_eq, ite_not]
  split_ifs; exact Eq.symm (by assumption); rfl
/--
@isnad1 id=eq.0h4v.s5.870642b81c4c from=translated src=- shape=58c5ef62 vocab=65763526
-/
lemma right_id (x : α) (f : α → Prob β) : pure x >>= f = f x := by
  ext y; simp only [prob_bind, prob_pure, exp_pure]
/--
@isnad1 id=eq.0h6v.s5.899bf5c2d6c7 from=translated src=- shape=a67b27fb vocab=f6f62158
-/
lemma assoc (f : Prob α) (g : α → Prob β) (h : β → Prob γ) :
    f >>= g >>= h = f >>= (λ x ↦ g x >>= h) := by
  ext z; simp only [prob_bind, exp_bind, Finsupp.sum_apply]

/-- Prob is a lawful monad-/
instance : LawfulMonad Prob := LawfulMonad.mk'
  (id_map := by intro α x; simp only [map_eq, id, left_id])
  (pure_bind := by intro α β x f; simp only [right_id])
  (bind_assoc := assoc)

/-- Independent expectations can be reordered
@isnad1 id=eq.0h5v.s5.814059b839f3 from=translated src=- shape=0b4f1972 vocab=48b60f0c
-/
lemma exp_comm (f : Prob α) (g : Prob β) (h : α → β → ℝ) :
    f.exp (λ x ↦ g.exp (λ y ↦ h x y)) = g.exp (λ y ↦ f.exp (λ x ↦ h x y)) := by
  simp only [exp, Finsupp.mul_sum]; rw [Finsupp.sum_comm]
  apply Finsupp.sum_congr; intro _ _; apply Finsupp.sum_congr; intro _ _; ring

/-- Independent computations can be reordered
@isnad1 id=eq.0h6v.s6.72f9113be4df from=translated src=- shape=7054494f vocab=f6f62158
-/
lemma bind_comm (f : Prob α) (g : Prob β) (h : α → β → Prob γ) :
    f >>= (λ x ↦ g >>= (λ y ↦ h x y)) = g >>= (λ y ↦ f >>= (λ x ↦ h x y)) := by
  ext z; simp only [prob_bind]; rw [exp_comm]

/-- Variant of bind_comm when h's are not obviously equal
@isnad1 id=eq.1h7v.s6.9d1c722eab3b from=translated src=- shape=1fe2d7b3 vocab=f6f62158
-/
lemma bind_comm_of_eq (f : Prob α) (g : Prob β) (h0 h1 : α → β → Prob γ) (e : h0 = h1) :
    f >>= (λ x ↦ g >>= (λ y ↦ h0 x y)) = g >>= (λ y ↦ f >>= (λ x ↦ h1 x y)) := by
  rw [e]; apply bind_comm

/-- Constants are their own expectation
@isnad1 id=eq.0h3v.s4.933cc0502f71 from=translated src=- shape=3dff761c vocab=48b60f0c
-/
@[simp] lemma exp_const (f : Prob α) (x : ℝ) : f.exp (λ _ ↦ x) = x := by
  simp only [exp, ←Finsupp.sum_mul, Prob.total, one_mul]

/-- We can drop the left side of a bind if it's unused
@isnad1 id=eq.0h4v.s4.dc6da2ab33d3 from=translated src=- shape=f45cd95d vocab=f6f62158
-/
@[simp] lemma bind_const (f : Prob α) (g : Prob β) : f >>= (λ _ ↦ g) = g := by
  ext x; simp only [prob_bind, exp_const]

/-- Map of a constant is pure
@isnad1 id=eq.0h4v.s5.1be5c32578d1 from=translated src=- shape=a8345bb3 vocab=0e61f59a
-/
lemma map_const (y : β) (x : Prob α) : (λ _ ↦ y) <$> x = pure y := bind_const _ _

/-- map sums probabilities
@isnad1 id=eq.0h5v.s5.33b4373de636 from=translated src=- shape=8604933a vocab=c11c257e
-/
lemma prob_map (f : α → β) (x : Prob α) (z : β) : (f <$> x).prob z = x.pr (λ y ↦ f y = z) := by
  simp only [map_eq, prob_bind, pr, prob_pure, eq_comm]

/-- injective map preserves probabilities
@isnad1 id=eq.1h5v.s6.56214aa46545 from=translated src=- shape=f7d98543 vocab=f46ab8a8
-/
lemma map_prob_of_inj {f : α → β} (inj : f.Injective) (x : Prob α) (y : α) :
    (f <$> x).prob (f y) = x.prob y := by
  simp only [prob_map, pr, exp, Finsupp.sum]; rw [Finset.sum_eq_single y]
  · simp only [ite_true, mul_one, prob]
  · intro z m zy
    simp only [Finsupp.mem_support_iff, ne_eq] at m
    simp only [inj.ne zy, ite_false, mul_zero]
  · intro m
    simp only [Finsupp.mem_support_iff, ne_eq, not_not] at m
    simp only [m, ite_true, mul_one]

/-- prob is in [0,1]
@isnad1 id=le.0h3v.s5.01363b3c4e59 from=translated src=- shape=a496f28a vocab=59ac79b7
-/
lemma prob_le_one (f : Prob α) (x : α) : f.prob x ≤ 1 := by
  by_cases m : x ∈ f.supp
  · rw [←f.total, ←Finset.sum_singleton f.prob]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp only [supp, Finsupp.mem_support_iff, ne_eq] at m
      simp only [Finset.singleton_subset_iff, Finsupp.mem_support_iff, ne_eq, m, not_false_eq_true]
    · intro _ _ _; apply prob_nonneg
  · simp only [f.zero m, zero_le_one]
/--
@isnad1 id=mem.0h3v.s5.ed73d8ce4f30 from=translated src=- shape=7a52f9b3 vocab=bc91e46f
-/
lemma prob_mem_Icc (f : Prob α) (x : α) : f.prob x ∈ Icc 0 1 := ⟨prob_nonneg _, prob_le_one f x⟩

/-- Congruence for exp
@isnad1 id=eq.1h4v.s5.e387eb5dba4c from=translated src=- shape=879c68b2 vocab=29812e99
-/
lemma exp_congr {f : Prob α} {g h : α → ℝ} (e : ∀ x, f.prob x ≠ 0 → (g x = h x)) :
    f.exp g = f.exp h := by
  simp only [exp]; apply Finsupp.sum_congr; intro x m
  simp only [Finsupp.mem_support_iff] at m; simp only [e _ m]

/-- General congruence for exp, allowing the probabilities to be different
@isnad1 id=eq.1h5v.s6.6e93f2e00319 from=translated src=- shape=cb876c43 vocab=e8a51eab
-/
lemma exp_congr' {f g : Prob α} {u v : α → ℝ} (h : ∀ x, f.prob x * u x = g.prob x * v x) :
    f.exp u = g.exp v := by
  simp only [exp, Finsupp.sum]
  rw [Finset.sum_subset (Finset.subset_union_left (s₁ := f.prob.support) (s₂ := g.prob.support)),
    Finset.sum_subset (Finset.subset_union_right (s₁ := f.prob.support) (s₂ := g.prob.support))]
  · exact Finset.sum_congr rfl (λ _ _ ↦ h _)
  · intro x _ m; simp only [Finsupp.mem_support_iff, not_not] at m; simp only [m, zero_mul]
  · intro x _ m; simp only [Finsupp.mem_support_iff, not_not] at m; simp only [m, zero_mul]

/-- Congruence for pr
@isnad1 id=eq.1h4v.s5.74572c28843f from=translated src=- shape=44b26725 vocab=ff87cf3b
-/
lemma pr_congr {f : Prob α} {p q : α → Prop} (e : ∀ x, f.prob x ≠ 0 → (p x ↔ q x)) :
    f.pr p = f.pr q := by
  simp only [pr]; apply exp_congr; intro x m; simp only [eq_iff_iff.mpr (e x m)]

/-- bind_congr but restricted to support
@isnad1 id=eq.1h5v.s6.35990de26d0a from=translated src=- shape=bd217a1a vocab=5fe64cad
-/
lemma bind_congr (f : Prob α) (g h : α → Prob β) (e : ∀ x, f.prob x ≠ 0 → g x = h x) :
    f >>= g = f >>= h := by
  ext y; simp only [prob_bind]; apply exp_congr; intro x m
  simp only [e _ m]

/-- total for Fintypes
@isnad1 id=eq.0h2v.s5.b68e899cc7d5 from=translated src=- shape=620f35d3 vocab=13a4437b
-/
lemma fintype_total (f : Prob α) [Fintype α] : (Finset.univ : Finset α).sum f.prob = 1 := by
  rw [←Finset.sum_subset (Finset.subset_univ f.supp)]; exact f.total
  intro x _ m; simp only [mem_iff, not_not] at m; exact m

-- Boolean probabilities are complements
/--
@isnad1 id=eq.0h1v.s5.a9f7b1b3269e from=translated src=- shape=9ef7e9b0 vocab=a50be170
-/
lemma bool_total (f : Prob Bool) : f.prob true + f.prob false = 1 := by
  simpa only [Fintype.sum_bool] using f.fintype_total
/--
@isnad1 id=eq.0h1v.s5.0532fb39472d from=translated src=- shape=827fd48c vocab=61133945
-/
lemma bool_prob_false_of_true {f : Prob Bool} : f.prob false = 1 - f.prob true := by
  apply eq_sub_of_add_eq; rw [add_comm]; exact f.bool_total
/--
@isnad1 id=eq.0h1v.s5.35a653e29cfc from=translated src=- shape=827fd48c vocab=61133945
-/
lemma bool_prob_true_of_false {f : Prob Bool} : f.prob true = 1 - f.prob false :=
  eq_sub_of_add_eq f.bool_total
/--
@isnad1 id=eq.0h2v.s5.ca3729cac529 from=translated src=- shape=b4948bdd vocab=68a74a9c
-/
lemma not_bool_prob {f : Prob Bool} {x : Bool} : (not <$> f).prob x = f.prob (not x) := by
  rw [←Bool.not_not x, map_prob_of_inj, Bool.not_not]; rw [Bool.injective_iff]; simp

/-- Bound a prob bind in terms of an intermediate event
@isnad1 id=le.0h6v.s6.157e125d230f from=translated src=- shape=b473bc61 vocab=f92dc998
-/
lemma le_prob_bind_of_cut {f : Prob α} {g : α → Prob β} (x : α) {y : β} :
    f.prob x * (g x).prob y ≤ (f >>= g).prob y := by
  simp only [prob_bind]
  have p : ∀ x, 0 ≤ f.prob x * (g x).prob y := λ _ ↦ mul_nonneg (prob_nonneg _) (prob_nonneg _)
  by_cases m : x ∈ f.supp
  · exact Finset.single_le_sum (f := λ x ↦ f.prob x * (g x).prob y) (λ _ _ ↦ p _) m
  · simp only [mem_iff, not_not] at m
    simp only [m, zero_mul]
    exact Finset.sum_nonneg (λ _ _ ↦ p _)

end Tengoku.AisafetyAtlas.Prob
-- Tengoku: root names of this library moved to Tengoku.AisafetyAtlas so they do not collide with other libraries (generated)
