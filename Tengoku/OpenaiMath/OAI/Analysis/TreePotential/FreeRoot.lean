import Tengoku.OpenaiMath.OAI.Analysis.TreePotential.TreeObstruction

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace FreeRoot
open TreeCalculus
open scoped Classical

/-- Free scalar labels: the first field includes the root, but the second field
    only tests genuine child increments. No root label is set equal to zero. -/
structure IsFreePotential (b : Node → ℝ) : Prop where
  label_bound : ∀ s, |b s| ≤ 1
  child_budget : QuadraticBudget .sibling (increments b)

lemma isFreePotential_iff (b : Node → ℝ) :
    IsFreePotential b ↔ IsTreeTest true .sibling (increments b) := by
  constructor
  · intro h
    exact ⟨by simp, by simpa using h.label_bound, h.child_budget, trivial⟩
  · intro h
    exact ⟨by simpa using h.potential_bound, h.quadratic_budget⟩

def includeEdge : TreeCoordinate false ↪ TreeCoordinate true where
  toFun := fun s => ⟨s.val, Or.inl rfl⟩
  inj' := by intro s t h; exact Subtype.ext (congrArg (fun u : TreeCoordinate true => u.val) h)

@[simp] lemma includeEdge_apply (s : TreeCoordinate false) :
    includeEdge s = (⟨s.val, Or.inl rfl⟩ : TreeCoordinate true) := rfl

@[simp] lemma includeEdge_child (s : Node) (n : ℕ) :
    includeEdge (childCoordinate false s n) = childCoordinate true s n := rfl

/-- The defining free-root norm uses only genuine edges. It is a restriction of
    the rooted-sibling test family, NOT the anchored rootless sibling family. -/
def freeTestFamily : TestFamily (TreeCoordinate false) :=
  restrictedTestFamily (treeTestFamily true .sibling) includeEdge

/-- The free-root test and norm correspondence retains the existence of a free root value. -/

theorem mem_freeTestFamily_iff (f : TreeCoordinate false → ℝ) :
    f ∈ freeTestFamily.carrier ↔ ∃ b : Node → ℝ, IsFreePotential b ∧
      ∀ s : TreeCoordinate false, f s = b s.val - b s.val.dropLast := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨potential (liftCoefficients true g.val), ?_, ?_⟩
    · apply (isFreePotential_iff _).mpr
      have hfun : increments (potential (liftCoefficients true g.val)) = liftCoefficients true g.val :=
        funext (increments_potential _)
      rw [hfun]
      exact g.property
    · intro s
      have hs : s.val ≠ [] := by simpa using s.property
      have h := increments_potential (liftCoefficients true g.val) s.val
      rw [increments, ite_eq_right hs] at h
      exact h.symm.trans (by simp only [])
  · rintro ⟨b, hb, hf⟩
    have htest := (isFreePotential_iff b).mp hb
    refine ⟨asTreeTest (increments b) htest, ?_⟩
    funext s
    have hs : s.val ≠ [] := by simpa using s.property
    apply (hf s).trans
    change b s.val - b s.val.dropLast = increments b s.val
    simp only [increments, ite_eq_right hs]

abbrev Space := TestCompletion freeTestFamily

def rootedInclusion : Space →L[ℝ] TestCompletion (treeTestFamily true .sibling) :=
  restrictedCompletionInclusion (treeTestFamily true .sibling) includeEdge

lemma distinct_bound_le_common (t : ℝ) :
    (Real.sqrt (1+t^2/576)-1)/4 ≤ Real.sqrt (1+t^2/4)-1 := by
  have hsmall : 1 ≤ Real.sqrt (1+t^2/576) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [sq_nonneg t]
  have hbig : Real.sqrt (1+t^2/576) ≤ Real.sqrt (1+t^2/4) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
  linarith

lemma rootless_restricted_potential (g : treeTestFamily true .sibling) (s : Node) :
    potential (liftCoefficients false (g.val ∘ includeEdge)) s =
      potential (liftCoefficients true g.val) s - liftCoefficients true g.val [] := by
  induction s using List.reverseRecOn with
  | nil => simp [liftCoefficients]
  | append_singleton s n ih =>
    rw [potential_child, potential_child, ih]
    have hc : liftCoefficients false (g.val ∘ includeEdge) (s ++ [n]) =
        liftCoefficients true g.val (s ++ [n]) := by
      simp [liftCoefficients]
    rw [hc]
    ring

def path (s : Node) : Space :=
  ((testVectorEquiv freeTestFamily).symm (pathArray false s) : TestVector freeTestFamily)

def boundedTree (h : ℕ) (s : Tree h) : Space := path ([0] ++ s.val)

end FreeRoot

end BoundedTreePotentials

end

end OAI
