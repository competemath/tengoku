/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.EffrosOperations
import Tengoku.Seed.Analysis.Convex.Join
import Tengoku.Seed.Analysis.Convex.Topology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Effros measurability of closed convex hulls

For compact-valued correspondences in a separable Banach space, we build the
convex hull by iterating the binary convex join.  Every finite stage remains
compact and Effros measurable.  The increasing union of the stages is the
convex hull, and its closure is therefore the closed convex hull.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory TopologicalSpace
open scoped Topology Pointwise

noncomputable section

namespace RandomSetTheory

/-! ## General closure properties of Effros measurability -/

/-- A countable union of Effros-measurable correspondences is Effros
measurable.-/
theorem effrosMeasurable_iUnion
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    {S : ℕ → Ω → Set X} (hS : ∀ n, RandomSet.IsEffrosMeasurable (S n)) :
    RandomSet.IsEffrosMeasurable (fun ω => ⋃ n, S n ω) := by
  intro U hU
  have hEq :
      {ω | ((⋃ n, S n ω) ∩ U).Nonempty} =
        ⋃ n, {ω | (S n ω ∩ U).Nonempty} := by
    ext ω
    constructor
    · rintro ⟨x, hx, hxU⟩
      rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
      exact Set.mem_iUnion.mpr ⟨n, x, hxn, hxU⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨n, x, hxn, hxU⟩
      exact ⟨x, Set.mem_iUnion.mpr ⟨n, hxn⟩, hxU⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun n => hS n U hU

/-- Taking the pointwise topological closure preserves Effros measurability.
This does not require the original fibres to be closed.-/
theorem effrosMeasurable_closure
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S) :
    RandomSet.IsEffrosMeasurable (fun ω => closure (S ω)) := by
  intro U hU
  have hEq :
      {ω | (closure (S ω) ∩ U).Nonempty} =
        {ω | (S ω ∩ U).Nonempty} := by
    ext ω
    exact closure_inter_open_nonempty_iff hU
  rw [hEq]
  exact hS U hU

/-! ## Binary convex joins -/

/-- The jointly continuous parametrization of a segment.-/
def convexJoinMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × E) × ℝ → E :=
  fun p => AffineMap.lineMap p.1.1 p.1.2 p.2

theorem continuous_convexJoinMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (convexJoinMap : (E × E) × ℝ → E) := by
  unfold convexJoinMap
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

/-- A convex join is the continuous image of a product with the unit
interval.-/
theorem convexJoin_eq_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Set E) :
    convexJoin ℝ A B =
      convexJoinMap '' ((A ×ˢ B) ×ˢ Icc (0 : ℝ) 1) := by
  ext z
  constructor
  · rw [mem_convexJoin]
    rintro ⟨x, hx, y, hy, hz⟩
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, rfl⟩
    exact ⟨((x, y), t), ⟨⟨hx, hy⟩, ht⟩, rfl⟩
  · rintro ⟨⟨⟨x, y⟩, t⟩, ⟨⟨hx, hy⟩, ht⟩, rfl⟩
    rw [mem_convexJoin]
    exact ⟨x, hx, y, hy, lineMap_mem_segment ℝ x y ht⟩

/-- The convex join of two compact sets is compact.-/
theorem isCompact_convexJoin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : Set E} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact (convexJoin ℝ A B) := by
  rw [convexJoin_eq_image]
  exact ((hA.prod hB).prod isCompact_Icc).image continuous_convexJoinMap

/-- Convex join preserves nonemptiness.-/
theorem nonempty_convexJoin
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty) :
    (convexJoin ℝ A B).Nonempty := by
  rcases hA with ⟨x, hx⟩
  rcases hB with ⟨y, hy⟩
  exact ⟨x, segment_subset_convexJoin hx hy (left_mem_segment ℝ x y)⟩

/-- Convex join preserves Effros measurability for nonempty closed-valued
correspondences.-/
theorem effrosMeasurable_convexJoin_of_closed
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {S T : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hSclosed : ∀ ω, IsClosed (S ω))
    (hTclosed : ∀ ω, IsClosed (T ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    (hTne : ∀ ω, (T ω).Nonempty) :
    RandomSet.IsEffrosMeasurable (fun ω => convexJoin ℝ (S ω) (T ω)) := by
  let P : Ω → Set ((E × E) × ℝ) := fun ω =>
    ((S ω ×ˢ T ω) ×ˢ Icc (0 : ℝ) 1)
  have hST : RandomSet.IsEffrosMeasurable (fun ω => S ω ×ˢ T ω) :=
    hS.prod hT hSclosed hTclosed hSne hTne
  have hP : RandomSet.IsEffrosMeasurable P :=
    hST.prod (RandomSet.isEffrosMeasurable_const (Icc (0 : ℝ) 1))
      (fun ω => (hSclosed ω).prod (hTclosed ω))
      (fun _ => isClosed_Icc)
      (fun ω => (hSne ω).prod (hTne ω))
      (fun _ => nonempty_Icc.2 zero_le_one)
  have himage := hP.image continuous_convexJoinMap
  apply himage.congr
  intro ω
  exact (convexJoin_eq_image (S ω) (T ω)).symm

/-- Compact-valued specialization of
`effrosMeasurable_convexJoin_of_closed`.-/
theorem effrosMeasurable_convexJoin
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {S T : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    (hTne : ∀ ω, (T ω).Nonempty) :
    RandomSet.IsEffrosMeasurable (fun ω => convexJoin ℝ (S ω) (T ω)) :=
  effrosMeasurable_convexJoin_of_closed hS hT
    (fun ω => (hScompact ω).isClosed)
    (fun ω => (hTcompact ω).isClosed) hSne hTne

/-! ## Iterated joins and the convex hull -/

/-- The `n`-th binary-convexification stage.-/
def convexJoinIterate {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Set E) : ℕ → Set E
  | 0 => S
  | n + 1 => convexJoin ℝ (convexJoinIterate S n) (convexJoinIterate S n)

@[simp] theorem convexJoinIterate_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) :
    convexJoinIterate S 0 = S := rfl

@[simp] theorem convexJoinIterate_succ
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Set E) (n : ℕ) :
    convexJoinIterate S (n + 1) =
      convexJoin ℝ (convexJoinIterate S n) (convexJoinIterate S n) := rfl

theorem convexJoinIterate_nonempty
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (hS : S.Nonempty) :
    ∀ n, (convexJoinIterate S n).Nonempty := by
  intro n
  induction n with
  | zero => exact hS
  | succ n ih => exact nonempty_convexJoin ih ih

theorem convexJoinIterate_mono_nat
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (hS : S.Nonempty) {m n : ℕ} (hmn : m ≤ n) :
    convexJoinIterate S m ⊆ convexJoinIterate S n := by
  induction n with
  | zero =>
      have : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact Subset.rfl
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · exact (ih hmn').trans
          (subset_convexJoin_left (convexJoinIterate_nonempty hS n))
      · have hm : m = n + 1 := by omega
        subst m
        exact Subset.rfl

theorem convexJoinIterate_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : IsCompact S) :
    ∀ n, IsCompact (convexJoinIterate S n) := by
  intro n
  induction n with
  | zero => exact hS
  | succ n ih => exact isCompact_convexJoin ih ih

theorem convexJoinIterate_subset_convex
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S C : Set E} (hSC : S ⊆ C) (hC : Convex ℝ C) :
    ∀ n, convexJoinIterate S n ⊆ C := by
  intro n
  induction n with
  | zero => exact hSC
  | succ n ih => exact convexJoin_subset ih ih hC

/-- The union of all binary-convexification stages is exactly the convex
hull.-/
theorem iUnion_convexJoinIterate_eq_convexHull
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (hS : S.Nonempty) :
    (⋃ n, convexJoinIterate S n) = convexHull ℝ S := by
  apply Subset.antisymm
  · exact iUnion_subset (convexJoinIterate_subset_convex
      (subset_convexHull ℝ S) (convex_convexHull ℝ S))
  · apply convexHull_min
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩
    · rw [convex_iff_segment_subset]
      intro x hx y hy z hz
      rcases mem_iUnion.mp hx with ⟨m, hxm⟩
      rcases mem_iUnion.mp hy with ⟨n, hyn⟩
      let k := max m n
      have hxk : x ∈ convexJoinIterate S k :=
        convexJoinIterate_mono_nat hS (Nat.le_max_left m n) hxm
      have hyk : y ∈ convexJoinIterate S k :=
        convexJoinIterate_mono_nat hS (Nat.le_max_right m n) hyn
      exact mem_iUnion.mpr ⟨k + 1, segment_subset_convexJoin hxk hyk hz⟩

theorem closure_iUnion_convexJoinIterate_eq_closedConvexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : S.Nonempty) :
    closure (⋃ n, convexJoinIterate S n) = closedConvexHull ℝ S := by
  rw [iUnion_convexJoinIterate_eq_convexHull hS,
    ← closedConvexHull_eq_closure_convexHull]

/-! ## Closed iterated joins

Closing every stage lets the construction start from arbitrary closed fibres;
compactness is no longer needed. -/

/-- The `n`-th closed binary-convexification stage.-/
def closedConvexJoinIterate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : Set E) : ℕ → Set E
  | 0 => S
  | n + 1 => closure
      (convexJoin ℝ (closedConvexJoinIterate S n)
        (closedConvexJoinIterate S n))

@[simp] theorem closedConvexJoinIterate_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Set E) :
    closedConvexJoinIterate S 0 = S := rfl

@[simp] theorem closedConvexJoinIterate_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (n : ℕ) :
    closedConvexJoinIterate S (n + 1) = closure
      (convexJoin ℝ (closedConvexJoinIterate S n)
        (closedConvexJoinIterate S n)) := rfl

theorem closedConvexJoinIterate_nonempty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : S.Nonempty) :
    ∀ n, (closedConvexJoinIterate S n).Nonempty := by
  intro n
  induction n with
  | zero => exact hS
  | succ n ih => exact (nonempty_convexJoin ih ih).closure

theorem closedConvexJoinIterate_isClosed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : IsClosed S) :
    ∀ n, IsClosed (closedConvexJoinIterate S n) := by
  intro n
  induction n with
  | zero => exact hS
  | succ _ _ => exact isClosed_closure

theorem closedConvexJoinIterate_mono_nat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : S.Nonempty) {m n : ℕ} (hmn : m ≤ n) :
    closedConvexJoinIterate S m ⊆ closedConvexJoinIterate S n := by
  induction n with
  | zero =>
      have : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact Subset.rfl
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · exact (ih hmn').trans
          ((subset_convexJoin_left
            (closedConvexJoinIterate_nonempty hS n)).trans subset_closure)
      · have hm : m = n + 1 := by omega
        subst m
        exact Subset.rfl

theorem closedConvexJoinIterate_subset_closedConvex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S C : Set E} (hSC : S ⊆ C) (hCconvex : Convex ℝ C)
    (hCclosed : IsClosed C) :
    ∀ n, closedConvexJoinIterate S n ⊆ C := by
  intro n
  induction n with
  | zero => exact hSC
  | succ n ih =>
      exact closure_minimal (convexJoin_subset ih ih hCconvex) hCclosed

theorem convex_iUnion_closedConvexJoinIterate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : S.Nonempty) :
    Convex ℝ (⋃ n, closedConvexJoinIterate S n) := by
  rw [convex_iff_segment_subset]
  intro x hx y hy z hz
  rcases Set.mem_iUnion.mp hx with ⟨m, hxm⟩
  rcases Set.mem_iUnion.mp hy with ⟨n, hyn⟩
  let k := max m n
  have hxk : x ∈ closedConvexJoinIterate S k :=
    closedConvexJoinIterate_mono_nat hS (Nat.le_max_left m n) hxm
  have hyk : y ∈ closedConvexJoinIterate S k :=
    closedConvexJoinIterate_mono_nat hS (Nat.le_max_right m n) hyn
  exact Set.mem_iUnion.mpr ⟨k + 1,
    subset_closure (segment_subset_convexJoin hxk hyk hz)⟩

/-- The closure of the increasing union of closed binary joins is the closed
convex hull.-/
theorem closure_iUnion_closedConvexJoinIterate_eq_closedConvexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : S.Nonempty) :
    closure (⋃ n, closedConvexJoinIterate S n) =
      closedConvexHull ℝ S := by
  apply Subset.antisymm
  · apply closure_minimal
    · exact iUnion_subset (closedConvexJoinIterate_subset_closedConvex
        (subset_closedConvexHull (𝕜 := ℝ)) convex_closedConvexHull
        isClosed_closedConvexHull)
    · exact isClosed_closedConvexHull
  · apply closedConvexHull_min
    · intro x hx
      exact subset_closure (Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩)
    · exact (convex_iUnion_closedConvexJoinIterate hS).closure
    · exact isClosed_closure

/-- Every binary-convexification stage of a nonempty compact-valued Effros
correspondence is again Effros measurable.-/
theorem effrosMeasurable_convexJoinIterate
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {S : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty) :
    ∀ n, RandomSet.IsEffrosMeasurable
      (fun ω => convexJoinIterate (S ω) n) := by
  intro n
  induction n with
  | zero => simpa using hS
  | succ n ih =>
      exact effrosMeasurable_convexJoin ih ih
        (fun ω => convexJoinIterate_compact (hScompact ω) n)
        (fun ω => convexJoinIterate_compact (hScompact ω) n)
        (fun ω => convexJoinIterate_nonempty (hSne ω) n)
        (fun ω => convexJoinIterate_nonempty (hSne ω) n)

/-- Every closed binary-convexification stage of a nonempty closed-valued
Effros correspondence is Effros measurable.-/
theorem effrosMeasurable_closedConvexJoinIterate
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {S : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hSclosed : ∀ ω, IsClosed (S ω))
    (hSne : ∀ ω, (S ω).Nonempty) :
    ∀ n, RandomSet.IsEffrosMeasurable
      (fun ω => closedConvexJoinIterate (S ω) n) := by
  intro n
  induction n with
  | zero => simpa using hS
  | succ n ih =>
      have hJoin := effrosMeasurable_convexJoin_of_closed ih ih
        (fun ω => closedConvexJoinIterate_isClosed (hSclosed ω) n)
        (fun ω => closedConvexJoinIterate_isClosed (hSclosed ω) n)
        (fun ω => closedConvexJoinIterate_nonempty (hSne ω) n)
        (fun ω => closedConvexJoinIterate_nonempty (hSne ω) n)
      simpa using effrosMeasurable_closure hJoin

/-- **Effros measurable closed convex hull.**  The closed convex hull of a
nonempty compact-valued Effros correspondence in a separable Banach space is
Effros measurable.-/
theorem effrosMeasurable_closedConvexHull_of_compact
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {S : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty) :
    RandomSet.IsEffrosMeasurable
      (fun ω => closedConvexHull ℝ (S ω)) := by
  have hUnion : RandomSet.IsEffrosMeasurable
      (fun ω => ⋃ n, convexJoinIterate (S ω) n) :=
    effrosMeasurable_iUnion
      (effrosMeasurable_convexJoinIterate hS hScompact hSne)
  have hClosure := effrosMeasurable_closure hUnion
  apply hClosure.congr
  intro ω
  exact closure_iUnion_convexJoinIterate_eq_closedConvexHull (hSne ω)

/-- **Effros measurable closed convex hull (closed-valued form).**  If `S`
is Effros measurable with nonempty closed fibres in a separable Banach space,
then its pointwise closed convex hull is Effros measurable.-/
theorem effrosMeasurable_closedConvexHull
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {S : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hSclosed : ∀ ω, IsClosed (S ω))
    (hSne : ∀ ω, (S ω).Nonempty) :
    RandomSet.IsEffrosMeasurable
      (fun ω => closedConvexHull ℝ (S ω)) := by
  have hUnion : RandomSet.IsEffrosMeasurable
      (fun ω => ⋃ n, closedConvexJoinIterate (S ω) n) :=
    effrosMeasurable_iUnion
      (effrosMeasurable_closedConvexJoinIterate hS hSclosed hSne)
  have hClosure := effrosMeasurable_closure hUnion
  apply hClosure.congr
  intro ω
  exact closure_iUnion_closedConvexJoinIterate_eq_closedConvexHull (hSne ω)

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
