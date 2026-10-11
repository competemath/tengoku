import Tengoku.OpenaiMath.OAI.Combinatorics.TreewidthL1.Particles

namespace OAI

universe treewidthLevel1 treewidthLevel2 treewidthLevel3 treewidthLevel4

/-! Deterministic causal recursion on a rooted finite tree. The depth certificate
is constructed from graph distance below; it is not an embedding hypothesis. -/
namespace BoundedTreewidthL1

structure RootedForest (I : Type*) where
  parent : I → Option I
  depth : I → ℕ
  decreases : ∀ i p, parent i = some p → depth p < depth i

namespace RootedForest
variable {I A : Type*}

noncomputable def run (R : RootedForest I) (seed : A) (step : I → A → A) (i : I) : A :=
  step i (match h : R.parent i with
    | none => seed
    | some p =>
      have : R.depth p < R.depth i := R.decreases i p h
      R.run seed step p)
termination_by R.depth i
decreasing_by assumption

lemma run_eq (R : RootedForest I) (seed : A) (step : I → A → A) (i : I) :
    R.run seed step i = step i ((R.parent i).elim seed (R.run seed step)) := by
  rw [run]
  split <;> simp_all

lemma run_invariant (R : RootedForest I) (seed : A) (step : I → A → A)
    (Q : A → Prop) (hseed : Q seed) (hstep : ∀ i a, Q a → Q (step i a)) :
    ∀ i, Q (R.run seed step i) := by
  intro i
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [run_eq]
    apply hstep
    cases hp : R.parent i with
    | none => exact hseed
    | some p =>
      apply ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p rfl

lemma run_measurable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (R : RootedForest I) (seed : Ω → A) (step : I → Ω → A → A)
    (hseed : Measurable seed)
    (hstep : ∀ i f, Measurable f → Measurable (fun ω => step i ω (f ω))) :
    ∀ i, Measurable (fun ω => R.run (seed ω) (fun j => step j ω) i) := by
  intro i
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    simp_rw [run_eq]
    cases hp : R.parent i with
    | none => simpa only [hp, Option.elim_none] using hstep i seed hseed
    | some p =>
      simpa only [hp, Option.elim_some] using hstep i _
        (ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p rfl)
end RootedForest
end BoundedTreewidthL1

namespace BoundedTreewidthL1.TreeParticles
open MeasureTheory ParticleSchedule ParticleBatch
variable {I V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J]

noncomputable def interface (R : RootedForest I) (bag : I → Finset V) (i : I) : Finset V :=
  (R.parent i).elim ∅ bag
noncomputable def retained (R : RootedForest I) (A : I → Finset J) (i : I) : Finset J :=
  (R.parent i).elim ∅ (fun p => A i ∩ A p)
noncomputable def fresh (R : RootedForest I) (A : I → Finset J) (i : I) : Finset J :=
  A i \ retained R A i
noncomputable def seed : (ι → V → ℝ) × (J → ι × ι) :=
  (fun _ _ => 0, fun _ => (Classical.choice inferInstance, Classical.choice inferInstance))
noncomputable def step (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) (S : (ι → V → ℝ) × (J → ι × ι)) :=
  launchBatch (interface R bag i) (fresh R A i).toList (retained R A i) S.1 S.2 (g i)
noncomputable def state (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) : (ι → V → ℝ) × (J → ι × ι) :=
  R.run seed (step R bag A g) i

lemma retained_subset (R : RootedForest I) (A : I → Finset J) (i : I) :
    retained R A i ⊆ A i := by
  unfold retained
  cases R.parent i with
  | none => exact Finset.empty_subset _
  | some p => exact Finset.inter_subset_left

lemma batch_data (R : RootedForest I) (A : I → Finset J) (i : I)
    {q : ℕ} (hA : (A i).card ≤ q) :
    (fresh R A i).toList.Nodup ∧
    (∀ a ∈ (fresh R A i).toList, a ∉ retained R A i) ∧
    (retained R A i ∪ (fresh R A i).toList.toFinset).card ≤ q := by
  classical
  refine ⟨Finset.nodup_toList _, ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)).2
  · simpa only [Finset.toList_toFinset, fresh,
      Finset.union_sdiff_of_subset (retained_subset R A i)] using hA

lemma interface_card
    {I : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype V]
    (R : RootedForest I) (bag : I → Finset V) {k : ℕ}
    (hbag : ∀ i, (bag i).card ≤ k) (i : I) : (interface R bag i).card ≤ k := by
  unfold interface
  cases R.parent i with
  | none => exact Nat.zero_le _
  | some p => exact hbag p

lemma state_eq
    {I : Type treewidthLevel1} {V : Type treewidthLevel2} {ι : Type treewidthLevel3}
    {J : Type treewidthLevel4} [Fintype V] [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq J]
    (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) :
    state (ι := ι) R bag A g i = step R bag A g i
      ((R.parent i).elim seed (state R bag A g)) := RootedForest.run_eq _ _ _ _
end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.TreeParticles
open MeasureTheory ParticleSchedule ParticleBatch
variable {I V ι J Ω : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J] [Fintype J] [MeasurableSpace Ω]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Measurability of the actual branching preparation, with all randomness
sampled beforehand. No measurable-choice assumption about the particle lists. -/
theorem measurable_state (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : Ω → I → J → V → ℝ)
    (hg : ∀ i a v, Measurable (fun ω => g ω i a v)) (i : I) :
    Measurable (fun ω => state (ι := ι) R bag A (g ω) i) := by
  apply R.run_measurable (fun _ => seed) (fun j ω S => step R bag A (g ω) j S)
    measurable_const
  intro j f hf
  exact measurable_launchBatch (interface R bag j) (fresh R A j).toList (retained R A j)
    (fun ω => (f ω).1) (fun ω => (f ω).2) (fun ω => g ω j)
    (fun a v => (measurable_pi_apply v).comp ((measurable_pi_apply a).comp hf.fst))
    (fun a => (measurable_pi_apply a).comp hf.snd) (hg j)

end BoundedTreewidthL1.TreeParticles

end OAI
