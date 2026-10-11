import Tengoku.OpenaiMath.OAI.Combinatorics.TreewidthL1.Construction

namespace OAI

universe treewidthLevel1 treewidthLevel2 treewidthLevel3

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

end BoundedTreewidthL1.ParticleLaws

namespace BoundedTreewidthL1.ParticleBatch
open ParticleSchedule
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]

def pairIndex (p : J → ι × ι) (a : J) (b : Bool) : ι := if b then (p a).2 else (p a).1

def PairUnique (C : Finset J) (p : J → ι × ι) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ u v : Bool, pairIndex p a u = pairIndex p b v → a = b ∧ u = v

lemma pairIndex_mem {C : Finset J} (p : J → ι × ι) {a : J} (ha : a ∈ C) (b : Bool) :
    pairIndex p a b ∈ usedPairs C p := by
  cases b
  · exact first_mem_used ha p
  · exact second_mem_used ha p

lemma PairUnique.mono
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι]
    {C D : Finset J} {p : J → ι × ι} (h : PairUnique D p) (hs : C ⊆ D) :
    PairUnique C p := fun a ha b hb u v => h a (hs ha) b (hs hb) u v

lemma PairUnique.empty
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι]
    (p : J → ι × ι) : PairUnique ∅ p := by
  intro a ha
  simp at ha

lemma PairUnique.update {C : Finset J} {p : J → ι × ι} (hp : PairUnique C p)
    (a : J) (ha : a ∉ C) (z : ι × ι)
    (hz : z.1 ∉ usedPairs C p ∧ z.2 ∉ usedPairs C p ∧ z.1 ≠ z.2) :
    PairUnique (insert a C) (Function.update p a z) := by
  intro b hb c hc u v he
  have hnew (w : Bool) : pairIndex (Function.update p a z) a w ∉ usedPairs C p := by
    cases w
    · simpa [pairIndex] using hz.1
    · simpa [pairIndex] using hz.2.1
  rcases Finset.mem_insert.mp hb with hba | hb
  · subst b
    rcases Finset.mem_insert.mp hc with hca | hc
    · subst c
      refine ⟨rfl,?_⟩
      cases u <;> cases v <;> simp_all [pairIndex]
    · have hca : c ≠ a := fun h => ha (h ▸ hc)
      have he' : pairIndex (Function.update p a z) a u = pairIndex p c v := by
        simpa [pairIndex,Function.update_of_ne hca] using he
      exact False.elim (hnew u (he'.symm ▸ pairIndex_mem p hc v))
  · have hba : b ≠ a := fun h => ha (h ▸ hb)
    rcases Finset.mem_insert.mp hc with hca | hc
    · subst c
      have he' : pairIndex p b u = pairIndex (Function.update p a z) a v := by
        simpa [pairIndex,Function.update_of_ne hba] using he
      exact False.elim (hnew v (he' ▸ pairIndex_mem p hb u))
    · have hca : c ≠ a := fun h => ha (h ▸ hc)
      apply hp b hb c hc u v
      simpa [pairIndex,Function.update_of_ne hba,Function.update_of_ne hca] using he

lemma launchBatch_unique (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial+2)
    (P : Finset V) (hP : P.card ≤ k) (l : List J) (C : Finset J)
    (hl : l.Nodup) (hfresh : ∀ a ∈ l, a ∉ C) (hcount : (C ∪ l.toFinset).card ≤ q)
    (F : ι → V → ℝ) (p : J → ι × ι) (hp : PairUnique C p) (g : J → V → ℝ) :
    PairUnique (C ∪ l.toFinset) (launchBatch P l C F p g).2 := by
  induction l generalizing C F p with
  | nil => simpa [launchBatch] using hp
  | cons a l ih =>
    have haC : a ∉ C := hfresh a (by simp)
    let z := pickPair P (usedPairs C p) F
    let F₁ := functionPairUpdate F z.1 z.2 (g a)
    let p₁ := Function.update p a z
    have hC : C.card ≤ q := (Finset.card_le_card Finset.subset_union_left).trans hcount
    have hz : z.1 ∉ usedPairs C p ∧ z.2 ∉ usedPairs C p ∧ z.1 ≠ z.2 ∧
        CommonWeakOrder P (F z.1) (F z.2) :=
      pickPair_spec k q hN P hP _ ((usedPairs_card C p).trans (by omega)) F
    have hnewCount : (insert a C ∪ l.toFinset).card ≤ q := by
      simpa only [List.toFinset_cons, Finset.insert_union, Finset.union_insert] using hcount
    have hnewFresh : ∀ b ∈ l, b ∉ insert a C := by
      intro b hb h
      rcases Finset.mem_insert.mp h with h | h
      · subst b
        exact (List.nodup_cons.mp hl).1 hb
      · exact hfresh b (by simp [hb]) h
    have hn : PairUnique (insert a C) p₁ := hp.update a haC z ⟨hz.1,hz.2.1,hz.2.2.1⟩
    have hres := ih (insert a C) hl.of_cons hnewFresh hnewCount F₁ p₁ hn
    simpa only [List.toFinset_cons, Finset.insert_union, Finset.union_insert, launchBatch] using hres

end BoundedTreewidthL1.ParticleBatch

namespace BoundedTreewidthL1.AnchorTreeParticles
open ParticleBatch
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι I J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]

/-- All simultaneously reserved pairs are disjoint in the ACTUAL depth-recursive
branching preparation. In particular every strictly older active reservation
avoids both indices reserved by the fresh own-bag launch. -/
theorem state_unique (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (k q : ℕ) (hN : Fintype.card ι = 2*q+k.factorial+2)
    (hbag : ∀ i, (bag i).card ≤ k) (hA : ∀ i, (A i).card ≤ q) :
    ∀ i, PairUnique (A i) (state (ι := ι) R bag A g i).2 := by
  intro i
  induction hi : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    let S := state (ι := ι) R bag A g
    have hp : PairUnique (retained R A i) ((R.parent i).elim seed S).2 := by
      cases he : R.parent i with
      | none => simp [retained,he,PairUnique.empty]
      | some p =>
        have hu := ih (R.depth p) (by have := R.decreases i p he; omega) p rfl
        simpa only [retained,he,Option.elim_some] using hu.mono Finset.inter_subset_right
    have hb := batch_data R A i (hA i)
    have hr := launchBatch_unique k q hN (bag i) (hbag i) (fresh R A i).toList (retained R A i)
      hb.1 hb.2.1 hb.2.2 ((R.parent i).elim seed S).1 ((R.parent i).elim seed S).2 hp (g i)
    rw [state_eq]
    simpa only [step,Finset.toList_toFinset,fresh,Finset.union_sdiff_of_subset (retained_subset R A i)] using hr
end BoundedTreewidthL1.AnchorTreeParticles

namespace BoundedTreewidthL1.ExpandedAnchor
open MeasureTheory AnchorTreeParticles ParticleBatch ExpandedParticleLaw ExpandedConstruction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I ι Ω : Type*} [Fintype V] [Fintype I] [Fintype ι] [Nonempty ι]
  [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma parent_antisymm
    {I : Type treewidthLevel1} [Fintype I]
    (R : RootedForest I) (i j : I)
    (h : R.parent i = some j) : R.parent j ≠ some i := by
  intro h'
  have := R.decreases i j h
  have := R.decreases j i h'
  omega

noncomputable def law (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (A : I → Finset I) (g : I → I → V → ℝ) (M : ℝ) :
    (I → State ι V) → ℝ :=
  let R := RootedTree.forest T hT root
  let S := state (ι := ι) R B A g
  ensemble T R.parent (parent_antisymm R) M (fun i => (S i).1) B
    (fun i => ((S i).2 i).1) (fun i => ((S i).2 i).2)
    (fun i => usedPairs (retained R A i) (S i).2)

lemma retained_functions
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} {ι : Type treewidthLevel3} [Fintype V]
    [Fintype I] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (R : RootedForest I) (A : I → Finset I)
    (S : I → (ι → V → ℝ) × (I → ι × ι))
    (hpairs : ∀ i p, R.parent i = some p → ∀ a ∈ A i ∩ A p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2) :
    ∀ p i, R.parent i = some p → ∀ r ∈ usedPairs (retained R A i) (S i).2,
      (S p).1 r = (S i).1 r := by
  intro p i hpi r hr
  simp only [usedPairs,retained,hpi,Option.elim_some,Finset.mem_union,Finset.mem_image] at hr
  rcases hr with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
  · obtain ⟨he,hf,_⟩ := hpairs i p hpi a ha
    simpa only [he] using hf.symm
  · obtain ⟨he,_,hf⟩ := hpairs i p hpi a ha
    simpa only [he] using hf.symm

end BoundedTreewidthL1.ExpandedAnchor

end OAI
