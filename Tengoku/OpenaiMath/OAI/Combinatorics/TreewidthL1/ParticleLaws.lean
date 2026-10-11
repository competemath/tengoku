import Tengoku.OpenaiMath.OAI.Combinatorics.TreewidthL1.BagLabels

namespace OAI

universe treewidthLevel1 treewidthLevel2 treewidthLevel3

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

lemma singleton_sum {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsFiniteMeasure μ] (S : Set A) :
    (∑ a, if a ∈ S then μ.real {a} else 0) = μ.real S := by
  classical
  rw [← Finset.sum_filter]
  rw [sum_measureReal_singleton]
  congr 1
  ext a
  simp

lemma measure_marginal {A D : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ : Measure A) [IsFiniteMeasure μ] (f : A → D) (c : D) :
    marginal f (fun a => μ.real {a}) c = (μ.map f).real {c} := by
  classical
  unfold marginal
  rw [show (∑ a, if f a = c then μ.real {a} else 0) =
      μ.real {a | f a = c} from singleton_sum μ _]
  rw [map_measureReal_apply (measurable_of_finite f) (measurableSet_singleton c)]
  rfl

lemma real_sum {A : Type*} [MeasurableSpace A] (μ : J → Measure A)
    [∀ j, IsFiniteMeasure (μ j)] (S : Set A) :
    (∑ j, μ j).real S = ∑ j, (μ j).real S := by
  simp only [measureReal_def, Measure.finsetSum_apply]
  exact ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)

lemma symmetrize_mass
    {V : Type treewidthLevel1} [Fintype V] [DecidableEq V]
    (μ : Measure (V → Bool)) [IsFiniteMeasure μ] :
    (symmetrizeCut μ).real univ = μ.real univ := by
  rw [measureReal_def, symmetrizeCut, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply measurable_complementCut MeasurableSet.univ]
  simp only [preimage_univ, smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  norm_num [measureReal_def]
  ring

noncomputable def particleMeasure (M : ℝ) (F : J → V → ℝ) : Measure (V → Bool) :=
  ∑ j, symmetrizeCut (sweep M (F j))

instance particleMeasure_finite (M : ℝ) (F : J → V → ℝ) :
    IsFiniteMeasure (particleMeasure M F) := by
  unfold particleMeasure
  infer_instance

lemma particleTrace_eq
    {V : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype V] [Fintype J] [DecidableEq V]
    (M : ℝ) (F : J → V → ℝ) (P : Finset V) :
    particleTrace M F P = (particleMeasure M F).map (fun ω => fun v : P => ω v) := by
  unfold particleTrace particleMeasure cutTrace
  rw [Measure.map_finset_sum (measurable_of_finite _).aemeasurable]

instance particleTrace_finite (M : ℝ) (F : J → V → ℝ) (P : Finset V) :
    IsFiniteMeasure (particleTrace M F P) := by
  rw [particleTrace_eq]
  infer_instance

end BoundedTreewidthL1.ParticleLaws
namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

lemma symmetrize_separation
    {V : Type treewidthLevel1} [Fintype V] [DecidableEq V]
    (μ : Measure (V → Bool)) [IsFiniteMeasure μ] (u v : V) :
    cutSeparation (symmetrizeCut μ) u v = cutSeparation μ u v := by
  unfold cutSeparation symmetrizeCut
  rw [measureReal_ennreal_smul_apply, measureReal_add_apply (by finiteness) (by finiteness),
    map_measureReal_apply measurable_complementCut (Set.toFinite _).measurableSet]
  have h : complementCut ⁻¹' {ω : V → Bool | ω u ≠ ω v} = {ω | ω u ≠ ω v} := by
    ext ω
    simp [complementCut]
  rw [h]
  norm_num
  ring

lemma flip_point_mass
    {V : Type treewidthLevel1} [Fintype V] [DecidableEq V]
    (μ : Measure (V → Bool)) (hs : μ.map complementCut = μ) (ω : V → Bool) :
    μ.real {complementCut ω} = μ.real {ω} := by
  conv_lhs => rw [← hs]
  rw [map_measureReal_apply measurable_complementCut (measurableSet_singleton _)]
  congr 1
  ext a
  simp only [mem_preimage, mem_singleton_iff]
  exact complementCut_involutive.injective.eq_iff

lemma marginal_test {A D : Type*} [Fintype A] [Fintype D]
    (f : A → D) (μ : A → ℝ) (h : D → ℝ) :
    (∑ c, marginal f μ c * h c) = ∑ a, μ a * h (f a) := by
  classical
  unfold marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [ite_mul, zero_mul]
  simp

lemma separation_of_marginal (ρ : (V → Bool) → ℝ) (P : Finset V)
    (μ : Measure (P → Bool)) [IsFiniteMeasure μ]
    (h : ∀ a, marginal (fun ω : V → Bool => fun v : P => ω v) ρ a = μ.real {a})
    (u v : P) : cutDistance ρ (fun ω => ω) u.val v.val = cutSeparation μ u v := by
  have ht := marginal_test (fun ω : V → Bool => fun v : P => ω v) ρ
    (fun a => if a u = a v then 0 else 1)
  simp only [h, mul_ite, mul_zero, mul_one] at ht
  rw [cutDistance, ← ht]
  unfold cutSeparation
  have hs := singleton_sum μ {a | a u ≠ a v}
  simp only [mem_ofPred_eq, Classical.ite_not] at hs
  convert! hs using 1
  apply Finset.sum_congr rfl
  intro label _
  split_ifs <;> rfl

lemma trace_separation (M : ℝ) (F : J → V → ℝ) (P : Finset V) (u v : P) :
    cutSeparation (particleTrace M F P) u v = cutSeparation (particleMeasure M F) u.val v.val := by
  unfold cutSeparation
  rw [particleTrace_eq, map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  rfl

end BoundedTreewidthL1.ParticleLaws
namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

lemma overlapping_traces
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} {J : Type treewidthLevel3} [Fintype V]
    [Fintype I] [Fintype J] [DecidableEq V]
    (M : ℝ) (B : I → Finset V) (F : I → J → V → ℝ) (i j : I)
    (h : particleTrace M (F i) (B i ∩ B j) = particleTrace M (F j) (B i ∩ B j)) :
    ∀ c, marginal (BagLabels.leftTrace (fun i => (B i : Set V)) i j)
        (fun a => (particleTrace M (F i) (B i)).real {a}) c =
      marginal (BagLabels.rightTrace (fun i => (B i : Set V)) i j)
        (fun a => (particleTrace M (F j) (B j)).real {a}) c := by
  intro c
  have hl : marginal (BagLabels.leftTrace (fun i => (B i : Set V)) i j)
      (fun a => (particleTrace M (F i) (B i)).real {a}) c =
      ((particleTrace M (F i) (B i)).map (BagLabels.leftTrace (fun i => (B i : Set V)) i j)).real {c} := by
    convert! (measure_marginal (particleTrace M (F i) (B i))
      (BagLabels.leftTrace (fun i => (B i : Set V)) i j) c) using 1
  have hr : marginal (BagLabels.rightTrace (fun i => (B i : Set V)) i j)
      (fun a => (particleTrace M (F j) (B j)).real {a}) c =
      ((particleTrace M (F j) (B j)).map (BagLabels.rightTrace (fun i => (B i : Set V)) i j)).real {c} := by
    convert! (measure_marginal (particleTrace M (F j) (B j))
      (BagLabels.rightTrace (fun i => (B i : Set V)) i j) c) using 1
  rw [hl,hr]
  let E : ((B i ∩ B j : Finset V) → Bool) → (↥((B i : Set V) ∩ (B j : Set V)) → Bool) :=
    fun a v => a ⟨v.val, Finset.mem_inter.mpr v.property⟩
  have he (A : J → V → ℝ) :
      (particleTrace M A (B i ∩ B j)).map E =
      (particleMeasure M A).map (fun ω => fun v : ↥((B i : Set V) ∩ (B j : Set V)) => ω v) := by
    rw [particleTrace_eq, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  have hh := congrArg (fun μ => μ.map E) h
  rw [he, he] at hh
  rw [particleTrace_eq, particleTrace_eq,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  exact congrArg (fun μ => μ.real {c}) hh

lemma norm_bound_from_edges
    {V : Type treewidthLevel1} [Fintype V] [DecidableEq V]
    {E : Type*} [NormedAddCommGroup E]
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ)
    (U : ℝ) (Φ : V → E)
    (he : ∀ u v (h : G.Adj u v), ‖Φ u - Φ v‖ ≤ U * ℓ ⟨s(u,v),h⟩) :
    ∀ u v, ‖Φ u - Φ v‖ ≤ U * shortestPathDistance G ℓ u v := by
  have hw {u v : V} (p : G.Walk u v) : ‖Φ u - Φ v‖ ≤ U * walkLength G ℓ p := by
    induction p with
    | nil => simp [walkLength]
    | @cons u v w huv p ih =>
      calc
        ‖Φ u - Φ w‖ ≤ ‖Φ u - Φ v‖ + ‖Φ v - Φ w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ U * ℓ ⟨s(u,v),huv⟩ + U * walkLength G ℓ p := add_le_add (he u v huv) ih
        _ = U * walkLength G ℓ (.cons huv p) := by rw [walkLength, mul_add]
  intro u v
  obtain ⟨p,hp,hlen⟩ := shortestPathDistance_attained G ℓ hG u v
  rw [← hlen]
  exact hw p

end BoundedTreewidthL1.ParticleLaws

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

end BoundedTreewidthL1.ParticleLaws
namespace BoundedTreewidthL1.ParticleLaws
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]

lemma gluing_without_path (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ) (m : ℝ) (hm : 0 < m)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = m)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (BagLabels.leftTrace B i j) (μ i) c = marginal (BagLabels.rightTrace B i j) (μ j) c)
    (hflip : ∀ i a, μ i (BagLabels.flip (B i) a) = μ i a) :
    ∃ ρ : (V → Bool) → ℝ,
      (∀ ω, 0 ≤ ρ ω) ∧ (∑ ω, ρ ω) = m ∧
      (∀ ω, ρ (complementCut ω) = ρ ω) ∧
      (∀ i a, marginal (fun ω => BagLabels.restrict B ω i) ρ a = μ i a) ∧
      ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        ∀ u v, ‖Φ u - Φ v‖ = cutDistance ρ (fun ω => ω) u v := by
  obtain ⟨ρ,hρ,hρmass,hρflip,hρlocal,hρpath,n,Φ,hΦ⟩ :=
    BagLabels.canonical_gluing T hT B hcover hrun μ m hm hμ
      (by intro i; convert! hmass i using 1)
      (by intro i j hij c; convert! hcons i j hij c using 1) hflip
  exact ⟨ρ,hρ,hρmass,hρflip,hρlocal,n,Φ,hΦ⟩

end BoundedTreewidthL1.ParticleLaws
namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

end BoundedTreewidthL1.ParticleLaws
namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root : I)

noncomputable def path (i : I) : T.Walk i root :=
  (hT.connected.exists_path_of_dist i root).choose
lemma path_isPath (i : I) : (path T hT root i).IsPath :=
  (hT.connected.exists_path_of_dist i root).choose_spec.1
lemma path_length (i : I) : (path T hT root i).length = T.dist i root :=
  (hT.connected.exists_path_of_dist i root).choose_spec.2

lemma snd_closer {i : I} (hi : i ≠ root) :
    T.dist (path T hT root i).snd root < T.dist i root := by
  have hlen := (path T hT root i).length_tail_add_one
    (SimpleGraph.Walk.not_nil_of_ne hi)
  have hdist := SimpleGraph.dist_le (path T hT root i).tail
  rw [path_length] at hlen
  omega

noncomputable def forest : RootedForest I where
  parent i := if i = root then none else some (path T hT root i).snd
  depth i := T.dist i root
  decreases := by
    classical
    intro i p hp
    by_cases hi : i = root
    · simp only [hi, ite_eq_left] at hp
      contradiction
    · simp only [hi, ite_false, Option.some.injEq] at hp
      subst p
      exact snd_closer T hT root hi

lemma parent_adj {i p : I} (hp : (forest T hT root).parent i = some p) : T.Adj i p := by
  classical
  change (if i = root then none else some (path T hT root i).snd) = some p at hp
  by_cases hi : i = root
  · simp only [ite_eq_left hi] at hp
    contradiction
  · simp only [ite_eq_right hi] at hp
    cases Option.some.inj hp
    exact SimpleGraph.Walk.adj_snd (SimpleGraph.Walk.not_nil_of_ne hi)

lemma parent_of_closer {i j : I} (hij : T.Adj i j)
    (hd : T.dist j root + 1 = T.dist i root) :
    (forest T hT root).parent i = some j := by
  classical
  have hi : i ≠ root := by
    intro he; subst i
    simp only [SimpleGraph.dist_self] at hd
    omega
  let q : T.Walk i root := (path T hT root j).cons hij
  have hq : q.length = T.dist i root := by
    simpa only [q, SimpleGraph.Walk.length_cons, path_length, Nat.add_comm] using hd
  have he : q = path T hT root i :=
    congrArg Subtype.val ((hT.isAcyclic.subsingleton_path i root).elim
      ⟨q,q.isPath_of_length_eq_dist hq⟩ ⟨_,path_isPath T hT root i⟩)
  change (if i = root then none else some (path T hT root i).snd) = some j
  rw [ite_eq_right hi, ← he]
  simp only [q, SimpleGraph.Walk.snd_cons]

/-- Every actual tree edge is a parent-child edge of the depth-certified forest. -/
theorem edge_orientation {i j : I} (hij : T.Adj i j) :
    (forest T hT root).parent i = some j ∨ (forest T hT root).parent j = some i := by
  have hd := hT.dist_eq_dist_add_one_of_adj root hij
  rw [SimpleGraph.dist_comm (u := root) (v := i),
    SimpleGraph.dist_comm (u := root) (v := j)] at hd
  rcases hd with hd | hd
  · exact Or.inl (parent_of_closer T hT root hij hd.symm)
  · exact Or.inr (parent_of_closer T hT root hij.symm hd.symm)

end BoundedTreewidthL1.RootedTree
namespace BoundedTreewidthL1.BagLabels
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Ω V I : Type*} [MeasurableSpace Ω] [Fintype V] [Fintype I]

/-- Explicit prepared law: the pushforward of the normalized tree density,
using the actual overlap couplings, with the convention 0/0 = 0. -/
noncomputable def canonicalLaw (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (p : (i : I) → (B i → Bool) → ℝ)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (p i) c = marginal (rightTrace B i j) (p j) c) :
    (V → Bool) → ℝ :=
  globalMass T B hcover p
    (TreeMarkov.interaction (fun i => B i → Bool) p (pairMass T B p))
    (TreeMarkov.interaction_symmetric (fun i => B i → Bool) p _
      (pairMass_symmetric T B p hcons))

lemma marginal_measurable {A C : Type*} [Fintype A]
    (f : A → C) (p : Ω → A → ℝ) (hp : ∀ a, Measurable (fun ξ => p ξ a)) (c : C) :
    Measurable (fun ξ => marginal f (p ξ) c) := by
  unfold marginal
  apply Finset.measurable_sum
  intro a ha
  by_cases he : f a = c
  · simpa only [he, ite_true] using hp a
  · simp only [he, ite_false]
    exact measurable_const

lemma pairMass_measurable
    {Ω : Type treewidthLevel1} {V : Type treewidthLevel2} {I : Type treewidthLevel3}
    [MeasurableSpace Ω] [Fintype V] [Fintype I]
    (T : SimpleGraph I) (B : I → Set V)
    (p : Ω → (i : I) → (B i → Bool) → ℝ)
    (hp : ∀ i a, Measurable (fun ξ => p ξ i a))
    (i j : I) (a : B i → Bool) (b : B j → Bool) :
    Measurable (fun ξ => pairMass T B (p ξ) i j a b) := by
  unfold pairMass glueWeights
  by_cases hij : T.Adj i j
  · simp only [hij, ite_true]
    by_cases hab : leftTrace B i j a = rightTrace B i j b
    · simp only [hab, ite_true]
      exact ((hp i a).mul (hp j b)).div
        (marginal_measurable (leftTrace B i j) (fun ξ => p ξ i) (hp i) _)
    · simp only [hab, ite_false]
      exact measurable_const
  · simp only [hij, ite_false]
    exact measurable_const

lemma canonicalLaw_measurable (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (p : Ω → (i : I) → (B i → Bool) → ℝ)
    (hcons : ∀ ξ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (p ξ i) c = marginal (rightTrace B i j) (p ξ j) c)
    (hp : ∀ i a, Measurable (fun ξ => p ξ i a)) (ω : V → Bool) :
    Measurable (fun ξ => canonicalLaw T B hcover (p ξ) (hcons ξ) ω) := by
  unfold canonicalLaw globalMass
  apply Finset.measurable_sum
  intro x hx
  by_cases he : assemble B hcover x = ω
  · simp only [he, ite_true, TreeMarkov.density]
    apply Measurable.mul
    · exact Finset.measurable_prod _ (fun i hi => hp i (x i))
    · apply Finset.measurable_prod
      intro e he
      induction e using Sym2.ind with
      | _ i j =>
        simp only [TreeMarkov.edgeFactor_mk, TreeMarkov.interaction]
        exact (pairMass_measurable T B p hp i j (x i) (x j)).div
          ((hp i (x i)).mul (hp j (x j)))
  · simp only [he, ite_false]
    exact measurable_const

lemma canonicalLaw_normalized (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (p : (i : I) → (B i → Bool) → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hp₁ : ∀ i, (∑ a, p i a) = 1)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (p i) c = marginal (rightTrace B i j) (p j) c) :
    (∀ ω, 0 ≤ canonicalLaw T B hcover p hcons ω) ∧
      (∑ ω, canonicalLaw T B hcover p hcons ω) = 1 := by
  obtain ⟨hs,hn,hcomp⟩ := bag_couplings T B p hp hp₁ hcons
  have hh := global_bag_law.{_,_,0} T hT B hcover hrun p
    (TreeMarkov.interaction (fun i => B i → Bool) p (pairMass T B p))
    (TreeMarkov.interaction_symmetric (fun i => B i → Bool) p _
      (pairMass_symmetric T B p hcons)) hn hcomp
  exact ⟨hh.1, hh.2.1⟩

end BoundedTreewidthL1.BagLabels

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]

lemma trace_restrict (M : ℝ) (F : ι → V → ℝ) (P Q : Finset V) (h : Q ⊆ P) :
    (particleTrace M F P).map (fun a : P → Bool => fun v : Q => a ⟨v,h v.property⟩) =
      particleTrace M F Q := by
  rw [particleTrace_eq, Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    particleTrace_eq]
  rfl

lemma trace_eq_of_subset (M : ℝ) (F H : ι → V → ℝ) (P Q : Finset V) (h : Q ⊆ P)
    (he : particleTrace M F P = particleTrace M H P) :
    particleTrace M F Q = particleTrace M H Q := by
  rw [← trace_restrict M F P Q h, he, trace_restrict]
end BoundedTreewidthL1.ParticleLaws

namespace BoundedTreewidthL1.TreeParticles
open ParticleLaws
variable {I V ι J : Type*} [Fintype I] [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq V] [DecidableEq ι] [DecidableEq J]

end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I Ω : Type*} [Fintype V] [Fintype I] [MeasurableSpace Ω]

lemma marginal_integral {A D : Type*} [Fintype A] [Fintype D]
    (ν : Measure Ω) (f : A → D) (μ : Ω → A → ℝ)
    (h : ∀ a, Integrable (fun ω => μ ω a) ν) (b : D) :
    marginal f (fun a => ∫ ω, μ ω a ∂ν) b = ∫ ω, marginal f (μ ω) b ∂ν := by
  unfold marginal
  rw [integral_finsetSum _ (fun a _ => if hfa : f a = b then
    by simpa only [hfa,↓reduceIte] using h a else
    by simp only [hfa,↓reduceIte]; exact integrable_zero Ω ℝ ν)]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp

/-- Averaging local laws first preserves exactly the co-bag metric and produces
an actual Markov-glued global law, not a measurable choice of random globals. -/
theorem averaged_bag_realization (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (μ : Ω → (i : I) → (B i → Bool) → ℝ) (m : ℝ) (hm : 0 < m)
    (hμ : ∀ ω i a, 0 ≤ μ ω i a) (hmass : ∀ ω i, (∑ a, μ ω i a) = m)
    (hint : ∀ i a, Integrable (fun ω => μ ω i a) ν)
    (hcons : ∀ ω i j, T.Adj i j → ∀ c,
      marginal (BagLabels.leftTrace B i j) (μ ω i) c =
        marginal (BagLabels.rightTrace B i j) (μ ω j) c)
    (hflip : ∀ ω i a, μ ω i (BagLabels.flip (B i) a) = μ ω i a) :
    ∃ ρ : (V → Bool) → ℝ,
      (∀ a, 0 ≤ ρ a) ∧ (∑ a, ρ a) = m ∧
      (∀ a, ρ (complementCut a) = ρ a) ∧
      (∀ i a, marginal (fun ω => BagLabels.restrict B ω i) ρ a = ∫ ω, μ ω i a ∂ν) ∧
      (∀ (r : ℕ) (e : Fin (r+1) ↪ I), T.comap e = SimpleGraph.pathGraph (r+1) →
        MarkovFlow.IsMarkovLaw (fun j => B (e j) → Bool)
          (marginal (fun ω j => BagLabels.restrict B ω (e j)) (fun ω => ρ ω / m))) ∧
      ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        (∀ u v, ‖Φ u - Φ v‖ = cutDistance ρ (fun ω => ω) u v) ∧
        ∀ i (u v : B i), ‖Φ u.val - Φ v.val‖ =
          ∫ ω, (∑ a, if a u = a v then 0 else μ ω i a) ∂ν := by
  let μ' : (i : I) → (B i → Bool) → ℝ := fun i a => ∫ ω, μ ω i a ∂ν
  have hμ' : ∀ i a, 0 ≤ μ' i a := fun i a => integral_nonneg (fun ω => hμ ω i a)
  have hm' : ∀ i, (∑ a, μ' i a) = m := by
    intro i
    dsimp only [μ']
    rw [← integral_finsetSum _ (fun a _ => hint i a)]
    simp only [hmass,integral_const,probReal_univ,one_smul]
  have hc' : ∀ i j, T.Adj i j → ∀ c,
      marginal (BagLabels.leftTrace B i j) (μ' i) c =
        marginal (BagLabels.rightTrace B i j) (μ' j) c := by
    intro i j hij c
    rw [marginal_integral ν _ _ (hint i),marginal_integral ν _ _ (hint j)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => hcons ω i j hij c)
  have hf' : ∀ i a, μ' i (BagLabels.flip (B i) a) = μ' i a := by
    intro i a
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => hflip ω i a))
  obtain ⟨ρ,hρ,hρmass,hρflip,hρlocal,hρpath,n,Φ,hΦ⟩ :=
    BagLabels.canonical_gluing T hT B hcover hrun μ' m hm hμ' hm' hc' hf'
  refine ⟨ρ,hρ,hρmass,hρflip,hρlocal,hρpath,n,Φ,hΦ,?_⟩
  intro i u v
  rw [hΦ]
  have ht := marginal_test (fun ω => BagLabels.restrict B ω i) ρ
    (fun a => if a u = a v then (0:ℝ) else 1)
  simp only [hρlocal,mul_ite,mul_zero,mul_one] at ht
  have he : cutDistance ρ (fun ω => ω) u.val v.val =
      ∑ a, if a u = a v then 0 else μ' i a := by
    rw [ht]
    rfl
  rw [he]
  rw [integral_finsetSum _ (fun a _ => if hab : a u = a v then
    by simp only [hab,↓reduceIte]; exact integrable_const 0 else
    by simpa only [hab,↓reduceIte] using hint i a)]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp [μ']

end BoundedTreewidthL1.ParticleLaws

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J Ω : Type*} [Fintype V] [Fintype I] [Fintype J]
  [DecidableEq V] [MeasurableSpace Ω]

end BoundedTreewidthL1.ParticleLaws

end OAI
