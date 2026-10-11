import Tengoku.OpenaiMath.OAI.Combinatorics.TreewidthL1.CachedEnsemble

namespace OAI

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles _root_.OAI.BoundedTreewidthL1.RootedTree TreeCache AnchorCache ParticleBatch ExpandedConstruction
open scoped ENNReal
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section

def count (k : ℕ) : ℕ := 2*(cacheBound k+1)+ k.factorial+2
instance count_neZero (k : ℕ) : NeZero (count k) := ⟨by dsimp [count]; omega⟩
def particleLip (k : ℕ) : ℝ := 3*((count k:ℝ)-1)
def upper (k : ℕ) : ℝ := (count k:ℝ)*particleLip k
lemma count_ge (k : ℕ) : 2 ≤ count k := by dsimp [count]; omega
lemma particleLip_pos (k : ℕ) : 0 < particleLip k := by
  have hh : (2:ℝ) ≤ count k := by exact_mod_cast count_ge k
  dsimp [particleLip]; linarith
lemma upper_pos (k : ℕ) : 0 < upper k := by
  have hh : 0 < count k := lt_of_lt_of_le (by omega) (count_ge k)
  exact mul_pos (by exact_mod_cast hh) (particleLip_pos k)

attribute [local instance 2000] Classical.decEq
variable {V : Type*} [Fintype V] [MetricSpace V] {n : ℕ}
variable (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (root : Fin (n+1))
  (B : Fin (n+1) → Finset V) (D : Fin (n+1) → V → ℝ) (k : ℕ) (J α π η : ℝ)
  (seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η)
variable {D α π η}
abbrev Space := (i : Fin (n+1)) → NoiseSpace (seed i).n (seed i).m
noncomputable def measure : Measure (Space seed) := Measure.pi (fun i => noiseLaw (seed i).m (seed i).mass)
variable (D α π η)
noncomputable def noise (ω : Space seed) (i : Fin (n+1)) (_ : Fin (n+1)) (v : V) : ℝ := noiseG (D i) (seed i).bump (ω i) v
noncomputable def states (ω : Space seed) := state (ι := Fin (count k)) (forest T hT root) B
  (active T hT root B D k dist J) (noise D α π η seed ω)
noncomputable def raw (cover : ∀ v, ∃ i, v ∈ B i) (H Δ : ℝ) (ω : Space seed) (x y : V) : ℝ :=
  cutDistance (ExpandedAnchor.law (ι := Fin (count k)) T hT root B (active T hT root B D k dist J)
    (noise D α π η seed ω) (H*((count k:ℝ)-1)+2*Δ))
    (ExpandedTree.assemble (fun i => (B i : Set V)) cover (ExpandedParticleLaw.label (ι := Fin (count k)))) x y

structure Model (cover : ∀ v, ∃ i, v ∈ B i) (run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected) where
  H : ℝ
  Δ : ℝ
  H_pos : 0 < H
  Δ_pos : 0 < Δ
  reach : ∀ ω i, FunctionParticleReachable dist 3 H (states T hT root B D k J α π η seed ω i).1
  trace : ∀ ω i p, (forest T hT root).parent i = some p →
    particleTrace (H*((count k:ℝ)-1)+2*Δ) (states T hT root B D k J α π η seed ω i).1 (B i) =
    particleTrace (H*((count k:ℝ)-1)+2*Δ) (states T hT root B D k J α π η seed ω p).1 (B i)
  pairs : ∀ ω i p, (forest T hT root).parent i = some p → ∀ a ∈
      active T hT root B D k dist J i ∩ active T hT root B D k dist J p,
    (states T hT root B D k J α π η seed ω i).2 a = (states T hT root B D k J α π η seed ω p).2 a ∧
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 a).1 =
      (states T hT root B D k J α π η seed ω p).1 ((states T hT root B D k J α π η seed ω p).2 a).1 ∧
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 a).2 =
      (states T hT root B D k J α π η seed ω p).1 ((states T hT root B D k J α π η seed ω p).2 a).2
  unique : ∀ ω i, PairUnique (active T hT root B D k dist J i) (states T hT root B D k J α π η seed ω i).2
  gap : ∀ ω i v,
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 i).1 v-
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 i).2 v =
    2*noise D α π η seed ω i i v
  nonneg : ∀ ω x y, 0 ≤ raw T hT root B D k J α π η seed cover H Δ ω x y
  integrable : ∀ x y, Integrable (fun ω => raw T hT root B D k J α π η seed cover H Δ ω x y) (measure seed)
  dim : ℕ
  map : V → PiLp (1 : ENNReal) (fun _ : Fin dim => ℝ)
  average : ∀ x y, ‖map x-map y‖ = ∫ ω, raw T hT root B D k J α π η seed cover H Δ ω x y ∂measure seed
  upper_bound : ∀ x y, ‖map x-map y‖ ≤ upper k*dist x y

namespace Model
variable {T hT root B D k J α π η seed} {cover : ∀ v, ∃ i, v ∈ B i}
  {run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected}
  (P : Model T hT root B D k J α π η seed cover run)
noncomputable def datum (ω : Space seed) :=
  CachedEnsemble.data T hT root B cover run D k dist J (states T hT root B D k J α π η seed ω)
    (P.H*((count k:ℝ)-1)+2*P.Δ) (P.pairs ω) (P.trace ω)
lemma datum_dist (ω : Space seed) (x y : V) :
    (P.datum ω).dist x y = raw T hT root B D k J α π η seed cover P.H P.Δ ω x y := rfl
lemma M_pos : 0 < P.H*((count k:ℝ)-1)+2*P.Δ := by
  have hh : (2:ℝ) ≤ count k := by exact_mod_cast count_ge k
  nlinarith [P.H_pos,P.Δ_pos]
lemma height (ω : Space seed) (i : Fin (n+1)) (r : Fin (count k)) (x : V) :
    |(states T hT root B D k J α π η seed ω i).1 r x| ≤ P.H*((count k:ℝ)-1) := by
  simpa only [Fintype.card_fin] using function_particles_height_bound P.H_pos (P.reach ω i) r x
include P
lemma lipschitz (ω : Space seed) (i : Fin (n+1)) (r : Fin (count k)) (x z : V) :
    |(states T hT root B D k J α π η seed ω i).1 r x-
      (states T hT root B D k J α π η seed ω i).1 r z| ≤ particleLip k*dist x z := by
  simpa only [Fintype.card_fin,particleLip] using function_particles_metric_bound (by norm_num : (0:ℝ)<3) (P.reach ω i) r x z
lemma pair_distinct (ω : Space seed) (i : Fin (n+1)) :
    ((states T hT root B D k J α π η seed ω i).2 i).1 ≠
    ((states T hT root B D k J α π η seed ω i).2 i).2 := by
  intro hh
  have hb := (P.unique ω i i (active_self T hT root B D k dist J i)
    i (active_self T hT root B D k dist J i) false true hh).2
  cases hb

lemma gap_probability (a : Fin (n+1)) (x : V) (C : Finset V)
    (t β γ : ℝ) (ht : 0 ≤ t) (hβ : 0 < β) (hγ : 0 < γ) (hπ : 0 ≤ π) (hx : 0 < D a x)
    (hamp : ∀ loc, GoodBump (D a) α η ((seed a).bump loc) x → ∀ s ∈ C,
      β ≤ |D a x-D a s| ∨ ∃ j, γ ≤ |(seed a).bump loc j x-(seed a).bump loc j s|)
    (hbudget : (C.card : ℝ)*(2*t/β+2*t/γ) ≤ 1/2) :
    ENNReal.ofReal (π/4) ≤ measure seed {ω : Space seed | ∀ s ∈ C, t ≤
      |positive (ι := Fin (count k)) (forest T hT root) B (active T hT root B D k dist J)
        (noise D α π η seed ω) a x-
       positive (ι := Fin (count k)) (forest T hT root) B (active T hT root B D k dist J)
        (noise D α π η seed ω) a s|} := by
  let (i : Fin (n+1)) := (seed i).probability
  let (i : Fin (n+1)) : Nonempty (NoiseSpace (seed i).n (seed i).m) :=
    nonempty_of_isProbabilityMeasure (noiseLaw (seed i).m (seed i).mass)
  apply NoiseCube.node_gap D α π η seed a x C _ _ _ t β γ ht hβ hγ hπ hx hamp hbudget
  · intro v
    apply measurable_positive
    intro i b v
    exact ((measurable_pi_apply v).comp (seed i).measurable).comp (measurable_pi_apply i)
  · exact positive_affine (forest T hT root) B (active T hT root B D k dist J)
      (fun i u => noiseG (D i) (seed i).bump u) a
      (TreeCache.fresh_eq_singleton T hT root B D k dist J a) (fun ω => P.pair_distinct ω a)

end Model
end
end BoundedTreewidthL1.AnchorExperiment

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles _root_.OAI.BoundedTreewidthL1.RootedTree TreeCache AnchorCache ParticleBatch ExpandedConstruction
attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section

end
end BoundedTreewidthL1.AnchorExperiment

end OAI
