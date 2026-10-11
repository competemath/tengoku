import Tengoku.OpenaiMath.OAI.Combinatorics.TreewidthL1.AnchorEmbedding

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

end BoundedTreewidthL1.ParticleLaws

namespace BoundedTreewidthL1.TreeParticles
variable {I J X : Type*} [DecidableEq J]
attribute [local instance] Classical.propDecidable

/-- The discrete launch location depends only on the rooted decomposition and
active keys. In particular it does not consult any preparatory randomness. -/
noncomputable def origin (R : RootedForest I) (A : I → Finset J) (root : I) : I → J → I :=
  R.run (fun _ => root) (fun i old a => if a ∈ retained R A i then old a else i)

lemma origin_eq (R : RootedForest I) (A : I → Finset J) (root i : I) (a : J) :
    origin R A root i a = if a ∈ retained R A i then
      ((R.parent i).elim (fun _ => root) (origin R A root)) a else i := by
  unfold origin
  rw [RootedForest.run_eq]

lemma origin_fresh (R : RootedForest I) (A : I → Finset J) (root i : I)
    (a : J) (ha : a ∈ A i) : a ∈ fresh R A (origin R A root i a) := by
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [origin_eq]
    by_cases hk : a ∈ retained R A i
    · rw [ite_eq_left hk]
      cases hp : R.parent i with
      | none => simp [retained,hp] at hk
      | some p =>
        simp only [Option.elim_some]
        have hap : a ∈ A p := (Finset.mem_inter.mp (by simpa [retained,hp] using hk)).2
        exact ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p hap rfl
    · rw [ite_eq_right hk]
      exact Finset.mem_sdiff.mpr ⟨ha,hk⟩

lemma origin_transport (R : RootedForest I) (A : I → Finset J) (root : I)
    (E : I → J → X)
    (hkeep : ∀ i p, R.parent i = some p → ∀ a ∈ A i ∩ A p, E i a = E p a)
    (i : I) (a : J) (ha : a ∈ A i) : E i a = E (origin R A root i a) a := by
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [origin_eq]
    by_cases hk : a ∈ retained R A i
    · rw [ite_eq_left hk]
      cases hp : R.parent i with
      | none => simp [retained,hp] at hk
      | some p =>
        simp only [Option.elim_some]
        have hap : a ∈ A i ∩ A p := by simpa [retained,hp] using hk
        exact (hkeep i p hp a hap).trans
          (ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p
            (Finset.mem_inter.mp hap).2 rfl)
    · rw [ite_eq_right hk]
end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.TreeParticles
open scoped BigOperators
variable {I V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J]

lemma two_particle_difference
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    (F : ι → V → ℝ) (a b : ι) (hab : a ≠ b)
    (g : V → ℝ) (hgap : ∀ v, F a v - F b v = 2*g v) (u v : V) :
    2*|g u-g v| ≤ ∑ t, |F t u-F t v| := by
  have hs : (∑ t ∈ ({a,b} : Finset ι), |F t u-F t v|) ≤ ∑ t, |F t u-F t v| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun t _ _ => abs_nonneg _)
  simp only [Finset.sum_pair hab] at hs
  have he : (F a u-F a v)-(F b u-F b v) = 2*(g u-g v) := by
    linarith [hgap u,hgap v]
  have ha := abs_sub (F a u-F a v) (F b u-F b v)
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
  exact ha.trans hs

end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.TreeParticles
open MeasureTheory ParticleLaws
open scoped BigOperators ENNReal
variable {I V ι J Ω : Type*} [Fintype I] [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq V] [DecidableEq ι] [DecidableEq J] [Fintype J] [MeasurableSpace Ω]

end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Set
open scoped unitInterval

theorem uniform_coefficient_integral_lower (a b : ℝ) :
    a/4 ≤ ∫ t : I, |a * (t : ℝ) - b| := by
  rw [unitInterval.measurePreserving_coe.integral_comp
    unitInterval.measurableEmbedding_coe (fun t : ℝ => |a*t-b|)]
  change a/4 ≤ ∫ t in Icc (0:ℝ) 1, |a*t-b|
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hi : ∀ x y : ℝ, IntervalIntegrable (fun t : ℝ => |a*t-b|) volume x y :=
    fun _ _ => (by fun_prop : Continuous (fun t : ℝ => |a*t-b|)).intervalIntegrable _ _
  have hl := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1/2)
    ((by fun_prop : Continuous (fun t : ℝ => b-a*t)).intervalIntegrable _ _)
    (hi 0 (1/2)) (fun t _ => by simpa only [neg_sub] using neg_le_abs (a*t-b))
  have hr := intervalIntegral.integral_mono_on (by norm_num : (1/2:ℝ) ≤ 1)
    ((by fun_prop : Continuous (fun t : ℝ => a*t-b)).intervalIntegrable _ _)
    (hi (1/2) 1) (fun t _ => le_abs_self (a*t-b))
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi 0 (1/2)) (hi (1/2) 1)
  have hli : (∫ t : ℝ in (0:ℝ)..(1/2:ℝ), b-a*t) = b/2-a/8 := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => a*t)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id]
    simp
    ring
  have hri : (∫ t : ℝ in (1/2:ℝ)..1, a*t-b) = 3*a/8-b/2 := by
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun t : ℝ => a*t)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id]
    simp
    ring
  rw [hli] at hl
  rw [hri] at hr
  linarith
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open Metric MeasureTheory
open scoped unitInterval
variable {V J : Type*} [MetricSpace V] [Fintype J]

noncomputable def cobagBump (A E : Set V) (r : ℝ) (x : V) : ℝ := by
  classical
  exact if A.Nonempty then min (infDist x A) (bump E r x) else bump E r x
noncomputable def cobagNoise (A : Set V) (E : J → Set V) (r : ℝ)
    (U : J → ℝ) (x : V) : ℝ := ∑ i, U i * cobagBump A (E i) r x

lemma cobagBump_eq_diff (A E : Set V) (r : ℝ) (x : V) :
    cobagBump A E r x = bump (E \ A) r x := by
  classical
  by_cases hA : A.Nonempty
  · have hd : (E \ A)ᶜ.Nonempty := by
      obtain ⟨a, ha⟩ := hA
      exact ⟨a, fun h => h.2 ha⟩
    by_cases hE : Eᶜ.Nonempty
    · have hi : infDist x (E \ A)ᶜ = min (infDist x Eᶜ) (infDist x A) := by
        have he : (E \ A)ᶜ = Eᶜ ∪ A := by ext z; simp; tauto
        rw [he, infDist, infEDist_union, ENNReal.toReal_min (infEDist_ne_top hE)
          (infEDist_ne_top hA)]
        rfl
      simp only [cobagBump, hA, ↓reduceIte, bump, hE, hd, hi]
      simp only [min_left_comm, min_comm]
    · have he : E = Set.univ := by
        apply Set.eq_univ_of_forall
        intro z
        by_contra hz
        exact hE ⟨z, hz⟩
      have hec : (Set.univ \ A : Set V)ᶜ = A := by ext z; simp
      simp [cobagBump, hA, bump, he, hec, min_comm]
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    simp [cobagBump, he]

lemma cobagNoise_eq_diff (A : Set V) (E : J → Set V) (r : ℝ) (U : J → ℝ) :
    cobagNoise A E r U = noise (fun i => E i \ A) (fun _ => r) U := by
  funext x
  simp [cobagNoise, noise, cobagBump_eq_diff]

lemma cobag_diff_disjoint
    {V : Type treewidthLevel1} {J : Type treewidthLevel2} [MetricSpace V] [Fintype J]
    (A : Set V) (E : J → Set V)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) :
    Pairwise (fun i j => Disjoint (E i \ A) (E j \ A)) :=
  fun _ _ hij => (hE hij).mono Set.sdiff_subset Set.sdiff_subset

theorem cobag_partition_properties (A : Set V) (E : J → Set V) (r : ℝ)
    (hr : 0 ≤ r) (hE : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : ∀ x, ∃ i, x ∈ E i) (U : J → ℝ) (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1) :
    LipschitzWith 1 (cobagNoise A E r U) ∧
    (∀ x, 0 ≤ cobagNoise A E r U x ∧ cobagNoise A E r U x ≤ r) ∧
    (∀ x ∈ A, cobagNoise A E r U x = 0) := by
  rw [cobagNoise_eq_diff]
  have h := disjoint_noise (fun i => E i \ A) (fun _ => r) U
    (cobag_diff_disjoint A E hE) (fun _ => hr) hU
  refine ⟨h.1, fun x => ⟨h.2.1 x, ?_⟩, ?_⟩
  · by_cases hx : x ∈ A
    · rw [h.2.2.2 x (fun i h => h.2 hx)]
      exact hr
    · obtain ⟨i, hi⟩ := hcover x
      exact h.2.2.1 i x ⟨hi,hx⟩
  · intro x hx
    exact h.2.2.2 x (fun i h => h.2 hx)

lemma cobagBump_bounds (A E : Set V) (r : ℝ) (hr : 0 ≤ r) (x : V) :
    0 ≤ cobagBump A E r x ∧ cobagBump A E r x ≤ r := by
  rw [cobagBump_eq_diff]
  exact bump_bounds _ _ hr _

lemma cobagBump_zero (A E : Set V) (r : ℝ) (hr : 0 ≤ r) (x : V) (hx : x ∉ E) :
    cobagBump A E r x = 0 := by
  rw [cobagBump_eq_diff]
  exact bump_zero _ _ hr _ (fun h => hx h.1)

lemma cobagBump_padding (A E : Set V) (r a : ℝ) (x : V)
    (har : a ≤ r) (hball : ball x a ⊆ E) (hA : A.Nonempty → a ≤ infDist x A) :
    a ≤ cobagBump A E r x := by
  classical
  unfold cobagBump
  split_ifs with hne
  · exact le_min (hA hne) (bump_padding E r x a har hball)
  · exact bump_padding E r x a har hball

lemma coefficient_affine_integral_lower {m : ℕ} (j : Fin (m+1))
    (a : Fin (m+1) → ℝ) :
    a j / 4 ≤ ∫ U : Fin (m+1) → I, |∑ i, (U i:ℝ) * a i| := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => I) j
  let f : I × (Fin m → I) → ℝ := fun z =>
    |(z.1:ℝ)*a j + ∑ i, (z.2 i:ℝ)*a (j.succAbove i)|
  have hc : Continuous f := by unfold f; fun_prop
  have hi : Integrable f := hc.integrable_of_hasCompactSupport (.of_compactSpace _)
  have he : (∫ U : Fin (m+1) → I, |∑ i, (U i:ℝ)*a i|) = ∫ z, f z := by
    have hh := (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => I) j).integral_comp
      e.measurableEmbedding f
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [] with U
    congr 1
    exact Fin.sum_univ_succAbove (fun i => (U i:ℝ)*a i) j
  rw [he]
  change a j / 4 ≤ ∫ z, f z ∂(volume.prod volume)
  rw [integral_prod_symm f hi]
  have hb (U : Fin m → I) : a j/4 ≤ ∫ t : I, f (t,U) := by
    convert uniform_coefficient_integral_lower (a j)
      (-(∑ i, (U i:ℝ)*a (j.succAbove i))) using 1
    congr 1
    funext t
    simp [f, mul_comm, sub_neg_eq_add]
  have hm := integral_mono (integrable_const (a j/4)) hi.integral_prod_right hb
  simpa using hm

theorem cobag_partition_averaging {m : ℕ} (A : Set V)
    (E : Fin (m+1) → Set V) (r α : ℝ) (hr : 0 < r) (_ : 0 < α) (hα1 : α ≤ 1)
    (_ : Pairwise (fun i j => Disjoint (E i) (E j)))
    (_ : ∀ x, ∃ i, x ∈ E i) (j : Fin (m+1)) (x y : V)
    (hx : ball x (α*r) ⊆ E j) (hy : y ∉ E j)
    (hA : A.Nonempty → α*r ≤ infDist x A) :
    α*r/4 ≤ ∫ U : Fin (m+1) → I,
      |cobagNoise A E r (fun i => (U i:ℝ)) x -
       cobagNoise A E r (fun i => (U i:ℝ)) y| := by
  classical
  let a : Fin (m+1) → ℝ := fun i => cobagBump A (E i) r x - cobagBump A (E i) r y
  have ha : α*r ≤ a j := by
    dsimp [a]
    rw [cobagBump_zero A (E j) r hr.le y hy, sub_zero]
    apply cobagBump_padding A (E j) r (α*r) x _ hx hA
    exact mul_le_of_le_one_left hr.le hα1
  have hsum (U : Fin (m+1) → I) :
      cobagNoise A E r (fun i => (U i:ℝ)) x -
      cobagNoise A E r (fun i => (U i:ℝ)) y = ∑ i, (U i:ℝ)*a i := by
    simp only [cobagNoise, a, mul_sub, Finset.sum_sub_distrib]
  simp_rw [hsum]
  exact (div_le_div_of_nonneg_right ha (by norm_num)).trans
    (coefficient_affine_integral_lower j a)
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Metric
open scoped unitInterval ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def cobagLocationLaw {n : ℕ} (μ : Fin n → ℝ) : Measure (Fin n) :=
  ∑ a, ENNReal.ofReal (μ a) • Measure.dirac a
noncomputable def cobagLaw {n : ℕ} (m : ℕ) (μ : Fin n → ℝ) :
    Measure (Fin n × (Fin (m+1) → I)) := (cobagLocationLaw μ).prod volume
noncomputable def cobagSample {V : Type*} [MetricSpace V] {n m : ℕ}
    (A : Set V) (P : Fin n → V → Fin (m+1)) (r : ℝ)
    (ω : Fin n × (Fin (m+1) → I)) (x : V) : ℝ :=
  cobagNoise A (fun j => {z | P ω.1 z = j}) r (fun j => (ω.2 j:ℝ)) x

lemma cobagLocationLaw_probability {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) :
    IsProbabilityMeasure (cobagLocationLaw μ) := by
  classical
  constructor
  simp only [cobagLocationLaw, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hμ a), hμ₁, ENNReal.ofReal_one]

lemma cobagLocationLaw_integral {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (f : Fin n → ℝ) :
    (∫ a, f a ∂cobagLocationLaw μ) = ∑ a, μ a * f a := by
  classical
  rw [cobagLocationLaw, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_smul_measure, integral_dirac]
    simp [ENNReal.toReal_ofReal (hμ a)]
  · intro a _
    exact (integrable_dirac (f := f) (by simp)).smul_measure (by simp)

lemma cobagSample_continuous {V : Type*} [MetricSpace V] {n m : ℕ}
    (A : Set V) (P : Fin n → V → Fin (m+1)) (r : ℝ) (x : V) :
    Continuous (fun ω => cobagSample A P r ω x) := by
  unfold cobagSample cobagNoise
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul
  · fun_prop
  · exact (continuous_of_discreteTopology (f := fun a : Fin n =>
      cobagBump A {z | P a z = j} r x)).comp continuous_fst

lemma cobagSample_integral {V : Type*} [MetricSpace V] {n m : ℕ}
    (A : Set V) (P : Fin n → V → Fin (m+1)) (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) (r : ℝ) (x y : V) :
    (∫ ω, |cobagSample A P r ω x - cobagSample A P r ω y| ∂cobagLaw m μ) =
      ∑ a, μ a * ∫ U : Fin (m+1) → I,
        |cobagSample A P r (a,U) x - cobagSample A P r (a,U) y| := by
  let := cobagLocationLaw_probability μ hμ hμ₁
  let : IsProbabilityMeasure (cobagLaw m μ) := by unfold cobagLaw; infer_instance
  have hc := ((cobagSample_continuous A P r x).sub (cobagSample_continuous A P r y)).abs
  have hi : Integrable (fun ω => |cobagSample A P r ω x - cobagSample A P r ω y|)
      (cobagLaw m μ) :=
    hc.integrable_of_hasCompactSupport (.of_compactSpace _)
  rw [cobagLaw, integral_prod _ hi, cobagLocationLaw_integral μ hμ]

end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Metric
open scoped unitInterval

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev FiniteSampleSpace (V : Type*) [Fintype V] :=
  Fin (Fintype.card (V → V)) × (Fin (Fintype.card V + 1) → I)

end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Metric
attribute [local instance] Classical.propDecidable Classical.decEq

end BoundedTreewidthL1.LaunchNoise

end OAI
