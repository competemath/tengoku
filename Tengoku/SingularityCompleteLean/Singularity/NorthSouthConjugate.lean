import Tengoku.SingularityCompleteLean.Singularity.NorthSouthPingPong
import Tengoku.Seed.Topology.Algebra.MulAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conjugating north--south dynamics

Conjugation transports the attracting and repelling points. A single element
and a conjugate therefore give a free subgroup when their four endpoints are
distinct.
-/

noncomputable section
open Set Filter
open scoped Classical Topology Pointwise

namespace Singularity

variable {G : Type} {X : Type*} [Group G] [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]

/-- Uniform north--south dynamics is preserved by conjugation.
@isnad1 id=uniformn.1h6v.s7.cdf5ad6781c1 from=translated src=- shape=9302f3ae vocab=7d978a3d
-/
theorem UniformNorthSouth.conjugate {g : G} {p q : X}
    (h : UniformNorthSouth g p q) (b : G) :
    UniformNorthSouth (b * g * b⁻¹) (b • p) (b • q) := by
  intro U hU V hV
  have hU' : (fun x : X => b • x) ⁻¹' U ∈ nhds p :=
    (continuous_const_smul b).continuousAt.preimage_mem_nhds hU
  have hV' : (fun x : X => b • x) ⁻¹' V ∈ nhds q :=
    (continuous_const_smul b).continuousAt.preimage_mem_nhds hV
  filter_upwards [h _ hU' _ hV'] with n hn
  intro x hx
  have hb : b⁻¹ • x ∉ (fun y : X => b • y) ⁻¹' V := by
    simpa using hx
  have him := hn (b⁻¹ • x) hb
  change b • (g ^ n • (b⁻¹ • x)) ∈ U at him
  have hpow : (b * g * b⁻¹) ^ n = b * g ^ n * b⁻¹ := by
    clear hn him
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ, ih]; group
  simpa only [hpow, mul_smul] using him

/-- An element and a conjugate with disjoint endpoint pairs have free positive powers.
@isnad1 id=ex.2h6v.s8.47695c12d376 from=translated src=- shape=31c9bb39 vocab=d276648d
-/
theorem northSouth_conjugate_free_powers [T2Space X] {g : G} {p q : X}
    (h : UniformNorthSouth g p q) (b : G)
    (hdistinct : Function.Injective (fun z : Bool × Bool =>
      if z.1 then b • (if z.2 then p else q) else (if z.2 then p else q))) :
    ∃ n : ℕ, 0 < n ∧ Function.Injective
      (FreeGroup.lift (fun i : Bool => if i then (b * g * b⁻¹) ^ n else g ^ n)) := by
  have hdyn (i : Bool) : UniformNorthSouth
      (if i then b * g * b⁻¹ else g) (if i then b • p else p) (if i then b • q else q) := by
    cases i
    · exact h
    · exact h.conjugate b
  have hdist : Function.Injective (fun z : Bool × Bool =>
      if z.2 then (if z.1 then b • p else p) else (if z.1 then b • q else q)) := by
    convert hdistinct using 1
    funext z
    rcases z with ⟨i, j⟩
    cases i <;> cases j <;> rfl
  obtain ⟨n, hn, hinj⟩ := northSouth_free_powers
    (fun i => if i then b * g * b⁻¹ else g)
    (fun i => if i then b • p else p) (fun i => if i then b • q else q) hdist hdyn
  refine ⟨n, hn, ?_⟩
  have he : (fun i : Bool => if i then (b * g * b⁻¹) ^ n else g ^ n) =
      (fun i : Bool => (if i then b * g * b⁻¹ else g) ^ n) := by
    funext i
    cases i <;> rfl
  rwa [← he] at hinj

/-- The conjugate-pair criterion supplies classical nonamenability.
@isnad1 id=not.2h6v.s7.c03a140dbb76 from=translated src=- shape=1c016e73 vocab=e3c694ca
-/
theorem no_invariantMean_of_northSouth_conjugate [T2Space X] {g : G} {p q : X}
    (h : UniformNorthSouth g p q) (b : G)
    (hdistinct : Function.Injective (fun z : Bool × Bool =>
      if z.1 then b • (if z.2 then p else q) else (if z.2 then p else q))) :
    ¬HasInvariantMean G := by
  obtain ⟨n, _, hinj⟩ := northSouth_conjugate_free_powers h b hdistinct
  exact no_invariantMean_of_free_subgroup _ hinj

end Singularity
