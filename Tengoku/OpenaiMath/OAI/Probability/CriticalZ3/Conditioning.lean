import Tengoku.OpenaiMath.OAI.Probability.CriticalZ3.SeedTrials

namespace OAI

universe uF

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

/-! The exact revealed-history law used by the adaptive queue.  In particular,
classifications depending only on revealed values do not change fresh bits. -/
namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

noncomputable def replace (J : Finset E) (ξ ω : E → Bool) : E → Bool :=
  fun e => if e ∈ J then ξ e else ω e

noncomputable def fixedParameter (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (ξ : E → Bool) : E → Set.Icc (0 : ℝ) 1 :=
  fun e => if e ∈ J then if ξ e = true then 1 else 0 else p e

def pattern (J : Finset E) (ξ : E → Bool) : Set (E → Bool) :=
  {ω | ∀ e ∈ J, ω e = ξ e}

theorem measurableSet_pattern (J : Finset E) (ξ : E → Bool) : MeasurableSet (pattern J ξ) := by
  simp only [pattern, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_pi_apply e) measurable_const))

omit [Countable E] in
theorem replace_eq_of_pattern {J : Finset E} {ξ ω : E → Bool} (h : ω ∈ pattern J ξ) :
    replace J ξ ω = ω := by
  funext e
  by_cases he : e ∈ J
  · exact (ite_eq_left he).trans (h e he).symm
  · exact ite_eq_right he

omit [Countable E] in
theorem map_replace (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    (ProductCylinder.law p).map (replace J ξ) = ProductCylinder.law (fixedParameter p J ξ) := by
  have h (e : E) :
      (bernoulliMeasure true false (p e)).map (fun b : Bool => if e ∈ J then ξ e else b) =
        bernoulliMeasure true false (fixedParameter p J ξ e) := by
    by_cases he : e ∈ J
    · simp only [he,ite_true,fixedParameter]
      cases ξ e <;> simp
    · simp only [he,ite_false,fixedParameter]
      exact Measure.map_id
  change (Measure.infinitePi (fun e => bernoulliMeasure true false (p e))).map
    (fun ω e => (fun b => if e ∈ J then ξ e else b) (ω e)) = _
  rw [Measure.infinitePi_map_pi]
  · simp only [h,ProductCylinder.law]
  · intro e; exact measurable_of_countable _

private abbrev bitSigma (e : E) : MeasurableSpace (E → Bool) :=
  MeasurableSpace.comap (fun ω => ω e) inferInstance

omit [Countable E] in
theorem pattern_extend_iff (J : Finset E) (a : J → Bool) (ω : E → Bool) :
    ω ∈ pattern J (ProductCylinder.extend J a) ↔ J.restrict ω = a := by
  constructor
  · intro h; funext e
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left e.2] using h e e.2
  · intro h e he
    have hh := congrFun h ⟨e,he⟩
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left he] using hh

omit [Countable E] in
theorem fixedParameter_congr (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    {ξ ξ' : E → Bool} (h : ∀ e ∈ J, ξ e = ξ' e) :
    fixedParameter p J ξ = fixedParameter p J ξ' := by
  funext e
  by_cases he : e ∈ J
  · simp only [fixedParameter,he,ite_true,h e he]
  · simp only [fixedParameter,he,ite_false]

theorem measurableSet_select (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) :
    MeasurableSet {ω | ω ∈ A (J.restrict ω)} := by
  have heq : {ω | ω ∈ A (J.restrict ω)} =
      ⋃ a : J → Bool, pattern J (ProductCylinder.extend J a) ∩ A a := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,pattern_extend_iff]
    exact ⟨fun h => ⟨J.restrict ω,rfl,h⟩, fun ⟨a,ha,h⟩ => ha.symm ▸ h⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun a => (measurableSet_pattern _ _).inter (hA a))

end InfiniteConditioning

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E I : Type}

end InfiniteConditioning

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type}

noncomputable def bitProbability (p : Set.Icc (0 : ℝ) 1) (b : Bool) : ℝ :=
  if b then p else 1-(p : ℝ)

theorem single_probability (p : E → Set.Icc (0 : ℝ) 1) (e : E) (b : Bool) :
    (ProductCylinder.law p).real {ω | ω e = b} = bitProbability (p e) b := by
  have h := Measure.infinitePi_map_eval (fun e : E => bernoulliMeasure true false (p e)) e
  have hm : Measurable (fun ω : E → Bool => ω e) := measurable_pi_apply e
  have he : {ω : E → Bool | ω e = b} = (fun ω => ω e) ⁻¹' {b} := rfl
  rw [he,Measure.real_def,←Measure.map_apply hm (measurableSet_singleton _)]
  change ((Measure.infinitePi (fun e : E => bernoulliMeasure true false (p e))).map
    (fun ω => ω e) {b}).toReal = _
  rw [h]
  change (bernoulliMeasure true false (p e)).real {b} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton _)]
  cases b <;> simp [bitProbability,unitInterval.coe_symm_eq]

def allValue (J : Finset E) (b : Bool) : Set (E → Bool) := {ω | ∀ e ∈ J, ω e = b}

theorem allValue_determined (J : Finset E) (b : Bool) :
    ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ allValue J b) := by
  intro ω ω' h
  apply propext
  constructor <;> intro hh e he
  · rw [←h e he]; exact hh e he
  · rw [h e he]; exact hh e he

theorem measurableSet_allValue (J : Finset E) (b : Bool) : MeasurableSet (allValue J b) :=
  ProductCylinder.measurableSet_determined J _
    (fun ω ω' h => eq_iff_iff.mp (allValue_determined J b ω ω' h))

variable [Countable E]

end InfiniteConditioning

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

end InfiniteConditioning

end OAI
