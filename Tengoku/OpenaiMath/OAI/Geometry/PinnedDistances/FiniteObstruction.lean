import Tengoku.OpenaiMath.OAI.Geometry.PinnedDistances.MeasureLimits

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter
namespace WeakPinned.Bounded
end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace WeakPinned.Bounded
open Variance
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩
local instance : MeasurableSingletonClass (Quad Sphere) := inferInstance
local instance : MeasurableSingletonClass ((Sphere × Sphere) × (Sphere × Sphere)) := inferInstance
local instance : MeasurableSingletonClass (Expanded Sphere) := Prod.instMeasurableSingletonClass
variable {V : Type u1} {I : Type u2} [Fintype V] [DecidableEq V] [Fintype I]
variable (G : Core.Fibers V I)

def zEquation : Set (Expanded ℂ) := {r | (r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
    (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)}
def wEquation : Set (Expanded ℂ) := {r | (r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
    (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)}

lemma zEquation_closed : IsClosed zEquation := isClosed_eq (by fun_prop) (by fun_prop)
lemma wEquation_closed : IsClosed wEquation := isClosed_eq (by fun_prop) (by fun_prop)

omit [Fintype I] in
lemma tripleWeight_mem {r : I × V × V × V}
    (hr : tripleWeight G.fiberWeight (fun e => prob (G.targets e)) r≠0) :
    r.2.1∈G.targets r.1 ∧ r.2.2.1∈G.targets r.1 ∧ r.2.2.2∈G.targets r.1 := by
  refine ⟨?_,?_,?_⟩
  all_goals
    by_contra h
    simp [tripleWeight,prob,h] at hr

lemma expanded_chart_zero (U₁ U₂ : V → ℂ) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty)
    (hrel : ∀ e y z,y∈G.targets e → z∈G.targets e →
      (U₁ y-U₁ (G.source e))*(U₂ y-U₂ (G.source e))=
      (U₁ z-U₁ (G.source e))*(U₂ z-U₂ (G.source e))) :
    (expandedProbability G (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)) hG hB :
      Measure (Expanded Sphere)) (expandedCoe '' zEquationᶜ)=0 ∧
    (expandedProbability G (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)) hG hB :
      Measure (Expanded Sphere)) (expandedCoe '' wEquationᶜ)=0 := by
  have hzero (s : Set (Expanded ℂ))
      (hs : ∀ r,tripleWeight G.fiberWeight (fun e => prob (G.targets e)) r≠0 →
        tripleValue G.source U₁ U₂ r∈s) :
      (expandedProbability G (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)) hG hB :
        Measure (Expanded Sphere)) (expandedCoe '' sᶜ)=0 := by
    have hh : ∀ᵐ r ∂  finiteLaw (tripleWeight G.fiberWeight (fun e => prob (G.targets e)))
        (tripleValue G.source (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere))),
        r∉expandedCoe '' sᶜ := by
      apply finiteLaw_ae
      intro r hr
      rintro ⟨q,hq,hqe⟩
      have he : q=tripleValue G.source U₁ U₂ r := expandedCoe_open.injective hqe
      subst q
      exact hq (hs r hr)
    change (finiteLaw (tripleWeight G.fiberWeight (fun e => prob (G.targets e)))
      (tripleValue G.source (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)))) (expandedCoe '' sᶜ)=0
    simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hh
  constructor
  · apply hzero
    intro r hr
    have hm := tripleWeight_mem G hr
    exact hrel r.1 r.2.2.1 r.2.1 hm.2.1 hm.1
  · apply hzero
    intro r hr
    have hm := tripleWeight_mem G hr
    exact hrel r.1 r.2.2.2 r.2.1 hm.2.2 hm.1

end WeakPinned.Bounded

end
end

end OAI
