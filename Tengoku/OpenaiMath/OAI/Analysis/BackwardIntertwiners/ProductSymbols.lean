import Tengoku.OpenaiMath.OAI.Analysis.BackwardIntertwiners.AtomicAlgebras

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] realOperatorTower realOperatorCommute complexNormalCalculus complexClosedCalculus realSelfAdjointCalculus

open InnerProductSpace ContinuousLinearMap

lemma ae_prod_count_iff {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p : X × ℤ → Prop} (hp : MeasurableSet {z | p z}) :
    (∀ᵐ z ∂μ.prod Measure.count, p z) ↔ ∀ᵐ x ∂μ, ∀ j : ℤ, p (x,j) := by
  rw [Measure.ae_prod_iff_ae_ae hp]
  simp_rw [Measure.ae_count_iff]

abbrev productMeasure : Measure (Base × ℤ) := baseMeasure.prod Measure.count

def IsProductMultiplier (T : GlobalHilbert →L[ℂ] GlobalHilbert) : Prop :=
  ∃ g : Lp ℂ ∞ productMeasure, ∀ f : GlobalHilbert,
    ∀ᵐ x ∂baseMeasure, ∀ j : ℤ, T f x j = g (x,j) * f x j

lemma DiagonalSymbol.product_measurable (a : DiagonalSymbol) :
    Measurable (fun z : Base × ℤ => a z.1 z.2) :=
  measurable_from_prod_countable_left a.measurable
lemma DiagonalSymbol.product_memLp (a : DiagonalSymbol) :
    MemLp (fun z : Base × ℤ => a z.1 z.2) ∞ productMeasure :=
  memLp_top_of_bound a.product_measurable.aestronglyMeasurable a.bound
    (Eventually.of_forall fun z => a.norm_le_bound z.1 z.2)

def productBoundedSymbol (g : Lp ℂ ∞ productMeasure) : DiagonalSymbol :=
  ⟨fun x j => if ‖g (x,j)‖ ≤ ‖g‖ then g (x,j) else 0,
    (by
      refine ⟨?_,‖g‖,norm_nonneg _,?_⟩
      · intro j
        have hm : Measurable (fun x : Base => g (x,j)) :=
          (Lp.stronglyMeasurable g).measurable.comp (measurable_id.prodMk measurable_const)
        exact Measurable.ite (measurableSet_le hm.norm measurable_const) hm measurable_const
      · intro x j
        dsimp only
        split_ifs with h
        · exact h
        · simp)⟩

end
end BackwardIntertwiners

end OAI
