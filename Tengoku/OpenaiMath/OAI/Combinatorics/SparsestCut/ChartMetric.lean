import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.TriangleRepair

namespace OAI

universe u1 u2 u3 u4 u5 u6

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartMetric
open scoped BigOperators RealInnerProductSpace
open TriangleRepair
noncomputable section
variable {ι : Type u1} {C : Type u2} {J : Type u3} {E : Type u4} {H : Type u5} [Fintype ι] [Fintype C] [Fintype J] [DecidableEq C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma neg_min_eq (a b : ℝ) : -min a b=max (-a) (-b) := by
  rcases le_total a b with h|h
  · rw [min_eq_left h,max_eq_left (neg_le_neg h)]
  · rw [min_eq_right h,max_eq_right (neg_le_neg h)]

omit [Fintype ι] [Fintype C] [InnerProductSpace ℝ H] in
lemma capped_angle (c : ι → C) (h : ι → H) {r : ℝ} (P : ι → E)
    (hg : ∀ v z y, -r≤ inner ℝ (P v-P z) (P y-P z))
    (hl : ∀ v z y, c v=c z → |inner ℝ (P v-P z) (P y-P z)|≤‖h v-h z‖^2) :
    ∀ v y z, -min (cappedDistance c h r v z) (cappedDistance c h r y z)≤
      inner ℝ (P v-P z) (P y-P z) := by
  intro v y z
  have h1 : -cappedDistance c h r v z≤ inner ℝ (P v-P z) (P y-P z) := by
    by_cases hc : c v=c z
    · have hh := (abs_le.mp (hl v z y hc)).1
      simp only [cappedDistance,hc,ite_true,neg_min_eq]
      exact max_le (hg v z y) hh
    · simpa only [cappedDistance,hc,ite_false] using hg v z y
  have h2 : -cappedDistance c h r y z≤ inner ℝ (P v-P z) (P y-P z) := by
    by_cases hc : c y=c z
    · have hh := (abs_le.mp (hl y z v hc)).1
      rw [real_inner_comm] at hh
      simp only [cappedDistance,hc,ite_true,neg_min_eq]
      exact max_le (hg v z y) hh
    · simpa only [cappedDistance,hc,ite_false] using hg v z y
  rw [neg_min_eq]
  exact max_le h1 h2

end
end UniformSparsestCut.ChartMetric

namespace UniformSparsestCut.GramMetric
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {V : Type u6} [Fintype V]
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)

def localCost (N S : ℕ) (q k ε a b R γ : ℝ) : ℝ :=
  2*((k+q*γ*(4*k)+ε*((S:ℝ)*N)*(9*k/ε)*(k/ε*R))*Real.log (b/a)+
    (ε*((S:ℝ)*N)*(2*q)*(4*k)*(1+(k/ε*R)^2+2*(k/ε*R)))/a)

def macroCost (N S : ℕ) (q k ε a b R T Rpos : ℝ) : ℝ :=
  q*(2*a+(2*T)^2/b)+4*ε*((S:ℝ)*N)*Real.log (b/a)+
    4*(ε*((S:ℝ)*N)*((k/ε*R)^2+2*(k/ε*R))*Real.log (b/a))+2*KernelApprox.cstar*q*Rpos

lemma localCost_nonneg {q k ε a b R γ : ℝ} (hq : 0≤q) (hk : 0≤k)
    (hε : 0<ε) (ha : 0<a) (hab : a≤b) (hR : 0≤R) (hγ : 0≤γ) :
    0≤localCost N S q k ε a b R γ := by
  have hl : 0≤Real.log (b/a) := Real.log_nonneg ((one_le_div ha).mpr hab)
  unfold localCost; positivity

end
end UniformSparsestCut.GramMetric

end

end OAI
