import Tengoku.OpenaiMath.OAI.Analysis.TreePotential.Leakage

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section FiniteMassApproximation
open Filter Topology
open scoped Classical
variable {I : Type*}

abbrev FiniteMass (I : Type*) := {μ : L1Mass I // (Function.support μ).Finite}

def finiteMassPartial (μ : L1Mass I) (S : Finset I) : FiniteMass I :=
  ⟨∑ i ∈ S, lp.single 1 i (μ i), S.finite_toSet.subset (by
    intro j hj
    by_contra hjs
    change j ∉ S at hjs
    apply hj
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single,
      ite_eq_right hjs])⟩

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

end FiniteMassApproximation

namespace CostHeads
open TreeCalculus BlockCalculus Filter Topology
open scoped Classical

end CostHeads

section SymmetricLenses
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma lens_half_difference (x u v : E) {R : ℝ}
    (hup : ‖x+u‖ ≤ R) (hum : ‖x-u‖ ≤ R)
    (hvp : ‖x+v‖ ≤ R) (hvm : ‖x-v‖ ≤ R) :
    ‖x+(1/2:ℝ) • (u-v)‖ ≤ R ∧ ‖x-(1/2:ℝ) • (u-v)‖ ≤ R := by
  have hp : x+(1/2:ℝ) • (u-v) = (1/2:ℝ) • ((x+u)+(x-v)) := by module
  have hm : x-(1/2:ℝ) • (u-v) = (1/2:ℝ) • ((x-u)+(x+v)) := by module
  rw [hp, hm, norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  constructor
  · nlinarith [norm_add_le (x+u) (x-v)]
  · nlinarith [norm_add_le (x-u) (x+v)]

end SymmetricLenses

namespace CostHeads
open TreeCalculus BlockCalculus Filter Topology
open scoped Classical

end CostHeads

section FurtherModuli
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def maximumModulus (t : ℝ) : EReal :=
  ⨅ x : {x : E // ‖x‖ = 1}, ⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ 1 ≤ ‖y‖},
      ((max ‖x.val+t • y.val‖ ‖x.val-t • y.val‖-1 : ℝ) : EReal)

lemma averagedModulus_le_maximum (t : ℝ) : averagedModulus E t ≤ maximumModulus E t := by
  apply iInf_mono
  intro x
  apply iSup_mono
  intro F
  apply iInf_mono
  intro y
  apply EReal.coe_le_coe_iff.mpr
  linarith [le_max_left ‖x.val+t • y.val‖ ‖x.val-t • y.val‖,
    le_max_right ‖x.val+t • y.val‖ ‖x.val-t • y.val‖]

end FurtherModuli

namespace CostHeads
open TreeCalculus BlockCalculus Filter Topology
open scoped Classical

/-- Empty heads are used exactly on zero components of the center. -/

def activeHead (A : FiniteOuterHead) (x : QuadraticOuter) : FiniteOuterHead where
  nodes n := if x n = 0 then ∅ else A.nodes n
  initial n := by
    by_cases h : x n = 0
    · simp only [h, ↓reduceIte]
      intro s r hs
      exact hs.elim
    · simpa only [h, ↓reduceIte] using A.initial n
  finite_nodes := A.finite_nodes.subset (by
    intro s hs
    change s.2.val ∈ (if x s.1 = 0 then ∅ else A.nodes s.1) at hs
    change s.2.val ∈ A.nodes s.1
    by_cases h : x s.1 = 0
    · simp only [h, ↓reduceIte, Set.mem_empty_iff_false] at hs
    · simpa only [h, ↓reduceIte] using hs)

theorem quadratic_maximum_modulus {t : ℝ} (ht : 0 < t) :
    ((Real.sqrt (1+t^2/16)-1 : ℝ) : EReal) ≤ maximumModulus QuadraticOuter t :=
  (quadratic_averaged_modulus ht).trans (averagedModulus_le_maximum QuadraticOuter t)

theorem quadratic_maximum_modulus_positive {t : ℝ} (ht : 0 < t) :
    0 < maximumModulus QuadraticOuter t := by
  have hs : 1 < Real.sqrt (1+t^2/16) := by
    have hh := Real.sq_sqrt (show 0 ≤ 1+t^2/16 by positivity)
    nlinarith [Real.sqrt_nonneg (1+t^2/16), sq_pos_of_pos ht]
  have hp : (0:EReal) < ((Real.sqrt (1+t^2/16)-1:ℝ):EReal) := by
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  exact hp.trans_le (quadratic_maximum_modulus ht)

end CostHeads
end BoundedTreePotentials

namespace BoundedTreePotentials.BlockCalculus
open TreeCalculus

end BoundedTreePotentials.BlockCalculus

end

end OAI
