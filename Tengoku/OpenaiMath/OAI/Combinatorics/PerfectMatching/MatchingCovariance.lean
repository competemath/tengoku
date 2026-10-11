import Tengoku.OpenaiMath.OAI.Combinatorics.PerfectMatching.Continuity
import Tengoku.OpenaiMath.OAI.Combinatorics.PerfectMatching.Covariance

namespace OAI

/-!
Normalized matching covariance: face rank, exact trace, and second variation.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Normalized matching directions on exactly the positive edge support. -/
def matchingNormalized (G : LooplessGraph V E) (x : E → ℝ) :
    G.Matching → {e // 0 < x e} → ℝ :=
  normalizedCentered (fun M e => G.indicator M e.val) (fun e => x e.val)

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_average (G : LooplessGraph V E) {x y : E → ℝ}
    {q : G.Matching → ℝ} (hq : q ∈ G.feasibleLaws y) (e : {e // 0 < x e}) :
    (∑ M, q M*matchingNormalized G x M e)=(y e.val-x e.val)/Real.sqrt (x e.val) := by
  simp only [matchingNormalized,normalizedCentered,← mul_div_assoc,mul_sub,
    ← Finset.sum_div,Finset.sum_sub_distrib,← Finset.sum_mul,hq.1.2,one_mul]
  rw [show (∑ M, q M*G.indicator M e.val)=y e.val from congrFun hq.2 e.val]

def normalizeLinear (x : E → ℝ) :
    ({e // 0 < x e} → ℝ) →ₗ[ℝ] ({e // 0 < x e} → ℝ) where
  toFun := fun u e => u e/Real.sqrt (x e.val)
  map_add' := by intro u v; ext e; exact add_div _ _ _
  map_smul' := by intro a u; ext e; exact mul_div_assoc _ _ _

omit [DecidableEq E] in
theorem sum_positive_support (x f : E → ℝ) (hf : ∀ e, ¬ 0 < x e → f e=0) :
    (∑ e, f e) = ∑ e : {e // 0 < x e}, f e.val := by
  classical
  have hz : (∑ e : {e // ¬ 0 < x e}, f e.val)=0 :=
    Finset.sum_eq_zero fun e _ => hf e.val e.property
  have hh := Fintype.sum_subtype_add_sum_subtype (fun e => 0 < x e) f
  rw [hz,add_zero] at hh
  exact hh.symm

def matchingScoreWeights (x : E → ℝ) (u : {e // 0 < x e} → ℝ) : E → ℝ :=
  LooplessGraph.positiveExtension x (fun e => u e/Real.sqrt (x e.val))

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_score (G : LooplessGraph V E) (x : E → ℝ)
    (u : {e // 0 < x e} → ℝ) (M : G.Matching) :
    linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e) M =
      matchingNormalized G x M ⬝ᵥ u := by
  classical
  unfold linearScore
  rw [← Finset.sum_sub_distrib]
  rw [sum_positive_support x _ (fun e he => by simp [matchingScoreWeights,LooplessGraph.positiveExtension,he])]
  rw [dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  simp only [matchingScoreWeights,LooplessGraph.positiveExtension_pos,matchingNormalized,normalizedCentered]
  ring

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_mulVec (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (u : {e // 0 < x e} → ℝ) (e : {e // 0 < x e}) :
    (covariance p (matchingNormalized G x) *ᵥ u) e =
      G.mean (fun M => p M * linearScore G (matchingScoreWeights x u)
        (∑ e, matchingScoreWeights x u e*x e) M) e.val / Real.sqrt (x e.val) := by
  let a := linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e)
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  calc
    _ = ∑ M, (p M*a M*G.indicator M e.val-x e.val*(p M*a M))/Real.sqrt (x e.val) := by
      rw [covariance_mulVec hp.1.1]
      apply Finset.sum_congr rfl
      intro M _
      rw [← matchingNormalized_score G x u M]
      change p M*((G.indicator M e.val-x e.val)/Real.sqrt (x e.val))*a M = _
      ring
    _ = _ := by
      rw [← Finset.sum_div,Finset.sum_sub_distrib,← Finset.mul_sum,hcenter,mul_zero,sub_zero]
      rfl

/-- The normalized covariance has the exact trace s-m. -/
theorem matching_covariance_trace (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) {m : ℕ}
    (hV : Fintype.card V=2*m) :
    (covariance p (matchingNormalized G x)).trace = Fintype.card {e // 0 < x e}-(m:ℝ) := by
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hsum : (∑ e : {e // 0 < x e}, x e.val)=(m:ℝ) := by
    rw [← G.marginal_sum hV hx]
    exact (sum_positive_support x x (fun e he => le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1)).symm
  unfold matchingNormalized
  rw [normalized_covariance_trace hp.1 _ ?_ _ ?_ (fun e => e.property),hsum]
  · intro M e
    simp only [LooplessGraph.indicator]
    split <;> norm_num
  · intro e
    exact congrFun hp.2 e.val

end MatchingEntropy

end

end OAI
