import Tengoku.OpenaiMath.OAI.Analysis.TreePotential.Clipping

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section WeightedMidpoints
variable {I : Type*} {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [spaceE : ∀ i, NormedSpace ℝ (E i)]

lemma lp_hasSum_sq {I : Type*} {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (x : HilbertSum E) :
    HasSum (fun i => ‖x i‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using lp.hasSum_norm (by norm_num) x

lemma lp_midpoint_sq (x z u v : HilbertSum E)
    (h : ∀ i, ‖x i‖^2+‖z i‖^2/16 ≤ ((‖u i‖+‖v i‖)/2)^2) :
    ‖x‖^2+‖z‖^2/16 ≤ ((‖u‖+‖v‖)/2)^2 := by
  let w : lp (fun _ : I => ℝ) 2 := (1/2 : ℝ) • (lp.toNorm u+lp.toNorm v)
  have hws : HasSum (fun i => ((‖u i‖+‖v i‖)/2)^2) (‖w‖^2) := by
    have he := lp_hasSum_sq w
    convert he using 1
    funext i
    change ((‖u i‖+‖v i‖)/2)^2 = ‖(1/2 : ℝ)*(‖u i‖+‖v i‖)‖^2
    rw [Real.norm_eq_abs, sq_abs]
    ring
  have hxs := (lp_hasSum_sq x).add ((lp_hasSum_sq z).div_const 16)
  have hh := hxs.summable.tsum_le_tsum h hws.summable
  rw [hxs.tsum_eq, hws.tsum_eq] at hh
  have hw : ‖w‖ ≤ (‖u‖+‖v‖)/2 := by
    dsimp [w]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    have ht := norm_add_le (lp.toNorm u) (lp.toNorm v)
    rw [lp.norm_toNorm, lp.norm_toNorm] at ht
    nlinarith
  nlinarith [norm_nonneg w]

end WeightedMidpoints

/-- A finite ancestral subset of the disjoint union of the finite-height trees. -/
structure FiniteOuterHead where
  nodes : ℕ → Set TreeCalculus.Node
  initial : ∀ n, TreeCalculus.Initial (nodes n)
  finite_nodes : {s : (n : ℕ) × Tree (n+1) | s.2.val ∈ nodes s.1}.Finite

namespace CostHeads
open BlockCalculus
open TreeCalculus
open scoped Classical

def linearHead (n : ℕ) (D : Set Node) (hD : Initial D) : LinearBlock n →L[ℝ] LinearBlock n :=
  (((linearBlockEquiv n).symm.toLinearMap.comp (headLM D)).comp (linearBlockEquiv n).toLinearMap).mkContinuous
    1 (by
      intro x
      change linearBlockCost n (head D (linearBlockEquiv n x)) ≤ 1*linearBlockCost n (linearBlockEquiv n x)
      simpa only [one_mul] using head_linearCost_le hD (linearBlockEquiv n x))

@[simp] lemma linearHead_equiv (n : ℕ) (D : Set Node) (hD : Initial D) (x : LinearBlock n) :
    linearBlockEquiv n (linearHead n D hD x) = head D (linearBlockEquiv n x) := rfl

lemma linearHead_norm (n : ℕ) (D : Set Node) (hD : Initial D) : ‖linearHead n D hD‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change linearBlockCost n (head D (linearBlockEquiv n x)) ≤ 1*linearBlockCost n (linearBlockEquiv n x)
  simpa only [one_mul] using head_linearCost_le hD (linearBlockEquiv n x)

def linearOuterHead (D : ℕ → Set Node) (hD : ∀ n, Initial (D n)) : LinearOuter →L[ℝ] LinearOuter :=
  lp.mapCLM 2 (fun n => linearHead (n+1) (D n) (hD n)) zero_le_one
    (fun n => linearHead_norm (n+1) (D n) (hD n))

@[simp] lemma linearOuterHead_apply (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x : LinearOuter) (n : ℕ) :
    linearOuterHead D hD x n = linearHead (n+1) (D n) (hD n) (x n) := rfl

/-- Paired estimates permit arbitrary old-head motion in the displacement. -/
theorem linearOuter_midpoint_sq (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x y : LinearOuter) (hx : linearOuterHead D hD x = x) :
    ‖x‖^2+‖y-linearOuterHead D hD y‖^2/16 ≤ ((‖x+y‖+‖x-y‖)/2)^2 := by
  apply lp_midpoint_sq
  intro n
  have hxn : head (D n) (linearBlockEquiv (n+1) (x n)) = linearBlockEquiv (n+1) (x n) := by
    have he := congrArg (fun z : LinearOuter => linearBlockEquiv (n+1) (z n)) hx
    simpa only [linearOuterHead_apply, linearHead_equiv] using he
  have he := linear_midpoint_tail (hD n) (linearBlockEquiv (n+1) (x n))
    (linearBlockEquiv (n+1) (y n)) hxn
  change Real.sqrt (‖x n‖^2+‖(y-linearOuterHead D hD y) n‖^2/16) ≤
    (‖(x+y) n‖+‖(x-y) n‖)/2 at he
  have hs := Real.sq_sqrt (show 0 ≤ ‖x n‖^2+‖(y-linearOuterHead D hD y) n‖^2/16 by positivity)
  have hn := Real.sqrt_nonneg (‖x n‖^2+‖(y-linearOuterHead D hD y) n‖^2/16)
  nlinarith [norm_nonneg ((x+y) n), norm_nonneg ((x-y) n)]

theorem linearOuter_midpoint (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x y : LinearOuter) (hx : linearOuterHead D hD x = x) :
    Real.sqrt (‖x‖^2+‖y-linearOuterHead D hD y‖^2/16) ≤ (‖x+y‖+‖x-y‖)/2 := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity, linearOuter_midpoint_sq D hD x y hx⟩

def quadraticHead (n : ℕ) (D : Set Node) (hD : Initial D) : QuadraticBlock n →L[ℝ] QuadraticBlock n :=
  (((quadraticBlockEquiv n).symm.toLinearMap.comp (headLM D)).comp (quadraticBlockEquiv n).toLinearMap).mkContinuous
    1 (by
      intro x
      change quadraticBlockCost n (head D (quadraticBlockEquiv n x)) ≤ 1*quadraticBlockCost n (quadraticBlockEquiv n x)
      simpa only [one_mul] using head_quadraticCost_le hD (quadraticBlockEquiv n x))

@[simp] lemma quadraticHead_equiv (n : ℕ) (D : Set Node) (hD : Initial D) (x : QuadraticBlock n) :
    quadraticBlockEquiv n (quadraticHead n D hD x) = head D (quadraticBlockEquiv n x) := rfl

lemma quadraticHead_norm (n : ℕ) (D : Set Node) (hD : Initial D) : ‖quadraticHead n D hD‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change quadraticBlockCost n (head D (quadraticBlockEquiv n x)) ≤ 1*quadraticBlockCost n (quadraticBlockEquiv n x)
  simpa only [one_mul] using head_quadraticCost_le hD (quadraticBlockEquiv n x)

def quadraticOuterHead (D : ℕ → Set Node) (hD : ∀ n, Initial (D n)) : QuadraticOuter →L[ℝ] QuadraticOuter :=
  lp.mapCLM 2 (fun n => quadraticHead (n+1) (D n) (hD n)) zero_le_one
    (fun n => quadraticHead_norm (n+1) (D n) (hD n))

@[simp] lemma quadraticOuterHead_apply (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x : QuadraticOuter) (n : ℕ) :
    quadraticOuterHead D hD x n = quadraticHead (n+1) (D n) (hD n) (x n) := rfl

/-- Paired estimates permit arbitrary old-head motion in the displacement. -/
theorem quadraticOuter_midpoint_sq (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x y : QuadraticOuter) (hx : quadraticOuterHead D hD x = x) :
    ‖x‖^2+‖y-quadraticOuterHead D hD y‖^2/16 ≤ ((‖x+y‖+‖x-y‖)/2)^2 := by
  apply lp_midpoint_sq
  intro n
  have hxn : head (D n) (quadraticBlockEquiv (n+1) (x n)) = quadraticBlockEquiv (n+1) (x n) := by
    have he := congrArg (fun z : QuadraticOuter => quadraticBlockEquiv (n+1) (z n)) hx
    simpa only [quadraticOuterHead_apply, quadraticHead_equiv] using he
  have he := quadratic_midpoint_tail (hD n) (quadraticBlockEquiv (n+1) (x n))
    (quadraticBlockEquiv (n+1) (y n)) hxn
  change Real.sqrt (‖x n‖^2+‖(y-quadraticOuterHead D hD y) n‖^2/16) ≤
    (‖(x+y) n‖+‖(x-y) n‖)/2 at he
  have hs := Real.sq_sqrt (show 0 ≤ ‖x n‖^2+‖(y-quadraticOuterHead D hD y) n‖^2/16 by positivity)
  have hn := Real.sqrt_nonneg (‖x n‖^2+‖(y-quadraticOuterHead D hD y) n‖^2/16)
  nlinarith [norm_nonneg ((x+y) n), norm_nonneg ((x-y) n)]

theorem quadraticOuter_midpoint (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x y : QuadraticOuter) (hx : quadraticOuterHead D hD x = x) :
    Real.sqrt (‖x‖^2+‖y-quadraticOuterHead D hD y‖^2/16) ≤ (‖x+y‖+‖x-y‖)/2 := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity, quadraticOuter_midpoint_sq D hD x y hx⟩

end CostHeads

section ScalarConsequences
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_displacement_le_avg (x y : E) : ‖y‖ ≤ (‖x+y‖+‖x-y‖)/2 := by
  have he : (2:ℝ) • y = (x+y)-(x-y) := by module
  have ht := norm_sub_le (x+y) (x-y)
  rw [← he, norm_smul] at ht
  norm_num at ht
  linarith

lemma norm_center_le_avg (x y : E) : ‖x‖ ≤ (‖x+y‖+‖x-y‖)/2 := by
  have he : (2:ℝ) • x = (x+y)+(x-y) := by module
  have ht := norm_add_le (x+y) (x-y)
  rw [← he, norm_smul] at ht
  norm_num at ht
  linarith

lemma scalar_midpoint_energy {r s p q : ℝ}
    (h : r^2+s^2/16 ≤ ((p+q)/2)^2) :
    s^2 ≤ 16*((p^2+q^2)/2-r^2) := by
  nlinarith [sq_nonneg (p-q)]

end ScalarConsequences

namespace CostHeads
open TreeCalculus BlockCalculus

end CostHeads

namespace BlockCalculus
open TreeCalculus

lemma linear_block_midpoint_sq {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x = x) :
    (linearBlockCost n x)^2+(linearBlockCost n (y-head D y))^2/16 ≤
      ((linearBlockCost n (x+y)+linearBlockCost n (x-y))/2)^2 := by
  have he := linear_midpoint_tail hD x y hx
  have hs := Real.sq_sqrt (show 0 ≤ (linearBlockCost n x)^2+(linearBlockCost n (y-head D y))^2/16 by positivity)
  have hn := Real.sqrt_nonneg ((linearBlockCost n x)^2+(linearBlockCost n (y-head D y))^2/16)
  nlinarith [linearCost_nonneg (pathSynthesis n) (x+y), linearCost_nonneg (pathSynthesis n) (x-y)]

end BlockCalculus

end BoundedTreePotentials

end

end OAI
