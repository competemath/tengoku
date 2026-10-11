import Tengoku.OpenaiMath.OAI.Analysis.TreePotential.Coordinates

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace CostHeads
open TreeCalculus BlockCalculus ForestCoordinates Filter Topology
open scoped Classical

lemma linear_coefficient_head (A : FiniteOuterHead) (x : LinearOuter) (s : ForestNode) :
    coefficient (fun n => linearBlockHilbertEquiv (n+1)) (linearOuterHead A.nodes A.initial x) s =
    if s.2.val ∈ A.nodes s.1 then coefficient (fun n => linearBlockHilbertEquiv (n+1)) x s else 0 := rfl

lemma linear_head_eq_self_iff (A : FiniteOuterHead) (x : LinearOuter) :
    linearOuterHead A.nodes A.initial x = x ↔ ∀ s : ForestNode,
      s.2.val ∉ A.nodes s.1 → coefficient (fun n => linearBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => linearBlockHilbertEquiv (n+1)) z s) h
    rw [linear_coefficient_head, ite_eq_right hs] at he
    exact he.symm
  · intro h
    apply coefficient_ext (fun n => linearBlockHilbertEquiv (n+1))
    intro s
    rw [linear_coefficient_head]
    split_ifs with hs
    · rfl
    · exact (h s hs).symm

lemma linear_head_eq_zero_iff (A : FiniteOuterHead) (x : LinearOuter) :
    linearOuterHead A.nodes A.initial x = 0 ↔ ∀ s : ForestNode,
      s.2.val ∈ A.nodes s.1 → coefficient (fun n => linearBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => linearBlockHilbertEquiv (n+1)) z s) h
    rw [linear_coefficient_head, ite_eq_left hs, coefficient_zero] at he
    exact he
  · intro h
    apply coefficient_ext (fun n => linearBlockHilbertEquiv (n+1))
    intro s
    rw [linear_coefficient_head, coefficient_zero]
    split_ifs with hs
    · exact h s hs
    · rfl

lemma linear_finite_head_approx (x : LinearOuter) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : LinearOuter, ∃ A : FiniteOuterHead, ‖x-p‖ < ε ∧ linearOuterHead A.nodes A.initial p = p := by
  obtain ⟨p,A,hd,hp⟩ := exists_finite_head_approx (fun n => linearBlockHilbertEquiv (n+1)) x hε
  exact ⟨p,A,hd,(linear_head_eq_self_iff A p).mpr hp⟩

def linearCoordinateTail (A : FiniteOuterHead) : ClosedFiniteCodim LinearOuter :=
  ForestCoordinates.coordinateTail (fun n => linearBlockHilbertEquiv (n+1)) A

lemma mem_linearCoordinateTail (A : FiniteOuterHead) (x : LinearOuter) :
    x ∈ (linearCoordinateTail A).space ↔ linearOuterHead A.nodes A.initial x = 0 := by
  exact (ForestCoordinates.mem_coordinateTail (fun n => linearBlockHilbertEquiv (n+1)) A x).trans
    (linear_head_eq_zero_iff A x).symm

lemma quadratic_coefficient_head (A : FiniteOuterHead) (x : QuadraticOuter) (s : ForestNode) :
    coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) (quadraticOuterHead A.nodes A.initial x) s =
    if s.2.val ∈ A.nodes s.1 then coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) x s else 0 := rfl

lemma quadratic_head_eq_self_iff (A : FiniteOuterHead) (x : QuadraticOuter) :
    quadraticOuterHead A.nodes A.initial x = x ↔ ∀ s : ForestNode,
      s.2.val ∉ A.nodes s.1 → coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) z s) h
    rw [quadratic_coefficient_head, ite_eq_right hs] at he
    exact he.symm
  · intro h
    apply coefficient_ext (fun n => quadraticBlockHilbertEquiv (n+1))
    intro s
    rw [quadratic_coefficient_head]
    split_ifs with hs
    · rfl
    · exact (h s hs).symm

lemma quadratic_head_eq_zero_iff (A : FiniteOuterHead) (x : QuadraticOuter) :
    quadraticOuterHead A.nodes A.initial x = 0 ↔ ∀ s : ForestNode,
      s.2.val ∈ A.nodes s.1 → coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) z s) h
    rw [quadratic_coefficient_head, ite_eq_left hs, coefficient_zero] at he
    exact he
  · intro h
    apply coefficient_ext (fun n => quadraticBlockHilbertEquiv (n+1))
    intro s
    rw [quadratic_coefficient_head, coefficient_zero]
    split_ifs with hs
    · exact h s hs
    · rfl

lemma quadratic_finite_head_approx (x : QuadraticOuter) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : QuadraticOuter, ∃ A : FiniteOuterHead, ‖x-p‖ < ε ∧ quadraticOuterHead A.nodes A.initial p = p := by
  obtain ⟨p,A,hd,hp⟩ := exists_finite_head_approx (fun n => quadraticBlockHilbertEquiv (n+1)) x hε
  exact ⟨p,A,hd,(quadratic_head_eq_self_iff A p).mpr hp⟩

def quadraticCoordinateTail (A : FiniteOuterHead) : ClosedFiniteCodim QuadraticOuter :=
  ForestCoordinates.coordinateTail (fun n => quadraticBlockHilbertEquiv (n+1)) A

lemma mem_quadraticCoordinateTail (A : FiniteOuterHead) (x : QuadraticOuter) :
    x ∈ (quadraticCoordinateTail A).space ↔ quadraticOuterHead A.nodes A.initial x = 0 := by
  exact (ForestCoordinates.mem_coordinateTail (fun n => quadraticBlockHilbertEquiv (n+1)) A x).trans
    (quadratic_head_eq_zero_iff A x).symm

end CostHeads

lemma sqrt_shift {r R d c : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (hc : 0 ≤ c) (hh : r ≤ R+d) :
    Real.sqrt (r^2+c) ≤ Real.sqrt (R^2+c)+d := by
  have hs := Real.sq_sqrt (show 0 ≤ R^2+c by positivity)
  have hn := Real.sqrt_nonneg (R^2+c)
  have hRT : R ≤ Real.sqrt (R^2+c) := by nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hrhs : r^2 ≤ (R+d)^2 := by nlinarith [mul_nonneg (show 0 ≤ R+d-r by linarith) (show 0 ≤ R+d+r by positivity)]
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hRT)]

section FiniteRankCompactness
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end FiniteRankCompactness

namespace CostHeads
open TreeCalculus BlockCalculus ForestCoordinates Filter Topology
open scoped Classical

/-- Transfer from finite centers to arbitrary completed centers, uniformly on
an entire closed finite-codimensional tail. -/
theorem linear_completed_tail_bound (x : LinearOuter) (hx : ‖x‖ = 1)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ F : ClosedFiniteCodim LinearOuter, ∀ y, y ∈ F.space → 1 ≤ ‖y‖ →
      Real.sqrt (1+t^2/16)-1-ε ≤ (‖x+t • y‖+‖x-t • y‖)/2-1 := by
  obtain ⟨p,A,hp,hA⟩ := linear_finite_head_approx x (show 0 < ε/2 by positivity)
  refine ⟨linearCoordinateTail A, ?_⟩
  intro y hy hyn
  have hy0 := (mem_linearCoordinateTail A y).mp hy
  have he := linearOuter_midpoint A.nodes A.initial p (t • y) hA
  rw [map_smul, hy0, smul_zero, sub_zero, norm_smul, Real.norm_of_nonneg ht.le] at he
  have hnorm : 1 ≤ ‖p‖+‖x-p‖ := by
    have hh := norm_sub_norm_le x p
    rw [hx] at hh
    linarith
  have hs := sqrt_shift zero_le_one (norm_nonneg p) (norm_nonneg (x-p))
    (show 0 ≤ t^2/16 by positivity) hnorm
  norm_num only [one_pow] at hs
  have hyb : Real.sqrt (‖p‖^2+t^2/16) ≤ Real.sqrt (‖p‖^2+(t*‖y‖)^2/16) := by
    apply Real.sqrt_le_sqrt
    have hh : t ≤ t*‖y‖ := by nlinarith
    nlinarith [norm_nonneg y]
  have hppert := midpoint_center_perturbation x p y t
  rw [norm_sub_rev p x] at hppert
  linarith

theorem linear_averaged_modulus {t : ℝ} (ht : 0 < t) :
    ((Real.sqrt (1+t^2/16)-1 : ℝ) : EReal) ≤ averagedModulus LinearOuter t := by
  apply averagedModulus_lower_bound
  intro x hx ε hε
  exact linear_completed_tail_bound x hx ht hε

/-- Transfer from finite centers to arbitrary completed centers, uniformly on
an entire closed finite-codimensional tail. -/
theorem quadratic_completed_tail_bound (x : QuadraticOuter) (hx : ‖x‖ = 1)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ F : ClosedFiniteCodim QuadraticOuter, ∀ y, y ∈ F.space → 1 ≤ ‖y‖ →
      Real.sqrt (1+t^2/16)-1-ε ≤ (‖x+t • y‖+‖x-t • y‖)/2-1 := by
  obtain ⟨p,A,hp,hA⟩ := quadratic_finite_head_approx x (show 0 < ε/2 by positivity)
  refine ⟨quadraticCoordinateTail A, ?_⟩
  intro y hy hyn
  have hy0 := (mem_quadraticCoordinateTail A y).mp hy
  have he := quadraticOuter_midpoint A.nodes A.initial p (t • y) hA
  rw [map_smul, hy0, smul_zero, sub_zero, norm_smul, Real.norm_of_nonneg ht.le] at he
  have hnorm : 1 ≤ ‖p‖+‖x-p‖ := by
    have hh := norm_sub_norm_le x p
    rw [hx] at hh
    linarith
  have hs := sqrt_shift zero_le_one (norm_nonneg p) (norm_nonneg (x-p))
    (show 0 ≤ t^2/16 by positivity) hnorm
  norm_num only [one_pow] at hs
  have hyb : Real.sqrt (‖p‖^2+t^2/16) ≤ Real.sqrt (‖p‖^2+(t*‖y‖)^2/16) := by
    apply Real.sqrt_le_sqrt
    have hh : t ≤ t*‖y‖ := by nlinarith
    nlinarith [norm_nonneg y]
  have hppert := midpoint_center_perturbation x p y t
  rw [norm_sub_rev p x] at hppert
  linarith

theorem quadratic_averaged_modulus {t : ℝ} (ht : 0 < t) :
    ((Real.sqrt (1+t^2/16)-1 : ℝ) : EReal) ≤ averagedModulus QuadraticOuter t := by
  apply averagedModulus_lower_bound
  intro x hx ε hε
  exact quadratic_completed_tail_bound x hx ht hε

end CostHeads

end BoundedTreePotentials

end

end OAI
