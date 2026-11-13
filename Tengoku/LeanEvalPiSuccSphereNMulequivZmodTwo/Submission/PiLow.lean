import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SphereClose
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SmoothApprox
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.MissesPoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Low homotopy groups of spheres are trivial

`π_k(Sⁿ) = 0` for `k < n`, and `Sⁿ` is simply connected for `n ≥ 2`.

Proof for `1 ≤ k < n`: represent a class by the normalization of a smooth raw map
`raw : ℝᵏ → ℝⁿ⁺¹` (`Submission.exists_approximation_of_homotopy_class`).  The cone
`(v, s) ↦ s • raw v` is a `C¹` map from a `(k+1)`-dimensional space to the
`(n+1)`-dimensional space, so by Sard-type dimension counting
(`ContDiff.dense_compl_range_of_finrank_lt_finrank`) its range has dense complement.
A point `w` outside the range and close to the basepoint normalizes to a sphere point
`y` missed by the representative, which is therefore nullhomotopic
(`Submission.homotopic_const_of_misses`).  For `k = 0` the statement is
path-connectedness of the sphere (`isPathConnected_sphere`).

Main declarations:

* `Submission.homotopy_class_eq_const_of_succ_lt`: every class in
  `π_{m+1}(Sⁿ)`, `m + 1 < n`, is the constant class;
* `Submission.homotopyGroup_sphere_subsingleton`: `π_k(Sⁿ)` is trivial for `k < n`;
* `Submission.sphere_simplyConnected`: `Sⁿ` is simply connected for `2 ≤ n`.
-/

noncomputable section

open scoped Topology unitInterval ContDiff
open Topology.Homotopy Metric Module

namespace Submission

/-- Every homotopy class in `π_{m+1}` of the `n`-sphere, with `m + 1 < n`, is the
class of the constant loop.-/
theorem homotopy_class_eq_const_of_succ_lt {m n : ℕ} (h : m + 1 < n)
    (x : UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
    (z : HomotopyGroup (Fin (m + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) x) :
    z = ⟦GenLoop.const⟧ := by
  obtain ⟨p, a, hz⟩ := exists_approximation_of_homotopy_class z
  subst hz
  -- the cone over the raw map
  have hc1 : ContDiff ℝ 1 fun q : (Fin (m + 1) → ℝ) × ℝ => q.2 • a.raw q.1 := by
    have hraw : ContDiff ℝ 1 a.raw := a.contDiff_raw.of_le (by exact_mod_cast le_top)
    exact contDiff_snd.smul (hraw.comp contDiff_fst)
  have hdim : finrank ℝ ((Fin (m + 1) → ℝ) × ℝ)
      < finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self,
      finrank_euclideanSpace_fin]
    omega
  have hdense : Dense (Set.range fun q : (Fin (m + 1) → ℝ) × ℝ => q.2 • a.raw q.1)ᶜ :=
    hc1.dense_compl_range_of_finrank_lt_finrank hdim
  -- a point outside the cone's range, close to the basepoint
  obtain ⟨w, hwc, hwball⟩ := hdense.exists_mem_open isOpen_ball
    ⟨(x : EuclideanSpace ℝ (Fin (n + 1))), mem_ball_self one_pos⟩
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, mem_ball, dist_zero_left, UnitSphere.norm_coe x] at hwball
    exact lt_irrefl 1 hwball
  have hymem : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    mem_sphere_zero_iff_norm.mpr (norm_normalize hw0)
  -- the representative misses the normalization of `w`
  have hmiss : ∀ t, a.representative t
      ≠ (⟨‖w‖⁻¹ • w, hymem⟩ : UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) := by
    intro t hty
    have hcoe : (a.representative t : EuclideanSpace ℝ (Fin (n + 1))) = ‖w‖⁻¹ • w :=
      congrArg Subtype.val hty
    rw [a.representative_coe t] at hcoe
    apply hwc
    refine ⟨((fun i => (t i : ℝ)), ‖w‖ * ‖a.raw (fun i => (t i : ℝ))‖⁻¹), ?_⟩
    show (‖w‖ * ‖a.raw (fun i => (t i : ℝ))‖⁻¹) • a.raw (fun i => (t i : ℝ)) = w
    rw [mul_smul, hcoe, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw0),
      one_smul]
  exact homotopy_class_eq_const_of_misses a.representative _ hmiss

/-- **Triviality of low homotopy groups of spheres**: `π_k(Sⁿ)` is a subsingleton
for `k < n`.-/
theorem homotopyGroup_sphere_subsingleton (k n : ℕ) (h : k < n)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Subsingleton
      (HomotopyGroup.Pi k (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  cases k with
  | zero =>
    haveI hpc : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrank 0 zero_le_one)
    haveI hzs : Subsingleton
        (ZerothHomotopy (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
      constructor
      intro a b
      induction a using Quotient.inductionOn with
      | h a =>
        induction b using Quotient.inductionOn with
        | h b => exact Quotient.sound (hpc.joined a b)
    exact (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).subsingleton
  | succ m =>
    constructor
    intro z z'
    rw [homotopy_class_eq_const_of_succ_lt h x z,
      homotopy_class_eq_const_of_succ_lt h x z']

/-- **Spheres of dimension at least `2` are simply connected.**-/
theorem sphere_simplyConnected (n : ℕ) (h : 2 ≤ n) :
    SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  haveI hpc : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrank 0 zero_le_one)
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨hpc, fun x γ => ?_⟩
  -- transport the loop to a generalized loop indexed by `Fin 1`
  let q : Ω^ (Fin 1) (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x :=
    ⟨⟨fun c => γ (c 0), by fun_prop⟩, by
      rintro c ⟨i, hi | hi⟩
      · rw [Fin.eq_zero i] at hi
        exact (congrArg γ hi).trans γ.source
      · rw [Fin.eq_zero i] at hi
        exact (congrArg γ hi).trans γ.target⟩
  have hsub : Subsingleton
      (HomotopyGroup.Pi 1 (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) :=
    homotopyGroup_sphere_subsingleton 1 n (by omega) x
  have hq : (⟦q⟧ : HomotopyGroup (Fin 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) = ⟦GenLoop.const⟧ :=
    hsub.elim _ _
  obtain ⟨H⟩ := Quotient.exact hq
  exact
    ⟨{  toFun := fun su => H (su.1, fun _ => su.2)
        map_zero_left := fun u => H.apply_zero _
        map_one_left := fun u => H.apply_one _
        prop' := fun s u hu => H.prop' s (fun _ => u)
          ⟨0, by rcases hu with h0 | h1
                 · exact Or.inl h0
                 · exact Or.inr h1⟩ }⟩

end Submission
