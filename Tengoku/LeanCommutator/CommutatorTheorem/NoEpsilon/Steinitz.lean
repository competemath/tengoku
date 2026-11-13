import Tengoku.Seed.Analysis.Convex.KreinMilman
import Tengoku.Seed.Analysis.Complex.Norm
import Tengoku.Seed.Data.List.NodupEquivFin
import Tengoku.Seed.LinearAlgebra.Dimension.Finite
import Tengoku.Seed.Topology.Algebra.Module.FiniteDimension
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/WuProver/lean-commutator@2f197491d436, `CommutatorTheorem/NoEpsilon/Steinitz.lean`: removed 21 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# The finite-dimensional Steinitz rearrangement argument

The box-fiber construction follows Section 1.2 of Eisenbrand and Weismantel,
arXiv:1707.00481v3. Its first ingredient is proved here directly: an extreme
point of a box with linear constraints has at most as many fractional coordinates
as the dimension of the target of the constraints.
-/

open scoped BigOperators Topology
open Set Filter

namespace NoEpsilon
namespace Steinitz

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unit box intersected with a fiber of a linear map.-/
def boxFiber {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : (ι → ℝ) →ₗ[ℝ] E) (b : E) : Set (ι → ℝ) :=
  Icc 0 1 ∩ L ⁻¹' {b}

-- Preserve the existing parameter list for downstream callers.
/-- Directions supported on fractional coordinates admit a two-sided perturbation in the box.-/
theorem exists_box_perturbation (a u : ι → ℝ) (ha : a ∈ Icc (0 : ι → ℝ) 1)
    (hu : ∀ i, ¬ (0 < a i ∧ a i < 1) → u i = 0) :
    ∃ ε : ℝ, 0 < ε ∧ a - ε • u ∈ Icc (0 : ι → ℝ) 1 ∧
      a + ε • u ∈ Icc (0 : ι → ℝ) 1 := by
  have hi (i : ι) : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ a i + t * u i ∧ a i + t * u i ≤ 1 := by
    by_cases hai : 0 < a i ∧ a i < 1
    · have hc : Tendsto (fun t : ℝ ↦ a i + t * u i) (𝓝 0) (𝓝 (a i)) := by
        have hcont : Continuous (fun t : ℝ ↦ a i + t * u i) := by fun_prop
        simpa only [ContinuousAt, zero_mul, add_zero] using hcont.continuousAt (x := 0)
      exact ((hc.eventually_const_lt hai.1).and (hc.eventually_lt_const hai.2)).mono
        (fun _ h ↦ ⟨h.1.le, h.2.le⟩)
    · filter_upwards [] with t
      simp only [hu i hai, mul_zero, add_zero]
      exact ⟨ha.1 i, ha.2 i⟩
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, a + t • u ∈ Icc (0 : ι → ℝ) 1 := by
    filter_upwards [Filter.eventually_all.mpr hi] with t ht
    exact ⟨fun i ↦ (ht i).1, fun i ↦ (ht i).2⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ / 2, by positivity, ?_, ?_⟩
  · have h := hball (show dist (-(δ / 2)) 0 < δ by
      simp only [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hδ)]
      linarith)
    simpa only [neg_smul, sub_eq_add_neg] using h
  · exact hball (show dist (δ / 2) 0 < δ by
      simp only [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
      linarith)

-- Preserve the existing parameter list for downstream callers.
/-- An extreme point has no nonzero feasible direction supported in its fractional coordinates.-/
theorem extreme_box_fiber_no_direction {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : (ι → ℝ) →ₗ[ℝ] E) (b : E) (a : ι → ℝ)
    (ha : a ∈ (boxFiber L b).extremePoints ℝ) (u : ι → ℝ)
    (hu : ∀ i, ¬ (0 < a i ∧ a i < 1) → u i = 0) (hLu : L u = 0) : u = 0 := by
  have ha' : a ∈ boxFiber L b := ha.1
  obtain ⟨ε, hε, hminus, hplus⟩ := exists_box_perturbation a u ha'.1 hu
  have hm : a - ε • u ∈ boxFiber L b := by
    refine ⟨hminus, ?_⟩
    simpa only [mem_preimage, mem_singleton_iff, map_sub, map_smul, hLu,
      smul_zero, sub_zero] using ha'.2
  have hp : a + ε • u ∈ boxFiber L b := by
    refine ⟨hplus, ?_⟩
    simpa only [mem_preimage, mem_singleton_iff, map_add, map_smul, hLu,
      smul_zero, add_zero] using ha'.2
  have heq := (mem_extremePoints_iff_left.mp ha).2 _ hm _ hp
    (mem_openSegment_sub_add (𝕜 := ℝ) a (ε • u))
  have hzero : ε • u = 0 := sub_eq_self.mp heq
  exact (smul_eq_zero.mp hzero).resolve_left (ne_of_gt hε)

-- Preserve the existing parameter list for downstream callers.
/-- The constraint images of the fractional coordinates of an extreme point are independent.-/
theorem extreme_fractional_linearIndependent {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : (ι → ℝ) →ₗ[ℝ] E) (b : E) (a : ι → ℝ)
    (ha : a ∈ (boxFiber L b).extremePoints ℝ) :
    LinearIndependent ℝ (fun i : {i : ι // 0 < a i ∧ a i < 1} ↦
      L (Pi.single i.val 1)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let u : ι → ℝ := ∑ k : {i : ι // 0 < a i ∧ a i < 1},
    c k • (Pi.single k.val (1 : ℝ) : ι → ℝ)
  have hu (i : ι) (hi : ¬ (0 < a i ∧ a i < 1)) : u i = 0 := by
    dsimp [u]
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hk : k.val ≠ i := by
      intro h
      exact hi (h ▸ k.property)
    simp [hk.symm]
  have hLu : L u = 0 := by
    dsimp [u]
    simpa only [map_sum, map_smul] using hc
  have hzero := extreme_box_fiber_no_direction L b a ha u hu hLu
  have hui : u j.val = c j := by
    dsimp [u]
    rw [Finset.sum_apply, Fintype.sum_eq_single j]
    · simp
    · intro k hkj
      have hk : k.val ≠ j.val := fun h ↦ hkj (Subtype.ext h)
      simp [hk.symm]
  have h := congrFun hzero j.val
  simpa only [hui, Pi.zero_apply] using h

-- Preserve the existing parameter list for downstream callers.
/-- Extreme box fibers have at most `finrank` many fractional coordinates.-/
theorem extreme_fractional_card_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (L : (ι → ℝ) →ₗ[ℝ] E) (b : E) (a : ι → ℝ)
    (ha : a ∈ (boxFiber L b).extremePoints ℝ) :
    Fintype.card {i : ι // 0 < a i ∧ a i < 1} ≤ Module.finrank ℝ E := by
  classical
  exact (extreme_fractional_linearIndependent L b a ha).fintype_card_le_finrank

-- Preserve the existing parameter list for downstream callers.
/-- Every nonempty box fiber admits a feasible point with at most `finrank` fractional entries.-/
theorem exists_few_fractional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : (ι → ℝ) →ₗ[ℝ] E) (b : E)
    (hfeasible : (boxFiber L b).Nonempty) :
    ∃ a ∈ boxFiber L b,
      Fintype.card {i : ι // 0 < a i ∧ a i < 1} ≤ Module.finrank ℝ E := by
  have hcompact : IsCompact (boxFiber L b) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage L.continuous_of_finiteDimensional)
  obtain ⟨a, ha⟩ := hcompact.extremePoints_nonempty hfeasible
  exact ⟨a, ha.1, extreme_fractional_card_le L b a ha⟩

/-- Total weight together with the two coordinates of the weighted vector sum.-/
def constraintMap (x : ι → Fin 2 → ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ℝ × (Fin 2 → ℝ)) where
  toFun a := (∑ i, a i, ∑ i, a i • x i)
  map_add' a b := by
    ext j <;> simp [Finset.sum_add_distrib, add_smul]
  map_smul' c a := by
    ext j <;> simp [Finset.mul_sum, mul_assoc]

-- Preserve the existing parameter list for downstream callers.
/-- Three affine constraints admit a box solution with at most three fractional entries.-/
theorem exists_weights_three_fractional (x : ι → Fin 2 → ℝ) (mass : ℝ)
    (hfeasible : (boxFiber (constraintMap x) (mass, 0)).Nonempty) :
    ∃ a ∈ boxFiber (constraintMap x) (mass, 0),
      Fintype.card {i : ι // 0 < a i ∧ a i < 1} ≤ 3 := by
  obtain ⟨a, ha, hfrac⟩ := exists_few_fractional (constraintMap x) (mass, 0) hfeasible
  refine ⟨a, ha, ?_⟩
  simpa [Module.finrank_prod] using hfrac

-- Preserve the existing parameter list for downstream callers.
/-- A box solution of mass `card - 3` with at most three fractional entries has a zero entry.-/
theorem exists_zero_of_three_fractional (a : ι → ℝ) (ha : a ∈ Icc (0 : ι → ℝ) 1)
    (hmass : ∑ i, a i = (Fintype.card ι : ℝ) - 3)
    (hfrac : Fintype.card {i : ι // 0 < a i ∧ a i < 1} ≤ 3) :
    ∃ i, a i = 0 := by
  classical
  by_contra hzero
  have hpos (i : ι) : 0 < a i :=
    lt_of_le_of_ne (ha.1 i) (Ne.symm (not_exists.mp hzero i))
  let F : Finset ι := Finset.univ.filter (fun i ↦ 0 < a i ∧ a i < 1)
  have houtside (i : ι) (hi : i ∉ F) : a i = 1 := by
    have hnot : ¬ (0 < a i ∧ a i < 1) := by simpa [F] using hi
    exact le_antisymm (ha.2 i) (le_of_not_gt (fun h ↦ hnot ⟨hpos i, h⟩))
  have hsum : ∑ i, (1 - a i) = ∑ i ∈ F, (1 - a i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ F)
    intro i _ hi
    rw [houtside i hi, sub_self]
  have hmass' : ∑ i, (1 - a i) = (3 : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, hmass]
    ring
  have hFne : F.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
    linarith
  have hstrict : ∑ i ∈ F, (1 - a i) < ∑ _i ∈ F, (1 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hFne (fun i _ ↦ by linarith [hpos i])
  have hcard : (F.card : ℝ) ≤ 3 := by
    exact_mod_cast (show F.card ≤ 3 by simpa [Fintype.card_subtype, F] using hfrac)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hstrict
  linarith

-- Preserve the existing parameter list for downstream callers.
/-- Reduce the weight mass by one while creating a zero coordinate, preserving the vector sum.-/
theorem exists_deletable_weights (x : ι → Fin 2 → ℝ) (hn : 2 < Fintype.card ι)
    (a : ι → ℝ) (ha : a ∈ boxFiber (constraintMap x) ((Fintype.card ι : ℝ) - 2, 0)) :
    ∃ a' ∈ boxFiber (constraintMap x) ((Fintype.card ι : ℝ) - 3, 0),
      ∃ i, a' i = 0 := by
  have hn' : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hden : 0 < (Fintype.card ι : ℝ) - 2 := by linarith
  let t : ℝ := ((Fintype.card ι : ℝ) - 3) / ((Fintype.card ι : ℝ) - 2)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
  have ht1 : t ≤ 1 := (div_le_one hden).mpr (by linarith)
  have ht : t * ((Fintype.card ι : ℝ) - 2) = (Fintype.card ι : ℝ) - 3 := by
    dsimp [t]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  have hscaled : t • a ∈ boxFiber (constraintMap x) ((Fintype.card ι : ℝ) - 3, 0) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      exact mul_nonneg ht0 (ha.1.1 i)
    · intro i
      exact (mul_le_mul_of_nonneg_left (ha.1.2 i) ht0).trans (by simpa using ht1)
    · change constraintMap x (t • a) = _
      rw [map_smul, show constraintMap x a = ((Fintype.card ι : ℝ) - 2, 0) from ha.2]
      ext <;> simp [ht]
  obtain ⟨a', ha', hfrac⟩ := exists_weights_three_fractional x
    ((Fintype.card ι : ℝ) - 3) ⟨t • a, hscaled⟩
  refine ⟨a', ha', exists_zero_of_three_fractional a' ha'.1 ?_ hfrac⟩
  exact congrArg Prod.fst ha'.2

/-- Admissible weights have weight deficit two and weighted vector sum zero.-/
def FeasibleOn (x : ι → Fin 2 → ℝ) (s : Finset ι) : Prop :=
  ∃ a : ι → ℝ, (∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) ∧
    (∑ i ∈ s, a i) = (s.card : ℝ) - 2 ∧ ∑ i ∈ s, a i • x i = 0

-- Preserve the existing parameter list for downstream callers.
/-- Feasible weights bound the sum of the unweighted vectors by two.-/
theorem norm_sum_le_two_of_feasible (x : ι → Fin 2 → ℝ) (s : Finset ι)
    (hx : ∀ i ∈ s, ‖x i‖ ≤ 1) (hs : FeasibleOn x s) : ‖∑ i ∈ s, x i‖ ≤ 2 := by
  obtain ⟨a, habox, hamass, havec⟩ := hs
  have hid : ∑ i ∈ s, x i = ∑ i ∈ s, (1 - a i) • x i := by
    simp only [sub_smul, one_smul, Finset.sum_sub_distrib, havec, sub_zero]
  rw [hid]
  calc
    ‖∑ i ∈ s, (1 - a i) • x i‖ ≤ ∑ i ∈ s, ‖(1 - a i) • x i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (1 - a i) := by
      apply Finset.sum_le_sum
      intro i hi
      have ha : 0 ≤ 1 - a i := sub_nonneg.mpr (habox i hi).2
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      simpa using mul_le_mul_of_nonneg_left (hx i hi) ha
    _ = 2 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hamass]
      ring

-- Preserve the existing parameter list for downstream callers.
/-- Unit vectors in a finite set have sum norm at most its cardinality.-/
theorem norm_sum_le_card (x : ι → Fin 2 → ℝ) (s : Finset ι)
    (hx : ∀ i ∈ s, ‖x i‖ ≤ 1) : ‖∑ i ∈ s, x i‖ ≤ s.card := by
  calc
    ‖∑ i ∈ s, x i‖ ≤ ∑ i ∈ s, ‖x i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, (1 : ℝ) := Finset.sum_le_sum hx
    _ = s.card := by simp

-- Preserve the existing parameter list for downstream callers.
/-- Constant weights initialize the deletion argument for a zero-sum family.-/
theorem feasibleOn_of_sum_zero (x : ι → Fin 2 → ℝ) (s : Finset ι)
    (hn : 2 < s.card) (hsum : ∑ i ∈ s, x i = 0) : FeasibleOn x s := by
  have hn' : (2 : ℝ) < s.card := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < s.card := by linarith
  let t : ℝ := ((s.card : ℝ) - 2) / s.card
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hn0.le
  have ht1 : t ≤ 1 := (div_le_one hn0).mpr (by linarith)
  refine ⟨fun _ ↦ t, fun _ _ ↦ ⟨ht0, ht1⟩, ?_, ?_⟩
  · simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [t]
    field_simp
  · rw [← Finset.smul_sum, hsum, smul_zero]

end Steinitz
end NoEpsilon
