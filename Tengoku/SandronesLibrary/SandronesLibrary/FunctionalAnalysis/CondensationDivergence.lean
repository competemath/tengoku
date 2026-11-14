/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.Condensation
import Tengoku.Seed.Topology.MetricSpace.Bounded
import Tengoku.Seed.Topology.Algebra.Module.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Banach–Steinhaus (1927): condensation of divergence, Theorem II

The proof follows the paper's two cases. For bounded operator norms, the Cauchy points form
an explicitly constructed closed linear subspace. If this subspace is proper, its complement
is dense and open. For unbounded norms, Theorem I supplies a dense Gδ set of unbounded outputs,
which cannot be Cauchy. Baire combines the countably many rows.

The main Cauchy version does not require complete codomains. The limit version uses complete
codomains to translate failure of convergence into failure of the Cauchy property.
-/

open Set Filter
open scoped Topology
open SandronesLibrary.Topology.NormedSpace

namespace SandronesLibrary.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedLinearSpace ℝ E]

section SingleRow

variable {F : Type*} [NormedAddCommGroup F] [NormedLinearSpace ℝ F]

/-- Private proof carrier: Cauchy sequences are preserved by addition and scalar multiplication.-/
private def cauchyPointsSubmodule (g : ℕ → E →L[ℝ] F) : Submodule ℝ E where
  carrier := {x | CauchySeq (fun q => g q x)}
  zero_mem' := by simpa using cauchySeq_const (0 : F)
  add_mem' := by
    intro x y hx hy
    change CauchySeq (fun q => g q (x + y))
    have hsum : (fun q => g q (x + y)) =
        (fun q => g q x) + (fun q => g q y) := by
      ext q
      simp
    rw [hsum]
    exact hx.add hy
  smul_mem' := by
    intro c x hx
    change CauchySeq (fun q => g q (c • x))
    have hcomp : (fun q => g q (c • x)) =
        (fun y : F => c • y) ∘ (fun q => g q x) := by
      ext q
      simp
    rw [hcomp]
    simpa only [CauchySeq, Filter.map_map] using hx.map (uniformContinuous_const_smul c)

/-- Uniformly bounded operator norms make the set of Cauchy points closed.
This is the approximation mechanism of Lemma 4 in Banach–Steinhaus (1927).

> **Entry**: functional-analysis.condensation.divergence
@isnad1 id=isclosed.2h4v.s8.8019856baf3b from=translated src=- shape=0672e6fd vocab=37a4f69a
-/
theorem isClosed_cauchy_points_of_operatorNorm_bound {g : ℕ → E →L[ℝ] F}
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ q, ‖g q‖ ≤ C) :
    IsClosed {x : E | CauchySeq (fun q => g q x)} := by
  apply isClosed_of_closure_subset
  intro x hx
  change CauchySeq (fun q => g q x)
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let δ : ℝ := ε / (3 * (C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδ_eq : δ * (3 * (C + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx δ hδ
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hy (ε / 3) (by positivity)
  have hsmall : C * dist x y < ε / 3 := by
    calc
      C * dist x y ≤ C * δ := mul_le_mul_of_nonneg_left hxy.le hC
      _ < ε / 3 := by nlinarith
  have hdist : ∀ q, dist (g q x) (g q y) ≤ C * dist x y := by
    intro q
    calc
      dist (g q x) (g q y) = ‖g q (x - y)‖ := by rw [map_sub, dist_eq_norm]
      _ ≤ ‖g q‖ * ‖x - y‖ := (g q).le_opNorm (x - y)
      _ ≤ C * dist x y := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_right (h q) (norm_nonneg (x - y))
  refine ⟨N, ?_⟩
  intro m hm n hn
  have htriangle : dist (g m x) (g n x) ≤
      dist (g m x) (g m y) + dist (g m y) (g n y) + dist (g n x) (g n y) := by
    calc
      _ ≤ dist (g m x) (g m y) + dist (g m y) (g n x) := dist_triangle _ _ _
      _ ≤ dist (g m x) (g m y) +
          (dist (g m y) (g n y) + dist (g n y) (g n x)) :=
        by linarith [dist_triangle (g m y) (g n y) (g n x)]
      _ = _ := by rw [dist_comm (g n y) (g n x)]; ring
  linarith [hdist m, hdist n, hN m hm n hn]

/-- For a uniformly norm-bounded row that fails to be Cauchy at one point, the non-Cauchy
points form a dense open set.
@isnad1 id=and.3h4v.s9.ad42db888873 from=translated src=- shape=d9e98f22 vocab=a72d16a7
-/
theorem dense_open_nonCauchy_points_of_operatorNorm_bound {g : ℕ → E →L[ℝ] F}
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ q, ‖g q‖ ≤ C)
    (hz : ∃ z : E, ¬ CauchySeq (fun q => g q z)) :
    Dense {x : E | ¬ CauchySeq (fun q => g q x)} ∧
      IsOpen {x : E | ¬ CauchySeq (fun q => g q x)} := by
  let S := cauchyPointsSubmodule g
  have hproper : S ≠ ⊤ := by
    intro htop
    obtain ⟨z, hz⟩ := hz
    have hmem : z ∈ S := by rw [htop]; trivial
    exact hz hmem
  have hInterior : interior (S : Set E) = ∅ := by
    by_contra hne
    exact hproper (S.eq_top_of_nonempty_interior' (nonempty_iff_ne_empty.mpr hne))
  exact ⟨interior_eq_empty_iff_dense_compl.mp hInterior,
    (isClosed_cauchy_points_of_operatorNorm_bound hC h).isOpen_compl⟩

variable [BanachSpace E]

/-- Whenever one point is non-Cauchy for a row, a dense Gδ set of points is non-Cauchy
for that row. The proof splits according to boundedness of the operator norms.
@isnad1 id=ex.1h3v.s8.1223b6d32798 from=translated src=- shape=76ebfbad vocab=d43ce125
-/
theorem exists_dense_Gδ_nonCauchy_points {g : ℕ → E →L[ℝ] F}
    (hz : ∃ z : E, ¬ CauchySeq (fun q => g q z)) :
    ∃ S : Set E, Dense S ∧ IsGδ S ∧ S ⊆ {x : E | ¬ CauchySeq (fun q => g q x)} := by
  by_cases hbound : ∃ C : ℝ, ∀ q, ‖g q‖ ≤ C
  · obtain ⟨C, hC⟩ := hbound
    have hCnonneg : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
    obtain ⟨hDense, hOpen⟩ := dense_open_nonCauchy_points_of_operatorNorm_bound hCnonneg hC hz
    exact ⟨_, hDense, hOpen.isGδ, Subset.rfl⟩
  · have hpoint : ∃ z : E, ∀ C : ℝ, ∃ q, C < ‖g q z‖ := by
      by_contra hpoint
      push Not at hpoint
      obtain ⟨C, _, hC⟩ := uniform_operatorNorm_bound_of_pointwise_bounded hpoint
      exact hbound ⟨C, hC⟩
    have hcommon := condensation_dense_Gδ (g := fun _ : ℕ => g) (fun _ => hpoint)
    have hsingle : Dense {x : E | ∀ C : ℝ, ∃ q, C < ‖g q x‖} ∧
        IsGδ {x : E | ∀ C : ℝ, ∃ q, C < ‖g q x‖} := by
      simpa only [forall_const] using hcommon
    refine ⟨_, hsingle.1, hsingle.2, ?_⟩
    intro x hx hcauchy
    obtain ⟨C, hC⟩ := hcauchy.isBounded_range.exists_norm_le
    obtain ⟨q, hq⟩ := hx C
    exact (not_lt_of_ge (hC _ (mem_range_self q))) hq

end SingleRow

variable [BanachSpace E]
variable {F : ℕ → Type*} [∀ p, NormedAddCommGroup (F p)]
variable [∀ p, NormedLinearSpace ℝ (F p)]

/-- **Theorem II, category conclusion**: if each row is non-Cauchy at some point, the points
where all rows are non-Cauchy are dense. Codomains may depend on the row.
@isnad1 id=dense.1h3v.s9.fef1d5bd05ff from=translated src=- shape=c93af280 vocab=adf4184f
-/
theorem condensation_divergence_dense {g : ∀ p : ℕ, ℕ → E →L[ℝ] F p}
    (h : ∀ p, ∃ z : E, ¬ CauchySeq (fun q => g p q z)) :
    Dense {x : E | ∀ p, ¬ CauchySeq (fun q => g p q x)} := by
  choose S hDense hGδ hSub using fun p => exists_dense_Gδ_nonCauchy_points (h p)
  apply (dense_iInter_of_Gδ hGδ hDense).mono
  intro x hx p
  exact hSub p (mem_iInter.mp hx p)

/-- **Theorem II, Cauchy form**: one common point makes every row non-Cauchy.
@isnad1 id=ex.1h3v.s9.84f41eea0160 from=translated src=- shape=9f44d224 vocab=20573f72
-/
theorem condensation_divergence_exists {g : ∀ p : ℕ, ℕ → E →L[ℝ] F p}
    (h : ∀ p, ∃ z : E, ¬ CauchySeq (fun q => g p q z)) :
    ∃ x : E, ∀ p, ¬ CauchySeq (fun q => g p q x) :=
  (condensation_divergence_dense h).nonempty

/-- **Theorem II, limit form**: for complete row codomains, if each row fails to converge at
some point, one common point makes every row fail to converge.
@isnad1 id=ex.1h3v.s9.0a68397d11bb from=translated src=- shape=bed34ecc vocab=7a4ccd3a
-/
theorem condensation_nonconvergence_exists [∀ p, BanachSpace (F p)]
    {g : ∀ p : ℕ, ℕ → E →L[ℝ] F p}
    (h : ∀ p, ∃ z : E, ¬ ∃ y : F p, Tendsto (fun q => g p q z) atTop (𝓝 y)) :
    ∃ x : E, ∀ p, ¬ ∃ y : F p, Tendsto (fun q => g p q x) atTop (𝓝 y) := by
  have hCauchy : ∀ p, ∃ z : E, ¬ CauchySeq (fun q => g p q z) := by
    intro p
    obtain ⟨z, hz⟩ := h p
    exact ⟨z, fun hc => hz (cauchySeq_tendsto_of_complete hc)⟩
  obtain ⟨x, hx⟩ := condensation_divergence_exists hCauchy
  refine ⟨x, ?_⟩
  intro p hlimit
  obtain ⟨y, hy⟩ := hlimit
  exact hx p hy.cauchySeq

end SandronesLibrary.FunctionalAnalysis
