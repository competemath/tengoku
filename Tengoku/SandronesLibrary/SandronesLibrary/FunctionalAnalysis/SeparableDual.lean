/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.BidualReflexive

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 可分性与双对偶

本文件记录典范双对偶嵌入与可分性之间可直接组装的基本推论。对偶可分性的更强
Hahn–Banach 判据与弱星单位球可度量化需要 F4 接口，不在此提前封装。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 若原空间可分且典范嵌入满射，则连续双对偶可分。

> **Entry**: functional-analysis.separable.dual
@isnad1 id=separabl.1h1v.s12.6f774437892d from=translated src=- shape=606e45b1 vocab=e65d6a19
-/
theorem separable_bidual_of_reflexive [TopologicalSpace.SeparableSpace E]
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)) :
    TopologicalSpace.SeparableSpace (StrongDual ℝ (StrongDual ℝ E)) := by
  exact hE.denseRange.separableSpace (NormedSpace.inclusionInDoubleDual ℝ E).continuous

/-- 若连续对偶可分，则原赋范空间可分。
@isnad1 id=separabl.0h1v.s6.9ca124b0bd5a from=translated src=- shape=2cabd5fe vocab=26e49f23
-/
theorem separable_of_separable_dual
    [TopologicalSpace.SeparableSpace (StrongDual ℝ E)] :
    TopologicalSpace.SeparableSpace E := by
  obtain ⟨D, hDcount, hDdense⟩ :=
    TopologicalSpace.exists_countable_dense (StrongDual ℝ E)
  let _ : Countable D := hDcount.to_subtype
  have hlt (d : D) : ‖(d : StrongDual ℝ E)‖ - (1 / 8 : ℝ) < ‖(d : StrongDual ℝ E)‖ := by
    norm_num
  let x : D → E := fun d ↦
    Classical.choose ((d : StrongDual ℝ E).exists_lt_apply_of_lt_opNorm (hlt d))
  have hxnorm (d : D) : ‖x d‖ < 1 :=
    (Classical.choose_spec
      ((d : StrongDual ℝ E).exists_lt_apply_of_lt_opNorm (hlt d))).1
  have hxeval (d : D) :
      ‖(d : StrongDual ℝ E)‖ - (1 / 8 : ℝ) < ‖(d : StrongDual ℝ E) (x d)‖ :=
    (Classical.choose_spec
      ((d : StrongDual ℝ E).exists_lt_apply_of_lt_opNorm (hlt d))).2
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range x)
  have hSclosure : S.topologicalClosure = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro z
    rw [mem_topologicalClosure_iff_forall_annihilator]
    intro f hf
    have hfzero : f = 0 := by
      by_contra hfne
      let g : StrongDual ℝ E := (‖f‖⁻¹ : ℝ) • f
      have hfnorm : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hfne
      have hgnorm : ‖g‖ = 1 := by
        simp [g, norm_smul, hfnorm]
      obtain ⟨d, hdD, hdist⟩ := hDdense.exists_dist_lt g (by norm_num : (0 : ℝ) < 1 / 8)
      let dD : D := ⟨d, hdD⟩
      have hdnorm : (7 / 8 : ℝ) < ‖d‖ := by
        have hrev : ‖g‖ - ‖d‖ ≤ ‖g - d‖ := norm_sub_norm_le g d
        rw [hgnorm, ← dist_eq_norm] at hrev
        linarith
      have hflower : (3 / 4 : ℝ) < ‖d (x dD)‖ := by
        have := hxeval dD
        change ‖d‖ - (1 / 8 : ℝ) < ‖d (x dD)‖ at this
        linarith
      have hfx : f (x dD) = 0 := by
        rw [mem_continuousAnnihilator_iff] at hf
        exact hf (x dD) (Submodule.subset_span (Set.mem_range_self dD))
      have hgx : g (x dD) = 0 := by
        simp [g, hfx]
      have hupper : ‖d (x dD)‖ < 1 / 8 := by
        calc
          ‖d (x dD)‖ = ‖(d - g) (x dD)‖ := by simp [hgx]
          _ ≤ ‖d - g‖ * ‖x dD‖ := (d - g).le_opNorm (x dD)
          _ < (1 / 8 : ℝ) := by
            have hdg : ‖d - g‖ < (1 / 8 : ℝ) := by
              rw [norm_sub_rev, ← dist_eq_norm]
              exact hdist
            nlinarith [hxnorm dD, norm_nonneg (d - g)]
      linarith
    simp [hfzero]
  have hSdense : Dense (S : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hSclosure
  have hSseparable : TopologicalSpace.IsSeparable (S : Set E) :=
    (Set.countable_range x).isSeparable.span
  exact hSdense.isSeparable_iff.mp hSseparable

/-- 可分自反空间的连续对偶可分。
@isnad1 id=separabl.1h1v.s12.feab66b96af8 from=translated src=- shape=6f3e846f vocab=e65d6a19
-/
theorem separable_dual_of_reflexive [TopologicalSpace.SeparableSpace E]
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)) :
    TopologicalSpace.SeparableSpace (StrongDual ℝ E) := by
  let _ : TopologicalSpace.SeparableSpace (StrongDual ℝ (StrongDual ℝ E)) :=
    separable_bidual_of_reflexive hE
  exact separable_of_separable_dual

end SandronesLibrary.FunctionalAnalysis
