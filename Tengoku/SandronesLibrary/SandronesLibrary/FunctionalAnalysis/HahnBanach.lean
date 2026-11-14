/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.InverseOperator
import Tengoku.Seed.Analysis.Normed.Module.HahnBanach

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hahn–Banach 延拓定理

本文件区分 Hahn–Banach 的两层教材表述：代数层把受次线性函数支配的实线性泛函延拓到全空间；
赋范层把子空间上的连续线性泛函等范数延拓。两层都直接使用 Mathlib 接口，不另造“次线性泛函”
或部分泛函结构。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {E : Type*}

/-- 实 Hahn–Banach 定理的支配形式。`N_hom` 与 `N_add` 正是函数 `N` 的正齐次性和次可加性，
也就是本条所称的次线性条件。

> **Entry**: functional-analysis.hahn-banach.extension-/
theorem hahnBanach_dominated_extension [AddCommGroup E] [Module ℝ E]
    (S : Submodule ℝ E) (f : S →ₗ[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : S, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : S, g x = f x) ∧ ∀ x, g x ≤ N x := by
  exact exists_extension_of_le_sublinear (⟨S, f⟩ : E →ₗ.[ℝ] ℝ) N N_hom N_add hf

/-- 赋范 Hahn–Banach 定理：子空间上的连续线性泛函可延拓到全空间且算子范数不变。-/
theorem hahnBanach_exists_extension_norm_eq [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Subspace ℝ E) (f : StrongDual ℝ S) :
    ∃ g : StrongDual ℝ E, (∀ x : S, g x = f x) ∧ ‖g‖ = ‖f‖ := by
  exact exists_extension_norm_eq S f

/-- 等范数延拓特别给出一个不增范数、并在原子空间上逐点一致的全空间泛函。-/
theorem hahnBanach_exists_extension_norm_le [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Subspace ℝ E) (f : StrongDual ℝ S) :
    ∃ g : StrongDual ℝ E, (∀ x : S, g x = f x) ∧ ‖g‖ ≤ ‖f‖ := by
  obtain ⟨g, hg, hnorm⟩ := hahnBanach_exists_extension_norm_eq S f
  exact ⟨g, hg, hnorm.le⟩

end SandronesLibrary.FunctionalAnalysis
