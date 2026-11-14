/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.CompactSpectrum
import Tengoku.Seed.Analysis.InnerProductSpace.Spectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 紧自伴算子的谱分解

本文件采用 Mathlib 的连续线性映射、紧算子和对称线性映射承载，组装紧自伴算子谱定理的教材式
结论：特征值为实、互异特征空间正交、特征空间的线性张成稠密，并且非零特征空间有限维。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Module End

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

private theorem dense_iSup_eigenspaces_of_orthogonal_eq_bot
    (T : E →ₗ[𝕜] E) (h : (⨆ μ, eigenspace T μ)ᗮ = ⊥) :
    Dense ((⨆ μ, eigenspace T μ : Submodule 𝕜 E) : Set E) := by
  let V : Submodule 𝕜 E := ⨆ μ, eigenspace T μ
  have hVorth : Vᗮ = ⊥ := h
  have hclosureOrth : V.topologicalClosureᗮ = ⊥ := by
    rw [V.orthogonal_closure, hVorth]
  have hclosure : V.topologicalClosure = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hclosureOrth
  rw [dense_iff_closure_eq, ← V.topologicalClosure_coe, hclosure]
  rfl

/-- 紧自伴算子的特征空间给出正交且稠密的谱分解。

这里“完备”明确表示所有特征空间之和的闭包是全空间，而不是代数直和已经等于全空间。
`star μ = μ` 在 `𝕜 = ℂ` 时正是特征值 `μ` 为实数。最后一项只对非零特征值断言有限维；核可以
是无限维的。

> **Entry**: functional-analysis.hilbert.compact-selfadjoint-spectral
@isnad1 id=and.2h3v.s11.16ad33b2ff3b from=translated src=- shape=5f128170 vocab=2c6ae855
-/
theorem compact_isSymmetric_spectral_decomposition {T : E →L[𝕜] E}
    (hK : IsCompactOperator T) (hT : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (∀ μ, HasEigenvalue (T : End 𝕜 E) μ → star μ = μ) ∧
      OrthogonalFamily 𝕜 (fun μ => eigenspace (T : End 𝕜 E) μ)
        (fun μ => (eigenspace (T : End 𝕜 E) μ).subtypeₗᵢ) ∧
      Dense ((⨆ μ, eigenspace (T : End 𝕜 E) μ : Submodule 𝕜 E) : Set E) ∧
      ∀ μ, μ ≠ 0 → FiniteDimensional 𝕜 (eigenspace (T : End 𝕜 E) μ) := by
  have hcomplete :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hK hT
  refine ⟨fun _ hμ => hT.conj_eigenvalue_eq_self hμ,
    hT.orthogonalFamily_eigenspaces,
    dense_iSup_eigenspaces_of_orthogonal_eq_bot (T : End 𝕜 E) hcomplete, ?_⟩
  exact fun μ hμ => ContinuousLinearMap.finite_dimensional_eigenspace hK μ hμ

end SandronesLibrary.FunctionalAnalysis
