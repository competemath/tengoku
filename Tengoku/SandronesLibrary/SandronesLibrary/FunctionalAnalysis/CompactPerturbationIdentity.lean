/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.CompactOperator
import Tengoku.Seed.Analysis.LocallyConvex.HahnBanach
import Tengoku.Seed.Analysis.Normed.Module.RieszLemma
import Tengoku.Seed.Analysis.Normed.Operator.Banach

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 恒等算子的紧扰动

本文件证明 Fredholm 理论的第一条基本结论：Banach 空间上的紧算子 `K` 使
`I - K` 的核有限维。证明只使用紧算子的复合、闭子空间限制与 Riesz 有限维判据，
不调用 Mathlib 的最终 Fredholm alternative。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Filter Function Set _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `I - K`，作为后续 Fredholm 论证中的具名算子。

> **Entry**: functional-analysis.fredholm.alternative-/
noncomputable def identitySubCompact (K : E →L[ℝ] E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - K

@[simp]
theorem identitySubCompact_apply (K : E →L[ℝ] E) (x : E) :
    identitySubCompact K x = x - K x := by
  rfl

private noncomputable def compactOnIdentitySubCompactKernel (K : E →L[ℝ] E) :
    (identitySubCompact K).ker →L[ℝ] (identitySubCompact K).ker :=
  (K.comp (identitySubCompact K).ker.subtypeL).codRestrict
    (identitySubCompact K).ker fun x ↦ by
      apply LinearMap.mem_ker.mpr
      have hx := LinearMap.mem_ker.mp x.2
      change x.1 - K x.1 = 0 at hx
      have hKx : K x.1 = x.1 := (sub_eq_zero.mp hx).symm
      simp [hKx]

@[simp]
private theorem compactOnIdentitySubCompactKernel_apply (K : E →L[ℝ] E)
    (x : (identitySubCompact K).ker) :
    compactOnIdentitySubCompactKernel K x = x := by
  apply Subtype.ext
  change K x.1 = x.1
  have hx := LinearMap.mem_ker.mp x.2
  change x.1 - K x.1 = 0 at hx
  exact (sub_eq_zero.mp hx).symm

/-- 紧算子 `K` 的恒等扰动 `I-K` 具有有限维核。

在核上 `K` 就是恒等算子；紧性在定义域限制和闭值域限制下保持，因此核上的恒等算子
是紧算子。Riesz 有限维判据随即给出结论。-/
theorem finiteDimensional_kernel_identitySubCompact [CompleteSpace E]
    (K : E →L[ℝ] E) (hK : IsCompactOperator K) :
    FiniteDimensional ℝ (identitySubCompact K).ker := by
  have hcomp : IsCompactOperator (compactOnIdentitySubCompactKernel K) := by
    apply IsCompactOperator.codRestrict
    · exact hK.comp_clm (identitySubCompact K).ker.subtypeL
    · exact (identitySubCompact K).isClosed_ker
  have hid : compactOnIdentitySubCompactKernel K =
      ContinuousLinearMap.id ℝ (identitySubCompact K).ker := by
    ext x
    exact congrArg Subtype.val (compactOnIdentitySubCompactKernel_apply K x)
  rw [hid] at hcomp
  exact identity_isCompactOperator_iff_finiteDimensional.mp hcomp

private theorem identitySubCompact_antilipschitz_on_complement [CompleteSpace E]
    (K : E →L[ℝ] E) (hK : IsCompactOperator K)
    (C : Submodule ℝ E) (hCclosed : IsClosed (C : Set E))
    (hdisj : Disjoint (identitySubCompact K).ker C) :
    ∃ c, AntilipschitzWith c ((identitySubCompact K).domRestrict C) := by
  let D := (identitySubCompact K).domRestrict C
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  by_contra! hanti
  have hsmall : ∀ c > 0, ∃ x : C, ‖D x‖ < c * ‖x‖ := hanti
  obtain ⟨a : ℝ, ha⟩ := NormedField.exists_one_lt_norm ℝ
  have ha0 : 0 < ‖a‖⁻¹ := by positivity
  obtain ⟨φ, _hφanti, hφpos, hφlim⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have hex (n : ℕ) : ∃ x : C,
      ‖x‖ ≤ 1 ∧ ‖a‖⁻¹ ≤ ‖x‖ ∧ ‖D x‖ < φ n := by
    obtain ⟨z, hz⟩ := hsmall (φ n) (hφpos n)
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
    obtain ⟨η, _hη, hupper, hlower, _⟩ :=
      rescale_to_shell ha (ε := 1) (by norm_num) hz0
    refine ⟨η • z, hupper.le, by simpa using hlower, ?_⟩
    rw [map_smul, norm_smul]
    calc
      ‖η‖ * ‖D z‖ < ‖η‖ * (φ n * ‖z‖) :=
        (mul_lt_mul_of_pos_left hz (norm_pos_iff.mpr (by aesop))).trans_le le_rfl
      _ = φ n * ‖η • z‖ := by rw [norm_smul]; ring
      _ ≤ φ n := by
        simpa using mul_le_of_le_one_right (le_of_lt (hφpos n)) hupper.le
  choose x hxupper hxlower hxsmall using hex
  have hDlim : Tendsto (fun n ↦ D (x n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n ↦ (hxsmall n).le) hφlim
  have hKcompact : IsCompactOperator (K.comp C.subtypeL) := hK.comp_clm C.subtypeL
  obtain ⟨Q, hQcompact, hQmem⟩ := hKcompact.image_closedBall_subset_compact 1
  obtain ⟨y, _hyQ, ψ, hψmono, hKy⟩ := hQcompact.tendsto_subseq
    (x := fun n ↦ K (x n : E)) fun n ↦ hQmem ⟨x n, by simpa using hxupper n, rfl⟩
  have hxlim : Tendsto (fun n ↦ (x (ψ n) : E)) atTop (𝓝 y) := by
    have hsum : Tendsto (fun n ↦ D (x (ψ n)) + K (x (ψ n) : E)) atTop (𝓝 (0 + y)) :=
      (hDlim.comp hψmono.tendsto_atTop).add hKy
    simpa [D, identitySubCompact_apply] using hsum
  have hyC : y ∈ C := hCclosed.mem_of_tendsto hxlim
    (Filter.Eventually.of_forall fun n ↦ (x (ψ n)).property)
  have hyker : y ∈ (identitySubCompact K).ker := by
    apply LinearMap.mem_ker.mpr
    have hDz : Tendsto (fun n ↦ identitySubCompact K (x (ψ n) : E)) atTop (𝓝 0) := by
      change Tendsto (fun n ↦ D (x (ψ n))) atTop (𝓝 0)
      exact hDlim.comp hψmono.tendsto_atTop
    exact tendsto_nhds_unique
      ((identitySubCompact K).continuous.continuousAt.tendsto.comp hxlim)
      hDz
  have hy0 : y = 0 := by
    have hybot : y ∈ (⊥ : Submodule ℝ E) := by
      rw [← disjoint_iff.mp hdisj]
      exact ⟨hyker, hyC⟩
    simpa using hybot
  subst y
  rw [NormedAddGroup.tendsto_nhds_zero] at hxlim
  have hev := hxlim (‖a‖⁻¹) ha0
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  exact (not_lt_of_ge (hxlower (ψ N)) (hN N le_rfl)).elim

/-- 紧算子 `K` 的恒等扰动 `I-K` 具有闭值域。

证明在有限维核的闭补空间上使用紧性反证得到正下界；该限制算子的值域因而闭，且补空间
与核直和为全空间，所以它与 `I-K` 的完整值域相同。-/
theorem isClosed_range_identitySubCompact [CompleteSpace E]
    (K : E →L[ℝ] E) (hK : IsCompactOperator K) :
    IsClosed (Set.range (identitySubCompact K)) := by
  let D := identitySubCompact K
  let _ : FiniteDimensional ℝ D.ker := finiteDimensional_kernel_identitySubCompact K hK
  have hcomp : D.ker.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional D.ker
  let C := hcomp.complement
  have hCclosed : IsClosed (C : Set E) := hcomp.isClosed_complement
  have hcompl : IsCompl D.ker C := hcomp.isCompl_complement
  obtain ⟨c, hc⟩ := identitySubCompact_antilipschitz_on_complement K hK C hCclosed hcompl.disjoint
  have hrangeC : IsClosed (Set.range (D.domRestrict C)) :=
    hc.isClosed_range (D.domRestrict C).uniformContinuous
  rw [show Set.range D = Set.range (D.domRestrict C) by
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      have hx : x ∈ D.ker ⊔ C := by
        rw [hcompl.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
      refine ⟨⟨v, hv⟩, ?_⟩
      change D v = D x
      have hDu : D u = 0 := LinearMap.mem_ker.mp hu
      calc
        D v = D u + D v := by rw [hDu, zero_add]
        _ = D (u + v) := (map_add D u v).symm
        _ = D x := congrArg D huv
    · rintro y ⟨x, rfl⟩
      exact ⟨x, rfl⟩]
  exact hrangeC

end SandronesLibrary.FunctionalAnalysis
