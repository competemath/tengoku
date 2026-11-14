/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.SpectrumNonemptyCompact
import Tengoku.Seed.Analysis.Normed.Operator.Compact.FiniteDimension
import Tengoku.Seed.Analysis.Normed.Operator.Compact.FredholmAlternative
import Tengoku.Seed.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 紧算子的非零谱

本文件研究复 Banach 空间上紧算子的非零谱。Mathlib 的 Fredholm alternative 已识别非零谱点
与特征值；这里进一步在一般 Banach 空间中证明相应特征空间有限维，并为谱的聚点边界提供接口。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Filter Function Module End Set _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- 紧算子的非零谱点恰好是非零特征值。

这里的 `HasEigenvalue` 使用底层线性映射 `(T : Module.End ℂ E)`；谱仍使用连续线性自同态
Banach 代数上的 `spectrum ℂ T`。

> **Entry**: functional-analysis.compact-spectrum
@isnad1 id=iff.2h3v.s8.c842bef6b2d1 from=translated src=- shape=b2a9c794 vocab=35821ab6
-/
theorem compact_hasEigenvalue_iff_mem_spectrum (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) {μ : ℂ} (hμ : μ ≠ 0) :
    HasEigenvalue (T : Module.End ℂ E) μ ↔ μ ∈ spectrum ℂ T :=
  hT.hasEigenvalue_iff_mem_spectrum hμ

/-- 一般复 Banach 空间上，紧算子的每个非零特征空间都是有限维的。

证明把 `T` 限制到 `μ`-特征空间。在该空间上限制算子等于 `μ • id`；因 `μ ≠ 0`，其紧性
等价于恒等算子的紧性，Riesz 有限维判据于是给出结论。这个证明不需要内积或自伴性。
@isnad1 id=finitedi.2h3v.s9.85119ee498be from=translated src=- shape=b70af8e7 vocab=1d381cb9
-/
theorem finiteDimensional_eigenspace_of_compact (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) (μ : ℂ) (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (eigenspace T.toLinearMap μ) := by
  replace hT := hT.restrict'
    ((mem_invtSubmodule_iff_forall_mem_of_mem _).mp
      (eigenspace_mem_invtSubmodule T.toLinearMap μ))
  rw [restrict_eigenspace, LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at hT
  rwa [← isCompactOperator_id_iff_finiteDimensional]

private noncomputable def compactOnKernelOfIdentitySub (K : E →L[ℂ] E) :
    (ContinuousLinearMap.id ℂ E - K).ker →L[ℂ]
      (ContinuousLinearMap.id ℂ E - K).ker :=
  (K.comp (ContinuousLinearMap.id ℂ E - K).ker.subtypeL).codRestrict
    (ContinuousLinearMap.id ℂ E - K).ker fun x ↦ by
      apply LinearMap.mem_ker.mpr
      have hx := LinearMap.mem_ker.mp x.2
      change x.1 - K x.1 = 0 at hx
      have hKx : K x.1 = x.1 := (sub_eq_zero.mp hx).symm
      change K x.1 - K (K x.1) = 0
      rw [hKx]
      exact hx

omit [CompleteSpace E] in
@[simp]
private theorem compactOnKernelOfIdentitySub_apply (K : E →L[ℂ] E)
    (x : (ContinuousLinearMap.id ℂ E - K).ker) :
    compactOnKernelOfIdentitySub K x = x := by
  apply Subtype.ext
  change K x.1 = x.1
  have hx := LinearMap.mem_ker.mp x.2
  change x.1 - K x.1 = 0 at hx
  exact (sub_eq_zero.mp hx).symm

omit [CompleteSpace E] in
/-- 复 Banach 空间上 `I-K` 的核有限维。这个标量一般化版本供紧算子的广义特征空间使用。-/
private theorem finiteDimensional_kernel_identity_sub_complex (K : E →L[ℂ] E)
    (hK : IsCompactOperator K) :
    FiniteDimensional ℂ (ContinuousLinearMap.id ℂ E - K).ker := by
  have hcomp : IsCompactOperator (compactOnKernelOfIdentitySub K) := by
    apply IsCompactOperator.codRestrict
    · exact hK.comp_clm (ContinuousLinearMap.id ℂ E - K).ker.subtypeL
    · exact (ContinuousLinearMap.id ℂ E - K).isClosed_ker
  have hid : compactOnKernelOfIdentitySub K =
      ContinuousLinearMap.id ℂ (ContinuousLinearMap.id ℂ E - K).ker := by
    ext x
    exact congrArg Subtype.val (compactOnKernelOfIdentitySub_apply K x)
  rw [hid] at hcomp
  exact isCompactOperator_id_iff_finiteDimensional.mp hcomp

private noncomputable def compactPowerRemainderComplex
    (K : E →L[ℂ] E) (n : ℕ) : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E - (ContinuousLinearMap.id ℂ E - K) ^ n

omit [CompleteSpace E] in
private theorem compactPowerRemainderComplex_isCompact (K : E →L[ℂ] E)
    (hK : IsCompactOperator K) (n : ℕ) :
    IsCompactOperator (compactPowerRemainderComplex K n) := by
  induction n with
  | zero =>
      simpa [compactPowerRemainderComplex] using
        (isCompactOperator_zero : IsCompactOperator (0 : E →L[ℂ] E))
  | succ n ih =>
      have heq : compactPowerRemainderComplex K (n + 1) =
          compactPowerRemainderComplex K n +
            ((ContinuousLinearMap.id ℂ E - K) ^ n).comp K := by
        ext x
        change x - ((ContinuousLinearMap.id ℂ E - K) ^ n) (x - K x) =
          (x - ((ContinuousLinearMap.id ℂ E - K) ^ n) x) +
            ((ContinuousLinearMap.id ℂ E - K) ^ n) (K x)
        rw [map_sub]
        module
      rw [heq]
      exact ih.add (hK.clm_comp ((ContinuousLinearMap.id ℂ E - K) ^ n))

omit [CompleteSpace E] in
/-- `I-K` 的每个幂都有有限维核。-/
private theorem finiteDimensional_kernel_pow_identity_sub_complex
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (n : ℕ) :
    FiniteDimensional ℂ ((ContinuousLinearMap.id ℂ E - K) ^ n).ker := by
  let R := compactPowerRemainderComplex K n
  have hR : IsCompactOperator R := compactPowerRemainderComplex_isCompact K hK n
  have heq : ContinuousLinearMap.id ℂ E - R =
      (ContinuousLinearMap.id ℂ E - K) ^ n := by
    ext x
    simp [R, compactPowerRemainderComplex]
  rw [← heq]
  exact finiteDimensional_kernel_identity_sub_complex R hR

omit [CompleteSpace E] in
/-- 紧算子每个非零特征值的任意有限阶广义特征空间都是有限维的。
@isnad1 id=finitedi.2h4v.s10.76a519ef93f8 from=translated src=- shape=35427f68 vocab=08efdd04
-/
theorem finiteDimensional_genEigenspace_of_compact (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) (μ : ℂ) (hμ : μ ≠ 0) (n : ℕ) :
    FiniteDimensional ℂ (Module.End.genEigenspace (T : Module.End ℂ E) μ n) := by
  rw [genEigenspace_nat]
  let K : E →L[ℂ] E := μ⁻¹ • T
  have hK : IsCompactOperator K := hT.smul μ⁻¹
  let D : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - K
  let _ : FiniteDimensional ℂ (D ^ n).ker := by
    exact finiteDimensional_kernel_pow_identity_sub_complex K hK n
  have hop : T.toLinearMap - μ • LinearMap.id = (-μ) • D.toLinearMap := by
    ext x
    change T x - μ • x = (-μ) • (x - μ⁻¹ • T x)
    simp only [neg_smul, smul_sub, smul_inv_smul₀ hμ]
    module
  have hpow : (T.toLinearMap - μ • LinearMap.id) ^ n =
      ((-μ) ^ n) • (D.toLinearMap ^ n) := by
    rw [hop, smul_pow]
  change FiniteDimensional ℂ
    (LinearMap.ker ((T.toLinearMap - μ • LinearMap.id) ^ n))
  have hker : LinearMap.ker ((T.toLinearMap - μ • LinearMap.id) ^ n) =
      LinearMap.ker (D.toLinearMap ^ n) := by
    rw [hpow, LinearMap.ker_smul _ _ (pow_ne_zero n (neg_ne_zero.mpr hμ))]
  have hDker : LinearMap.ker (D.toLinearMap ^ n) = (D ^ n).ker := by
    rw [← ContinuousLinearMap.toLinearMap_pow]
  have hall : LinearMap.ker ((T.toLinearMap - μ • LinearMap.id) ^ n) =
      (D ^ n).ker := hker.trans hDker
  exact LinearEquiv.finiteDimensional
    (LinearEquiv.ofEq _ _ hall.symm)

/-- 对任意正数 `ε`，紧算子谱中模至少为 `ε` 的点只有有限多个。

这是“零是非零谱唯一可能聚点”的定量形式。证明若存在无限多个彼此不同且远离零的特征值，
就在相应特征向量的递增有限维张成中逐次应用 Riesz 引理；所得有界向量序列的 `T`-像两两保持
固定正距离，违背紧性。
@isnad1 id=finite.2h3v.s8.955307cb6354 from=translated src=- shape=02f24792 vocab=fb039f4e
-/
theorem finite_spectrum_norm_ge_of_compact (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) {ε : ℝ} (hε : 0 < ε) :
    {μ : ℂ | μ ∈ spectrum ℂ T ∧ ε ≤ ‖μ‖}.Finite := by
  let S : Set ℂ := {μ : ℂ | μ ∈ spectrum ℂ T ∧ ε ≤ ‖μ‖}
  change S.Finite
  by_contra hSfinite
  have hSinf : S.Infinite := Set.not_finite.mp hSfinite
  let _ : Infinite S := Set.infinite_coe_iff.mpr hSinf
  let e : ℕ ↪ S := Infinite.natEmbedding S
  let μ (n : ℕ) : ℂ := (e n).1
  have hμmem (n : ℕ) : μ n ∈ spectrum ℂ T := (e n).2.1
  have hμnorm (n : ℕ) : ε ≤ ‖μ n‖ := (e n).2.2
  have hμne (n : ℕ) : μ n ≠ 0 := by
    intro hn
    have h := hμnorm n
    rw [hn, norm_zero] at h
    linarith
  have hμinj : Function.Injective μ := by
    intro m n hmn
    exact e.injective (Subtype.ext hmn)
  have heigen (n : ℕ) : HasEigenvalue (T : Module.End ℂ E) (μ n) :=
    (hT.hasEigenvalue_iff_mem_spectrum (hμne n)).mpr (hμmem n)
  choose v hv using fun n ↦ (heigen n).exists_hasEigenvector
  have hvli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (T : Module.End ℂ E) μ hμinj v hv
  let V (n : ℕ) : Submodule ℂ E :=
    Submodule.span ℂ (Set.range fun i : Fin n ↦ v i)
  have hV_mono {m n : ℕ} (hmn : m ≤ n) : V m ≤ V n := by
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨⟨i, i.2.trans_le hmn⟩, rfl⟩
  have hVmono (n : ℕ) : V n ≤ V (n + 1) := hV_mono (Nat.le_succ n)
  have hv_not_mem (n : ℕ) : v n ∉ V n := by
    have hli : LinearIndependent ℂ (fun i : Fin (n + 1) ↦ v i) :=
      hvli.comp (fun i : Fin (n + 1) ↦ (i : ℕ)) Fin.val_injective
    have hlast := (linearIndependent_finSucc'.mp hli).2
    have heq : Fin.init (fun i : Fin (n + 1) ↦ v i) = fun i : Fin n ↦ v i := by
      ext i
      rfl
    rw [heq] at hlast
    exact hlast
  have hv_mem_succ (n : ℕ) : v n ∈ V (n + 1) := by
    apply Submodule.subset_span
    exact ⟨Fin.last n, by simp⟩
  have hVproper (n : ℕ) : V n < V (n + 1) :=
    lt_of_le_of_ne (hVmono n) fun h ↦ hv_not_mem n (h ▸ hv_mem_succ n)
  have hVclosed (n : ℕ) : IsClosed (V n : Set E) := by
    let _ : FiniteDimensional ℂ (V n) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range fun i : Fin n ↦ v i)
    exact (V n).closed_of_finiteDimensional
  obtain ⟨c : ℂ, hc⟩ := NormedField.exists_one_lt_norm ℂ
  have hx (n : ℕ) : ∃ x : E, x ∈ V (n + 1) ∧
      1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + ‖c‖ ∧ ∀ y ∈ V n, 1 ≤ ‖x - y‖ := by
    have hclosed : IsClosed
        ((V n).comap (V (n + 1)).subtype : Set (V (n + 1))) := by
      exact (hVclosed n).preimage (V (n + 1)).subtypeL.continuous
    obtain ⟨z : V (n + 1), hznorm, hdist⟩ :=
      riesz_lemma_of_norm_lt hc (show ‖c‖ < 1 + ‖c‖ by linarith) hclosed
        ⟨⟨Classical.choose (SetLike.exists_of_lt (hVproper n)),
            (Classical.choose_spec (SetLike.exists_of_lt (hVproper n))).1⟩,
          (Classical.choose_spec (SetLike.exists_of_lt (hVproper n))).2⟩
    refine ⟨z.1, z.2, by simpa using hdist 0 (by simp), hznorm, ?_⟩
    intro y hy
    exact hdist ⟨y, hVmono n hy⟩ (by simpa)
  choose x hxV _hxlower hxupper hxfar using hx
  have hT_mem_V (n : ℕ) {z : E} (hz : z ∈ V n) : T z ∈ V n := by
    apply Submodule.span_induction (p := fun z _ ↦ T z ∈ V n) _ (by simp)
        (fun a b _ _ ha hb ↦ by simpa using Submodule.add_mem (V n) ha hb)
        (fun a z _ hz ↦ by simpa using Submodule.smul_mem (V n) a hz) hz
    rintro _ ⟨i, rfl⟩
    change T (v i) ∈ V n
    have hi := mem_eigenspace_iff.mp (hv i).1
    change T (v i) = μ i • v i at hi
    rw [hi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsub_mem_V (n : ℕ) {z : E} (hz : z ∈ V (n + 1)) :
      T z - μ n • z ∈ V n := by
    apply Submodule.span_induction (p := fun z _ ↦ T z - μ n • z ∈ V n) _
        (by simp) (fun a b _ _ ha hb ↦ by
          rw [map_add, smul_add, add_sub_add_comm]
          exact Submodule.add_mem (V n) ha hb)
        (fun a z _ hz ↦ by
          rw [map_smul]
          simpa only [smul_sub, smul_smul, mul_comm] using
            Submodule.smul_mem (V n) a hz) hz
    rintro _ ⟨i, rfl⟩
    change T (v i) - μ n • v i ∈ V n
    have hi_eigen := mem_eigenspace_iff.mp (hv i).1
    change T (v i) = μ i • v i at hi_eigen
    rw [hi_eigen]
    by_cases hi : (i : ℕ) = n
    · rw [hi]
      simp
    · have hil : (i : ℕ) < n := by omega
      have hi' : Fin n := ⟨i, hil⟩
      have hvV : v i ∈ V n := by
        apply Submodule.subset_span
        refine ⟨⟨i.val, hil⟩, ?_⟩
        rfl
      rw [← sub_smul]
      exact Submodule.smul_mem (V n) (μ i - μ n) hvV
  have hsep (m n : ℕ) (hmn : m < n) : ε ≤ ‖T (x n) - T (x m)‖ := by
    let y : E := x n - (μ n)⁻¹ • (T (x n) - T (x m))
    have hymem : y ∈ V n := by
      have hxm : x m ∈ V n := hV_mono (Nat.succ_le_of_lt hmn) (hxV m)
      have hbase : T (x n) - μ n • x n - T (x m) ∈ V n :=
        Submodule.sub_mem _ (hsub_mem_V n (hxV n)) (hT_mem_V n hxm)
      have hy : y = -(μ n)⁻¹ • (T (x n) - μ n • x n - T (x m)) := by
        dsimp [y]
        simp only [neg_smul, smul_sub, inv_smul_smul₀ (hμne n)]
        module
      rw [hy]
      exact Submodule.smul_mem _ _ hbase
    have heq : T (x n) - T (x m) = μ n • (x n - y) := by
      calc
        T (x n) - T (x m) = μ n • ((μ n)⁻¹ • (T (x n) - T (x m))) := by
          rw [smul_smul, mul_inv_cancel₀ (hμne n), one_smul]
        _ = μ n • (x n - y) := by simp [y]
    rw [heq, norm_smul]
    calc
      ε ≤ ‖μ n‖ := hμnorm n
      _ = ‖μ n‖ * 1 := (mul_one _).symm
      _ ≤ ‖μ n‖ * ‖x n - y‖ :=
        mul_le_mul_of_nonneg_left (hxfar n y hymem) (norm_nonneg _)
  obtain ⟨Q, hQcompact, hQmem⟩ := hT.image_closedBall_subset_compact (1 + ‖c‖)
  obtain ⟨y, _hyQ, ψ, hψmono, hTx⟩ := hQcompact.tendsto_subseq
    (x := fun n ↦ T (x n)) fun n ↦ hQmem ⟨x n, by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxupper n, rfl⟩
  have hcauchy := hTx.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ε hε
  have hlt := hN (N + 1) (by omega)
  rw [dist_eq_norm] at hlt
  exact (not_le_of_gt hlt)
    (hsep (ψ N) (ψ (N + 1)) (hψmono (by omega)))

/-- 紧算子的任意互异谱点序列都趋于零。

这准确表达“零是谱的唯一可能聚点”：对每个 `ε > 0`，前一定理给出有限个模至少为 `ε`
的谱点；序列的单射性保证它最终避开这有限集。定理不声称 `0` 必然属于谱或必然真是聚点，
因为有限秩算子以及有限维空间都可能只有有限谱。
@isnad1 id=tendsto.3h3v.s8.8d37240f92ed from=translated src=- shape=cc2be1a1 vocab=fd3862fc
-/
theorem tendsto_zero_of_injective_spectrum_sequence (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) (μ : ℕ → ℂ) (hμ : ∀ n, μ n ∈ spectrum ℂ T)
    (hμinj : Function.Injective μ) :
    Tendsto μ atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  let S : Set ℂ := {z : ℂ | z ∈ spectrum ℂ T ∧ ε ≤ ‖z‖}
  have hSfinite : S.Finite := finite_spectrum_norm_ge_of_compact T hT hε
  have hpre : (μ ⁻¹' S).Finite := hSfinite.preimage hμinj.injOn
  let F : Finset ℕ := hpre.toFinset
  rw [eventually_atTop]
  refine ⟨F.sup id + 1, fun n hn ↦ ?_⟩
  by_contra hnorm
  have hnS : μ n ∈ S := ⟨hμ n, le_of_not_gt hnorm⟩
  have hnF : n ∈ F := by
    simpa [F] using hnS
  have hnle : n ≤ F.sup id := Finset.le_sup (f := id) hnF
  omega

end SandronesLibrary.FunctionalAnalysis
