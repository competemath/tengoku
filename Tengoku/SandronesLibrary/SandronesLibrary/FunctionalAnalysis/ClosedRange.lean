/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.AnnihilatorClosure
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.DualOperator
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.HahnBanach
import Tengoku.Seed.Analysis.Normed.Operator.Banach
import Tengoku.Seed.Analysis.Normed.Operator.Extend

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 闭值域定理

本文件研究 Banach 空间之间连续线性映射的值域、核与对偶算子。
对偶算子仍使用 `dualOperator`，连续零化子仍使用
`StrongDual.polarSubmodule`，不引入 Fredholm 承载。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Set Function

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- 对偶算子的核精确是原算子值域的连续零化子。

> **Entry**: functional-analysis.closed-range
@isnad1 id=eq.0h3v.s9.5dea8b868b0c from=translated src=- shape=ef0428d1 vocab=8357cd01
-/
theorem dualOperator_ker_eq_range_annihilator (T : E →L[ℝ] F) :
    (dualOperator T).ker = StrongDual.polarSubmodule ℝ T.range := by
  ext f
  rw [LinearMap.mem_ker, mem_continuousAnnihilator_iff]
  constructor
  · intro hf y hy
    obtain ⟨x, rfl⟩ := hy
    simpa using congrFun (congrArg DFunLike.coe hf) x
  · intro hf
    ext x
    exact hf (T x) (T.mem_range_self x)

/-- 对偶算子的值域总包含在原算子核的连续零化子中。
@isnad1 id=le.0h3v.s10.1aa076db697b from=translated src=- shape=42e7afd4 vocab=090f168e
-/
theorem dualOperator_range_le_ker_annihilator (T : E →L[ℝ] F) :
    (dualOperator T).range ≤ StrongDual.polarSubmodule ℝ T.ker := by
  intro f hf
  obtain ⟨g, rfl⟩ := hf
  rw [mem_continuousAnnihilator_iff]
  intro x hx
  have hTx : T x = 0 := LinearMap.mem_ker.mp hx
  change g (T x) = 0
  rw [hTx, map_zero]

/-- 连续零化子是范数对偶中的闭线性子空间。
@isnad1 id=isclosed.0h2v.s9.8f3685425e97 from=translated src=- shape=6f66ed18 vocab=99878fcc
-/
theorem continuousAnnihilator_isClosed (S : Submodule ℝ E) :
    IsClosed (StrongDual.polarSubmodule ℝ S : Set (StrongDual ℝ E)) := by
  rw [show (StrongDual.polarSubmodule ℝ S : Set (StrongDual ℝ E)) =
      ⋂ x ∈ S, ((ContinuousLinearMap.apply ℝ ℝ) x).ker by
    ext f
    simp [mem_continuousAnnihilator_iff, LinearMap.mem_ker]]
  exact isClosed_biInter fun x _ ↦ ((ContinuousLinearMap.apply ℝ ℝ) x).isClosed_ker

private noncomputable def dualOperatorToKerAnnihilator (T : E →L[ℝ] F) :
    StrongDual ℝ F →L[ℝ] StrongDual.polarSubmodule ℝ T.ker :=
  (dualOperator T).codRestrict (StrongDual.polarSubmodule ℝ T.ker)
    (fun f ↦ dualOperator_range_le_ker_annihilator T
      ((dualOperator T).mem_range_self f))

@[simp] private theorem dualOperatorToKerAnnihilator_apply_coe (T : E →L[ℝ] F)
    (f : StrongDual ℝ F) :
    (dualOperatorToKerAnnihilator T f : StrongDual ℝ E) = dualOperator T f := rfl

private theorem dualOperatorToKerAnnihilator_surjective_iff (T : E →L[ℝ] F) :
    Surjective (dualOperatorToKerAnnihilator T) ↔
      (dualOperator T).range = StrongDual.polarSubmodule ℝ T.ker := by
  constructor
  · intro hsurj
    apply le_antisymm (dualOperator_range_le_ker_annihilator T)
    intro f hf
    obtain ⟨g, hg⟩ := hsurj ⟨f, hf⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  · intro heq f
    have hf : (f : StrongDual ℝ E) ∈ (dualOperator T).range := heq.symm ▸ f.property
    obtain ⟨g, hg⟩ := hf
    refine ⟨g, Subtype.ext ?_⟩
    exact hg

private noncomputable def quotientKerOperator (T : E →L[ℝ] F) :
    HasQuotient.Quotient E T.ker →L[ℝ] F :=
  T.ker.liftQL T le_rfl

@[simp] private theorem quotientKerOperator_mk (T : E →L[ℝ] F) (x : E) :
    quotientKerOperator T (T.ker.mkQ x) = T x := by
  rfl

private theorem quotientKerOperator_injective (T : E →L[ℝ] F) :
    Injective (quotientKerOperator T) := by
  intro x y hxy
  revert hxy
  refine Submodule.Quotient.induction_on T.ker x ?_
  intro a
  refine Submodule.Quotient.induction_on T.ker y ?_
  intro b hab
  change T a = T b at hab
  rw [Submodule.Quotient.eq]
  apply LinearMap.mem_ker.mpr
  rw [map_sub]
  exact sub_eq_zero.mpr hab

private theorem quotientKerOperator_range (T : E →L[ℝ] F) :
    Set.range (quotientKerOperator T) = Set.range T := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | _ x => exact ⟨x, quotientKerOperator_mk T x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨T.ker.mkQ x, quotientKerOperator_mk T x⟩

private noncomputable def quotientKerFunctional (T : E →L[ℝ] F)
    (f : StrongDual ℝ E) (hf : f ∈ StrongDual.polarSubmodule ℝ T.ker) :
    StrongDual ℝ (HasQuotient.Quotient E T.ker) :=
  T.ker.liftQL f fun x hx ↦ (mem_continuousAnnihilator_iff T.ker f).mp hf x hx

@[simp] private theorem quotientKerFunctional_mk (T : E →L[ℝ] F)
    (f : StrongDual ℝ E) (hf : f ∈ StrongDual.polarSubmodule ℝ T.ker) (x : E) :
    quotientKerFunctional T f hf (T.ker.mkQ x) = f x := by
  rfl

/-- 原算子值域闭时，对偶算子的值域精确等于原算子核的连续零化子。
@isnad1 id=eq.1h3v.s10.5e7a7207ca9f from=translated src=- shape=0688b753 vocab=5540d9ff
-/
theorem dualOperator_range_eq_ker_annihilator_of_isClosed_range
    [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : IsClosed (Set.range T)) :
    (dualOperator T).range = StrongDual.polarSubmodule ℝ T.ker := by
  apply le_antisymm (dualOperator_range_le_ker_annihilator T)
  intro f hf
  let _ : IsClosed (T.ker : Set E) := T.isClosed_ker
  let Q := quotientKerOperator T
  have hQinj : Injective Q := quotientKerOperator_injective T
  have hQrange : IsClosed (Set.range Q) := by
    rw [quotientKerOperator_range]
    exact hT
  obtain ⟨K, hK⟩ := ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range
    (𝕜 := ℝ) (E := HasQuotient.Quotient E T.ker) (F := F) Q hQinj hQrange
  let qf := quotientKerFunctional T f hf
  have hbound : ∃ C : ℝ, ∀ x : E, ‖f x‖ ≤ C * ‖T x‖ := by
    refine ⟨‖qf‖ * K, ?_⟩
    intro x
    have hqf : ‖qf (T.ker.mkQ x)‖ ≤ ‖qf‖ * ‖T.ker.mkQ x‖ := qf.le_opNorm _
    have hanti := hK.le_mul_dist (T.ker.mkQ x) 0
    simp only [dist_zero_right, map_zero, Q, quotientKerOperator_mk] at hanti
    calc
      ‖f x‖ = ‖qf (T.ker.mkQ x)‖ := by rw [quotientKerFunctional_mk]
      _ ≤ ‖qf‖ * ‖T.ker.mkQ x‖ := hqf
      _ ≤ ‖qf‖ * (K * ‖T x‖) :=
        mul_le_mul_of_nonneg_left hanti (norm_nonneg qf)
      _ = (‖qf‖ * K) * ‖T x‖ := by ring
  let frange : StrongDual ℝ T.range := f.toLinearMap.compLeftInverse T.toLinearMap
  obtain ⟨g, hg, _hgnorm⟩ := hahnBanach_exists_extension_norm_eq T.range frange
  refine ⟨g, ?_⟩
  ext x
  have happly := LinearMap.compLeftInverse_apply_of_bdd
    f.toLinearMap T.toLinearMap hbound x (T x) rfl
  have hgTx := hg ⟨T x, T.mem_range_self x⟩
  change g (T x) = f x
  rw [hgTx]
  exact happly

/-- 若对偶算子的值域已经等于原算子核的零化子，则原算子值域闭。
@isnad1 id=isclosed.1h3v.s10.0786b96ed76f from=translated src=- shape=e7f138ec vocab=5540d9ff
-/
theorem isClosed_range_of_dualOperator_range_eq_ker_annihilator
    [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (heq : (dualOperator T).range = StrongDual.polarSubmodule ℝ T.ker) :
    IsClosed (Set.range T) := by
  let _ : IsClosed (T.ker : Set E) := T.isClosed_ker
  let _ : IsClosed (StrongDual.polarSubmodule ℝ T.ker : Set (StrongDual ℝ E)) :=
    continuousAnnihilator_isClosed T.ker
  have hsurj : Surjective (dualOperatorToKerAnnihilator T) :=
    (dualOperatorToKerAnnihilator_surjective_iff T).2 heq
  obtain ⟨C, hCpos, hpre⟩ :=
    ContinuousLinearMap.exists_preimage_norm_le
      (𝕜 := ℝ) (𝕜' := ℝ) (E := StrongDual ℝ F)
      (F := StrongDual.polarSubmodule ℝ T.ker)
      (dualOperatorToKerAnnihilator T) hsurj
  let Q := quotientKerOperator T
  have hQnorm : ∀ q, ‖q‖ ≤ C * ‖Q q‖ := by
    intro q
    by_cases hq₀ : q = 0
    · subst q
      simp
    obtain ⟨φ, hφnorm, hφq⟩ := exists_dual_vector ℝ q (norm_ne_zero_iff.mpr hq₀)
    let f : StrongDual ℝ E := φ.comp T.ker.mkQL
    have hfann : f ∈ StrongDual.polarSubmodule ℝ T.ker := by
      rw [mem_continuousAnnihilator_iff]
      intro x hx
      have hx₀ : T.ker.mkQL x = 0 := by
        rw [Submodule.mkQL_apply, Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero T.ker).2 hx
      simp [f, hx₀]
    let y : StrongDual.polarSubmodule ℝ T.ker := ⟨f, hfann⟩
    obtain ⟨g, hgy, hgnorm⟩ := hpre y
    have hfnorm : ‖f‖ ≤ 1 := by
      have hmk : ‖T.ker.mkQL‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro x
        rw [one_mul, Submodule.mkQL_apply, Submodule.mkQ_apply]
        exact Submodule.Quotient.norm_mk_le T.ker x
      calc
        ‖f‖ ≤ ‖φ‖ * ‖T.ker.mkQL‖ := φ.opNorm_comp_le T.ker.mkQL
        _ ≤ 1 * 1 := by simpa [hφnorm] using hmk
        _ = 1 := one_mul 1
    have hynorm : ‖y‖ ≤ 1 := by simpa [y] using hfnorm
    have hφg : φ q = g (Q q) := by
      refine Submodule.Quotient.induction_on T.ker q ?_
      intro x
      have hcoe := congrArg Subtype.val hgy
      have happly := congrFun (congrArg DFunLike.coe hcoe) x
      change φ (T.ker.mkQ x) = g (Q (T.ker.mkQ x))
      rw [show Q (T.ker.mkQ x) = T x by exact quotientKerOperator_mk T x]
      simpa [f, y] using happly.symm
    calc
      ‖q‖ = |φ q| := by simp [hφq]
      _ = |g (Q q)| := by rw [hφg]
      _ = ‖g (Q q)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖g‖ * ‖Q q‖ := g.le_opNorm _
      _ ≤ (C * ‖y‖) * ‖Q q‖ :=
        mul_le_mul_of_nonneg_right hgnorm (norm_nonneg _)
      _ ≤ (C * 1) * ‖Q q‖ := by gcongr
      _ = C * ‖Q q‖ := by rw [mul_one]
  let K : NNReal := ⟨C, hCpos.le⟩
  have hanti : AntilipschitzWith K Q := by
    apply (antilipschitzWith_iff_le_mul_dist).2
    intro q r
    change dist q r ≤ C * dist (Q q) (Q r)
    simpa [dist_eq_norm] using hQnorm (q - r)
  have hclosedQ : IsClosed (Set.range Q) :=
    hanti.isClosed_range Q.uniformContinuous
  rwa [quotientKerOperator_range] at hclosedQ

/-- 闭值域与“对偶值域等于核的零化子”的充要刻画。
@isnad1 id=iff.0h3v.s10.913d80479cbe from=translated src=- shape=58fecb00 vocab=5540d9ff
-/
theorem isClosed_range_iff_dualOperator_range_eq_ker_annihilator
    [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F) :
    IsClosed (Set.range T) ↔
      (dualOperator T).range = StrongDual.polarSubmodule ℝ T.ker :=
  ⟨dualOperator_range_eq_ker_annihilator_of_isClosed_range T,
    isClosed_range_of_dualOperator_range_eq_ker_annihilator T⟩

end SandronesLibrary.FunctionalAnalysis
