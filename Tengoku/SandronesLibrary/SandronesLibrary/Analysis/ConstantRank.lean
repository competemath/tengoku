/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.InverseImplicit
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension
import Tengoku.Seed.Analysis.Convex.Basic
import Tengoku.Seed.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rudin 9.32 常秩定理

本文件严格采用 Rudin 的坐标变换

`G(x) = x + S (P (F(x) - A x))`,

而不是预先选定定义域和值域坐标后的投影正规形。证明依次构造线性右逆、Rudin
坐标变换、局部微分同胚以及沿 `ker A` 纤维下降的余项。
-/

noncomputable section

namespace SandronesLibrary.Analysis.Multivariable

open Set Filter
open scoped _root_.Topology

/-- Rudin 9.32 常秩定理所用的欧氏空间记号。

> **Entry**: analysis.multivariable.constant-rank-theorem-/
abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n m r : ℕ}

/-- Rudin 证明中 `Y₁ = range A` 上的线性右逆 `S`，即公式 (68)。
@isnad1 id=ex.0h3v.s13.b5e133ae8f5a from=translated src=- shape=f48e90ff vocab=98d5208f
-/
lemma range_right_inverse
    (A : Euc n →L[ℝ] Euc m) :
    ∃ S : A.range →L[ℝ] Euc n,
      ∀ y : A.range, A (S y) = y := by
  obtain ⟨S, hS⟩ := A.rangeRestrict.exists_rightInverse_of_surjective
    (by simp)
  refine ⟨S, fun y ↦ ?_⟩
  have hy := DFunLike.congr_fun hS y
  exact congr_arg Subtype.val hy

/-- Rudin 公式 (69) 的纯微分与代数部分：构造 `G`，证明 `G'(a)=I` 和公式 (70)。
@isnad1 id=ex.5h8v.s14.cf29251ae9da from=translated src=- shape=ea2cba3a vocab=596fd936
-/
lemma rudin_coordinate_map
    {E : Set (Euc n)} {F : Euc n → Euc m} {a : Euc n}
    (hF : ContDiffOn ℝ 1 F E)
    (A : Euc n →L[ℝ] Euc m) (hA : HasFDerivAt F A a)
    (P : Euc m →L[ℝ] Euc m) (hP : P.comp P = P)
    (hPrange : P.range = A.range)
    (S : A.range →L[ℝ] Euc n) (hS : ∀ y : A.range, A (S y) = y) :
    ∃ G : Euc n → Euc n,
      (∀ x, G x = x + S ⟨P (F x - A x), by
        rw [← hPrange]
        exact LinearMap.mem_range_self (P : Euc m →ₗ[ℝ] Euc m) (F x - A x)⟩) ∧
      ContDiffOn ℝ 1 G E ∧
      HasFDerivAt G (ContinuousLinearMap.id ℝ (Euc n)) a ∧
      ∀ x ∈ E, A (G x) = P (F x) := by
  let PA : Euc m →L[ℝ] A.range :=
    P.codRestrict A.range (by
      intro y
      rw [← hPrange]
      exact LinearMap.mem_range_self (P : Euc m →ₗ[ℝ] Euc m) y)
  let T : Euc m →L[ℝ] Euc n := S.comp PA
  let R : Euc n → Euc m := F - A
  let G : Euc n → Euc n := fun x ↦ x + T (R x)
  have hR : ContDiffOn ℝ 1 R E := hF.sub A.contDiff.contDiffOn
  have hG : ContDiffOn ℝ 1 G E := contDiffOn_id.add
    (T.contDiff.comp_contDiffOn hR)
  have hRderiv : HasFDerivAt R (0 : Euc n →L[ℝ] Euc m) a := by
    simpa [R] using hA.sub A.hasFDerivAt
  have hGderiv : HasFDerivAt G (ContinuousLinearMap.id ℝ (Euc n)) a := by
    have hT : HasFDerivAt (fun x ↦ T (R x)) (0 : Euc n →L[ℝ] Euc n) a := by
      have hraw := T.hasFDerivAt.comp a hRderiv
      have hraw0 := hraw.congr_fderiv (ContinuousLinearMap.comp_zero T)
      exact hraw0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)
    have hid : HasFDerivAt (fun x : Euc n ↦ x)
        (ContinuousLinearMap.id ℝ (Euc n)) a :=
      (ContinuousLinearMap.id ℝ (Euc n)).hasFDerivAt
    have hadd := (hid.add hT).congr_fderiv (add_zero _)
    exact hadd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hPA : P.comp A = A := by
    apply ContinuousLinearMap.ext
    intro x
    have hx : A x ∈ P.range := by
      rw [hPrange]
      exact LinearMap.mem_range_self (A : Euc n →ₗ[ℝ] Euc m) x
    obtain ⟨y, hy⟩ := hx
    have hp := DFunLike.congr_fun hP y
    change P (P y) = P y at hp
    change P (A x) = A x
    rw [← hy]
    exact hp
  refine ⟨G, ?_, hG, hGderiv, ?_⟩
  · intro x
    change x + T (R x) = x + S _
    congr 1
  · intro x _
    change A (x + T (R x)) = P (F x)
    rw [map_add]
    have hAS : A (T (R x)) = P (R x) := hS (PA (R x))
    rw [hAS]
    change A x + P (F x - A x) = P (F x)
    rw [map_sub, show P (A x) = A x by
      exact DFunLike.congr_fun hPA x]
    abel

/-- 由 `G'(a)=I` 和导数连续性，缩到一个导数处处可逆的邻域，并取得 `C¹` 局部逆。
@isnad1 id=ex.4h4v.s11.808fe8ca223e from=translated src=- shape=823a5046 vocab=b0ecd24c
-/
lemma rudin_local_diffeomorph_near
    {E : Set (Euc n)} {G : Euc n → Euc n} {a : Euc n}
    (hE : IsOpen E) (ha : a ∈ E) (hG : ContDiffOn ℝ 1 G E)
    (hGa : HasFDerivAt G (ContinuousLinearMap.id ℝ (Euc n)) a) :
    ∃ e : OpenPartialHomeomorph (Euc n) (Euc n),
      a ∈ e.source ∧ e.source ⊆ E ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      (∀ x ∈ e.target, (fderiv ℝ e.symm x).IsInvertible) ∧
      ∀ x ∈ e.source, e x = G x := by
  let I : Euc n ≃L[ℝ] Euc n := ContinuousLinearEquiv.refl ℝ (Euc n)
  have hGa' : HasFDerivAt G (I : Euc n →L[ℝ] Euc n) a := hGa
  have hG_at : ContDiffAt ℝ 1 G a :=
    (hG a ha).contDiffAt (hE.mem_nhds ha)
  let e₀ := hG_at.toOpenPartialHomeomorph G hGa' (by norm_num)
  have ha₀ : a ∈ e₀.source :=
    hG_at.mem_toOpenPartialHomeomorph_source hGa' (by norm_num)
  have hderiv_cont : ContinuousAt (fderiv ℝ G) a :=
    hG_at.continuousAt_fderiv (by norm_num)
  have hinv_nhds : {x | ∃ L : Euc n ≃L[ℝ] Euc n,
      (L : Euc n →L[ℝ] Euc n) = fderiv ℝ G x} ∈ 𝓝 a := by
    have hI := I.nhds
    rw [show (I : Euc n →L[ℝ] Euc n) = fderiv ℝ G a by
      exact hGa'.fderiv.symm] at hI
    exact hderiv_cont.preimage_mem_nhds hI
  obtain ⟨W, hWsub, hWopen, haW⟩ := mem_nhds_iff.mp hinv_nhds
  let D := E ∩ W
  have hDopen : IsOpen D := hE.inter hWopen
  let e₁ := e₀.restrOpen D hDopen
  have ha₁ : a ∈ e₁.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨ha₀, ha, haW⟩
  have hsource₁ : e₁.source ⊆ E := by
    intro x hx
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    exact hx.2.1
  have he₁G : (e₁ : Euc n → Euc n) = G := by simp [e₁, e₀]
  have he₁ : ContDiffOn ℝ 1 e₁ e₁.source := by
    simpa only [he₁G] using hG.mono hsource₁
  have he₁inv : ContDiffOn ℝ 1 e₁.symm e₁.target := by
    intro y hy
    have hxsource : e₁.symm y ∈ e₁.source := e₁.mapsTo_symm hy
    have hxD : e₁.symm y ∈ D := by
      rw [OpenPartialHomeomorph.restrOpen_source] at hxsource
      exact hxsource.2
    obtain ⟨L, hL⟩ := hWsub hxD.2
    have hGx : ContDiffAt ℝ 1 G (e₁.symm y) :=
      (hG _ hxD.1).contDiffAt (hE.mem_nhds hxD.1)
    have hderiv : HasFDerivAt e₁ (L : Euc n →L[ℝ] Euc n) (e₁.symm y) := by
      rw [he₁G, hL]
      exact (hGx.differentiableAt (by norm_num)).hasFDerivAt
    exact (e₁.contDiffAt_symm hy hderiv (by simpa only [he₁G] using hGx)).contDiffWithinAt
  have hHinv : ∀ y ∈ e₁.target, (fderiv ℝ e₁.symm y).IsInvertible := by
    intro y hy
    have hxsource : e₁.symm y ∈ e₁.source := e₁.mapsTo_symm hy
    have hxD : e₁.symm y ∈ D := by
      rw [OpenPartialHomeomorph.restrOpen_source] at hxsource
      exact hxsource.2
    obtain ⟨L, hL⟩ := hWsub hxD.2
    have hGx : ContDiffAt ℝ 1 G (e₁.symm y) :=
      (hG _ hxD.1).contDiffAt (hE.mem_nhds hxD.1)
    have hderiv : HasFDerivAt e₁ (L : Euc n →L[ℝ] Euc n) (e₁.symm y) := by
      rw [he₁G, hL]
      exact (hGx.differentiableAt (by norm_num)).hasFDerivAt
    have hsymm := e₁.hasFDerivAt_symm hy hderiv
    rw [hsymm.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  exact ⟨e₁, ha₁, hsource₁, he₁, he₁inv, hHinv,
    fun x hx ↦ by rw [he₁G]⟩

/-- 将局部微分同胚的目标限制到包含基点像的开球；新目标凸，其他性质保持不变。
@isnad1 id=ex.6h5v.s12.44eb35be575a from=translated src=- shape=d159a5dc vocab=3c435616
-/
lemma rudin_restrict_target_to_convex_ball
    {E : Set (Euc n)} {G : Euc n → Euc n} {a : Euc n}
    (e₁ : OpenPartialHomeomorph (Euc n) (Euc n))
    (ha : a ∈ e₁.source) (hsource : e₁.source ⊆ E)
    (he : ContDiffOn ℝ 1 e₁ e₁.source)
    (heinv : ContDiffOn ℝ 1 e₁.symm e₁.target)
    (hHinv : ∀ x ∈ e₁.target, (fderiv ℝ e₁.symm x).IsInvertible)
    (heG : ∀ x ∈ e₁.source, e₁ x = G x) :
    ∃ e : OpenPartialHomeomorph (Euc n) (Euc n),
      a ∈ e.source ∧ e.source ⊆ E ∧ Convex ℝ e.target ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      (∀ x ∈ e.target, (fderiv ℝ e.symm x).IsInvertible) ∧
      ∀ x ∈ e.source, e x = G x := by
  have hmapa : e₁ a ∈ e₁.target := e₁.map_source ha
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e₁.open_target (e₁ a) hmapa
  let B := Metric.ball (e₁ a) ε
  let e := (e₁.symm.restrOpen B Metric.isOpen_ball).symm
  have htarget : e.target = B := by
    rw [show e.target = e₁.target ∩ B by simp [e]]
    exact inter_eq_right.mpr hball
  have hcoe : (e : Euc n → Euc n) = e₁ := by simp [e]
  have hcoeinv : (e.symm : Euc n → Euc n) = e₁.symm := by simp [e]
  have hae : a ∈ e.source := by
    have hBa : e₁ a ∈ B := Metric.mem_ball_self hε
    simpa [e, B, ha] using hBa
  have hsource_e1 : e.source ⊆ e₁.source := by
    intro x hx
    have hx' : x ∈ e₁.source ∧ e₁ x ∈ B := by simpa [e] using hx
    exact hx'.1
  refine ⟨e, hae, (fun x hx ↦ hsource (hsource_e1 hx)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [htarget]
    exact convex_ball _ _
  · simpa only [hcoe] using he.mono hsource_e1
  · rw [hcoeinv]
    exact heinv.mono (by rw [htarget]; exact hball)
  · intro x hx
    rw [hcoeinv]
    have hxB : x ∈ B := by rw [← htarget]; exact hx
    exact hHinv x (hball hxB)
  · intro x hx
    rw [hcoe]
    exact heG x (hsource_e1 hx)

/-- 反函数定理与缩邻域步骤：把 `G'(a)=I` 提升为局部 `C¹` 双射，并将目标缩成凸球。
@isnad1 id=ex.4h4v.s11.e49bc8c7f397 from=translated src=- shape=c053a553 vocab=0d894549
-/
lemma rudin_shrink_local_diffeomorph
    {E : Set (Euc n)} {G : Euc n → Euc n} {a : Euc n}
    (hE : IsOpen E) (ha : a ∈ E) (hG : ContDiffOn ℝ 1 G E)
    (hGa : HasFDerivAt G (ContinuousLinearMap.id ℝ (Euc n)) a) :
    ∃ e : OpenPartialHomeomorph (Euc n) (Euc n),
      a ∈ e.source ∧ e.source ⊆ E ∧ Convex ℝ e.target ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      (∀ x ∈ e.target, (fderiv ℝ e.symm x).IsInvertible) ∧
      ∀ x ∈ e.source, e x = G x := by
  obtain ⟨e₁, ha₁, hsource, he, heinv, hHinv, heG⟩ :=
    rudin_local_diffeomorph_near hE ha hG hGa
  exact rudin_restrict_target_to_convex_ball e₁ ha₁ hsource he heinv hHinv heG

/-- Rudin 公式 (69)：`G(x)=x+SP(F(x)-Ax)` 在 `a` 附近给出局部 `C¹` 坐标变换。
其局部逆记作 `H=e.symm`；目标邻域被缩小为凸集，以便随后沿线段积分。
@isnad1 id=ex.7h8v.s14.953a2435fa66 from=translated src=- shape=4c668770 vocab=6da6ebb5
-/
lemma rudin_coordinate_change
    {E : Set (Euc n)} {F : Euc n → Euc m} {a : Euc n}
    (hE : IsOpen E) (ha : a ∈ E) (hF : ContDiffOn ℝ 1 F E)
    (A : Euc n →L[ℝ] Euc m) (hA : HasFDerivAt F A a)
    (P : Euc m →L[ℝ] Euc m) (hP : P.comp P = P)
    (hPrange : P.range = A.range)
    (S : A.range →L[ℝ] Euc n) (hS : ∀ y : A.range, A (S y) = y) :
    ∃ e : OpenPartialHomeomorph (Euc n) (Euc n),
      a ∈ e.source ∧ e.source ⊆ E ∧ Convex ℝ e.target ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      (∀ x ∈ e.target, (fderiv ℝ e.symm x).IsInvertible) ∧
      (∀ x ∈ e.source,
        e x = x + S ⟨P (F x - A x), by
          rw [← hPrange]
          exact LinearMap.mem_range_self (P : Euc m →ₗ[ℝ] Euc m) (F x - A x)⟩) ∧
      ∀ x ∈ e.target, P (F (e.symm x)) = A x := by
  obtain ⟨G, hGdef, hG, hGa, hAG⟩ :=
    rudin_coordinate_map hF A hA P hP hPrange S hS
  obtain ⟨e, hae, hsource, hconv, he, heinv, hHinv, heG⟩ :=
    rudin_shrink_local_diffeomorph hE ha hG hGa
  refine ⟨e, hae, hsource, hconv, he, heinv, hHinv, ?_, ?_⟩
  · intro x hx
    rw [heG x hx, hGdef]
  · intro x hx
    have hxsource : e.symm x ∈ e.source := e.mapsTo_symm hx
    have h := hAG (e.symm x) (hsource hxsource)
    rw [← heG (e.symm x) hxsource, e.right_inv hx] at h
    exact h.symm

/-- Rudin 公式 (75)--(78) 的微分核心：若 `Φ=F∘H` 的秩与 `A` 相同且
`P ∘ Φ' = A`，则 `ker A ⊆ ker Φ'`。
@isnad1 id=eq.5h7v.s12.2f1c0f958dc7 from=translated src=- shape=d4ef5242 vocab=5878282c
-/
lemma transformed_derivative_vanishes_on_kernel
    (A : Euc n →L[ℝ] Euc m) (P : Euc m →L[ℝ] Euc m)
    (L : Euc n →L[ℝ] Euc m)
    (hPrange : P.range = A.range)
    (hrankA : Module.finrank ℝ A.range = r)
    (hrankL : Module.finrank ℝ L.range = r)
    (hcomp : P.comp L = A) :
    ∀ h, A h = 0 → L h = 0 := by
  let q : L.range →ₗ[ℝ] A.range :=
    (P : Euc m →ₗ[ℝ] Euc m).domRestrict L.range |>.codRestrict A.range (by
      intro z
      rw [← hPrange]
      exact LinearMap.mem_range_self (P : Euc m →ₗ[ℝ] Euc m) z)
  have hqsurj : Function.Surjective q := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    refine ⟨⟨L x, LinearMap.mem_range_self (L : Euc n →ₗ[ℝ] Euc m) x⟩, ?_⟩
    apply Subtype.ext
    have hx := DFunLike.congr_fun hcomp x
    change P (L x) = A x at hx
    exact hx
  have hdim : Module.finrank ℝ L.range = Module.finrank ℝ A.range :=
    hrankL.trans hrankA.symm
  have hqinj : Function.Injective q :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hqsurj
  intro h hAh
  apply Subtype.ext_iff.mp (hqinj (a₁ :=
    ⟨L h, LinearMap.mem_range_self (L : Euc n →ₗ[ℝ] Euc m) h⟩) (a₂ := 0) ?_)
  apply Subtype.ext
  have hh := DFunLike.congr_fun hcomp h
  change P (L h) = A h at hh
  change P (L h) = P 0
  simpa using hh.trans hAh

/-- Rudin 公式 (77)--(78) 的链式法则步骤：纤维端点之间的线段函数导数恒为零。
@isnad1 id=hasderiv.8h8v.s12.17784820576c from=translated src=- shape=cdf86691 vocab=4e8ce842
-/
lemma fiber_path_hasDerivAt_zero
    {V : Set (Euc n)} (hVopen : IsOpen V) (hV : Convex ℝ V)
    {ψ : Euc n → Euc m} (hψ : DifferentiableOn ℝ ψ V)
    (A : Euc n →L[ℝ] Euc m)
    (hker : ∀ x ∈ V, ∀ h, A h = 0 → fderiv ℝ ψ x h = 0)
    {x₁ x₂ : Euc n} (hx₁ : x₁ ∈ V) (hx₂ : x₂ ∈ V) (hAx : A x₁ = A x₂) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ ψ (AffineMap.lineMap x₁ x₂ s)) 0 t := by
  intro t ht
  have hzt : AffineMap.lineMap x₁ x₂ t ∈ V := hV.lineMap_mem hx₁ hx₂ ht
  have hψt : DifferentiableAt ℝ ψ (AffineMap.lineMap x₁ x₂ t) :=
    (hψ _ hzt).differentiableAt (hVopen.mem_nhds hzt)
  have hA_sub : A (x₂ - x₁) = 0 := by
    rw [map_sub, hAx, sub_self]
  have hzero : fderiv ℝ ψ (AffineMap.lineMap x₁ x₂ t) (x₂ - x₁) = 0 :=
    hker _ hzt _ hA_sub
  change HasDerivAt (ψ ∘ AffineMap.lineMap x₁ x₂) 0 t
  exact (hψt.hasFDerivAt.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap).congr_deriv hzero

/-- 一元中值定理步骤：闭区间上导数恒为零时，两端函数值相同。
@isnad1 id=eq.1h2v.s8.9141bbf47f6a from=translated src=- shape=ec75a20a vocab=c37a8f16
-/
lemma interval_endpoints_eq_of_hasDerivAt_zero
    {g : ℝ → Euc m}
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g 0 t) :
    g 0 = g 1 := by
  apply (convex_Icc (0 : ℝ) 1).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ)
  · intro t ht
    exact (hg t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hg t ht).hasFDerivAt.hasFDerivWithinAt.fderivWithin
      ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt ht)]
    exact ContinuousLinearMap.toSpanSingleton_zero ℝ
  · exact left_mem_Icc.mpr zero_le_one
  · exact right_mem_Icc.mpr zero_le_one

/-- 在开凸集 `V` 上，若 `ψ'` 消灭 `ker A`，则 `ψ` 在 `A` 的每条纤维上为常值；
这是 Rudin 的公式 (74)。
@isnad1 id=eq.7h7v.s11.1d0b84ba6910 from=translated src=- shape=45ec003d vocab=68e32e43
-/
lemma residual_constant_on_fibers
    {V : Set (Euc n)} (hVopen : IsOpen V) (hV : Convex ℝ V)
    {ψ : Euc n → Euc m} (hψ : DifferentiableOn ℝ ψ V)
    (A : Euc n →L[ℝ] Euc m)
    (hker : ∀ x ∈ V, ∀ h, A h = 0 → fderiv ℝ ψ x h = 0) :
    ∀ ⦃x₁⦄, x₁ ∈ V → ∀ ⦃x₂⦄, x₂ ∈ V → A x₁ = A x₂ → ψ x₁ = ψ x₂ := by
  intro x₁ hx₁ x₂ hx₂ hAx
  have hpath := fiber_path_hasDerivAt_zero hVopen hV hψ A hker hx₁ hx₂ hAx
  have hend := interval_endpoints_eq_of_hasDerivAt_zero hpath
  simpa using hend

/-- Rudin 公式 (79)--(80)：纤维常值的 `ψ` 唯一下降为 `A(V)` 上取值于 `ker P`
的 `C¹` 映射 `φ`。
@isnad1 id=ex.5h7v.s14.2465df46e71e from=translated src=- shape=cdbddf7b vocab=da4c0b23
-/
lemma residual_descends_contDiff
    {V : Set (Euc n)} (hVopen : IsOpen V)
    {ψ : Euc n → Euc m} (hψ : ContDiffOn ℝ 1 ψ V)
    (A : Euc n →L[ℝ] Euc m) (P : Euc m →L[ℝ] Euc m)
    (S : A.range →L[ℝ] Euc n) (hS : ∀ y : A.range, A (S y) = y)
    (hψker : ∀ x ∈ V, P (ψ x) = 0)
    (hfiber : ∀ ⦃x₁⦄, x₁ ∈ V → ∀ ⦃x₂⦄, x₂ ∈ V →
      A x₁ = A x₂ → ψ x₁ = ψ x₂) :
    ∃ φ : A.range → P.ker,
      ContDiffOn ℝ 1 φ {y | (y : Euc m) ∈ A '' V} ∧
      ∀ x ∈ V, (φ ⟨A x, LinearMap.mem_range_self (A : Euc n →ₗ[ℝ] Euc m) x⟩ : Euc m) = ψ x := by
  classical
  let pick : A.range → Euc n := fun y ↦
    if hy : (y : Euc m) ∈ A '' V then Classical.choose hy else 0
  let φ : A.range → P.ker := fun y ↦ P.ker.orthogonalProjectionOnto (ψ (pick y))
  have hpick_mem (y : A.range) (hy : (y : Euc m) ∈ A '' V) : pick y ∈ V := by
    simp only [pick, dite_eq_left hy]
    exact (Classical.choose_spec hy).1
  have hA_pick (y : A.range) (hy : (y : Euc m) ∈ A '' V) : A (pick y) = y := by
    simp only [pick, dite_eq_left hy]
    exact (Classical.choose_spec hy).2
  have hφeq : ∀ x ∈ V,
      (φ ⟨A x, LinearMap.mem_range_self (A : Euc n →ₗ[ℝ] Euc m) x⟩ : Euc m) = ψ x := by
    intro x hx
    let y : A.range := ⟨A x, LinearMap.mem_range_self (A : Euc n →ₗ[ℝ] Euc m) x⟩
    have hy : (y : Euc m) ∈ A '' V := ⟨x, hx, rfl⟩
    have hp := hpick_mem y hy
    have hsame : ψ (pick y) = ψ x := hfiber hp hx (by simpa [y] using hA_pick y hy)
    change (P.ker.orthogonalProjectionOnto (ψ (pick y)) : Euc m) = ψ x
    rw [hsame]
    exact congr_arg Subtype.val
      (P.ker.orthogonalProjectionOnto_mem_subspace_eq_self ⟨ψ x, hψker x hx⟩)
  refine ⟨φ, ?_, hφeq⟩
  intro y hy
  obtain ⟨x₀, hx₀, hAx₀⟩ := hy
  let qarg : A.range → Euc n := fun z ↦ x₀ + S (z - y)
  let q : A.range → P.ker := fun z ↦ P.ker.orthogonalProjectionOnto (ψ (qarg z))
  have hqarg_y : qarg y = x₀ := by simp [qarg]
  have hψ_at : ContDiffAt ℝ 1 ψ x₀ :=
    (hψ x₀ hx₀).contDiffAt (hVopen.mem_nhds hx₀)
  have hqarg : ContDiff ℝ 1 qarg := by fun_prop
  have hψ_qarg : ContDiffAt ℝ 1 ψ (qarg y) := by rwa [hqarg_y]
  have hq_at : ContDiffAt ℝ 1 q y := by
    exact P.ker.orthogonalProjectionOnto.contDiff.contDiffAt.comp y
      (hψ_qarg.comp y hqarg.contDiffAt)
  apply hq_at.contDiffWithinAt.congr_of_eventuallyEq
  · have hev : ∀ᶠ z in 𝓝 y, qarg z ∈ V :=
      hqarg.continuous.continuousAt (by rw [hqarg_y]; exact hVopen.mem_nhds hx₀)
    have hevWithin : ∀ᶠ z in 𝓝[{y | (y : Euc m) ∈ A '' V}] y, qarg z ∈ V :=
      Filter.Eventually.filter_mono inf_le_left hev
    filter_upwards [hevWithin] with z hz
    have hAz : A (qarg z) = z := by
      simp [qarg, map_add, hS, hAx₀]
    have heq := hφeq (qarg z) hz
    apply Subtype.ext
    have hsub : (⟨A (qarg z), LinearMap.mem_range_self
        (A : Euc n →ₗ[ℝ] Euc m) (qarg z)⟩ : A.range) = z := Subtype.ext hAz
    rw [hsub] at heq
    change (φ z : Euc m) = (P.ker.orthogonalProjectionOnto (ψ (qarg z)) : Euc m)
    rw [heq]
    exact congr_arg Subtype.val
      (P.ker.orthogonalProjectionOnto_mem_subspace_eq_self
        ⟨ψ (qarg z), hψker (qarg z) hz⟩).symm
  · apply Subtype.ext
    have hsub : (⟨A x₀, LinearMap.mem_range_self
        (A : Euc n →ₗ[ℝ] Euc m) x₀⟩ : A.range) = y := Subtype.ext hAx₀
    have heq := hφeq x₀ hx₀
    rw [hsub] at heq
    change (φ y : Euc m) = (q y : Euc m)
    rw [heq]
    change ψ x₀ = (P.ker.orthogonalProjectionOnto (ψ (qarg y)) : Euc m)
    rw [hqarg_y]
    exact congr_arg Subtype.val
      (P.ker.orthogonalProjectionOnto_mem_subspace_eq_self
        ⟨ψ x₀, hψker x₀ hx₀⟩).symm

/-- 公式 (72) 中剩余项 `ψ=F∘H-A` 仍为 `C¹`。
@isnad1 id=contdiff.3h6v.s10.305e0d02030e from=translated src=- shape=6d2e79b5 vocab=f1f523dd
-/
lemma residual_contDiff
    {E : Set (Euc n)} {F : Euc n → Euc m}
    {e : OpenPartialHomeomorph (Euc n) (Euc n)}
    (hsource : e.source ⊆ E) (hF : ContDiffOn ℝ 1 F E)
    (heinv : ContDiffOn ℝ 1 e.symm e.target)
    (A : Euc n →L[ℝ] Euc m) :
    ContDiffOn ℝ 1 (fun x ↦ F (e.symm x) - A x) e.target := by
  have hcomp : ContDiffOn ℝ 1 (fun x ↦ F (e.symm x)) e.target :=
    (hF.mono hsource).comp (fun x hx ↦ heinv x hx) e.mapsTo_symm
  exact hcomp.sub A.contDiff.contDiffOn

/-- 由 Rudin 公式 (71) `PF(Hx)=Ax` 与 `PA=A`，剩余项 `ψ` 取值于 `ker P`。
@isnad1 id=eq.3h7v.s11.02e0271edbbc from=translated src=- shape=69c8246b vocab=4131db79
-/
lemma residual_mem_projection_kernel
    {F : Euc n → Euc m} {e : OpenPartialHomeomorph (Euc n) (Euc n)}
    (A : Euc n →L[ℝ] Euc m) (P : Euc m →L[ℝ] Euc m)
    (hPA : P.comp A = A)
    (hproj : ∀ x ∈ e.target, P (F (e.symm x)) = A x) :
    ∀ x ∈ e.target, P (F (e.symm x) - A x) = 0 := by
  intro x hx
  rw [map_sub, hproj x hx]
  have hPAx := DFunLike.congr_fun hPA x
  rw [ContinuousLinearMap.comp_apply] at hPAx
  rw [hPAx, sub_self]

/-- 将公式 (75)--(78) 专门应用于 `Φ=F∘H` 和 `ψ=Φ-A`，得到
`ker A ⊆ ker ψ'(x)`。
@isnad1 id=eq.11h10v.s13.85bda09921b5 from=translated src=- shape=152c698f vocab=c17b0a49
-/
lemma rudin_residual_derivative_vanishes
    {E : Set (Euc n)} {F : Euc n → Euc m}
    {e : OpenPartialHomeomorph (Euc n) (Euc n)}
    (hE : IsOpen E) (hsource : e.source ⊆ E) (hF : ContDiffOn ℝ 1 F E)
    (heinv : ContDiffOn ℝ 1 e.symm e.target)
    (hHinv : ∀ x ∈ e.target, (fderiv ℝ e.symm x).IsInvertible)
    (A : Euc n →L[ℝ] Euc m) (P : Euc m →L[ℝ] Euc m)
    (hPrange : P.range = A.range)
    (hrankA : Module.finrank ℝ A.range = r)
    (hrank : ∀ x ∈ E, Module.finrank ℝ (fderiv ℝ F x).range = r)
    (hproj : ∀ x ∈ e.target, P (F (e.symm x)) = A x) :
    ∀ x ∈ e.target, ∀ h, A h = 0 →
      fderiv ℝ (fun z ↦ F (e.symm z) - A z) x h = 0 := by
  intro x hx h hAh
  have hxsource : e.symm x ∈ e.source := e.mapsTo_symm hx
  have hxE : e.symm x ∈ E := hsource hxsource
  have hHdiff : DifferentiableAt ℝ e.symm x :=
    ((heinv.differentiableOn (by norm_num)) x hx).differentiableAt
      (e.open_target.mem_nhds hx)
  have hFdiff : DifferentiableAt ℝ F (e.symm x) :=
    ((hF.differentiableOn (by norm_num)) _ hxE).differentiableAt
      (hE.mem_nhds hxE)
  let Φ : Euc n → Euc m := fun z ↦ F (e.symm z)
  let L : Euc n →L[ℝ] Euc m := fderiv ℝ Φ x
  have hLcomp : L = (fderiv ℝ F (e.symm x)).comp (fderiv ℝ e.symm x) := by
    exact fderiv_comp x hFdiff hHdiff
  have hrangeL : L.range = (fderiv ℝ F (e.symm x)).range := by
    rw [hLcomp]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (hHinv x hx).surjective)
  have hrankL : Module.finrank ℝ L.range = r := by
    rw [hrangeL]
    exact hrank _ hxE
  have hΦdiff : DifferentiableAt ℝ Φ x := hFdiff.comp x hHdiff
  have hlocal : (fun z ↦ P (Φ z)) =ᶠ[𝓝 x] fun z ↦ A z :=
    by
      filter_upwards [e.open_target.mem_nhds hx] with z hz
      exact hproj z hz
  have hcomp : P.comp L = A := by
    have hd := hlocal.fderiv_eq (𝕜 := ℝ)
    have hleft : fderiv ℝ (fun z ↦ P (Φ z)) x = P.comp L :=
      (P.hasFDerivAt.comp x hΦdiff.hasFDerivAt).fderiv
    have hright : fderiv ℝ (fun z ↦ A z) x = A := A.hasFDerivAt.fderiv
    rwa [hleft, hright] at hd
  have hLzero : L h = 0 :=
    transformed_derivative_vanishes_on_kernel A P L hPrange hrankA hrankL hcomp h hAh
  have hres : fderiv ℝ (fun z ↦ Φ z - A z) x = L - A :=
    (hΦdiff.hasFDerivAt.sub A.hasFDerivAt).fderiv
  change fderiv ℝ (fun z ↦ Φ z - A z) x h = 0
  rw [hres]
  change L h - A h = 0
  rw [hLzero, hAh, sub_zero]

/-- **Rudin 9.32 常秩定理**。`F` 在开集 `E ⊆ ℝⁿ` 上为 `C¹`，且导数处处具有
固定秩 `r`。令 `A=F'(a)`，并任选一个像为 `range A` 的投影 `P`。则存在局部 `C¹`
坐标变换 `H` 和取值于 `ker P` 的 `C¹` 映射 `φ`，使

`F(H(x)) = A x + φ(A x)`。

这里 `e.symm` 就是 Rudin 的 `H : V → U`，`e.source=U`、`e.target=V`。
@isnad1 id=ex.6h7v.s14.38afe57fbf2a from=translated src=- shape=e90e63b6 vocab=a9db0f46
-/
theorem constant_rank_theorem_rudin_9_32
    {E : Set (Euc n)} {F : Euc n → Euc m} {a : Euc n}
    (hE : IsOpen E) (ha : a ∈ E) (hF : ContDiffOn ℝ 1 F E)
    (hrank : ∀ x ∈ E, Module.finrank ℝ (fderiv ℝ F x).range = r)
    (P : Euc m →L[ℝ] Euc m) (hP : P.comp P = P)
    (hPrange : P.range = (fderiv ℝ F a).range) :
    ∃ e : OpenPartialHomeomorph (Euc n) (Euc n),
      a ∈ e.source ∧ e.source ⊆ E ∧ Convex ℝ e.target ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      ∃ φ : (fderiv ℝ F a).range → P.ker,
        ContDiffOn ℝ 1 φ
          {y | (y : Euc m) ∈ (fderiv ℝ F a) '' e.target} ∧
        ∀ x ∈ e.target,
          F (e.symm x) = fderiv ℝ F a x +
            (φ ⟨fderiv ℝ F a x,
              LinearMap.mem_range_self
                (fderiv ℝ F a : Euc n →ₗ[ℝ] Euc m) x⟩ : Euc m) := by
  let A := fderiv ℝ F a
  obtain ⟨S, hS⟩ := range_right_inverse A
  have hFa : HasFDerivAt F A a :=
    (((hF.differentiableOn (by norm_num)) a ha).differentiableAt (hE.mem_nhds ha)).hasFDerivAt
  obtain ⟨e, hae, hsource, hconv, he, heinv, hHinv, hG, hproj⟩ :=
    rudin_coordinate_change hE ha hF A hFa P hP hPrange S hS
  let ψ : Euc n → Euc m := fun x ↦ F (e.symm x) - A x
  have hψ : ContDiffOn ℝ 1 ψ e.target :=
    residual_contDiff hsource hF heinv A
  have hPA : P.comp A = A := by
    apply ContinuousLinearMap.ext
    intro x
    have hAx : A x ∈ P.range := by
      rw [hPrange]
      exact LinearMap.mem_range_self (A : Euc n →ₗ[ℝ] Euc m) x
    obtain ⟨y, hy⟩ := hAx
    rw [ContinuousLinearMap.comp_apply, ← hy]
    exact DFunLike.congr_fun hP y
  have hψker : ∀ x ∈ e.target, P (ψ x) = 0 :=
    residual_mem_projection_kernel A P hPA hproj
  have hrankA : Module.finrank ℝ A.range = r := hrank a ha
  have hderivker : ∀ x ∈ e.target, ∀ h, A h = 0 → fderiv ℝ ψ x h = 0 :=
    rudin_residual_derivative_vanishes hE hsource hF heinv hHinv A P hPrange hrankA hrank hproj
  have hfiber : ∀ ⦃x₁⦄, x₁ ∈ e.target → ∀ ⦃x₂⦄, x₂ ∈ e.target →
      A x₁ = A x₂ → ψ x₁ = ψ x₂ :=
    residual_constant_on_fibers e.open_target hconv
      (hψ.differentiableOn (by norm_num)) A hderivker
  obtain ⟨φ, hφ, hφeq⟩ :=
    residual_descends_contDiff e.open_target hψ A P S hS hψker hfiber
  refine ⟨e, hae, hsource, hconv, he, heinv, φ, hφ, ?_⟩
  intro x hx
  have := hφeq x hx
  dsimp [ψ] at this
  change F (e.symm x) = A x +
    (φ ⟨A x, LinearMap.mem_range_self (A : Euc n →ₗ[ℝ] Euc m) x⟩ : Euc m)
  rw [this]
  abel

end SandronesLibrary.Analysis.Multivariable
