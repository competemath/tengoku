/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.DifferentialForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 欧氏空间上微分形式的坐标表达式

本模块给出 `Euclid 空间` `Fin n → ℝ` 上 1、2、3 次微分形式的标准坐标展开：
坐标 1-形式 `dx_i`、坐标 2-形式 `dx_i ∧ dx_j`，以及一般形式在标准基上的分量展开。
它把 `analysis.multivariable.differential-forms` 中抽象的交替映射载体落到教材中
常见的坐标写法。

> **Entry**: analysis.forms.coordinate-expression
-/

noncomputable section

namespace SandronesLibrary.Analysis.FormCoordinateExpression

open SandronesLibrary.Analysis.DifferentialForms
open ContinuousAlternatingMap
open scoped TensorProduct

universe u

/-! ## 坐标形式 -/

/-- 坐标 1-形式 `dx_i`：常值形式，取值 `v ↦ v i`。-/
def coordinateForm {n : ℕ} (i : Fin n) : DifferentialForm (Fin n → ℝ) 1 :=
  fun _ => (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Fin n → ℝ) (F := ℝ)
    (0 : Fin 1)) (ContinuousLinearMap.proj i)

/-- 坐标 1-形式在单个切向量上的取值就是该向量的第 `i` 个坐标。
@isnad1 id=eq.0h4v.s8.58d42d3902d2 from=translated src=- shape=83c4e15b vocab=f8ff8b16
-/
@[simp]
theorem coordinateForm_apply {n : ℕ} (i : Fin n) (x : Fin n → ℝ) (v : Fin 1 → Fin n → ℝ) :
    coordinateForm i x v = v 0 i := by
  simp only [coordinateForm, ContinuousAlternatingMap.ofSubsingletonLIE_apply,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, ContinuousLinearMap.proj_apply]

/-! ## 两个 1 次交替映射的楔积 -/

/-- 两个 1 次交替映射的楔积在二元组上的显式取值。这是 `coordinateTwoForm_apply`
的核心技术引理：`k = l = 1` 时 shuffle 和只有两个置换类，逐项计算即可。
@isnad1 id=eq.0h4v.s9.6ed48c3f3791 from=translated src=- shape=eb5acd93 vocab=61242668
-/
theorem alternatingWedge_one_apply {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E [⋀^Fin 1]→ₗ[ℝ] ℝ) (v : Fin 2 → E) :
    alternatingWedge a b v =
      a (fun _ : Fin 1 => v 0) * b (fun _ : Fin 1 => v 1) -
        a (fun _ : Fin 1 => v 1) * b (fun _ : Fin 1 => v 0) := by
  rw [alternatingWedge, LinearMap.compAlternatingMap_apply, AlternatingMap.domDomCongr_apply]
  have hcond : (a.domCoprod b) = MultilinearMap.alternatization (MultilinearMap.domCoprod a b) := by
    have h := MultilinearMap.domCoprod_alternization_eq (a := a) (b := b)
    simpa using h.symm
  rw [hcond, MultilinearMap.alternatization_apply]
  let sw : Equiv.Perm (Fin 1 ⊕ Fin 1) := Equiv.swap (Sum.inl 0) (Sum.inr 0)
  let e : Fin 2 → Equiv.Perm (Fin 1 ⊕ Fin 1) := fun t => if t = 0 then 1 else sw
  have hcard : Fintype.card (Equiv.Perm (Fin 1 ⊕ Fin 1)) = 2 := by
    rw [Fintype.card_perm, Fintype.card_sum]
    simp
  have hne : (1 : Equiv.Perm (Fin 1 ⊕ Fin 1)) ≠ sw := by
    intro h
    have h2 := congrArg (fun σ : Equiv.Perm (Fin 1 ⊕ Fin 1) => σ (Sum.inl (0 : Fin 1))) h
    simp [sw] at h2
  have hinj : Function.Injective e := by
    intro t1 t2 h
    fin_cases t1 <;> fin_cases t2 <;> simp_all [e]
  have hbij : Function.Bijective e := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [hcard]; simp⟩
  let F : Equiv.Perm (Fin 1 ⊕ Fin 1) → ℝ ⊗[ℝ] ℝ :=
    fun σ => Equiv.Perm.sign σ •
      (MultilinearMap.domDomCongr σ (MultilinearMap.domCoprod a b)) (v ∘ finSumFinEquiv)
  have hsum : (∑ σ : Equiv.Perm (Fin 1 ⊕ Fin 1), F σ) = F (e 0) + F (e 1) := by
    rw [← Fintype.sum_bijective e hbij (fun t => F (e t)) F (fun t => rfl), Fin.sum_univ_two]
  have hF1 : F 1 = (a (fun _ : Fin 1 => v 0)) ⊗ₜ[ℝ] (b (fun _ : Fin 1 => v 1)) := by
    have hf1 : ∀ i : Fin 1,
        v (finSumFinEquiv ((1 : Equiv.Perm (Fin 1 ⊕ Fin 1)) (Sum.inl i))) = v 0 := by
      intro i; fin_cases i; rfl
    have hf2 : ∀ i : Fin 1,
        v (finSumFinEquiv ((1 : Equiv.Perm (Fin 1 ⊕ Fin 1)) (Sum.inr i))) = v 1 := by
      intro i; fin_cases i; rfl
    simp only [F, Equiv.Perm.sign_one, one_smul, MultilinearMap.domDomCongr_apply,
      MultilinearMap.domCoprod_apply, Function.comp_apply, hf1, hf2]
    rfl
  have hFsw : F (Equiv.swap (Sum.inl (0:Fin 1)) (Sum.inr (0:Fin 1))) =
      -((a (fun _ : Fin 1 => v 1)) ⊗ₜ[ℝ] (b (fun _ : Fin 1 => v 0))) := by
    have hg1 : ∀ i : Fin 1,
        v (finSumFinEquiv
          ((Equiv.swap (Sum.inl (0:Fin 1)) (Sum.inr (0:Fin 1))) (Sum.inl i))) = v 1 := by
      intro i; fin_cases i; simp; rfl
    have hg2 : ∀ i : Fin 1,
        v (finSumFinEquiv
          ((Equiv.swap (Sum.inl (0:Fin 1)) (Sum.inr (0:Fin 1))) (Sum.inr i))) = v 0 := by
      intro i; fin_cases i; simp; rfl
    simp only [F, MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply]
    rw [Equiv.Perm.sign_swap (by simp : Sum.inl (0:Fin 1) ≠ Sum.inr (0:Fin 1))]
    rw [Units.smul_def, show ((-1 : ℤˣ) : ℤ) = -1 by simp, neg_one_zsmul]
    simp only [Function.comp_apply, hg1, hg2]
    rfl
  change (TensorProduct.lid ℝ ℝ) (∑ σ, F σ) =
      a (fun _ : Fin 1 => v 0) * b (fun _ : Fin 1 => v 1) -
        a (fun _ : Fin 1 => v 1) * b (fun _ : Fin 1 => v 0)
  rw [hsum, map_add, show F (e 0) = F 1 by simp [e],
    show F (e 1) = F (Equiv.swap (Sum.inl (0:Fin 1)) (Sum.inr (0:Fin 1))) by simp [e, sw],
    hF1, hFsw, map_neg, TensorProduct.lid_tmul, TensorProduct.lid_tmul]
  ring

/-! ## 坐标 2-形式 -/

/-- 坐标 2-形式 `dx_i ∧ dx_j`。-/
def coordinateTwoForm {n : ℕ} (i j : Fin n) : DifferentialForm (Fin n → ℝ) 2 :=
  formWedge (coordinateForm i) (coordinateForm j)

/-- 坐标 2-形式在二元组上的取值是 `2×2` 子式。
@isnad1 id=eq.0h5v.s8.2c518387fa03 from=translated src=- shape=34d13392 vocab=367f8603
-/
theorem coordinateTwoForm_apply {n : ℕ} (i j : Fin n) (x : Fin n → ℝ) (v : Fin 2 → Fin n → ℝ) :
    coordinateTwoForm i j x v = v 0 i * v 1 j - v 1 i * v 0 j := by
  rw [coordinateTwoForm, formWedge_apply, alternatingWedge_one_apply]
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap, coordinateForm_apply]

/-! ## 展开 -/

/-- 1 次形式沿标准基的坐标展开。
@isnad1 id=eq.0h3v.s10.18dda8ec7713 from=translated src=- shape=7d497ca4 vocab=bc9d193c
-/
theorem oneForm_coordinate_expansion {n : ℕ} (ω : DifferentialForm (Fin n → ℝ) 1)
    (x : Fin n → ℝ) :
    ω x = ∑ i, (ω x ![Pi.single i 1]) • coordinateForm i x := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply Module.Basis.ext_alternating (Pi.basisFun ℝ (Fin n))
  intro v hv
  have hvec : (fun i : Fin 1 => (Pi.basisFun ℝ (Fin n)) (v i)) =
      ![Pi.single (v 0) (1:ℝ)] := by
    funext i; fin_cases i; simp [Pi.basisFun_apply]
  rw [hvec]
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, coordinateForm_apply]
  rw [Finset.sum_eq_single (v 0)]
  · simp [Pi.single_eq_same]
  · intro b _ hb
    rw [Matrix.cons_val_zero, Pi.single_eq_of_ne hb, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `ℝ²` 上 2 次形式沿唯一坐标 2-形式的展开。
@isnad1 id=eq.0h2v.s11.47771cbedb18 from=translated src=- shape=0d16a5d5 vocab=6774dd44
-/
theorem twoForm_coordinate_expansion_plane (ω : DifferentialForm (Fin 2 → ℝ) 2)
    (x : Fin 2 → ℝ) :
    ω x = (ω x ![Pi.single 0 1, Pi.single 1 1]) • coordinateTwoForm 0 1 x := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply Module.Basis.ext_alternating (Pi.basisFun ℝ (Fin 2))
  intro v hv
  have hvec : (fun i : Fin 2 => (Pi.basisFun ℝ (Fin 2)) (v i)) =
      ![Pi.single (v 0) (1:ℝ), Pi.single (v 1) (1:ℝ)] := by
    funext i; fin_cases i <;> simp [Pi.basisFun_apply]
  rw [hvec]
  have hclass : v = ![0, 1] ∨ v = ![1, 0] := by
    have h0 : v 0 = 0 ∨ v 0 = 1 := by
      generalize hv0 : v 0 = x
      fin_cases x <;> simp
    have h1 : v 1 ≠ v 0 := fun h => (by decide : (1:Fin 2) ≠ 0) (hv h)
    rcases h0 with h0 | h0
    · left
      funext i
      fin_cases i
      · exact h0
      · have : v 1 = 1 := by
          generalize hv1 : v 1 = y
          fin_cases y <;> simp_all
        simp [this]
    · right
      funext i
      fin_cases i
      · exact h0
      · have : v 1 = 0 := by
          generalize hv1 : v 1 = y
          fin_cases y <;> simp_all
        simp [this]
  rcases hclass with h | h
  · rw [h]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.smul_apply]
    rw [coordinateTwoForm_apply]
    simp
  · rw [h]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (![Pi.single (1:Fin 2) (1:ℝ), Pi.single (0:Fin 2) (1:ℝ)] : Fin 2 → Fin 2 → ℝ) =
        ![Pi.single (0:Fin 2) (1:ℝ), Pi.single (1:Fin 2) (1:ℝ)] ∘ Equiv.swap (0:Fin 2) 1 by
      funext i; fin_cases i <;> simp]
    rw [AlternatingMap.map_swap]
    · simp only [ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.smul_apply]
      rw [coordinateTwoForm_apply]
      simp
    · decide

/-- `Fin 2 → Fin 3` 的单射只有六个有序对。-/
private theorem fin_two_three_classification (v : Fin 2 → Fin 3) (hv : Function.Injective v) :
    (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 2) ∨ (v 0 = 1 ∧ v 1 = 0) ∨
    (v 0 = 1 ∧ v 1 = 2) ∨ (v 0 = 2 ∧ v 1 = 0) ∨ (v 0 = 2 ∧ v 1 = 1) := by
  have h0 : v 0 = 0 ∨ v 0 = 1 ∨ v 0 = 2 := by
    generalize h : v 0 = x; fin_cases x <;> simp
  have h1 : v 1 = 0 ∨ v 1 = 1 ∨ v 1 = 2 := by
    generalize h : v 1 = x; fin_cases x <;> simp
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1
  · exact absurd (hv (h0.trans h1.symm)) (by decide)
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr (Or.inl ⟨h0, h1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h0, h1⟩))
  · exact absurd (hv (h0.trans h1.symm)) (by decide)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, h1⟩))))
  · exact absurd (hv (h0.trans h1.symm)) (by decide)

/-- `ℝ³` 上 2 次形式沿坐标 2-形式族 `i < j` 的展开。
@isnad1 id=eq.0h2v.s11.04dad360cb5f from=translated src=- shape=0ebf0e85 vocab=5b81ecd3
-/
theorem twoForm_coordinate_expansion_space (ω : DifferentialForm (Fin 3 → ℝ) 2)
    (x : Fin 3 → ℝ) :
    ω x = ∑ p ∈ (Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 < p.2)),
      (ω x ![Pi.single p.1 1, Pi.single p.2 1]) • coordinateTwoForm p.1 p.2 x := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply Module.Basis.ext_alternating (Pi.basisFun ℝ (Fin 3))
  intro v hv
  have hvec : (fun i : Fin 2 => (Pi.basisFun ℝ (Fin 3)) (v i)) =
      ![Pi.single (v 0) (1:ℝ), Pi.single (v 1) (1:ℝ)] := by
    funext i; fin_cases i <;> simp [Pi.basisFun_apply]
  rw [hvec]
  have hfilter : (Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 < p.2)) =
      ({((0:Fin 3),(1:Fin 3)), ((0:Fin 3),(2:Fin 3)), ((1:Fin 3),(2:Fin 3))} :
        Finset (Fin 3 × Fin 3)) := by
    ext p
    rcases p with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> decide
  rw [hfilter]
  have hclass := fin_two_three_classification v hv
  rcases hclass with ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩
  · rw [h0, h1]
    simp only [ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.smul_apply, coordinateTwoForm_apply]
    simp
  · rw [h0, h1]
    simp only [ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.smul_apply, coordinateTwoForm_apply]
    simp
  · rw [h0, h1]
    conv_lhs => rw [show
      (![Pi.single (1:Fin 3) (1:ℝ), Pi.single (0:Fin 3) (1:ℝ)] : Fin 2 → Fin 3 → ℝ) =
        ![Pi.single (0:Fin 3) (1:ℝ), Pi.single (1:Fin 3) (1:ℝ)] ∘ Equiv.swap (0:Fin 2) 1 by
      funext i; fin_cases i <;> simp]
    rw [AlternatingMap.map_swap]
    · simp only [ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.sum_apply,
        ContinuousAlternatingMap.smul_apply, coordinateTwoForm_apply]
      simp
    · decide
  · rw [h0, h1]
    simp only [ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.smul_apply, coordinateTwoForm_apply]
    simp
  · rw [h0, h1]
    conv_lhs => rw [show
      (![Pi.single (2:Fin 3) (1:ℝ), Pi.single (0:Fin 3) (1:ℝ)] : Fin 2 → Fin 3 → ℝ) =
        ![Pi.single (0:Fin 3) (1:ℝ), Pi.single (2:Fin 3) (1:ℝ)] ∘ Equiv.swap (0:Fin 2) 1 by
      funext i; fin_cases i <;> simp]
    rw [AlternatingMap.map_swap]
    · simp only [ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.sum_apply,
        ContinuousAlternatingMap.smul_apply, coordinateTwoForm_apply]
      simp
    · decide
  · rw [h0, h1]
    conv_lhs => rw [show
      (![Pi.single (2:Fin 3) (1:ℝ), Pi.single (1:Fin 3) (1:ℝ)] : Fin 2 → Fin 3 → ℝ) =
        ![Pi.single (1:Fin 3) (1:ℝ), Pi.single (2:Fin 3) (1:ℝ)] ∘ Equiv.swap (0:Fin 2) 1 by
      funext i; fin_cases i <;> simp]
    rw [AlternatingMap.map_swap]
    · simp only [ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.sum_apply,
        ContinuousAlternatingMap.smul_apply, coordinateTwoForm_apply]
      simp
    · decide

/-- 体积形式的范数界：对 `Fin 3` 的 `Basis.det`，用行列式的置换展开给出常数 `6` 的估计。-/
private theorem basis_det_norm_bound (v : Fin 3 → (Fin 3 → ℝ)) :
    ‖(Pi.basisFun ℝ (Fin 3)).det v‖ ≤ 6 * ∏ i, ‖v i‖ := by
  have hmat : (Pi.basisFun ℝ (Fin 3)).toMatrix v = Matrix.of (fun i j : Fin 3 => v j i) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rfl
  rw [Module.Basis.det_apply, hmat, Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin 3), ‖Equiv.Perm.sign σ • ∏ i, v i (σ i)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin 3), ∏ i, ‖v i‖ := by
        apply Finset.sum_le_sum
        intro σ _
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · rw [h, Units.smul_def]
          simp only [Units.val_one, one_smul, norm_prod]
          exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
            (fun i _ => norm_le_pi_norm (v i) (σ i))
        · rw [h, Units.smul_def]
          rw [show ((-1 : ℤˣ) : ℤ) = -1 by simp, neg_one_zsmul, norm_neg, norm_prod]
          exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
            (fun i _ => norm_le_pi_norm (v i) (σ i))
    _ = 6 * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
        norm_num

/-- `ℝ³` 上的坐标 3-形式（体积形式），即标准基取向的行列式形式。-/
def coordinateThreeForm : DifferentialForm (Fin 3 → ℝ) 3 :=
  fun _ => ((Pi.basisFun ℝ (Fin 3)).det).mkContinuous 6 basis_det_norm_bound

/-- `ℝ³` 上 3 次形式沿体积形式的展开。
@isnad1 id=eq.0h2v.s11.ef3f39f3b51d from=translated src=- shape=c259353d vocab=cc32e931
-/
theorem threeForm_coordinate_expansion_space (ω : DifferentialForm (Fin 3 → ℝ) 3)
    (x : Fin 3 → ℝ) :
    ω x = (ω x ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1]) • coordinateThreeForm x := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [ContinuousAlternatingMap.toAlternatingMap_smul]
  have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin 3)) (ω x).toAlternatingMap
  rw [h]
  have hscalar : (ω x).toAlternatingMap (Pi.basisFun ℝ (Fin 3)) =
      ω x ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] := by
    rw [ContinuousAlternatingMap.coe_toAlternatingMap]
    congr 1
    funext i; fin_cases i <;> simp [Pi.basisFun_apply]
  rw [hscalar]
  congr 1

end SandronesLibrary.Analysis.FormCoordinateExpression
